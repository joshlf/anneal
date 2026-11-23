// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Milestone 5: ITree-strength strictly safe-Rust `syn` AST mutators
//! (`CallBoundaryOutliner`, `LayoutPaddingPerturber`, `BranchLoopWeaver`,
//! `ExtOracleInjector`, `IndirectDispatchOutliner`) plus
//! [`generate_itree_batch`] and [`annotate_itree_external_callees`].
//!
//! Enforces a hard zero-`unsafe` invariant: [`contains_unsafe_token`] verifies
//! that **zero** `unsafe` tokens appear anywhere in any emitted candidate
//! program. All arithmetic in generated bodies uses widening integer casts and
//! primitive operators (`((a as u64) + (b as u64)) as u32`) so `-Zmir-opt-level=0`
//! lowers them to pure MIR `CastKind::IntToInt` + `Rvalue::BinaryOp` +
//! `SwitchInt` + `TerminatorKind::Call` without unmodeled `core::num` or
//! `core::hint::black_box` intrinsic calls.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::visit::{self, Visit};
use syn::visit_mut::{self, VisitMut};
use syn::{Attribute, BinOp, Block, Expr, File, FnArg, Item, Lit, Pat, ReturnType, Stmt, Type};

pub use crate::input_gen::{
    ArgPinConstraint, ArgPinFallbackReason, ConcolicBranchGuard, ConcolicTrialPhase,
    ConcolicTrialPlan, RelaxPinResult, arg_pin_term, flip_branch_guard, neg_arg_pin_term,
    negate_arg_pin, pin_term, relax_pin_constraint,
};
use crate::input_gen::{MirInputDictionary, ScalarLayout, width_mask};
use crate::instrument::{EnvAction, EnvSchedule};
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

fn collect_u32_param_idents(func: &syn::ItemFn) -> Vec<Ident> {
    let mut idents = Vec::new();
    for input in &func.sig.inputs {
        if let FnArg::Typed(pat_ty) = input
            && matches!(
                pat_ty.ty.as_ref(),
                Type::Path(tp) if tp.qself.is_none() && tp.path.is_ident("u32")
            )
            && let Pat::Ident(pat_id) = pat_ty.pat.as_ref()
        {
            idents.push(pat_id.ident.clone());
        }
    }
    idents
}

fn first_u32_param_expr(func: &syn::ItemFn, fallback: u32) -> Expr {
    let idents = collect_u32_param_idents(func);
    if let Some(id) = idents.first() {
        return syn::parse_quote!(#id);
    }
    syn::parse_quote!(#fallback)
}

fn second_u32_param_expr(func: &syn::ItemFn, fallback: u32) -> Expr {
    let idents = collect_u32_param_idents(func);
    if let Some(id) = idents.get(1).or_else(|| idents.first()) {
        return syn::parse_quote!(#id);
    }
    syn::parse_quote!(#fallback)
}

fn combined_u32_param_expr(func: &syn::ItemFn, fallback: u32, shift: u32) -> Expr {
    let idents = collect_u32_param_idents(func);
    match idents.as_slice() {
        [p0, p1, ..] if shift > 0 => syn::parse_quote!(#p0 ^ (#p1 >> #shift)),
        [p0, p1, ..] => syn::parse_quote!(#p0 ^ #p1),
        [p0] => syn::parse_quote!(#p0),
        [] => syn::parse_quote!(#fallback),
    }
}

fn existing_itree_helper_depth(file: &File) -> usize {
    file.items
        .iter()
        .filter(|it| {
            matches!(
                it,
                Item::Fn(f)
                    if f.sig.ident.to_string().starts_with("__anneal_")
                        && !f.sig.ident.to_string().starts_with("__anneal_itree_outlined_stage2_")
            )
        })
        .count()
}

fn preamble_arg_shifts(file: &File) -> (u32, u32) {
    let pass_depth = existing_itree_helper_depth(file).min(5) as u32;
    let outer_shift = (pass_depth + 1) * 4;
    (outer_shift, outer_shift.saturating_sub(2))
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
        || existing.contains(&format!("__anneal_itree_indirect_{tag}"))
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

        let (outer_shift, inner_shift) = preamble_arg_shifts(file);
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
                let arg0_expr = first_u32_param_expr(func, k_const);
                let arg1_expr = second_u32_param_expr(func, k_const);
                let stage1_local = format_ident!("__itree_call_s1_{}", tag);
                let local_ident = format_ident!("__itree_call_res_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #stage1_local: u32 = #helper_ident(#arg0_expr, #arg1_expr >> #outer_shift);
                    let #local_ident: u32 = #stage2_ident(#stage1_local, (#arg1_expr >> #inner_shift) ^ #k_const);
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
                let arg0_expr = first_u32_param_expr(func, k_const);
                let arg1_expr = second_u32_param_expr(func, k_const);
                let local_ident = format_ident!("__itree_call_res_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #local_ident: u32 = #helper_ident(#arg0_expr, #arg1_expr >> #outer_shift);
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

        let (outer_shift, _) = preamble_arg_shifts(file);
        let target_idx = target_fn_index(file);
        if let Some(idx) = target_idx
            && let Item::Fn(func) = &mut file.items[idx]
        {
            let arg_expr = combined_u32_param_expr(func, mask, outer_shift);
            let ans_ident = format_ident!("__itree_oracle_ans_{}", tag);
            let injected: Vec<Stmt> = syn::parse_quote! {
                let #ans_ident: u32 = #oracle_ident(#arg_expr);
            };
            weave_into_fn_body(func, injected, &ans_ident);
        }

        file.items.push(oracle_item);
    }
}

/// 5. Outlines an indirect-call computation across a real function call
/// boundary: a top-level safe helper `__anneal_itree_indirect_<tag>(seed, delta)`
/// whose body is one of
/// - `&T as &dyn Trait` unsizing for two traits, a virtual call through each
///   vtable, and `core::ptr::addr_eq` on the two trait-object references (one
///   data address, two vtables);
/// - a call through a `fn(u32, u32) -> u32` pointer chosen at run time between
///   two nested functions, then through a pointer coerced from a non-capturing
///   closure;
/// - closures capturing a local by shared reference, by value (`move`), and by
///   unique reference (an `FnMut` closure called twice);
/// - `core::ptr::addr_eq` on slice references into one array that share a data
///   address but differ in length, and on two that start at different elements.
///
/// The root function only calls the helper, so `TraceCheck` sees one boundary
/// call with `u32` arguments and a `u32` return. Every trait, `impl`, struct,
/// and function the helper needs is declared inside its body, so a candidate
/// gains exactly one top-level item and nothing for
/// [`stage_itree_candidate_items`] to prefix other than that function. The
/// helper never panics and never returns `0`, and it derives its arguments
/// from the root's parameters as [`CallBoundaryOutliner`] does, so the argument
/// freedom of the boundary calls woven in before it is preserved.
#[derive(Debug, Default, Clone, Copy)]
pub struct IndirectDispatchOutliner;

impl ItreeAstMutator for IndirectDispatchOutliner {
    fn name(&self) -> &'static str {
        "IndirectDispatchOutliner"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let raw_tag = rng.next_u64();
        let tag = disambiguate_itree_tag(file, raw_tag);
        let variant = (raw_tag >> 16) % 4;
        let helper_ident = format_ident!("__anneal_itree_indirect_{}", tag);
        let k_const = ((rng.next_u64() % 251) as u32).wrapping_add(1);

        let helper_item: Item = match variant {
            0 => syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    trait AnnealDynProbe {
                        fn probe(&self, x: u32) -> u32;
                        fn stamp(&self) -> u32;
                    }
                    trait AnnealDynAlt {
                        fn alt(&self) -> u32;
                    }
                    struct AnnealDynHolderA {
                        bias: u32,
                    }
                    struct AnnealDynHolderB {
                        pad: u32,
                        bias: u32,
                    }
                    impl AnnealDynProbe for AnnealDynHolderA {
                        fn probe(&self, x: u32) -> u32 {
                            (x >> 1) ^ (self.bias & 0xFFFFu32)
                        }
                        fn stamp(&self) -> u32 {
                            (self.bias & 0x3Fu32) ^ 0x15u32
                        }
                    }
                    impl AnnealDynProbe for AnnealDynHolderB {
                        fn probe(&self, x: u32) -> u32 {
                            ((x >> 2) ^ self.pad) ^ (self.bias & 0xFFFFu32)
                        }
                        fn stamp(&self) -> u32 {
                            ((self.pad ^ self.bias) & 0x3Fu32) ^ 0x2Au32
                        }
                    }
                    impl AnnealDynAlt for AnnealDynHolderA {
                        fn alt(&self) -> u32 {
                            (self.bias >> 3) & 0x7Fu32
                        }
                    }
                    let holder = AnnealDynHolderA { bias: delta ^ #k_const };
                    let other = AnnealDynHolderB {
                        pad: (seed & 0xFFu32) ^ #k_const,
                        bias: (delta >> 1) ^ #k_const,
                    };
                    let as_probe: &dyn AnnealDynProbe = &holder as &dyn AnnealDynProbe;
                    let other_probe: &dyn AnnealDynProbe = &other as &dyn AnnealDynProbe;
                    let as_alt: &dyn AnnealDynAlt = &holder as &dyn AnnealDynAlt;
                    let picked: &dyn AnnealDynProbe = if (seed & 1u32) == 0u32 {
                        as_probe
                    } else {
                        other_probe
                    };
                    let dispatched: u32 = picked.probe(seed) ^ picked.stamp();
                    let alt_bits: u32 = as_alt.alt();
                    let same_bit: u32 = if core::ptr::addr_eq(as_probe, as_alt) {
                        2u32
                    } else {
                        0u32
                    };
                    let diff_bit: u32 = if core::ptr::addr_eq(as_probe, other_probe) {
                        0u32
                    } else {
                        4u32
                    };
                    let mix: u32 = (dispatched << 3) ^ (alt_bits << 3) ^ same_bit ^ diff_bit;
                    (mix >> 1) + #k_const
                }
            },
            1 => syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    fn anneal_fnptr_mix(a: u32, b: u32) -> u32 {
                        (a >> 1) ^ (b & 0xFFFFu32)
                    }
                    fn anneal_fnptr_fold(a: u32, b: u32) -> u32 {
                        (a & 0xFFFF_FF00u32) | ((b >> 2) & 0xFFu32)
                    }
                    let op: fn(u32, u32) -> u32 = if (seed & 1u32) == 0u32 {
                        anneal_fnptr_mix
                    } else {
                        anneal_fnptr_fold
                    };
                    let lifted: fn(u32, u32) -> u32 = |a: u32, b: u32| (a ^ b) >> 1;
                    let raw_op: *const () = op as *const ();
                    let raw_lifted: *const () = lifted as *const ();
                    let raw_seed: *const u32 = &seed as *const u32;
                    let same_op: u32 = if core::ptr::addr_eq(raw_op, op as *const ()) {
                        2u32
                    } else {
                        0u32
                    };
                    let same_lifted: u32 = if core::ptr::addr_eq(raw_lifted, lifted as *const ()) {
                        4u32
                    } else {
                        0u32
                    };
                    let diff_stack: u32 = if core::ptr::addr_eq(raw_op, raw_seed) {
                        0u32
                    } else {
                        8u32
                    };
                    let first: u32 = op(seed, delta);
                    let second: u32 = lifted(first, #k_const);
                    let combined: u32 = (second << 4) ^ same_op ^ same_lifted ^ diff_stack;
                    (combined >> 1) + #k_const
                }
            },
            2 => syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    let bias: u32 = (delta & 0xFFFFu32) ^ #k_const;
                    let bias_ref: &u32 = &bias;
                    let by_ref = |x: u32| {
                        let same: u32 = if core::ptr::addr_eq(&bias, bias_ref) {
                            8u32
                        } else {
                            0u32
                        };
                        ((x >> 1) ^ (*bias_ref)) ^ same
                    };
                    let by_val = move |x: u32| (x & 0xFFFF_FFFEu32) ^ (bias >> 2);
                    let first: u32 = by_ref(seed);
                    let second: u32 = by_val(first);
                    let mut acc: u32 = second ^ (*bias_ref & 0xFFu32);
                    let mut bump = |d: u32| {
                        acc = (acc >> 1) ^ d;
                    };
                    bump(#k_const);
                    bump(bias & 0xFFu32);
                    (acc >> 1) + #k_const
                }
            },
            _ => syn::parse_quote! {
                #[inline(never)]
                pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                    let arr: [u32; 3] = [seed, delta, #k_const];
                    let whole: &[u32] = &arr;
                    let [lead @ .., _, _] = &arr;
                    let short: &[u32] = lead;
                    let [_, tail @ ..] = &arr;
                    let shifted: &[u32] = tail;
                    let same_bit: u32 = if core::ptr::addr_eq(whole, short) {
                        2u32
                    } else {
                        0u32
                    };
                    let diff_bit: u32 = if core::ptr::addr_eq(whole, shifted) {
                        0u32
                    } else {
                        4u32
                    };
                    let picked: u32 = (arr[0] >> 1) & 0xFFFF_FFF8u32;
                    let masked: u32 = (arr[1] & 0xFFF8u32) ^ same_bit ^ diff_bit;
                    ((picked ^ masked) >> 1) + #k_const
                }
            },
        };

        let (outer_shift, _) = preamble_arg_shifts(file);
        let target_idx = target_fn_index(file);
        if let Some(idx) = target_idx
            && let Item::Fn(func) = &mut file.items[idx]
        {
            let arg0_expr = first_u32_param_expr(func, k_const);
            let arg1_expr = second_u32_param_expr(func, k_const);
            let local_ident = format_ident!("__itree_ind_res_{}", tag);
            let injected: Vec<Stmt> = syn::parse_quote! {
                let #local_ident: u32 = #helper_ident(#arg0_expr, #arg1_expr >> #outer_shift);
            };
            weave_into_fn_body(func, injected, &local_ident);
        }

        file.items.push(helper_item);
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
/// indexes them when it picks a pass's mutator: the
/// [`ITREE_BASE_MUTATOR_COUNT`] base mutators, then
/// [`IndirectDispatchOutliner`] (see [`apply_itree_mutation_passes`]).
pub const ITREE_AST_MUTATORS: [&dyn ItreeAstMutator; 5] = [
    &CallBoundaryOutliner,
    &LayoutPaddingPerturber,
    &BranchLoopWeaver,
    &ExtOracleInjector,
    &IndirectDispatchOutliner,
];

/// Number of leading [`ITREE_AST_MUTATORS`] entries that the passes rotate
/// through.
const ITREE_BASE_MUTATOR_COUNT: usize = 4;

/// Index in [`ITREE_AST_MUTATORS`] of [`IndirectDispatchOutliner`].
const ITREE_INDIRECT_MUTATOR_INDEX: usize = ITREE_BASE_MUTATOR_COUNT;

/// One pass in `ITREE_INDIRECT_PASS_DENOMINATOR` runs
/// [`IndirectDispatchOutliner`] instead of a base mutator.
const ITREE_INDIRECT_PASS_DENOMINATOR: usize = 16;

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
    /// `BranchLoopWeaver`, `ExtOracleInjector`, or `IndirectDispatchOutliner`).
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
/// base mutator rotates with `id`; every later pass draws a different base
/// mutator.
///
/// Each of the two PRNG draws of the base schedule (the pass count, and a
/// later pass's mutator) also decides, through its quotient, whether that pass
/// runs [`IndirectDispatchOutliner`] instead (one pass in
/// [`ITREE_INDIRECT_PASS_DENOMINATOR`], and never two passes of one
/// candidate). The redirect consumes no extra draw, so a candidate none of
/// whose passes is redirected keeps the PRNG stream, and so the program, that
/// the base schedule alone would give it.
fn apply_itree_mutation_passes(
    parsed: &mut File,
    cand_rng: &mut DetRng,
    id: usize,
) -> Vec<ItreeMutationStep> {
    let mutator_count = ITREE_BASE_MUTATOR_COUNT;
    let pass_draw = cand_rng.next_u64() as usize;
    let num_passes = 1 + pass_draw % 2;
    let first_indirect = (pass_draw / 2) % ITREE_INDIRECT_PASS_DENOMINATOR == 0;
    let first_idx = id % mutator_count;
    let mut steps = Vec::with_capacity(num_passes);
    for pass in 0..num_passes {
        let m_idx = if pass == 0 {
            if first_indirect {
                ITREE_INDIRECT_MUTATOR_INDEX
            } else {
                first_idx
            }
        } else {
            let draw = cand_rng.next_u64() as usize;
            let base_idx = (first_idx + 1 + draw % (mutator_count - 1)) % mutator_count;
            let later_indirect =
                (draw / (mutator_count - 1)) % ITREE_INDIRECT_PASS_DENOMINATOR == 0;
            if later_indirect && !first_indirect {
                ITREE_INDIRECT_MUTATOR_INDEX
            } else {
                base_idx
            }
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

// ---------------------------------------------------------------------------
// Concrete ITree candidate evaluator (the concolic explorer's replay oracle).
// ---------------------------------------------------------------------------

/// Upper bound on evaluation steps (expressions + loop iterations) per
/// [`ItreeConcreteEvaluator::run`], so a non-terminating candidate yields an
/// `Err` instead of hanging trial synthesis.
const ITREE_EVAL_STEP_LIMIT: usize = 200_000;

/// Unsigned integer type of a value computed by [`ItreeConcreteEvaluator`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvalIntTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    /// Unsuffixed integer literal whose type is fixed by its context (the
    /// other operand, a `let` annotation, or a parameter type).
    Infer,
}

impl EvalIntTy {
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "u128" => Self::U128,
            "usize" => Self::Usize,
            _ => return None,
        })
    }

    fn bits(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 | Self::Usize => 64,
            Self::U128 | Self::Infer => 128,
        }
    }

    fn max(self) -> u128 {
        width_mask(self.bits())
    }
}

/// Declared Rust type of a parameter, `let` binding, struct field, or return.
#[derive(Debug, Clone, PartialEq, Eq)]
enum EvalTy {
    Int(EvalIntTy),
    Bool,
    Unit,
    Named(String),
    /// `&T` (including `&[T]`): shared reference without trait-object erasure.
    Ref,
    /// `&dyn Trait`: shared trait-object reference carrying vtable identity.
    DynRef(String),
    /// `*const T`: safe raw pointer (never dereferenced in safe Rust).
    ConstPtr,
    /// `fn(..) -> ..`: a function item or a closure that captures nothing.
    FnPtr,
    /// `[T; N]` with element type `T`.
    Array(Box<EvalTy>),
    /// No annotation (`let x = ...`).
    Infer,
}

fn dyn_trait_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Paren(p) => dyn_trait_name(&p.elem),
        Type::Group(g) => dyn_trait_name(&g.elem),
        Type::TraitObject(o) => {
            let mut principal: Option<String> = None;
            for bound in &o.bounds {
                match bound {
                    syn::TypeParamBound::Trait(tb) => {
                        let id = tb.path.get_ident()?;
                        if principal.is_some() {
                            return None;
                        }
                        principal = Some(id.to_string());
                    }
                    syn::TypeParamBound::Lifetime(_) => {}
                    _ => return None,
                }
            }
            principal
        }
        _ => None,
    }
}

fn is_trait_object_type(ty: &Type) -> bool {
    match ty {
        Type::Paren(p) => is_trait_object_type(&p.elem),
        Type::Group(g) => is_trait_object_type(&g.elem),
        Type::TraitObject(_) => true,
        _ => false,
    }
}

fn eval_ty_of(ty: &Type) -> EvalTy {
    match ty {
        Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
            let name = tp.path.segments[0].ident.to_string();
            if name == "bool" {
                EvalTy::Bool
            } else if let Some(it) = EvalIntTy::from_name(&name) {
                EvalTy::Int(it)
            } else {
                EvalTy::Named(name)
            }
        }
        Type::Tuple(t) if t.elems.is_empty() => EvalTy::Unit,
        Type::Paren(p) => eval_ty_of(&p.elem),
        Type::Group(g) => eval_ty_of(&g.elem),
        Type::Reference(r) if r.mutability.is_none() => match dyn_trait_name(&r.elem) {
            Some(tr) => EvalTy::DynRef(tr),
            // Reject multi-bound or qualified trait-object references (such as
            // `&(dyn Trait + Send)`) rather than stripping `dyn` into `Ref` and
            // mis-dispatching to an inherent method.
            None if is_trait_object_type(&r.elem) => EvalTy::Named(quote!(#ty).to_string()),
            None => EvalTy::Ref,
        },
        Type::Ptr(p) if p.mutability.is_none() => EvalTy::ConstPtr,
        Type::BareFn(_) => EvalTy::FnPtr,
        Type::Array(a) => EvalTy::Array(Box::new(eval_ty_of(&a.elem))),
        other => EvalTy::Named(quote!(#other).to_string()),
    }
}

fn ret_ty_of(output: &ReturnType) -> EvalTy {
    match output {
        ReturnType::Default => EvalTy::Unit,
        ReturnType::Type(_, ty) => eval_ty_of(ty),
    }
}

/// Abstract address identity modeled by [`ItreeConcreteEvaluator`] for
/// `core::ptr::addr_eq`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvalAddr {
    /// `(binding identity, byte offset within that binding)`.
    Local(u64, u64),
    /// Function item in `EvalRun::fn_table`.
    FnItem(usize),
    /// Capture-free closure in `EvalRun::closures`.
    ClosureFn(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EvalValue {
    Int(u128, EvalIntTy),
    Bool(bool),
    Struct(String, BTreeMap<String, EvalValue>),
    Unit,
    /// `[T; N]` array, or the elements that a slice reference views.
    Array(Vec<EvalValue>),
    /// Shared reference.
    Ref(Box<EvalRef>),
    /// Safe `*const T` raw pointer (never dereferenced; used for `addr_eq`).
    ConstPtr {
        addr: Option<EvalAddr>,
        nonzero: bool,
    },
    /// Function item or function pointer (index into `EvalRun::fn_table`).
    FnRef(usize),
    /// Closure (index into `EvalRun::closures`); `captures` records whether it
    /// captured any variable, so only a capture-free closure coerces to a
    /// function pointer.
    Closure {
        id: usize,
        captures: bool,
    },
}

/// A shared reference: the referent's value and, when the evaluator can place
/// it, its address (plus optional `&dyn Trait` vtable identity).
///
/// Safe Rust cannot mutate a referent while a shared reference to it is live
/// (the evaluator's subset has no interior mutability), so the snapshot `val`
/// taken when the reference was created is the referent's value for as long
/// as the reference is usable.
#[derive(Debug, Clone, PartialEq, Eq)]
struct EvalRef {
    /// Address of the referent, or `None` when the address is not modeled (a
    /// temporary, whose address the compiler may share with another constant's,
    /// or a place whose byte offset depends on a layout the evaluator does not
    /// compute).
    addr: Option<EvalAddr>,
    val: EvalValue,
    /// Principal trait name when coerced or cast to `&dyn Trait`.
    dyn_trait: Option<String>,
}

impl EvalRef {
    /// The reference that auto-dereferencing reaches: `self`, or the innermost
    /// reference when `self` refers to a reference.
    fn autoderef(mut self) -> EvalRef {
        loop {
            match self.val {
                EvalValue::Ref(inner) => self = *inner,
                _ => return self,
            }
        }
    }
}

/// Auto-dereferenced value of `v` (the referent of any chain of references).
fn eval_autoderef(v: EvalValue) -> EvalValue {
    match v {
        EvalValue::Ref(r) => r.autoderef().val,
        other => other,
    }
}

/// Size in bytes of `v`, when the evaluator knows its layout (unsigned
/// integers, `bool`, and arrays of those).
fn eval_value_size(v: &EvalValue) -> Option<u64> {
    match v {
        EvalValue::Int(_, EvalIntTy::Infer) => None,
        EvalValue::Int(_, t) => Some(u64::from(t.bits() / 8)),
        EvalValue::Bool(_) => Some(1),
        EvalValue::Array(elems) => {
            let mut total = 0u64;
            for e in elems {
                total = total.checked_add(eval_value_size(e)?)?;
            }
            Some(total)
        }
        _ => None,
    }
}

/// Whether `v` certainly occupies at least one byte.
fn eval_value_is_sized_nonzero(v: &EvalValue) -> bool {
    match v {
        EvalValue::Int(..)
        | EvalValue::Bool(_)
        | EvalValue::Ref(_)
        | EvalValue::ConstPtr { .. }
        | EvalValue::FnRef(_) => true,
        // A closure's runtime size can be 0 even when `ClosureFreeIdents`
        // saw a free local (e.g., moving a ZST like `[u32; 0]`, or Rust
        // 2021+ disjoint non-capturing `let _ = x;`).
        EvalValue::Unit | EvalValue::Closure { .. } => false,
        EvalValue::Array(elems) => elems.iter().any(eval_value_is_sized_nonzero),
        EvalValue::Struct(_, fields) => fields.values().any(eval_value_is_sized_nonzero),
    }
}

/// Whether `v` has a `Copy` type. A closure that is not `move` borrows such a
/// capture however its body uses it, so the capture keeps its address inside
/// the closure. A struct or a closure may instead be moved into the closure
/// (when the body uses it by value), which the evaluator does not determine.
fn eval_value_is_copy(v: &EvalValue) -> bool {
    match v {
        EvalValue::Int(..)
        | EvalValue::Bool(_)
        | EvalValue::Unit
        | EvalValue::Ref(_)
        | EvalValue::ConstPtr { .. }
        | EvalValue::FnRef(_) => true,
        EvalValue::Array(elems) => elems.iter().all(eval_value_is_copy),
        EvalValue::Struct(..) | EvalValue::Closure { .. } => false,
    }
}

/// `core::ptr::addr_eq(a, b)` on two references or `*const` raw pointers.
///
/// Two references into one binding are equal iff their byte offsets are
/// equal, references into two live bindings are never equal, a function
/// pointer is equal to itself and never equal to a live non-ZST stack
/// binding, and comparisons between two distinct functions are rejected rather
/// than guessed (LLVM ICF may merge functions). Zero-sized referents and
/// unmodeled addresses are likewise rejected.
///
/// A raw pointer, unlike a reference, may outlive the variable it points to,
/// whose address a later variable or call may then reuse. The caller
/// (`EvalRun::eval_call`) therefore passes a raw pointer into a variable only
/// while that variable is in scope in the frame that compares it.
fn eval_addr_eq(a: &EvalValue, b: &EvalValue) -> EvalRes {
    let extract = |v: &EvalValue| -> Result<(Option<EvalAddr>, bool), EvalCtrl> {
        match v {
            EvalValue::Ref(r) => Ok((r.addr, eval_value_is_sized_nonzero(&r.val))),
            EvalValue::ConstPtr { addr, nonzero } => Ok((*addr, *nonzero)),
            _ => eval_unsupported("`addr_eq` on a non-pointer operand"),
        }
    };
    let (addr_a, nz_a) = extract(a)?;
    let (addr_b, nz_b) = extract(b)?;
    if !nz_a || !nz_b {
        return eval_unsupported("`addr_eq` on a possibly zero-sized referent");
    }
    match (addr_a, addr_b) {
        (Some(EvalAddr::Local(alloc_a, off_a)), Some(EvalAddr::Local(alloc_b, off_b))) => {
            Ok(EvalValue::Bool(alloc_a == alloc_b && off_a == off_b))
        }
        (Some(EvalAddr::FnItem(i)), Some(EvalAddr::FnItem(j))) if i == j => {
            Ok(EvalValue::Bool(true))
        }
        (Some(EvalAddr::ClosureFn(i)), Some(EvalAddr::ClosureFn(j))) if i == j => {
            Ok(EvalValue::Bool(true))
        }
        (Some(EvalAddr::FnItem(_) | EvalAddr::ClosureFn(_)), Some(EvalAddr::Local(..)))
        | (Some(EvalAddr::Local(..)), Some(EvalAddr::FnItem(_) | EvalAddr::ClosureFn(_))) => {
            Ok(EvalValue::Bool(false))
        }
        _ => eval_unsupported("`addr_eq` on a referent at an unmodeled or ICF-sensitive address"),
    }
}

/// Whether `path` names `core::ptr::addr_eq` (`core::ptr::addr_eq` or
/// `std::ptr::addr_eq`, without generic arguments).
fn is_core_ptr_addr_eq_path(path: &syn::Path) -> bool {
    path.segments.len() == 3
        && path.segments.iter().all(|seg| seg.arguments.is_none())
        && (path.segments[0].ident == "core" || path.segments[0].ident == "std")
        && path.segments[1].ident == "ptr"
        && path.segments[2].ident == "addr_eq"
}

/// Non-local control flow and evaluation failures.
enum EvalCtrl {
    Return(EvalValue),
    Break,
    Continue,
    /// A Rust panic: arithmetic overflow / division by zero (`-C opt-level=0`
    /// overflow checks), or a scheduled `PanicOnCall` boundary unwind.
    Panic,
    /// A construct outside the evaluator's (seed + mutator) Rust subset.
    Unsupported(String),
}

type EvalRes = Result<EvalValue, EvalCtrl>;

fn eval_unsupported<T>(what: impl Into<String>) -> Result<T, EvalCtrl> {
    Err(EvalCtrl::Unsupported(what.into()))
}

fn eval_coerce(v: EvalValue, ty: &EvalTy) -> EvalRes {
    match (v, ty) {
        (v, EvalTy::Infer) => Ok(v),
        (EvalValue::Int(x, EvalIntTy::Infer), EvalTy::Int(t)) => {
            if x <= t.max() {
                Ok(EvalValue::Int(x, *t))
            } else {
                eval_unsupported("integer literal out of range for its type")
            }
        }
        (EvalValue::Int(x, s), EvalTy::Int(t)) if s == *t => Ok(EvalValue::Int(x, s)),
        (EvalValue::Bool(b), EvalTy::Bool) => Ok(EvalValue::Bool(b)),
        (EvalValue::Unit, EvalTy::Unit) => Ok(EvalValue::Unit),
        (EvalValue::Struct(n, f), EvalTy::Named(m)) if n == *m => Ok(EvalValue::Struct(n, f)),
        (v @ EvalValue::Ref(_), EvalTy::Ref) => Ok(v),
        (EvalValue::Ref(r), EvalTy::DynRef(tr)) => {
            let mut inner = r.autoderef();
            inner.dyn_trait = Some(tr.clone());
            Ok(EvalValue::Ref(Box::new(inner)))
        }
        (EvalValue::Ref(r), EvalTy::ConstPtr) => Ok(EvalValue::ConstPtr {
            addr: r.addr,
            nonzero: eval_value_is_sized_nonzero(&r.val),
        }),
        (v @ EvalValue::ConstPtr { .. }, EvalTy::ConstPtr) => Ok(v),
        (v @ EvalValue::FnRef(_), EvalTy::FnPtr) => Ok(v),
        (
            v @ EvalValue::Closure {
                captures: false, ..
            },
            EvalTy::FnPtr,
        ) => Ok(v),
        (EvalValue::Array(elems), EvalTy::Array(elem_ty)) => elems
            .into_iter()
            .map(|e| eval_coerce(e, elem_ty))
            .collect::<Result<Vec<_>, _>>()
            .map(EvalValue::Array),
        (v, ty) => eval_unsupported(format!("value {v:?} does not have type {ty:?}")),
    }
}

fn eval_encode(v: &EvalValue) -> Result<Vec<u8>, EvalCtrl> {
    match v {
        EvalValue::Int(_, EvalIntTy::Infer) => eval_unsupported("untyped integer at a boundary"),
        EvalValue::Int(x, t) => Ok(x.to_le_bytes()[..(t.bits() / 8) as usize].to_vec()),
        EvalValue::Bool(b) => Ok(vec![u8::from(*b)]),
        EvalValue::Unit => Ok(Vec::new()),
        EvalValue::Struct(..) => eval_unsupported("struct value at a boundary"),
        EvalValue::Array(_)
        | EvalValue::Ref(_)
        | EvalValue::ConstPtr { .. }
        | EvalValue::FnRef(_)
        | EvalValue::Closure { .. } => eval_unsupported("non-scalar value at a boundary"),
    }
}

fn eval_decode(bytes: &[u8], ty: &EvalTy) -> EvalRes {
    match ty {
        EvalTy::Int(t) if *t != EvalIntTy::Infer && bytes.len() == (t.bits() / 8) as usize => {
            let mut le = [0u8; 16];
            le[..bytes.len()].copy_from_slice(bytes);
            Ok(EvalValue::Int(u128::from_le_bytes(le), *t))
        }
        EvalTy::Bool if bytes.len() == 1 && bytes[0] <= 1 => Ok(EvalValue::Bool(bytes[0] == 1)),
        EvalTy::Unit if bytes.is_empty() => Ok(EvalValue::Unit),
        _ => eval_unsupported(format!(
            "scheduled return of {} byte(s) does not decode as {ty:?}",
            bytes.len()
        )),
    }
}

fn eval_lit(lit: &Lit) -> EvalRes {
    match lit {
        Lit::Int(li) => {
            let Ok(v) = li.base10_parse::<u128>() else {
                return eval_unsupported("integer literal");
            };
            let ty = match li.suffix() {
                "" => EvalIntTy::Infer,
                s => match EvalIntTy::from_name(s) {
                    Some(t) => t,
                    None => return eval_unsupported(format!("integer literal suffix `{s}`")),
                },
            };
            if v > ty.max() {
                return eval_unsupported("integer literal out of range");
            }
            Ok(EvalValue::Int(v, ty))
        }
        Lit::Bool(b) => Ok(EvalValue::Bool(b.value)),
        _ => eval_unsupported("non-integer literal"),
    }
}

fn eval_binop(op: &BinOp, l: EvalValue, r: EvalValue) -> EvalRes {
    use EvalValue::{Bool, Int};
    match (l, r) {
        (Int(a, ta), Int(b, tb)) => {
            if matches!(op, BinOp::Shl(_) | BinOp::Shr(_)) {
                if ta == EvalIntTy::Infer {
                    return eval_unsupported("shift of an untyped integer literal");
                }
                if b >= u128::from(ta.bits()) {
                    return Err(EvalCtrl::Panic);
                }
                let v = if matches!(op, BinOp::Shl(_)) {
                    (a << b) & ta.max()
                } else {
                    a >> b
                };
                return Ok(Int(v, ta));
            }
            let t = match (ta, tb) {
                (EvalIntTy::Infer, t) | (t, EvalIntTy::Infer) => t,
                (x, y) if x == y => x,
                (x, y) => return eval_unsupported(format!("mismatched integer types {x:?}/{y:?}")),
            };
            let mask = t.max();
            if a > mask || b > mask {
                return eval_unsupported("integer literal out of range for its type");
            }
            let checked = |v: Option<u128>| match v {
                Some(v) if v <= mask => Ok(Int(v, t)),
                _ => Err(EvalCtrl::Panic),
            };
            match op {
                BinOp::Add(_) => checked(a.checked_add(b)),
                BinOp::Sub(_) => checked(a.checked_sub(b)),
                BinOp::Mul(_) => checked(a.checked_mul(b)),
                BinOp::Div(_) => checked(a.checked_div(b)),
                BinOp::Rem(_) => checked(a.checked_rem(b)),
                BinOp::BitXor(_) => Ok(Int(a ^ b, t)),
                BinOp::BitAnd(_) => Ok(Int(a & b, t)),
                BinOp::BitOr(_) => Ok(Int(a | b, t)),
                BinOp::Eq(_) => Ok(Bool(a == b)),
                BinOp::Ne(_) => Ok(Bool(a != b)),
                BinOp::Lt(_) => Ok(Bool(a < b)),
                BinOp::Le(_) => Ok(Bool(a <= b)),
                BinOp::Gt(_) => Ok(Bool(a > b)),
                BinOp::Ge(_) => Ok(Bool(a >= b)),
                _ => eval_unsupported("integer binary operator"),
            }
        }
        (Bool(a), Bool(b)) => match op {
            BinOp::Eq(_) => Ok(Bool(a == b)),
            BinOp::Ne(_) => Ok(Bool(a != b)),
            BinOp::BitXor(_) => Ok(Bool(a ^ b)),
            BinOp::BitAnd(_) => Ok(Bool(a & b)),
            BinOp::BitOr(_) => Ok(Bool(a | b)),
            _ => eval_unsupported("boolean binary operator"),
        },
        (l, r) => eval_unsupported(format!("binary operator on {l:?} and {r:?}")),
    }
}

/// The plain operator of a compound assignment (`a += b` -> `+`).
fn compound_assign_base(op: &BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::AddAssign(_) => BinOp::Add(Default::default()),
        BinOp::SubAssign(_) => BinOp::Sub(Default::default()),
        BinOp::MulAssign(_) => BinOp::Mul(Default::default()),
        BinOp::DivAssign(_) => BinOp::Div(Default::default()),
        BinOp::RemAssign(_) => BinOp::Rem(Default::default()),
        BinOp::BitXorAssign(_) => BinOp::BitXor(Default::default()),
        BinOp::BitAndAssign(_) => BinOp::BitAnd(Default::default()),
        BinOp::BitOrAssign(_) => BinOp::BitOr(Default::default()),
        BinOp::ShlAssign(_) => BinOp::Shl(Default::default()),
        BinOp::ShrAssign(_) => BinOp::Shr(Default::default()),
        _ => return None,
    })
}

fn eval_pattern_matches(
    pat: &Pat,
    v: &EvalValue,
    bindings: &mut BTreeMap<String, EvalValue>,
) -> Result<bool, EvalCtrl> {
    let lit_eq = |lit: &Lit| -> Result<bool, EvalCtrl> {
        Ok(match (eval_lit(lit)?, v) {
            (EvalValue::Int(a, _), EvalValue::Int(b, _)) => a == *b,
            (EvalValue::Bool(a), EvalValue::Bool(b)) => a == *b,
            _ => return eval_unsupported("literal pattern type mismatch"),
        })
    };
    match pat {
        Pat::Wild(_) => Ok(true),
        Pat::Lit(pl) => lit_eq(&pl.lit),
        Pat::Ident(pi) if pi.subpat.is_none() && pi.by_ref.is_none() => {
            bindings.insert(pi.ident.to_string(), v.clone());
            Ok(true)
        }
        Pat::Or(po) => {
            for case in &po.cases {
                if eval_pattern_matches(case, v, bindings)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Pat::Paren(pp) => eval_pattern_matches(&pp.pat, v, bindings),
        Pat::Range(pr) => {
            let EvalValue::Int(x, _) = v else {
                return eval_unsupported("range pattern on a non-integer");
            };
            let bound = |e: &Option<Box<Expr>>| -> Result<Option<u128>, EvalCtrl> {
                match e.as_deref() {
                    None => Ok(None),
                    Some(Expr::Lit(l)) => match eval_lit(&l.lit)? {
                        EvalValue::Int(b, _) => Ok(Some(b)),
                        _ => eval_unsupported("range pattern bound"),
                    },
                    Some(_) => eval_unsupported("range pattern bound"),
                }
            };
            let lo = bound(&pr.start)?.unwrap_or(0);
            let ok_hi = match (bound(&pr.end)?, &pr.limits) {
                (None, _) => true,
                (Some(hi), syn::RangeLimits::Closed(_)) => *x <= hi,
                (Some(hi), syn::RangeLimits::HalfOpen(_)) => *x < hi,
            };
            Ok(*x >= lo && ok_hi)
        }
        _ => eval_unsupported("match pattern"),
    }
}

/// Pre-order indices of the root body's decision nodes (`if`, `match`,
/// `while`, `&&`, `||`), keyed by node address (stable while the evaluator's
/// owned `File` is alive and never mutated).
#[derive(Default)]
struct BranchSiteCollector {
    sites: BTreeMap<usize, u32>,
}

impl BranchSiteCollector {
    fn add<T>(&mut self, node: &T) {
        let next = self.sites.len() as u32;
        self.sites.entry(node as *const T as usize).or_insert(next);
    }
}

impl<'ast> Visit<'ast> for BranchSiteCollector {
    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        self.add(node);
        visit::visit_expr_if(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        self.add(node);
        visit::visit_expr_match(self, node);
    }

    fn visit_expr_while(&mut self, node: &'ast syn::ExprWhile) {
        self.add(node);
        visit::visit_expr_while(self, node);
    }

    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        if matches!(node.op, BinOp::And(_) | BinOp::Or(_)) {
            self.add(node);
        }
        visit::visit_expr_binary(self, node);
    }

    // Functions, methods, and closures nested inside the root body are
    // separate (uninstrumented) bodies.
    fn visit_item_fn(&mut self, _node: &'ast syn::ItemFn) {}

    fn visit_item_impl(&mut self, _node: &'ast syn::ItemImpl) {}

    fn visit_item_trait(&mut self, _node: &'ast syn::ItemTrait) {}

    fn visit_expr_closure(&mut self, _node: &'ast syn::ExprClosure) {}
}

/// Collect all identifier bindings introduced by pattern `pat`.
fn collect_pat_idents(pat: &Pat, out: &mut BTreeSet<String>) {
    match pat {
        Pat::Ident(pi) => {
            out.insert(pi.ident.to_string());
            if let Some((_, sub)) = &pi.subpat {
                collect_pat_idents(sub, out);
            }
        }
        Pat::Type(pt) => collect_pat_idents(&pt.pat, out),
        Pat::Paren(pp) => collect_pat_idents(&pp.pat, out),
        Pat::Reference(pr) => collect_pat_idents(&pr.pat, out),
        Pat::Slice(ps) => {
            for e in &ps.elems {
                collect_pat_idents(e, out);
            }
        }
        Pat::Tuple(pt) => {
            for e in &pt.elems {
                collect_pat_idents(e, out);
            }
        }
        Pat::Or(po) => {
            for c in &po.cases {
                collect_pat_idents(c, out);
            }
        }
        Pat::Struct(ps) => {
            for f in &ps.fields {
                collect_pat_idents(&f.pat, out);
            }
        }
        Pat::TupleStruct(pt) => {
            for e in &pt.elems {
                collect_pat_idents(e, out);
            }
        }
        _ => {}
    }
}

/// Free single-identifier path expressions of a closure body (respecting
/// local `let` bindings, `match` arm patterns, and nested closure parameters):
/// the names the closure may capture from the enclosing function.
#[derive(Default)]
struct ClosureFreeIdents {
    names: BTreeSet<String>,
    bound: Vec<BTreeSet<String>>,
    /// Set when the closure body contains any macro invocation whose token
    /// stream `syn::Visit` cannot inspect for captured identifiers.
    has_macro: bool,
}

impl<'ast> Visit<'ast> for ClosureFreeIdents {
    fn visit_block(&mut self, node: &'ast Block) {
        self.bound.push(BTreeSet::new());
        for stmt in &node.stmts {
            self.visit_stmt(stmt);
        }
        self.bound.pop();
    }

    fn visit_local(&mut self, node: &'ast syn::Local) {
        if let Some(init) = &node.init {
            self.visit_expr(&init.expr);
            if let Some((_, diverge)) = &init.diverge {
                self.visit_expr(diverge);
            }
        }
        if let Some(scope) = self.bound.last_mut() {
            collect_pat_idents(&node.pat, scope);
        }
    }

    fn visit_arm(&mut self, node: &'ast syn::Arm) {
        let mut scope = BTreeSet::new();
        collect_pat_idents(&node.pat, &mut scope);
        self.bound.push(scope);
        if let Some((_, guard)) = &node.guard {
            self.visit_expr(guard);
        }
        self.visit_expr(&node.body);
        self.bound.pop();
    }

    fn visit_expr_closure(&mut self, node: &'ast syn::ExprClosure) {
        let mut scope = BTreeSet::new();
        for input in &node.inputs {
            collect_pat_idents(input, &mut scope);
        }
        self.bound.push(scope);
        self.visit_expr(&node.body);
        self.bound.pop();
    }

    fn visit_expr_for_loop(&mut self, node: &'ast syn::ExprForLoop) {
        self.visit_expr(&node.expr);
        let mut scope = BTreeSet::new();
        collect_pat_idents(&node.pat, &mut scope);
        self.bound.push(scope);
        self.visit_block(&node.body);
        self.bound.pop();
    }

    fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
        self.bound.push(BTreeSet::new());
        self.visit_expr(&node.cond);
        self.visit_block(&node.then_branch);
        self.bound.pop();
        if let Some((_, else_branch)) = &node.else_branch {
            self.visit_expr(else_branch);
        }
    }

    fn visit_expr_while(&mut self, node: &'ast syn::ExprWhile) {
        self.bound.push(BTreeSet::new());
        self.visit_expr(&node.cond);
        self.visit_block(&node.body);
        self.bound.pop();
    }

    fn visit_expr_let(&mut self, node: &'ast syn::ExprLet) {
        self.visit_expr(&node.expr);
        if let Some(scope) = self.bound.last_mut() {
            collect_pat_idents(&node.pat, scope);
        }
    }

    fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
        if node.qself.is_none()
            && let Some(id) = node.path.get_ident()
        {
            let name = id.to_string();
            if !self.bound.iter().any(|s| s.contains(&name)) {
                self.names.insert(name);
            }
        }
    }

    fn visit_macro(&mut self, _node: &'ast syn::Macro) {
        self.has_macro = true;
    }

    // Items declared inside the closure body cannot capture.
    fn visit_item(&mut self, _node: &'ast Item) {}
}

/// Root-function event predicted by [`ItreeConcreteEvaluator`], the evaluator-side
/// analogue of the native harness's `RecordedEvent` (boundary calls carry the same
/// little-endian `raw_args` / `raw_ret` encoding).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ItreeConcreteEvent {
    /// Decision at a root-body `if` / `match` / `while` / `&&` / `||` node: `site`
    /// is the node's pre-order index and `tag` the `switchInt` discriminant the
    /// native harness records (`1` / `0` for boolean decisions, the scrutinee
    /// value for an integer `match`, so two inputs reaching one wildcard arm with
    /// different scrutinees stay distinct, as in `RecordedEvent::Branch`).
    Branch { site: u32, tag: u128 },
    /// Boundary call to the (unprefixed) external callee `callee` that returned.
    ExtCall {
        callee: String,
        args: Vec<Vec<u8>>,
        ret: Vec<u8>,
    },
    /// Boundary call that unwound (scheduled `PanicOnCall` or a panicking callee body).
    ExtCallPanic { callee: String, args: Vec<Vec<u8>> },
}

/// Terminal outcome of an [`ItreeConcreteRun`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ItreeConcreteOutcome {
    /// Normal return with the little-endian return value.
    Return(Vec<u8>),
    /// The root invocation unwound.
    Panic,
}

/// Predicted `(events, outcome)` of one root invocation; two runs with equal
/// [`ItreeConcreteRun`]s produce native traces that the harness deduplicates.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItreeConcreteRun {
    pub events: Vec<ItreeConcreteEvent>,
    pub outcome: ItreeConcreteOutcome,
}

impl ItreeConcreteRun {
    /// `(event position, callee, args, ret)` of every boundary call that returned.
    pub fn ext_calls(&self) -> Vec<(usize, &str, &[Vec<u8>], &[u8])> {
        self.events
            .iter()
            .enumerate()
            .filter_map(|(pos, ev)| match ev {
                ItreeConcreteEvent::ExtCall { callee, args, ret } => {
                    Some((pos, callee.as_str(), args.as_slice(), ret.as_slice()))
                }
                _ => None,
            })
            .collect()
    }

    /// Number of branch decisions strictly before event position `pos`
    /// (`PinConstraint.beforeGuardIdx` of a call at `pos`).
    pub fn branches_before(&self, pos: usize) -> usize {
        self.events[..pos.min(self.events.len())]
            .iter()
            .filter(|ev| matches!(ev, ItreeConcreteEvent::Branch { .. }))
            .count()
    }

    /// Whether `self` follows `base`'s exact event prefix `base.events[..pos]`
    /// (same branch decisions and same boundary calls with the same arguments and
    /// returns, i.e. `guards.take beforeGuardIdx` and `pins.take pinIdx`).
    pub fn shares_prefix_with(&self, base: &ItreeConcreteRun, pos: usize) -> bool {
        pos <= base.events.len()
            && pos <= self.events.len()
            && self.events[..pos] == base.events[..pos]
    }
}

/// Concrete interpreter for the strictly safe Rust subset emitted by
/// [`ITREE_AST_MUTATORS`] over the ITree seeds (unsigned integer arithmetic with
/// `-C opt-level=0` overflow panics, casts, `if` / `match` / `while`, `let` /
/// assignment, struct literals and field reads, arrays, shared references,
/// nested helper functions, boundary calls, and, inside a function body:
/// struct / trait / `impl` items with `&self` methods called directly or
/// through a `&dyn Trait`, calls through function pointers, closures that
/// capture by value or by reference, and `core::ptr::addr_eq`).
///
/// Executing the root function records the same observable boundary that the
/// native harness traces: root-body branch decisions and calls to top-level
/// (`#[anneal_trace::external]`) callees with their little-endian arguments and
/// returns, honoring an [`EnvSchedule`] exactly like `EnvSchedule::next_action`
/// (FIFO responses, defaults, `PanicOnCall`, pass-through). Constructs outside
/// the subset make [`Self::run`] return `Err` rather than guess.
pub struct ItreeConcreteEvaluator {
    file: File,
    root_fn_name: String,
    fns: BTreeMap<String, usize>,
    structs: BTreeMap<String, Vec<(String, EvalTy)>>,
    branch_sites: BTreeMap<usize, u32>,
}

impl ItreeConcreteEvaluator {
    /// Parses `source` and indexes its top-level functions / structs and the
    /// decision nodes of `root_fn_name`'s body.
    pub fn new(source: &str, root_fn_name: &str) -> Result<Self, String> {
        let file = syn::parse_str::<File>(source).map_err(|e| e.to_string())?;
        let mut fns = BTreeMap::new();
        let mut structs = BTreeMap::new();
        for (idx, item) in file.items.iter().enumerate() {
            match item {
                Item::Fn(f) => {
                    fns.insert(f.sig.ident.to_string(), idx);
                }
                Item::Struct(s) => {
                    let fields = s
                        .fields
                        .iter()
                        .filter_map(|f| Some((f.ident.as_ref()?.to_string(), eval_ty_of(&f.ty))))
                        .collect();
                    structs.insert(s.ident.to_string(), fields);
                }
                _ => {}
            }
        }
        let Some(&root_idx) = fns.get(root_fn_name) else {
            return Err(format!("root function `{root_fn_name}` not found"));
        };
        let mut evaluator = Self {
            file,
            root_fn_name: root_fn_name.to_string(),
            fns,
            structs,
            branch_sites: BTreeMap::new(),
        };
        let mut collector = BranchSiteCollector::default();
        if let Item::Fn(root) = &evaluator.file.items[root_idx] {
            collector.visit_block(&root.block);
        }
        evaluator.branch_sites = collector.sites;
        Ok(evaluator)
    }

    fn top_fn(&self, name: &str) -> Option<&syn::ItemFn> {
        match self.file.items.get(*self.fns.get(name)?)? {
            Item::Fn(f) => Some(f),
            _ => None,
        }
    }

    /// Unprefixed names of the boundary callees (every top-level function other
    /// than the root, matching [`annotate_itree_external_callees`]).
    pub fn external_callees(&self) -> Vec<String> {
        self.fns
            .keys()
            .filter(|n| **n != self.root_fn_name)
            .cloned()
            .collect()
    }

    /// Argument bit-validity domains of boundary callee `callee` (`bool` ->
    /// [`ScalarLayout::bool_layout`], `uN` -> `N`-bit unsigned).
    pub fn callee_arg_layouts(&self, callee: &str) -> Option<Vec<ScalarLayout>> {
        let f = self.top_fn(callee)?;
        f.sig
            .inputs
            .iter()
            .map(|input| match input {
                FnArg::Typed(pt) => match eval_ty_of(&pt.ty) {
                    EvalTy::Bool => Some(ScalarLayout::bool_layout()),
                    EvalTy::Int(t) if t != EvalIntTy::Infer => {
                        Some(ScalarLayout::unsigned((t.bits() / 8) as usize))
                    }
                    _ => None,
                },
                FnArg::Receiver(_) => None,
            })
            .collect()
    }

    /// Return bit-validity domain of boundary callee `callee` (`()` ->
    /// `ScalarLayout::unsigned(0)`, `bool` -> [`ScalarLayout::bool_layout`], `uN` ->
    /// `N`-bit unsigned).
    pub fn callee_return_layout(&self, callee: &str) -> Option<ScalarLayout> {
        let f = self.top_fn(callee)?;
        match ret_ty_of(&f.sig.output) {
            EvalTy::Unit => Some(ScalarLayout::unsigned(0)),
            EvalTy::Bool => Some(ScalarLayout::bool_layout()),
            EvalTy::Int(t) if t != EvalIntTy::Infer => {
                Some(ScalarLayout::unsigned((t.bits() / 8) as usize))
            }
            _ => None,
        }
    }

    /// Executes the root function on `root_args` (one value per parameter,
    /// truncation-checked against the parameter types) under `schedule`, whose
    /// queues are keyed by `callee_key_prefix` + callee name (the staged
    /// `b{batch}_c{candidate}__` names used by the native trace collector).
    pub fn run(
        &self,
        root_args: &[u128],
        schedule: &EnvSchedule,
        callee_key_prefix: &str,
    ) -> Result<ItreeConcreteRun, String> {
        let root = self
            .top_fn(&self.root_fn_name)
            .ok_or_else(|| format!("root function `{}` not found", self.root_fn_name))?;
        if root.sig.inputs.len() != root_args.len() {
            return Err(format!(
                "root function takes {} argument(s), got {}",
                root.sig.inputs.len(),
                root_args.len()
            ));
        }
        let mut args = Vec::with_capacity(root_args.len());
        for (input, &raw) in root.sig.inputs.iter().zip(root_args) {
            let FnArg::Typed(pt) = input else {
                return Err("root function takes a receiver".to_string());
            };
            match eval_ty_of(&pt.ty) {
                EvalTy::Int(t) if t != EvalIntTy::Infer && raw <= t.max() => {
                    args.push(EvalValue::Int(raw, t));
                }
                EvalTy::Bool if raw <= 1 => args.push(EvalValue::Bool(raw == 1)),
                ty => return Err(format!("root argument {raw} does not fit {ty:?}")),
            }
        }
        let mut ctx = EvalRun {
            ev: self,
            schedule: schedule.clone(),
            callee_key_prefix,
            events: Vec::new(),
            global_call_idx: 0,
            steps: 0,
            fn_table: Vec::new(),
            closures: Vec::new(),
            next_frame_id: 0,
            next_alloc_id: 0,
        };
        let outcome = match ctx.call_fn(root, args, true) {
            Ok(v) => ItreeConcreteOutcome::Return(match eval_encode(&v) {
                Ok(b) => b,
                Err(EvalCtrl::Unsupported(m)) => return Err(m),
                Err(_) => return Err("unencodable root return".to_string()),
            }),
            Err(EvalCtrl::Panic) => ItreeConcreteOutcome::Panic,
            Err(EvalCtrl::Unsupported(m)) => return Err(m),
            Err(_) => return Err("unexpected control flow escaped the root".to_string()),
        };
        Ok(ItreeConcreteRun {
            events: ctx.events,
            outcome,
        })
    }

    /// [`Self::run`] for the ITree seeds' `kernel_step(magic: u32, payload_len: u32)`.
    pub fn run_kernel_step(
        &self,
        magic: u32,
        payload_len: u32,
        schedule: &EnvSchedule,
        callee_key_prefix: &str,
    ) -> Result<ItreeConcreteRun, String> {
        self.run(
            &[u128::from(magic), u128::from(payload_len)],
            schedule,
            callee_key_prefix,
        )
    }
}

/// Fields of a struct declared by an item statement, in declaration order.
type EvalStructDef = Vec<(String, EvalTy)>;

/// Methods of the `impl` items of one block, keyed by
/// `(Self type, Option<Trait name>, method name)` (`None` for inherent `impl`s).
type EvalMethodTable<'a> = BTreeMap<(String, Option<String>, String), &'a syn::ImplItemFn>;

struct EvalFrame<'a> {
    scopes: Vec<BTreeMap<String, EvalValue>>,
    /// Binding identities (`EvalRef::addr`) of the variables of `scopes` that a
    /// reference was taken to; parallel to `scopes`.
    allocs: Vec<BTreeMap<String, u64>>,
    /// Variables of the outermost scope whose address is not modeled: the
    /// captures of a closure that may hold them either by reference or by
    /// value (see `EvalRun::call_closure`).
    unplaced: BTreeSet<String>,
    /// Number of bindings of each name made in this frame so far. A closure
    /// records the count of every variable it captures by reference and
    /// refuses to run once one of them was bound again, since the name would
    /// then resolve to a different variable.
    bind_gen: BTreeMap<String, u64>,
    local_fns: Vec<BTreeMap<String, &'a syn::ItemFn>>,
    local_structs: Vec<BTreeMap<String, EvalStructDef>>,
    local_methods: Vec<EvalMethodTable<'a>>,
    /// Identity of this function, method, or closure invocation.
    id: u64,
    /// Only the root body is instrumented: its branches and top-level calls are
    /// observable events; callee bodies run natively.
    is_root: bool,
}

impl<'a> EvalFrame<'a> {
    fn new(scope: BTreeMap<String, EvalValue>, id: u64, is_root: bool) -> Self {
        let mut frame = Self {
            scopes: Vec::new(),
            allocs: Vec::new(),
            unplaced: BTreeSet::new(),
            bind_gen: BTreeMap::new(),
            local_fns: Vec::new(),
            local_structs: Vec::new(),
            local_methods: Vec::new(),
            id,
            is_root,
        };
        frame.push_scope(scope);
        frame
    }

    /// Enter a scope whose bindings are `scope`.
    fn push_scope(&mut self, scope: BTreeMap<String, EvalValue>) {
        for name in scope.keys() {
            *self.bind_gen.entry(name.clone()).or_insert(0) += 1;
        }
        self.scopes.push(scope);
        self.allocs.push(BTreeMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.allocs.pop();
    }

    /// Bind `name` to `v` in the innermost scope (shadowing any binding of
    /// `name` there, which is a new variable with a new address).
    fn bind(&mut self, name: String, v: EvalValue) {
        *self.bind_gen.entry(name.clone()).or_insert(0) += 1;
        if let Some(allocs) = self.allocs.last_mut() {
            allocs.remove(&name);
        }
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, v);
        }
    }
}

/// A closure value: its expression, the variables it captured, and where it
/// was created.
struct EvalClosure<'a> {
    expr: &'a syn::ExprClosure,
    /// Captured variables and their values when the closure was created.
    env: BTreeMap<String, EvalValue>,
    /// `move` closure: it owns the copies in `env`.
    by_move: bool,
    /// Frame that created the closure.
    def_frame: u64,
    /// `EvalFrame::bind_gen` of every captured variable at creation.
    gens: Vec<(String, u64)>,
    /// Lexical `fn` / `struct` / `impl` items visible where the closure was created.
    local_fns: Vec<BTreeMap<String, &'a syn::ItemFn>>,
    local_structs: Vec<BTreeMap<String, EvalStructDef>>,
    local_methods: Vec<EvalMethodTable<'a>>,
}

struct EvalRun<'a> {
    ev: &'a ItreeConcreteEvaluator,
    schedule: EnvSchedule,
    callee_key_prefix: &'a str,
    events: Vec<ItreeConcreteEvent>,
    global_call_idx: usize,
    steps: usize,
    /// Functions that `EvalValue::FnRef` values index.
    fn_table: Vec<&'a syn::ItemFn>,
    /// Closures that `EvalValue::Closure` values index.
    closures: Vec<EvalClosure<'a>>,
    /// Next `EvalFrame::id`.
    next_frame_id: u64,
    /// Next binding identity for `EvalRef::addr`.
    next_alloc_id: u64,
}

impl<'a> EvalRun<'a> {
    fn tick(&mut self) -> Result<(), EvalCtrl> {
        self.steps += 1;
        if self.steps > ITREE_EVAL_STEP_LIMIT {
            return eval_unsupported("evaluation step limit exceeded");
        }
        Ok(())
    }

    fn record_branch<T>(&mut self, frame: &EvalFrame<'a>, node: &T, tag: u128) {
        if frame.is_root
            && let Some(&site) = self.ev.branch_sites.get(&(node as *const T as usize))
        {
            self.events.push(ItreeConcreteEvent::Branch { site, tag });
        }
    }

    fn call_fn(&mut self, func: &'a syn::ItemFn, args: Vec<EvalValue>, is_root: bool) -> EvalRes {
        if func.sig.inputs.len() != args.len() {
            return eval_unsupported(format!("arity mismatch calling `{}`", func.sig.ident));
        }
        let mut scope = BTreeMap::new();
        for (input, arg) in func.sig.inputs.iter().zip(args) {
            let FnArg::Typed(pt) = input else {
                return eval_unsupported("method receiver");
            };
            let Pat::Ident(pi) = pt.pat.as_ref() else {
                return eval_unsupported("parameter pattern");
            };
            scope.insert(pi.ident.to_string(), eval_coerce(arg, &eval_ty_of(&pt.ty))?);
        }
        let mut frame = EvalFrame::new(scope, self.fresh_frame_id(), is_root);
        let value = match self.eval_block(&mut frame, &func.block) {
            Ok(v) | Err(EvalCtrl::Return(v)) => v,
            Err(EvalCtrl::Break | EvalCtrl::Continue) => {
                return eval_unsupported("`break` / `continue` outside of a loop");
            }
            Err(e) => return Err(e),
        };
        eval_coerce(value, &ret_ty_of(&func.sig.output))
    }

    fn fresh_frame_id(&mut self) -> u64 {
        let id = self.next_frame_id;
        self.next_frame_id += 1;
        id
    }

    /// Call the `&self` method `method` of an `impl` item on the reference
    /// `self_ref`.
    fn call_method(
        &mut self,
        method: &'a syn::ImplItemFn,
        self_ref: EvalValue,
        args: Vec<EvalValue>,
    ) -> EvalRes {
        let mut inputs = method.sig.inputs.iter();
        match inputs.next() {
            Some(FnArg::Receiver(rcv))
                if rcv.reference.is_some()
                    && rcv.mutability.is_none()
                    && rcv.colon_token.is_none() => {}
            _ => return eval_unsupported("method without a `&self` receiver"),
        }
        if inputs.len() != args.len() {
            return eval_unsupported(format!("arity mismatch calling `{}`", method.sig.ident));
        }
        let mut scope = BTreeMap::new();
        scope.insert("self".to_string(), self_ref);
        for (input, arg) in inputs.zip(args) {
            let FnArg::Typed(pt) = input else {
                return eval_unsupported("method receiver");
            };
            let Pat::Ident(pi) = pt.pat.as_ref() else {
                return eval_unsupported("parameter pattern");
            };
            scope.insert(pi.ident.to_string(), eval_coerce(arg, &eval_ty_of(&pt.ty))?);
        }
        let mut frame = EvalFrame::new(scope, self.fresh_frame_id(), false);
        let value = match self.eval_block(&mut frame, &method.block) {
            Ok(v) | Err(EvalCtrl::Return(v)) => v,
            Err(EvalCtrl::Break | EvalCtrl::Continue) => {
                return eval_unsupported("`break` / `continue` outside of a loop");
            }
            Err(e) => return Err(e),
        };
        eval_coerce(value, &ret_ty_of(&method.sig.output))
    }

    /// Create the closure value of `expr`, capturing every free variable of
    /// `frame` that its body names.
    fn make_closure(&mut self, frame: &EvalFrame<'a>, expr: &'a syn::ExprClosure) -> EvalRes {
        if expr.asyncness.is_some()
            || expr.constness.is_some()
            || expr.movability.is_some()
            || expr.lifetimes.is_some()
        {
            return eval_unsupported("closure qualifier");
        }
        let mut free = ClosureFreeIdents::default();
        free.visit_expr_closure(expr);
        if free.has_macro {
            return eval_unsupported("macro in closure body");
        }
        let mut env = BTreeMap::new();
        let mut gens = Vec::new();
        for name in free.names {
            if let Some(v) = Self::lookup(frame, &name) {
                gens.push((
                    name.clone(),
                    frame.bind_gen.get(&name).copied().unwrap_or(0),
                ));
                env.insert(name, v);
            }
        }
        let id = self.closures.len();
        let captures = !env.is_empty();
        self.closures.push(EvalClosure {
            expr,
            env,
            by_move: expr.capture.is_some(),
            def_frame: frame.id,
            gens,
            local_fns: frame.local_fns.clone(),
            local_structs: frame.local_structs.clone(),
            local_methods: frame.local_methods.clone(),
        });
        Ok(EvalValue::Closure { id, captures })
    }

    /// Call closure `id` from `frame`.
    ///
    /// A closure that captures by reference and is called from the frame that
    /// created it reads its captured variables' current values (sharing their
    /// stack allocation identities for `addr_eq`) and writes any it assigns
    /// back to them (a unique borrow). A captured struct or closure may be held
    /// by reference or by value, so its address inside the closure is not
    /// modeled. A `move` closure, or a closure that captures nothing, runs on
    /// the values captured at creation; such a call must not assign a captured
    /// variable, because the evaluator has no storage that would carry the
    /// assignment to the next call. A closure that borrows its captures and is
    /// called from any other frame (for example from the body of another
    /// closure) is rejected: only the frame that created it can supply the
    /// addresses of the variables it borrows.
    fn call_closure(
        &mut self,
        frame: &mut EvalFrame<'a>,
        id: usize,
        args: Vec<EvalValue>,
    ) -> EvalRes {
        let Some(closure) = self.closures.get(id) else {
            return eval_unsupported("unknown closure");
        };
        let expr = closure.expr;
        let live = !closure.by_move && closure.def_frame == frame.id;
        let mut env = closure.env.clone();
        let local_fns = closure.local_fns.clone();
        let local_structs = closure.local_structs.clone();
        let local_methods = closure.local_methods.clone();
        if !closure.by_move && !live && !env.is_empty() {
            return eval_unsupported(
                "by-reference closure called outside the frame that created it",
            );
        }
        if live {
            for (name, generation) in &closure.gens {
                if frame.bind_gen.get(name).copied().unwrap_or(0) != *generation {
                    return eval_unsupported(format!(
                        "closure-captured variable `{name}` was bound again"
                    ));
                }
            }
        }
        let mut live_allocs = BTreeMap::new();
        // Captured variables whose address inside the closure is not modeled.
        let mut unplaced = BTreeSet::new();
        if live {
            for (name, slot) in &mut env {
                match Self::lookup(frame, name) {
                    Some(v) => *slot = v,
                    None => {
                        return eval_unsupported(format!(
                            "closure-captured variable `{name}` left scope"
                        ));
                    }
                }
                if !eval_value_is_copy(slot) {
                    unplaced.insert(name.clone());
                } else if let Some(alloc) = self.alloc_id_of(frame, name) {
                    live_allocs.insert(name.clone(), alloc);
                }
            }
        }
        if expr.inputs.len() != args.len() {
            return eval_unsupported("arity mismatch calling a closure");
        }
        let mut params = BTreeMap::new();
        for (input, arg) in expr.inputs.iter().zip(args) {
            let (pat, ty) = match input {
                Pat::Type(pt) => (pt.pat.as_ref(), eval_ty_of(&pt.ty)),
                other => (other, EvalTy::Infer),
            };
            let Pat::Ident(pi) = pat else {
                return eval_unsupported("closure parameter pattern");
            };
            if pi.subpat.is_some() || pi.by_ref.is_some() {
                return eval_unsupported("closure parameter pattern");
            }
            params.insert(pi.ident.to_string(), eval_coerce(arg, &ty)?);
        }
        let before = env.clone();
        // A closure body is not instrumented, so it runs like a callee body.
        let mut closure_frame = EvalFrame::new(env, self.fresh_frame_id(), false);
        closure_frame.local_fns = local_fns;
        closure_frame.local_structs = local_structs;
        closure_frame.local_methods = local_methods;
        if !live_allocs.is_empty()
            && let Some(allocs0) = closure_frame.allocs.first_mut()
        {
            *allocs0 = live_allocs;
        }
        closure_frame.unplaced = unplaced;
        closure_frame.push_scope(params);
        let value = match self.eval_expr(&mut closure_frame, &expr.body) {
            Ok(v) | Err(EvalCtrl::Return(v)) => v,
            Err(EvalCtrl::Break | EvalCtrl::Continue) => {
                return eval_unsupported("`break` / `continue` outside of a loop");
            }
            Err(e) => return Err(e),
        };
        let value = match &expr.output {
            ReturnType::Default => value,
            ReturnType::Type(_, ty) => eval_coerce(value, &eval_ty_of(ty))?,
        };
        let after = closure_frame.scopes.swap_remove(0);
        if after != before {
            if !live {
                return eval_unsupported("closure assigned a captured variable it does not borrow");
            }
            for (name, v) in after {
                if before.get(&name) != Some(&v) {
                    Self::assign_var(frame, &name, v)?;
                }
            }
        }
        Ok(value)
    }

    fn eval_block(&mut self, frame: &mut EvalFrame<'a>, block: &'a Block) -> EvalRes {
        let mut fns = BTreeMap::new();
        let mut structs = BTreeMap::new();
        let mut methods: EvalMethodTable<'a> = BTreeMap::new();
        for stmt in &block.stmts {
            match stmt {
                Stmt::Item(Item::Fn(f)) => {
                    fns.insert(f.sig.ident.to_string(), f);
                }
                Stmt::Item(Item::Struct(st)) => {
                    let fields: EvalStructDef = st
                        .fields
                        .iter()
                        .filter_map(|f| Some((f.ident.as_ref()?.to_string(), eval_ty_of(&f.ty))))
                        .collect();
                    // Only a non-generic struct whose fields are all named
                    // is a struct the evaluator can build and read.
                    if st.generics.params.is_empty() && fields.len() == st.fields.len() {
                        structs.insert(st.ident.to_string(), fields);
                    }
                }
                Stmt::Item(Item::Impl(im)) => {
                    let self_ty = match im.self_ty.as_ref() {
                        Type::Path(tp) if tp.qself.is_none() => tp.path.get_ident(),
                        _ => None,
                    };
                    let trait_name = match &im.trait_ {
                        None => Some(None),
                        Some((None, path, _)) => path.get_ident().map(|id| Some(id.to_string())),
                        Some((Some(_), _, _)) => None,
                    };
                    // A generic `impl`, negative `impl`, or one for a non-local
                    // type/trait registers nothing, so calling it is rejected.
                    if let Some(self_ty) = self_ty
                        && let Some(trait_name) = trait_name
                        && im.generics.params.is_empty()
                    {
                        for impl_item in &im.items {
                            if let syn::ImplItem::Fn(m) = impl_item {
                                let key = (
                                    self_ty.to_string(),
                                    trait_name.clone(),
                                    m.sig.ident.to_string(),
                                );
                                methods.insert(key, m);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        frame.push_scope(BTreeMap::new());
        frame.local_fns.push(fns);
        frame.local_structs.push(structs);
        frame.local_methods.push(methods);
        let res = self.eval_stmts(frame, &block.stmts);
        frame.local_methods.pop();
        frame.local_structs.pop();
        frame.local_fns.pop();
        frame.pop_scope();
        res
    }

    fn eval_stmts(&mut self, frame: &mut EvalFrame<'a>, stmts: &'a [Stmt]) -> EvalRes {
        let mut last = EvalValue::Unit;
        for (i, stmt) in stmts.iter().enumerate() {
            last = EvalValue::Unit;
            match stmt {
                Stmt::Local(loc) => self.eval_local(frame, loc)?,
                // Declarations that `eval_block` indexed; a trait without default
                // methods declares only signatures. Reject traits carrying default
                // method bodies up front so an empty `impl Trait for T {}` cannot
                // hide a trait method from `eval_method_call`'s inherent-vs-trait
                // ambiguity check.
                Stmt::Item(Item::Fn(_) | Item::Struct(_) | Item::Impl(_)) => {}
                Stmt::Item(Item::Trait(tr)) => {
                    if tr.items.iter().any(|item| {
                        matches!(item, syn::TraitItem::Fn(f) if f.default.is_some())
                    }) {
                        return eval_unsupported("trait with a default method");
                    }
                }
                Stmt::Item(_) => return eval_unsupported("nested item"),
                Stmt::Expr(e, semi) => {
                    let v = self.eval_expr(frame, e)?;
                    if semi.is_none() && i + 1 == stmts.len() {
                        last = v;
                    }
                }
                Stmt::Macro(_) => return eval_unsupported("macro statement"),
            }
        }
        Ok(last)
    }

    fn eval_local(
        &mut self,
        frame: &mut EvalFrame<'a>,
        loc: &'a syn::Local,
    ) -> Result<(), EvalCtrl> {
        if let Pat::Slice(ps) = &loc.pat {
            let Some(init) = &loc.init else {
                return eval_unsupported("uninitialized `let`");
            };
            if init.diverge.is_some() {
                return eval_unsupported("`let ... else`");
            }
            let v = self.eval_expr(frame, &init.expr)?;
            return Self::bind_slice_pattern(frame, ps, v);
        }
        let (name, ty) = match &loc.pat {
            Pat::Ident(pi) if pi.subpat.is_none() && pi.by_ref.is_none() => {
                (Some(pi.ident.to_string()), EvalTy::Infer)
            }
            Pat::Wild(_) => (None, EvalTy::Infer),
            Pat::Type(pt) => match pt.pat.as_ref() {
                Pat::Ident(pi) if pi.subpat.is_none() && pi.by_ref.is_none() => {
                    (Some(pi.ident.to_string()), eval_ty_of(&pt.ty))
                }
                Pat::Wild(_) => (None, eval_ty_of(&pt.ty)),
                _ => return eval_unsupported("`let` pattern"),
            },
            _ => return eval_unsupported("`let` pattern"),
        };
        let Some(init) = &loc.init else {
            return eval_unsupported("uninitialized `let`");
        };
        if init.diverge.is_some() {
            return eval_unsupported("`let ... else`");
        }
        let v = self.eval_expr(frame, &init.expr)?;
        let v = eval_coerce(v, &ty)?;
        if let Some(name) = name {
            frame.bind(name, v);
        }
        Ok(())
    }

    /// Bind the identifiers of the irrefutable array pattern `ps` (elements
    /// that are `_`, an identifier, `..`, or `name @ ..`) to the elements of
    /// `v`: an array, or a reference to one, in which case every identifier
    /// binds a reference to its element or sub-array.
    fn bind_slice_pattern(
        frame: &mut EvalFrame<'a>,
        ps: &'a syn::PatSlice,
        v: EvalValue,
    ) -> Result<(), EvalCtrl> {
        let (elems, base_addr, by_ref) = match v {
            EvalValue::Array(elems) => (elems, None, false),
            EvalValue::Ref(r) => {
                let r = r.autoderef();
                let local_addr = match r.addr {
                    Some(EvalAddr::Local(alloc, off)) => Some((alloc, off)),
                    _ => None,
                };
                match r.val {
                    EvalValue::Array(elems) => (elems, local_addr, true),
                    _ => return eval_unsupported("array pattern on a non-array"),
                }
            }
            _ => return eval_unsupported("array pattern on a non-array"),
        };
        let is_rest = |p: &Pat| match p {
            Pat::Rest(_) => true,
            Pat::Ident(pi) => {
                matches!(pi.subpat.as_ref(), Some((_, sub)) if matches!(**sub, Pat::Rest(_)))
            }
            _ => false,
        };
        let pats: Vec<&Pat> = ps.elems.iter().collect();
        let rest_positions: Vec<usize> = (0..pats.len()).filter(|&i| is_rest(pats[i])).collect();
        let (rest_pos, rest_len) = match rest_positions.as_slice() {
            [] if pats.len() == elems.len() => (None, 0),
            [pos] if pats.len() - 1 <= elems.len() => (Some(*pos), elems.len() - (pats.len() - 1)),
            _ => return eval_unsupported("array pattern length mismatch"),
        };
        // Byte offset of element `idx` from the array's start, when every
        // element before it has a known size.
        let offset_of = |idx: usize| -> Option<u64> {
            let mut off = 0u64;
            for e in &elems[..idx] {
                off = off.checked_add(eval_value_size(e)?)?;
            }
            Some(off)
        };
        for (i, pat) in pats.iter().enumerate() {
            // Elements `[start, end)` that pattern element `i` covers.
            let (start, end) = match rest_pos {
                Some(pos) if i == pos => (pos, pos + rest_len),
                Some(pos) if i > pos => (i - 1 + rest_len, i + rest_len),
                _ => (i, i + 1),
            };
            let pi = match pat {
                Pat::Wild(_) | Pat::Rest(_) => continue,
                Pat::Ident(pi) if pi.by_ref.is_none() && pi.mutability.is_none() => pi,
                _ => return eval_unsupported("array pattern element"),
            };
            let covered = if is_rest(pat) {
                EvalValue::Array(elems[start..end].to_vec())
            } else if pi.subpat.is_none() {
                elems[start].clone()
            } else {
                return eval_unsupported("array pattern element");
            };
            let bound = if by_ref {
                let addr = match (base_addr, offset_of(start)) {
                    (Some((alloc, base_off)), Some(off)) => base_off
                        .checked_add(off)
                        .map(|total| EvalAddr::Local(alloc, total)),
                    _ => None,
                };
                EvalValue::Ref(Box::new(EvalRef {
                    addr,
                    val: covered,
                    dyn_trait: None,
                }))
            } else {
                covered
            };
            frame.bind(pi.ident.to_string(), bound);
        }
        Ok(())
    }

    fn lookup(frame: &EvalFrame<'a>, name: &str) -> Option<EvalValue> {
        frame
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    /// Identity of the variable `name` of `frame` (for `EvalRef::addr`),
    /// assigned on first use; `None` for a variable whose address is not
    /// modeled (`EvalFrame::unplaced`).
    fn alloc_id_of(&mut self, frame: &mut EvalFrame<'a>, name: &str) -> Option<u64> {
        let depth = frame
            .scopes
            .iter()
            .rposition(|scope| scope.contains_key(name))?;
        if depth == 0 && frame.unplaced.contains(name) {
            return None;
        }
        if let Some(&id) = frame.allocs[depth].get(name) {
            return Some(id);
        }
        let id = self.next_alloc_id;
        self.next_alloc_id += 1;
        frame.allocs[depth].insert(name.to_string(), id);
        Some(id)
    }

    /// The shared reference `&place`.
    ///
    /// A variable has an address of its own; an array element's is its
    /// array's plus the sizes of the elements before it; a struct field's
    /// depends on a layout the evaluator does not compute, and a temporary's
    /// may be shared with another constant's, so neither is modeled.
    fn eval_borrow(&mut self, frame: &mut EvalFrame<'a>, place: &'a Expr) -> EvalRes {
        let unplaced = |val: EvalValue| {
            Ok(EvalValue::Ref(Box::new(EvalRef {
                addr: None,
                val,
                dyn_trait: None,
            })))
        };
        match place {
            Expr::Paren(p) => self.eval_borrow(frame, &p.expr),
            Expr::Group(g) => self.eval_borrow(frame, &g.expr),
            Expr::Path(p) if p.qself.is_none() && p.path.get_ident().is_some() => {
                let name = p
                    .path
                    .get_ident()
                    .map(ToString::to_string)
                    .unwrap_or_default();
                let Some(val) = Self::lookup(frame, &name) else {
                    // A function item: `&f` borrows a temporary.
                    let val = self.eval_expr(frame, place)?;
                    return unplaced(val);
                };
                let addr = self
                    .alloc_id_of(frame, &name)
                    .map(|alloc| EvalAddr::Local(alloc, 0));
                Ok(EvalValue::Ref(Box::new(EvalRef {
                    addr,
                    val,
                    dyn_trait: None,
                })))
            }
            Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
                match self.eval_expr(frame, &u.expr)? {
                    r @ EvalValue::Ref(_) => Ok(r),
                    _ => eval_unsupported("dereference of a non-reference"),
                }
            }
            Expr::Field(f) => {
                let EvalValue::Ref(base) = self.eval_borrow(frame, &f.base)? else {
                    return eval_unsupported("field borrow");
                };
                match (base.autoderef().val, &f.member) {
                    (EvalValue::Struct(_, fields), syn::Member::Named(id)) => {
                        match fields.get(&id.to_string()) {
                            Some(val) => unplaced(val.clone()),
                            None => eval_unsupported(format!("unknown field `{id}`")),
                        }
                    }
                    _ => eval_unsupported("field borrow"),
                }
            }
            Expr::Index(ix) => {
                let EvalValue::Ref(base) = self.eval_borrow(frame, &ix.expr)? else {
                    return eval_unsupported("index borrow");
                };
                let base = base.autoderef();
                let EvalValue::Array(elems) = base.val else {
                    return eval_unsupported("index of a non-array");
                };
                let idx = self.eval_index(frame, &ix.index, elems.len())?;
                let mut addr = match base.addr {
                    Some(EvalAddr::Local(alloc, off)) => Some((alloc, off)),
                    _ => None,
                };
                for e in &elems[..idx] {
                    addr = match (addr, eval_value_size(e)) {
                        (Some((alloc, off)), Some(sz)) => off.checked_add(sz).map(|o| (alloc, o)),
                        _ => None,
                    };
                }
                Ok(EvalValue::Ref(Box::new(EvalRef {
                    addr: addr.map(|(alloc, off)| EvalAddr::Local(alloc, off)),
                    val: elems[idx].clone(),
                    dyn_trait: None,
                })))
            }
            _ => {
                let val = self.eval_expr(frame, place)?;
                unplaced(val)
            }
        }
    }

    /// Evaluate the index expression of `base[index]` for an array of `len`
    /// elements: an out-of-bounds index panics, as the bounds check does.
    fn eval_index(
        &mut self,
        frame: &mut EvalFrame<'a>,
        index: &'a Expr,
        len: usize,
    ) -> Result<usize, EvalCtrl> {
        match self.eval_expr(frame, index)? {
            EvalValue::Int(i, EvalIntTy::Usize | EvalIntTy::Infer) => match usize::try_from(i) {
                Ok(i) if i < len => Ok(i),
                _ => Err(EvalCtrl::Panic),
            },
            _ => eval_unsupported("non-`usize` index"),
        }
    }

    fn assign(frame: &mut EvalFrame<'a>, target: &Expr, v: EvalValue) -> Result<(), EvalCtrl> {
        let Expr::Path(p) = target else {
            return eval_unsupported("assignment target");
        };
        let Some(id) = p.path.get_ident() else {
            return eval_unsupported("assignment target path");
        };
        Self::assign_var(frame, &id.to_string(), v)
    }

    /// Assign `v` to the innermost variable `name` of `frame`.
    fn assign_var(frame: &mut EvalFrame<'a>, name: &str, v: EvalValue) -> Result<(), EvalCtrl> {
        for scope in frame.scopes.iter_mut().rev() {
            if let Some(slot) = scope.get_mut(name) {
                let new = match (&*slot, v) {
                    (EvalValue::Int(_, t), EvalValue::Int(x, EvalIntTy::Infer)) => {
                        eval_coerce(EvalValue::Int(x, EvalIntTy::Infer), &EvalTy::Int(*t))?
                    }
                    (_, v) => v,
                };
                *slot = new;
                return Ok(());
            }
        }
        eval_unsupported(format!("assignment to unknown variable `{name}`"))
    }

    fn eval_expr(&mut self, frame: &mut EvalFrame<'a>, expr: &'a Expr) -> EvalRes {
        self.tick()?;
        match expr {
            Expr::Lit(l) => eval_lit(&l.lit),
            Expr::Path(p) => {
                let Some(id) = p.path.get_ident() else {
                    return eval_unsupported("multi-segment path");
                };
                let name = id.to_string();
                if let Some(v) = Self::lookup(frame, &name) {
                    return Ok(v);
                }
                // A function nested in an enclosing block, used as a value.
                // (A top-level function is a trace boundary: a call through a
                // pointer to it would bypass the boundary's instrumentation.)
                let local_fn = frame
                    .local_fns
                    .iter()
                    .rev()
                    .find_map(|fns| fns.get(&name).copied());
                match local_fn {
                    Some(f) => Ok(EvalValue::FnRef(self.fn_ref_index(f))),
                    None => eval_unsupported(format!("unknown variable `{id}`")),
                }
            }
            Expr::Paren(p) => self.eval_expr(frame, &p.expr),
            Expr::Group(g) => self.eval_expr(frame, &g.expr),
            Expr::Block(b) if b.label.is_none() => self.eval_block(frame, &b.block),
            Expr::Unary(u) => match (&u.op, self.eval_expr(frame, &u.expr)?) {
                (syn::UnOp::Deref(_), EvalValue::Ref(r)) => {
                    // Dereferencing `&dyn Trait` yields an unsized trait object
                    // place; returning `r.val` would drop `dyn_trait` and let
                    // `(*r).method()` dispatch to an inherent `impl`.
                    if r.dyn_trait.is_some() {
                        return eval_unsupported("dereference of a trait object");
                    }
                    Ok(r.val)
                }
                (syn::UnOp::Not(_), EvalValue::Bool(b)) => Ok(EvalValue::Bool(!b)),
                (syn::UnOp::Not(_), EvalValue::Int(x, t)) if t != EvalIntTy::Infer => {
                    Ok(EvalValue::Int(!x & t.max(), t))
                }
                _ => eval_unsupported("unary operator"),
            },
            Expr::Binary(b) => self.eval_binary(frame, b),
            Expr::Cast(c) => match (self.eval_expr(frame, &c.expr)?, eval_ty_of(&c.ty)) {
                (EvalValue::Int(x, _), EvalTy::Int(t)) if t != EvalIntTy::Infer => {
                    Ok(EvalValue::Int(x & t.max(), t))
                }
                (EvalValue::Bool(b), EvalTy::Int(t)) if t != EvalIntTy::Infer => {
                    Ok(EvalValue::Int(u128::from(b), t))
                }
                // Safe trait-object unsizing (`&T as &dyn Trait`): records the
                // vtable's principal trait while preserving referent & address.
                (EvalValue::Ref(r), EvalTy::DynRef(tr)) => {
                    let mut inner = r.autoderef();
                    inner.dyn_trait = Some(tr);
                    Ok(EvalValue::Ref(Box::new(inner)))
                }
                // Safe cast between non-trait reference types (`&[T; N] as &[T]`).
                (v @ EvalValue::Ref(_), EvalTy::Ref) => Ok(v),
                // Safe raw-pointer casts (`&T as *const T`, `fn(...) as *const ()`,
                // `*const T as *const ()`).
                (EvalValue::Ref(r), EvalTy::ConstPtr) => Ok(EvalValue::ConstPtr {
                    addr: r.addr,
                    nonzero: eval_value_is_sized_nonzero(&r.val),
                }),
                (EvalValue::FnRef(idx), EvalTy::ConstPtr) => Ok(EvalValue::ConstPtr {
                    addr: Some(EvalAddr::FnItem(idx)),
                    nonzero: true,
                }),
                (
                    EvalValue::Closure {
                        id,
                        captures: false,
                    },
                    EvalTy::ConstPtr,
                ) => Ok(EvalValue::ConstPtr {
                    addr: Some(EvalAddr::ClosureFn(id)),
                    nonzero: true,
                }),
                (v @ EvalValue::ConstPtr { .. }, EvalTy::ConstPtr) => Ok(v),
                _ => eval_unsupported("cast"),
            },
            Expr::If(i) => self.eval_if(frame, i),
            Expr::Match(m) => self.eval_match(frame, m),
            Expr::While(w) => self.eval_while(frame, w),
            Expr::Assign(a) => {
                let v = self.eval_expr(frame, &a.right)?;
                Self::assign(frame, &a.left, v)?;
                Ok(EvalValue::Unit)
            }
            Expr::Call(c) => self.eval_call(frame, c),
            Expr::Struct(s) => self.eval_struct_lit(frame, s),
            Expr::Field(f) => match (eval_autoderef(self.eval_expr(frame, &f.base)?), &f.member) {
                (EvalValue::Struct(_, fields), syn::Member::Named(id)) => fields
                    .get(&id.to_string())
                    .cloned()
                    .map_or_else(|| eval_unsupported(format!("unknown field `{id}`")), Ok),
                _ => eval_unsupported("field access"),
            },
            Expr::Return(r) => {
                let v = match &r.expr {
                    Some(e) => self.eval_expr(frame, e)?,
                    None => EvalValue::Unit,
                };
                Err(EvalCtrl::Return(v))
            }
            Expr::Break(b) if b.label.is_none() && b.expr.is_none() => Err(EvalCtrl::Break),
            Expr::Continue(c) if c.label.is_none() => Err(EvalCtrl::Continue),
            Expr::Reference(r) if r.mutability.is_none() => self.eval_borrow(frame, &r.expr),
            Expr::Array(a) => {
                let mut elems = Vec::with_capacity(a.elems.len());
                for e in &a.elems {
                    elems.push(self.eval_expr(frame, e)?);
                }
                Ok(EvalValue::Array(elems))
            }
            Expr::Index(ix) => match eval_autoderef(self.eval_expr(frame, &ix.expr)?) {
                EvalValue::Array(elems) => {
                    let idx = self.eval_index(frame, &ix.index, elems.len())?;
                    Ok(elems[idx].clone())
                }
                _ => eval_unsupported("index of a non-array"),
            },
            Expr::Closure(c) => self.make_closure(frame, c),
            Expr::MethodCall(mc) => self.eval_method_call(frame, mc),
            _ => eval_unsupported(format!(
                "expression `{}`",
                quote!(#expr).to_string().chars().take(48).collect::<String>()
            )),
        }
    }

    fn eval_binary(&mut self, frame: &mut EvalFrame<'a>, b: &'a syn::ExprBinary) -> EvalRes {
        if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) {
            let EvalValue::Bool(lv) = self.eval_expr(frame, &b.left)? else {
                return eval_unsupported("non-boolean `&&` / `||` operand");
            };
            self.record_branch(frame, b, u128::from(lv));
            let short_circuits = if matches!(b.op, BinOp::And(_)) { !lv } else { lv };
            if short_circuits {
                return Ok(EvalValue::Bool(lv));
            }
            return match self.eval_expr(frame, &b.right)? {
                EvalValue::Bool(rv) => Ok(EvalValue::Bool(rv)),
                _ => eval_unsupported("non-boolean `&&` / `||` operand"),
            };
        }
        if let Some(base_op) = compound_assign_base(&b.op) {
            let cur = self.eval_expr(frame, &b.left)?;
            let rhs = self.eval_expr(frame, &b.right)?;
            let v = eval_binop(&base_op, cur, rhs)?;
            Self::assign(frame, &b.left, v)?;
            return Ok(EvalValue::Unit);
        }
        let l = self.eval_expr(frame, &b.left)?;
        let r = self.eval_expr(frame, &b.right)?;
        eval_binop(&b.op, l, r)
    }

    fn eval_if(&mut self, frame: &mut EvalFrame<'a>, i: &'a syn::ExprIf) -> EvalRes {
        let EvalValue::Bool(cv) = self.eval_expr(frame, &i.cond)? else {
            return eval_unsupported("non-boolean `if` condition");
        };
        self.record_branch(frame, i, u128::from(cv));
        if cv {
            self.eval_block(frame, &i.then_branch)
        } else if let Some((_, e)) = &i.else_branch {
            self.eval_expr(frame, e)
        } else {
            Ok(EvalValue::Unit)
        }
    }

    fn eval_match(&mut self, frame: &mut EvalFrame<'a>, m: &'a syn::ExprMatch) -> EvalRes {
        let scrutinee = self.eval_expr(frame, &m.expr)?;
        let tag = match &scrutinee {
            EvalValue::Int(v, _) => *v,
            EvalValue::Bool(b) => u128::from(*b),
            _ => return eval_unsupported("`match` on a non-scalar scrutinee"),
        };
        for arm in &m.arms {
            if arm.guard.is_some() {
                return eval_unsupported("match arm guard");
            }
            let mut bindings = BTreeMap::new();
            if !eval_pattern_matches(&arm.pat, &scrutinee, &mut bindings)? {
                continue;
            }
            self.record_branch(frame, m, tag);
            frame.push_scope(bindings);
            let res = self.eval_expr(frame, &arm.body);
            frame.pop_scope();
            return res;
        }
        eval_unsupported("no `match` arm matched (non-exhaustive pattern subset)")
    }

    fn eval_while(&mut self, frame: &mut EvalFrame<'a>, w: &'a syn::ExprWhile) -> EvalRes {
        if w.label.is_some() {
            return eval_unsupported("labeled loop");
        }
        loop {
            self.tick()?;
            let EvalValue::Bool(cv) = self.eval_expr(frame, &w.cond)? else {
                return eval_unsupported("non-boolean `while` condition");
            };
            self.record_branch(frame, w, u128::from(cv));
            if !cv {
                return Ok(EvalValue::Unit);
            }
            match self.eval_block(frame, &w.body) {
                Ok(_) | Err(EvalCtrl::Continue) => {}
                Err(EvalCtrl::Break) => return Ok(EvalValue::Unit),
                Err(e) => return Err(e),
            }
        }
    }

    fn eval_struct_lit(&mut self, frame: &mut EvalFrame<'a>, s: &'a syn::ExprStruct) -> EvalRes {
        if s.rest.is_some() || s.qself.is_some() {
            return eval_unsupported("struct literal with `..` or qualified path");
        }
        let Some(id) = s.path.get_ident() else {
            return eval_unsupported("struct literal path");
        };
        let name = id.to_string();
        // A struct declared in an enclosing block shadows a top-level one.
        let local_def = frame
            .local_structs
            .iter()
            .rev()
            .find_map(|structs| structs.get(&name).cloned());
        let Some(def) = local_def.or_else(|| self.ev.structs.get(&name).cloned()) else {
            return eval_unsupported(format!("unknown struct `{name}`"));
        };
        let mut fields = BTreeMap::new();
        for fv in &s.fields {
            let syn::Member::Named(fid) = &fv.member else {
                return eval_unsupported("tuple struct literal");
            };
            let fname = fid.to_string();
            let Some((_, fty)) = def.iter().find(|(n, _)| *n == fname) else {
                return eval_unsupported(format!("unknown field `{fname}`"));
            };
            let fty = fty.clone();
            let v = self.eval_expr(frame, &fv.expr)?;
            fields.insert(fname, eval_coerce(v, &fty)?);
        }
        if fields.len() != def.len() {
            return eval_unsupported("struct literal with missing fields");
        }
        Ok(EvalValue::Struct(name, fields))
    }

    fn eval_call(&mut self, frame: &mut EvalFrame<'a>, c: &'a syn::ExprCall) -> EvalRes {
        let Expr::Path(p) = c.func.as_ref() else {
            return eval_unsupported("call target");
        };
        if p.qself.is_none() && is_core_ptr_addr_eq_path(&p.path) {
            if c.args.len() != 2 {
                return eval_unsupported("arity mismatch calling `addr_eq`");
            }
            let lhs = self.eval_expr(frame, &c.args[0])?;
            let rhs = self.eval_expr(frame, &c.args[1])?;
            // A raw pointer may dangle, and a dead variable's address may be
            // reused (two calls of one function place their locals at one
            // address): compare a raw pointer into a variable only while that
            // variable is in scope in this frame.
            for operand in [&lhs, &rhs] {
                if let EvalValue::ConstPtr {
                    addr: Some(EvalAddr::Local(alloc, _)),
                    ..
                } = operand
                    && !frame
                        .allocs
                        .iter()
                        .any(|scope| scope.values().any(|id| id == alloc))
                {
                    return eval_unsupported(
                        "`addr_eq` on a raw pointer whose referent may be out of scope",
                    );
                }
            }
            return eval_addr_eq(&lhs, &rhs);
        }
        let Some(id) = p.path.get_ident() else {
            return eval_unsupported("qualified call target");
        };
        let name = id.to_string();
        // A variable shadows a function of the same name.
        let callee_var = Self::lookup(frame, &name);
        let mut args = Vec::with_capacity(c.args.len());
        for a in &c.args {
            args.push(self.eval_expr(frame, a)?);
        }
        match callee_var {
            Some(EvalValue::Closure { id, .. }) => return self.call_closure(frame, id, args),
            Some(EvalValue::FnRef(idx)) => {
                let Some(&f) = self.fn_table.get(idx) else {
                    return eval_unsupported("unknown function pointer");
                };
                return self.call_fn(f, args, false);
            }
            Some(_) => return eval_unsupported(format!("call of non-callable `{name}`")),
            None => {}
        }
        for fns in frame.local_fns.iter().rev() {
            if let Some(&f) = fns.get(&name) {
                return self.call_fn(f, args, false);
            }
        }
        let ev = self.ev;
        let Some(f) = ev.top_fn(&name) else {
            return eval_unsupported(format!("unknown callee `{name}`"));
        };
        if name == ev.root_fn_name {
            return eval_unsupported("recursive call of the root function");
        }
        if !frame.is_root {
            return self.call_fn(f, args, false);
        }
        self.external_call(f, name, args)
    }

    /// Index of `f` in `fn_table`, adding it on first use.
    fn fn_ref_index(&mut self, f: &'a syn::ItemFn) -> usize {
        match self.fn_table.iter().position(|g| std::ptr::eq(*g, f)) {
            Some(idx) => idx,
            None => {
                self.fn_table.push(f);
                self.fn_table.len() - 1
            }
        }
    }

    /// Call `receiver.method(args)` on a struct declared in an enclosing block
    /// (directly, or behind a reference such as a `&dyn Trait`): a `&dyn Trait`
    /// receiver dispatches strictly to `(Self, Some(Trait), method)`; a concrete
    /// receiver prefers an inherent `impl` and otherwise requires a unique
    /// matching trait `impl` in scope.
    fn eval_method_call(
        &mut self,
        frame: &mut EvalFrame<'a>,
        mc: &'a syn::ExprMethodCall,
    ) -> EvalRes {
        if mc.turbofish.is_some() {
            return eval_unsupported("method call with generic arguments");
        }
        // Auto-reference a by-value receiver, so that `self` is a reference
        // in either case. (The receiver is evaluated once; the address of an
        // auto-referenced receiver is left unmodeled.)
        let self_ref = match self.eval_expr(frame, &mc.receiver)? {
            EvalValue::Ref(r) => EvalValue::Ref(Box::new(r.autoderef())),
            val => EvalValue::Ref(Box::new(EvalRef {
                addr: None,
                val,
                dyn_trait: None,
            })),
        };
        let EvalValue::Ref(r) = self_ref else {
            return eval_unsupported("method receiver");
        };
        let EvalValue::Struct(ty_name, _) = &r.val else {
            return eval_unsupported("method call on a non-struct receiver");
        };
        let method_name = mc.method.to_string();
        let method = if let Some(ref tr) = r.dyn_trait {
            let key = (ty_name.clone(), Some(tr.clone()), method_name.clone());
            frame
                .local_methods
                .iter()
                .rev()
                .find_map(|methods| methods.get(&key).copied())
        } else {
            let inherent_key = (ty_name.clone(), None, method_name.clone());
            if let Some(m) = frame
                .local_methods
                .iter()
                .rev()
                .find_map(|methods| methods.get(&inherent_key).copied())
            {
                // The evaluator records `&dyn Trait` only at the coercion
                // sites it sees (a typed `let`, parameter, field, or return
                // value, and an `as` cast). A reference that an `if` / `match`
                // arm or an array element unsizes implicitly reaches here
                // without `dyn_trait`, where native Rust dispatches through
                // the vtable to the trait `impl`. When a trait `impl` of the
                // receiver's type also defines this method, the inherent
                // `impl` is therefore not known to be the callee.
                let trait_also_defines = frame.local_methods.iter().any(|methods| {
                    methods
                        .keys()
                        .any(|(s, tr, mn)| s == ty_name && tr.is_some() && mn == &method_name)
                });
                if trait_also_defines {
                    return eval_unsupported(format!(
                        "method `{}` defined by both an inherent and a trait `impl`",
                        mc.method
                    ));
                }
                Some(m)
            } else {
                let mut found: Option<&'a syn::ImplItemFn> = None;
                let mut ambiguous = false;
                for methods in frame.local_methods.iter().rev() {
                    for ((s, tr, mn), &m) in methods {
                        if s == ty_name && tr.is_some() && mn == &method_name {
                            if found.is_some() {
                                ambiguous = true;
                                break;
                            }
                            found = Some(m);
                        }
                    }
                    if ambiguous {
                        break;
                    }
                }
                if ambiguous { None } else { found }
            }
        };
        let Some(method) = method else {
            return eval_unsupported(format!("unknown or ambiguous method `{}`", mc.method));
        };
        let mut args = Vec::with_capacity(mc.args.len());
        for a in &mc.args {
            args.push(self.eval_expr(frame, a)?);
        }
        // Inside an `impl` body, `self` has the concrete `&Self` type rather
        // than `&dyn Trait`.
        let concrete_self = EvalValue::Ref(Box::new(EvalRef {
            addr: r.addr,
            val: r.val,
            dyn_trait: None,
        }));
        self.call_method(method, concrete_self, args)
    }

    fn external_call(
        &mut self,
        f: &'a syn::ItemFn,
        callee: String,
        args: Vec<EvalValue>,
    ) -> EvalRes {
        if f.sig.inputs.len() != args.len() {
            return eval_unsupported(format!("arity mismatch calling `{callee}`"));
        }
        let mut typed = Vec::with_capacity(args.len());
        let mut raw_args = Vec::with_capacity(args.len());
        for (input, arg) in f.sig.inputs.iter().zip(args) {
            let FnArg::Typed(pt) = input else {
                return eval_unsupported("method receiver");
            };
            let v = eval_coerce(arg, &eval_ty_of(&pt.ty))?;
            raw_args.push(eval_encode(&v)?);
            typed.push(v);
        }
        let global_idx = self.global_call_idx;
        self.global_call_idx += 1;
        let key = format!("{}{callee}", self.callee_key_prefix);
        match self.schedule.next_action(&key, global_idx) {
            EnvAction::PanicOnCall(_) => {
                self.events.push(ItreeConcreteEvent::ExtCallPanic {
                    callee,
                    args: raw_args,
                });
                Err(EvalCtrl::Panic)
            }
            EnvAction::ReturnBytes(bytes) => {
                let v = eval_decode(&bytes, &ret_ty_of(&f.sig.output))?;
                self.events.push(ItreeConcreteEvent::ExtCall {
                    callee,
                    args: raw_args,
                    ret: bytes,
                });
                Ok(v)
            }
            EnvAction::PassThrough => match self.call_fn(f, typed, false) {
                Ok(v) => {
                    let ret = eval_encode(&v)?;
                    self.events.push(ItreeConcreteEvent::ExtCall {
                        callee,
                        args: raw_args,
                        ret,
                    });
                    Ok(v)
                }
                Err(EvalCtrl::Panic) => {
                    self.events.push(ItreeConcreteEvent::ExtCallPanic {
                        callee,
                        args: raw_args,
                    });
                    Err(EvalCtrl::Panic)
                }
                Err(e) => Err(e),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Evaluator-verified concolic `argPinTerm` / `negArgPinTerm` exploration.
// ---------------------------------------------------------------------------

/// Root inputs `(magic, payload_len)` of the fixed boundary probes from which
/// [`synthesize_itree_concolic_trials`] relaxes pins by default (the non-panic
/// probes of `itree_eval`'s trial builder).
pub const ITREE_CONCOLIC_BASE_INPUTS: [(u32, u32); 8] = [
    (0x414E_4E4C, 2048),
    (0x414E_4E4C, 64),
    (0x0000_0010, 0x80),
    (0x0000_0000, 0),
    (0x0000_0001, 1),
    (0x0000_0002, 2),
    (0x0000_0003, 3),
    (0xDEAD_BEEF, 0),
];

/// Number of return-value perturbation rounds per pin once argument negation
/// is exhausted.
const ITREE_CONCOLIC_RET_ROUNDS: usize = 2;

/// One concolic trial synthesized by [`explore_itree_concolic_trials`] and
/// verified by re-executing the candidate with [`ItreeConcreteEvaluator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItreeConcolicTrial {
    /// Root input `magic`.
    pub magic: u32,
    /// Root input `payload_len`.
    pub payload_len: u32,
    /// Environment schedule (staged callee keys); empty for argument negations
    /// and branch flips, prefix-return pins plus one perturbed return for
    /// return-value perturbations.
    pub schedule: EnvSchedule,
    /// Exploration phase (`NegateCallArg` / `PerturbOracleReturn` / `FlipBranchGuard`).
    pub phase: ConcolicTrialPhase,
    /// Index into the explorer's base inputs of the concrete run this trial relaxes.
    pub base_index: usize,
    /// Event position, in the base run, of the relaxed call or flipped decision.
    pub target_event_pos: usize,
    /// Predicted `(events, outcome)` of the candidate on this trial.
    pub predicted: ItreeConcreteRun,
}

/// Deterministic candidate root inputs for steering a run away from base input
/// `(m0, p0)`: single-field variations (which keep guards on the other field),
/// dictionary constants, correlated variations preserving `m ^ p`, `m - p`, and
/// `m + p` (so calls whose arguments mix both inputs stay pinned), and seeded
/// random draws.
fn concolic_candidate_pool(
    m0: u32,
    p0: u32,
    dict: &MirInputDictionary,
    seed: u64,
) -> Vec<(u32, u32)> {
    const DELTAS: [u32; 21] = [
        1, 2, 3, 4, 7, 8, 12, 15, 16, 32, 48, 64, 0x80, 0x100, 0x200, 0x400, 0x401, 0x800,
        0x1000, 0x2000, 0x8000_0000,
    ];
    let mut values: Vec<u32> = Vec::new();
    let mut push_value = |v: u128| {
        if let Ok(v) = u32::try_from(v)
            && !values.contains(&v)
        {
            values.push(v);
        }
    };
    for name in ["magic", "payload_len"] {
        for &h in dict.field_hints.get(name).map(Vec::as_slice).unwrap_or(&[]) {
            push_value(h);
            push_value(h.wrapping_add(1));
            push_value(h.wrapping_sub(1));
        }
    }
    for v in dict.candidates_for_width(32).into_iter().take(48) {
        push_value(v);
    }

    let mut pool = Vec::new();
    let mut seen = BTreeSet::new();
    let mut push = |m: u32, p: u32| {
        if (m, p) != (m0, p0) && seen.insert((m, p)) {
            pool.push((m, p));
        }
    };
    for d in DELTAS {
        push(m0, p0.wrapping_add(d));
        push(m0, p0.wrapping_sub(d));
        push(m0, p0 ^ d);
    }
    for &v in &values {
        push(m0, v);
    }
    for d in DELTAS {
        push(m0.wrapping_add(d), p0);
        push(m0.wrapping_sub(d), p0);
        push(m0 ^ d, p0);
    }
    for &v in &values {
        push(v, p0);
    }
    for d in DELTAS {
        push(m0 ^ d, p0 ^ d);
        push(m0.wrapping_add(d), p0.wrapping_add(d));
        push(m0.wrapping_add(d), p0.wrapping_sub(d));
    }
    let mut rng = DetRng::new(seed ^ (u64::from(m0) << 32) ^ u64::from(p0));
    for _ in 0..24 {
        push(rng.next_u64() as u32, p0);
        push(m0, rng.next_u64() as u32);
        push(rng.next_u64() as u32, rng.next_u64() as u32);
    }
    pool
}

/// Branch / callee / outcome skeleton of a run (call values erased), used to
/// prefer argument negations and return perturbations that steer execution onto
/// an unseen observable path.
fn concolic_path_shape(run: &ItreeConcreteRun) -> Vec<(u32, u128, &str)> {
    let mut shape: Vec<(u32, u128, &str)> = run
        .events
        .iter()
        .map(|ev| match ev {
            ItreeConcreteEvent::Branch { site, tag } => (*site, *tag, ""),
            ItreeConcreteEvent::ExtCall { callee, .. } => (u32::MAX, 0, callee.as_str()),
            ItreeConcreteEvent::ExtCallPanic { callee, .. } => (u32::MAX, 1, callee.as_str()),
        })
        .collect();
    if matches!(run.outcome, ItreeConcreteOutcome::Panic) {
        shape.push((u32::MAX, 2, "__panic"));
    }
    shape
}

/// Owned [`concolic_path_shape`]: the run's observable path skeleton (branch
/// decisions and callee sequence, call values erased) — the evaluator-side
/// analogue of the native `compute_itree_obs_shape_hash` that
/// `cumulative_distinct_obs_paths` counts (which also ignores call values).
type ConcolicShape = Vec<(u32, u128, String)>;

fn concolic_owned_shape(run: &ItreeConcreteRun) -> ConcolicShape {
    concolic_path_shape(run)
        .into_iter()
        .map(|(site, tag, callee)| (site, tag, callee.to_string()))
        .collect()
}

/// Maximum number of prefix-preserving argument negations examined per pin and
/// round while looking for one that also reaches an unseen path shape.
const ITREE_CONCOLIC_SHAPE_SEARCH_LIMIT: usize = 128;

/// Ordered `(site, tag)` sequence of all branch decisions in `run`.
fn concolic_branch_decisions(run: &ItreeConcreteRun) -> Vec<(u32, u128)> {
    run.events
        .iter()
        .filter_map(|ev| match ev {
            ItreeConcreteEvent::Branch { site, tag } => Some((*site, *tag)),
            _ => None,
        })
        .collect()
}

type ConcolicArgKey = (Vec<ItreeConcreteEvent>, String);

/// Records every boundary call of `run` under its exact event prefix, so later
/// negations of the same pin (same prefix, same callee) exclude these tuples.
fn register_concolic_args(
    seen_args: &mut BTreeMap<ConcolicArgKey, BTreeSet<Vec<Vec<u8>>>>,
    run: &ItreeConcreteRun,
) {
    for (pos, ev) in run.events.iter().enumerate() {
        if let ItreeConcreteEvent::ExtCall { callee, args, .. }
        | ItreeConcreteEvent::ExtCallPanic { callee, args } = ev
        {
            seen_args
                .entry((run.events[..pos].to_vec(), callee.clone()))
                .or_default()
                .insert(args.clone());
        }
    }
}

struct ConcolicPinState {
    base: usize,
    pin_idx: usize,
    pos: usize,
    pin: ArgPinConstraint,
    exhausted: Option<ArgPinFallbackReason>,
}

/// Evaluator-verified concolic exploration over an ITree candidate, following
/// `Nightowl.MultiInterp.relaxPinConstraint` / `flipBranchGuard` with concrete
/// re-execution in place of an SMT solver:
///
/// 1. **`argPinTerm` negation** (round-robin over every boundary call `j` of every
///    base run, for at most `ceil(max_trials / 2)` rounds): search deterministic
///    candidate inputs for one whose run keeps the base run's exact event prefix
///    before call `j` (all earlier branch decisions = `guards.take beforeGuardIdx`,
///    all earlier calls with identical arguments and returns = `pins.take pinIdx`)
///    and reaches call `j` on the same callee with an argument tuple satisfying
///    `neg_arg_pin_term` (distinct from the base arguments and from every tuple
///    already exercised at that prefix), whether call `j` then returns or its
///    callee unwinds on the new arguments. Among such negations the one reaching an
///    unseen path shape is preferred (the path after call `j` is unconstrained, and
///    `cumulative_distinct_obs_paths` ignores call values, so only new shapes add
///    observable paths), then one keeping the base's branch decisions. 0-argument
///    calls are skipped (`negArgPinTerm` is `false`), and calls whose argument
///    domain is exhausted or that no candidate input can steer fall back.
/// 2. **Oracle return perturbation**, strictly after every argument negation:
///    the base input with prefix-return pins plus a perturbed return for call `j`
///    (identical arguments), preferring returns that reach an unseen path shape.
/// 3. **Branch flips** with any remaining budget.
///
/// Every emitted trial's predicted run is distinct from all base runs and earlier
/// trials, and the whole procedure is deterministic for fixed inputs and `seed_u64`.
pub fn explore_itree_concolic_trials(
    source: &str,
    root_fn_name: &str,
    callee_key_prefix: &str,
    base_inputs: &[(u32, u32)],
    dict: &MirInputDictionary,
    max_trials: usize,
    seed_u64: u64,
) -> Vec<ItreeConcolicTrial> {
    let mut out: Vec<ItreeConcolicTrial> = Vec::new();
    if max_trials == 0 {
        return out;
    }
    let Ok(ev) = ItreeConcreteEvaluator::new(source, root_fn_name) else {
        return out;
    };
    let empty = EnvSchedule::new();
    let mut run_cache: BTreeMap<(u32, u32), Option<std::rc::Rc<ItreeConcreteRun>>> =
        BTreeMap::new();
    let mut run_plain = |m: u32, p: u32| -> Option<std::rc::Rc<ItreeConcreteRun>> {
        run_cache
            .entry((m, p))
            .or_insert_with(|| {
                ev.run_kernel_step(m, p, &empty, callee_key_prefix)
                    .ok()
                    .map(std::rc::Rc::new)
            })
            .clone()
    };

    let mut bases: Vec<(usize, u32, u32, ItreeConcreteRun)> = Vec::new();
    for (idx, &(m, p)) in base_inputs.iter().enumerate() {
        if bases.iter().any(|b| (b.1, b.2) == (m, p)) {
            continue;
        }
        if let Some(run) = run_plain(m, p) {
            bases.push((idx, m, p, (*run).clone()));
        }
    }
    let mut seen_runs: BTreeSet<ItreeConcreteRun> = bases.iter().map(|b| b.3.clone()).collect();
    // Path shapes already covered (bases and accepted trials): the coverage
    // metric `cumulative_distinct_obs_paths` only grows on a new shape.
    let mut seen_shapes: BTreeSet<ConcolicShape> =
        bases.iter().map(|b| concolic_owned_shape(&b.3)).collect();
    let mut used_plain_inputs: BTreeSet<(u32, u32)> = bases.iter().map(|b| (b.1, b.2)).collect();
    let mut seen_args: BTreeMap<ConcolicArgKey, BTreeSet<Vec<Vec<u8>>>> = BTreeMap::new();
    for b in &bases {
        register_concolic_args(&mut seen_args, &b.3);
    }
    let pools: Vec<Vec<(u32, u32)>> = bases
        .iter()
        .map(|b| concolic_candidate_pool(b.1, b.2, dict, seed_u64 ^ (b.0 as u64)))
        .collect();

    let mut pins: Vec<ConcolicPinState> = Vec::new();
    for (bi, b) in bases.iter().enumerate() {
        let mut pin_idx = 0usize;
        for (pos, ev_item) in b.3.events.iter().enumerate() {
            let (callee, args, ret) = match ev_item {
                ItreeConcreteEvent::ExtCall { callee, args, ret } => {
                    (callee.as_str(), args.as_slice(), ret.clone())
                }
                ItreeConcreteEvent::ExtCallPanic { callee, args } => {
                    let ret_len = ev
                        .callee_return_layout(callee)
                        .map(|l| l.size_bytes)
                        .unwrap_or(0);
                    (callee.as_str(), args.as_slice(), vec![0u8; ret_len])
                }
                _ => continue,
            };
            let mut pin = ArgPinConstraint::new(
                pin_idx,
                callee,
                b.3.branches_before(pos),
                args.to_vec(),
                ret,
            );
            if let Some(layouts) = ev.callee_arg_layouts(callee)
                && layouts.len() == args.len()
            {
                pin = pin.with_arg_layouts(layouts);
            }
            let exhausted = pin.is_zero_arg().then_some(ArgPinFallbackReason::ZeroArgCall);
            pins.push(ConcolicPinState {
                base: bi,
                pin_idx,
                pos,
                pin,
                exhausted,
            });
            pin_idx += 1;
        }
    }

    // Phase 1: `negArgPinTerm` under preserved prefix guards and earlier full pins,
    // capped at `ceil(max_trials / 2)` rounds so a call with an unbounded (`u32`)
    // argument domain cannot starve the return-value and branch phases.
    let arg_round_cap = max_trials.div_ceil(2).max(1);
    let mut arg_round = 0usize;
    while out.len() < max_trials && arg_round < arg_round_cap {
        arg_round += 1;
        let mut progressed = false;
        for ps in &mut pins {
            if out.len() >= max_trials {
                break;
            }
            if ps.exhausted.is_some() {
                continue;
            }
            let base = &bases[ps.base].3;
            let key = (base.events[..ps.pos].to_vec(), ps.pin.callee.clone());
            for tuple in seen_args.get(&key).into_iter().flatten() {
                ps.pin.record_excluded_arg_tuple(tuple.clone());
            }
            if ps.pin.is_arg_domain_exhausted() {
                ps.exhausted = Some(ArgPinFallbackReason::DomainExhausted);
                continue;
            }
            // Among prefix-preserving negations prefer, in order: one reaching an
            // unseen path shape (downstream of call `j` the path is unconstrained by
            // `relaxPinConstraint`, and only a new shape adds an observable path),
            // then one keeping the base's branch decisions, then the first found.
            let base_branches = concolic_branch_decisions(base);
            type Found = (u32, u32, Vec<Vec<u8>>, std::rc::Rc<ItreeConcreteRun>);
            let mut new_shape_found: Option<Found> = None;
            let mut branch_preserving_found: Option<Found> = None;
            let mut first_found: Option<Found> = None;
            let mut satisfying = 0usize;
            for &(m, p) in &pools[ps.base] {
                if used_plain_inputs.contains(&(m, p)) {
                    continue;
                }
                let Some(run) = run_plain(m, p) else {
                    continue;
                };
                if !run.shares_prefix_with(base, ps.pos) || seen_runs.contains(&*run) {
                    continue;
                }
                // The call may return or unwind on its new arguments: either way
                // it was made with `arg != prev_arg` under the preserved prefix
                // (the native recorder logs an unwinding pass-through call as
                // `ExtCallPanic` with its `raw_args`), and a callee panic is a new
                // observable outcome that only argument steering can reach.
                let (callee, args) = match run.events.get(ps.pos) {
                    Some(ItreeConcreteEvent::ExtCall { callee, args, .. })
                    | Some(ItreeConcreteEvent::ExtCallPanic { callee, args }) => (callee, args),
                    _ => continue,
                };
                if *callee != ps.pin.callee || !ps.pin.neg_arg_pin_term(args) {
                    continue;
                }
                let args = args.clone();
                if !seen_shapes.contains(&concolic_owned_shape(&run)) {
                    new_shape_found = Some((m, p, args, run));
                    break;
                }
                if branch_preserving_found.is_none()
                    && concolic_branch_decisions(&run) == base_branches
                {
                    branch_preserving_found = Some((m, p, args.clone(), run.clone()));
                }
                if first_found.is_none() {
                    first_found = Some((m, p, args, run));
                }
                satisfying += 1;
                if satisfying >= ITREE_CONCOLIC_SHAPE_SEARCH_LIMIT {
                    break;
                }
            }
            let found = new_shape_found.or(branch_preserving_found).or(first_found);
            match found {
                Some((m, p, new_args, run)) => {
                    let run = (*run).clone();
                    register_concolic_args(&mut seen_args, &run);
                    ps.pin.record_excluded_arg_tuple(new_args.clone());
                    if ps.pin.is_arg_domain_exhausted() {
                        ps.exhausted = Some(ArgPinFallbackReason::DomainExhausted);
                    }
                    used_plain_inputs.insert((m, p));
                    seen_shapes.insert(concolic_owned_shape(&run));
                    seen_runs.insert(run.clone());
                    out.push(ItreeConcolicTrial {
                        magic: m,
                        payload_len: p,
                        schedule: EnvSchedule::new(),
                        phase: ConcolicTrialPhase::NegateCallArg {
                            pin_idx: ps.pin_idx,
                            callee: ps.pin.callee.clone(),
                            new_arg_tuple: new_args,
                        },
                        base_index: bases[ps.base].0,
                        target_event_pos: ps.pos,
                        predicted: run,
                    });
                    progressed = true;
                }
                None => {
                    ps.exhausted = Some(if ps.pin.is_arg_domain_exhausted() {
                        ArgPinFallbackReason::DomainExhausted
                    } else {
                        ArgPinFallbackReason::PrefixLocked
                    });
                }
            }
        }
        if !progressed {
            break;
        }
    }
    for ps in &mut pins {
        if ps.exhausted.is_none() {
            let base = &bases[ps.base].3;
            let key = (base.events[..ps.pos].to_vec(), ps.pin.callee.clone());
            for tuple in seen_args.get(&key).into_iter().flatten() {
                ps.pin.record_excluded_arg_tuple(tuple.clone());
            }
            ps.exhausted = Some(if ps.pin.is_arg_domain_exhausted() {
                ArgPinFallbackReason::DomainExhausted
            } else {
                ArgPinFallbackReason::NegationRoundCapReached
            });
        }
    }

    // Phase 2: oracle return perturbation on identical arguments, pinning every
    // earlier call's return so the FIFO schedule stays aligned with the prefix.
    let mut used_rets: BTreeMap<ConcolicArgKey, BTreeSet<Vec<u8>>> = BTreeMap::new();
    for _round in 0..ITREE_CONCOLIC_RET_ROUNDS {
        for ps in &pins {
            if out.len() >= max_trials {
                break;
            }
            let (b_idx, m0, p0, base) = {
                let b = &bases[ps.base];
                (b.0, b.1, b.2, &b.3)
            };
            let (callee, args, ret, base_panicked) = match &base.events[ps.pos] {
                ItreeConcreteEvent::ExtCall { callee, args, ret } => (callee, args, ret, false),
                ItreeConcreteEvent::ExtCallPanic { callee, args } => {
                    (callee, args, &ps.pin.ret_bytes, true)
                }
                _ => continue,
            };
            if ret.is_empty() {
                continue;
            }
            let ret_layout = ev
                .callee_return_layout(callee)
                .unwrap_or_else(|| ScalarLayout::unsigned(ret.len().min(16)));
            if ret_layout.valid_start == ret_layout.valid_end {
                continue;
            }
            let key = (base.events[..ps.pos].to_vec(), callee.clone());
            let used = used_rets.entry(key).or_insert_with(|| {
                if base_panicked {
                    BTreeSet::new()
                } else {
                    BTreeSet::from([ret.clone()])
                }
            });
            let mut prefix_sched = EnvSchedule::new();
            for prior in &base.events[..ps.pos] {
                if let ItreeConcreteEvent::ExtCall { callee, ret, .. } = prior {
                    let k = format!("{callee_key_prefix}{callee}");
                    prefix_sched.register_callee_return_size(&k, ret.len());
                    prefix_sched.push_callee_response(&k, ret.clone());
                }
            }
            let target_key = format!("{callee_key_prefix}{callee}");
            let ret_bits = {
                let mut le = [0u8; 16];
                let n = ret.len().min(16);
                le[..n].copy_from_slice(&ret[..n]);
                u128::from_le_bytes(le)
            };
            let width = (ret.len().min(16) * 8) as u32;
            let mut cands: Vec<u128> = vec![
                0,
                1,
                ret_bits ^ 1,
                ret_bits.wrapping_add(1),
                ret_bits.wrapping_sub(1),
                width_mask(width),
                ret_bits ^ (1u128 << width.saturating_sub(1)),
            ];
            cands.extend(dict.candidates_for_width(width).into_iter().take(16));
            let mut fallback: Option<(Vec<u8>, EnvSchedule, ItreeConcreteRun)> = None;
            let mut chosen: Option<(Vec<u8>, EnvSchedule, ItreeConcreteRun)> = None;
            for bits in cands {
                let masked = bits & width_mask(width);
                if masked < ret_layout.valid_start || masked > ret_layout.valid_end {
                    continue;
                }
                let bytes = masked.to_le_bytes()[..ret.len().min(16)].to_vec();
                if used.contains(&bytes) {
                    continue;
                }
                let mut sched = prefix_sched.clone();
                sched.register_callee_return_size(&target_key, ret.len());
                sched.push_callee_response(&target_key, bytes.clone());
                let Ok(run) = ev.run_kernel_step(m0, p0, &sched, callee_key_prefix) else {
                    continue;
                };
                let follows = run.shares_prefix_with(base, ps.pos)
                    && matches!(
                        run.events.get(ps.pos),
                        Some(ItreeConcreteEvent::ExtCall { callee: c, args: a, ret: r })
                            if c == callee && a == args && *r == bytes
                    );
                if !follows || seen_runs.contains(&run) {
                    continue;
                }
                if !seen_shapes.contains(&concolic_owned_shape(&run)) {
                    chosen = Some((bytes, sched, run));
                    break;
                }
                if fallback.is_none() {
                    fallback = Some((bytes, sched, run));
                }
            }
            if let Some((bytes, sched, run)) = chosen.or(fallback) {
                used.insert(bytes);
                seen_shapes.insert(concolic_owned_shape(&run));
                seen_runs.insert(run.clone());
                out.push(ItreeConcolicTrial {
                    magic: m0,
                    payload_len: p0,
                    schedule: sched,
                    phase: ConcolicTrialPhase::PerturbOracleReturn {
                        pin_idx: ps.pin_idx,
                        callee: callee.clone(),
                        reason: ps
                            .exhausted
                            .unwrap_or(ArgPinFallbackReason::NegationRoundCapReached),
                    },
                    base_index: b_idx,
                    target_event_pos: ps.pos,
                    predicted: run,
                });
            }
        }
    }

    // Phase 3: flip branch decisions (keeping every earlier event fixed).
    for (bi, b) in bases.iter().enumerate() {
        let mut guard_idx = 0usize;
        for (pos, event) in b.3.events.iter().enumerate() {
            if out.len() >= max_trials {
                return out;
            }
            let ItreeConcreteEvent::Branch { site, tag } = event else {
                continue;
            };
            let found = pools[bi].iter().find_map(|&(m, p)| {
                if used_plain_inputs.contains(&(m, p)) {
                    return None;
                }
                let run = run_plain(m, p)?;
                let flipped = run.shares_prefix_with(&b.3, pos)
                    && matches!(
                        run.events.get(pos),
                        Some(ItreeConcreteEvent::Branch { site: s, tag: t })
                            if s == site && t != tag
                    );
                (flipped && !seen_runs.contains(&*run)).then_some((m, p, run))
            });
            if let Some((m, p, run)) = found {
                let run = (*run).clone();
                let new_tag = match run.events[pos] {
                    ItreeConcreteEvent::Branch { tag, .. } => tag,
                    _ => *tag,
                };
                used_plain_inputs.insert((m, p));
                register_concolic_args(&mut seen_args, &run);
                seen_shapes.insert(concolic_owned_shape(&run));
                seen_runs.insert(run.clone());
                out.push(ItreeConcolicTrial {
                    magic: m,
                    payload_len: p,
                    schedule: EnvSchedule::new(),
                    phase: ConcolicTrialPhase::FlipBranchGuard {
                        guard_idx,
                        flipped_bits: new_tag,
                    },
                    base_index: b.0,
                    target_event_pos: pos,
                    predicted: run,
                });
            }
            guard_idx += 1;
        }
    }
    out
}

/// Synthesizes up to `trials` deterministic `(magic, payload_len, EnvSchedule)`
/// concolic inputs for an ITree candidate by relaxing the boundary-call pins of
/// its runs on [`ITREE_CONCOLIC_BASE_INPUTS`] (see [`explore_itree_concolic_trials`]):
/// argument-negating trials (`arg != prev_arg` under identical prefixes) come
/// before oracle return-value perturbations, followed by branch flips.
pub fn synthesize_itree_concolic_trials(
    source: &str,
    root_fn_name: &str,
    staged_prefix: &str,
    dict: &MirInputDictionary,
    trials: usize,
    seed_u64: u64,
) -> Vec<(u32, u32, EnvSchedule)> {
    explore_itree_concolic_trials(
        source,
        root_fn_name,
        staged_prefix,
        &ITREE_CONCOLIC_BASE_INPUTS,
        dict,
        trials,
        seed_u64,
    )
    .into_iter()
    .map(|t| (t.magic, t.payload_len, t.schedule))
    .collect()
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

    fn le32(v: u32) -> Vec<u8> {
        v.to_le_bytes().to_vec()
    }

    fn ext_call(callee: &str, args: &[u32], ret: u32) -> ItreeConcreteEvent {
        ItreeConcreteEvent::ExtCall {
            callee: callee.to_string(),
            args: args.iter().map(|&a| le32(a)).collect(),
            ret: le32(ret),
        }
    }

    fn branch(site: u32, tag: u128) -> ItreeConcreteEvent {
        ItreeConcreteEvent::Branch { site, tag }
    }

    #[test]
    fn concrete_evaluator_reproduces_seed_semantics_schedules_and_overflow_panics() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let empty = EnvSchedule::new();
        let ev0 = ItreeConcreteEvaluator::new(seeds[0], "kernel_step").expect("seed 0");
        assert_eq!(ev0.external_callees(), vec!["ext_oracle".to_string()]);
        // `if magic == 0x414E_4E4C` (site 0) -> `if payload_len > 1024` (site 1).
        let r = ev0.run_kernel_step(0x414E_4E4C, 2048, &empty, "b0_c0__").unwrap();
        assert_eq!(
            r.events,
            vec![branch(0, 1), branch(1, 1), ext_call("ext_oracle", &[2048], 1543)]
        );
        assert_eq!(r.outcome, ItreeConcreteOutcome::Return(le32(1543)));
        let r = ev0.run_kernel_step(0x414E_4E4C, 64, &empty, "b0_c0__").unwrap();
        assert_eq!(
            r.events,
            vec![branch(0, 1), branch(1, 0), ext_call("ext_oracle", &[65], 55)]
        );
        // `else if payload_len == 0x80` is site 2.
        let r = ev0.run_kernel_step(0x10, 0x80, &empty, "b0_c0__").unwrap();
        assert_eq!(
            r.events,
            vec![branch(0, 0), branch(2, 1), ext_call("ext_oracle", &[0x80], 103)]
        );
        let r = ev0.run_kernel_step(0, 0, &empty, "b0_c0__").unwrap();
        assert_eq!(r.events, vec![branch(0, 0), branch(2, 0)]);
        assert_eq!(r.outcome, ItreeConcreteOutcome::Return(le32(0)));

        // Scheduled `PanicOnCall(0)` unwinds at the first boundary call; a queued
        // response (staged key) replaces the callee's return.
        let r = ev0
            .run_kernel_step(
                0x414E_4E4C,
                2048,
                &EnvSchedule::new().with_panic_on_call(0),
                "b0_c0__",
            )
            .unwrap();
        assert_eq!(
            r.events,
            vec![
                branch(0, 1),
                branch(1, 1),
                ItreeConcreteEvent::ExtCallPanic {
                    callee: "ext_oracle".to_string(),
                    args: vec![le32(2048)],
                },
            ]
        );
        assert_eq!(r.outcome, ItreeConcreteOutcome::Panic);
        let mut sched = EnvSchedule::new();
        sched.push_callee_response("b0_c0__ext_oracle", le32(7));
        let r = ev0.run_kernel_step(0x414E_4E4C, 2048, &sched, "b0_c0__").unwrap();
        assert_eq!(r.events[2], ext_call("ext_oracle", &[2048], 7));
        assert_eq!(r.outcome, ItreeConcreteOutcome::Return(le32(7)));

        // Seed 2: `match magic % 4` arm 3 chains three boundary calls.
        let ev2 = ItreeConcreteEvaluator::new(seeds[2], "kernel_step").unwrap();
        let r = ev2.run_kernel_step(3, 3, &empty, "p__").unwrap();
        assert_eq!(
            r.events,
            vec![
                branch(0, 3),
                ext_call("ext_oracle", &[3], 26),
                ext_call("ext_oracle", &[26], 141),
                ext_call("ext_oracle", &[141], 716),
            ]
        );
        // Seed 3: `while i < payload_len % 4` loop decisions interleave with calls.
        let ev3 = ItreeConcreteEvaluator::new(seeds[3], "kernel_step").unwrap();
        let r = ev3.run_kernel_step(1, 3, &empty, "p__").unwrap();
        assert_eq!(
            r.events,
            vec![
                branch(0, 1),
                ext_call("ext_oracle", &[1], 4128),
                branch(0, 1),
                ext_call("ext_oracle", &[4128], 6192),
                branch(0, 1),
                ext_call("ext_oracle", &[6192], 7224),
                branch(0, 0),
            ]
        );
        assert_eq!(r.outcome, ItreeConcreteOutcome::Return(le32(7224)));

        // `-C opt-level=0` overflow checks: in the root body after a returning call,
        // and inside a pass-through callee body (recorded as an unwinding call).
        let overflow_src = r#"
            pub fn ext_id(x: u32) -> u32 { x }
            pub fn ext_inc(x: u32) -> u32 { x + 1 }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                if payload_len == 7 { ext_inc(magic) } else { ext_id(magic) + payload_len }
            }
        "#;
        let evo = ItreeConcreteEvaluator::new(overflow_src, "kernel_step").unwrap();
        let r = evo.run_kernel_step(u32::MAX, 1, &empty, "").unwrap();
        assert_eq!(
            r.events,
            vec![branch(0, 0), ext_call("ext_id", &[u32::MAX], u32::MAX)]
        );
        assert_eq!(r.outcome, ItreeConcreteOutcome::Panic);
        let r = evo.run_kernel_step(u32::MAX, 7, &empty, "").unwrap();
        assert_eq!(
            r.events,
            vec![
                branch(0, 1),
                ItreeConcreteEvent::ExtCallPanic {
                    callee: "ext_inc".to_string(),
                    args: vec![le32(u32::MAX)],
                },
            ]
        );
        assert_eq!(r.outcome, ItreeConcreteOutcome::Panic);

        // Constructs outside the subset are rejected instead of guessed.
        let method_src = r#"
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 { magic.wrapping_add(payload_len) }
        "#;
        let evm = ItreeConcreteEvaluator::new(method_src, "kernel_step").unwrap();
        assert!(evm.run_kernel_step(1, 2, &empty, "").is_err());
        assert!(ItreeConcreteEvaluator::new(method_src, "missing_root").is_err());

        // An integer `match` records the `switchInt` discriminant (like the native
        // harness), so two scrutinees reaching one wildcard arm stay distinct.
        let wildcard_src = r#"
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                match payload_len { 0 => magic, _ => 1 }
            }
        "#;
        let evw = ItreeConcreteEvaluator::new(wildcard_src, "kernel_step").unwrap();
        let r5 = evw.run_kernel_step(9, 5, &empty, "").unwrap();
        let r7 = evw.run_kernel_step(9, 7, &empty, "").unwrap();
        assert_eq!(r5.events, vec![branch(0, 5)]);
        assert_eq!(r7.events, vec![branch(0, 7)]);
        assert_eq!(r5.outcome, r7.outcome);
        assert_ne!(r5, r7);
    }

    #[test]
    fn concrete_evaluator_supports_every_generated_itree_candidate() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let mut evaluated = 0usize;
        for batch_seed in [0x3333_4444u64, 0xABCD_1234, 0x1111_2222, 0x9999_AAAA] {
            for cand in generate_itree_batch(seeds, 20, batch_seed)
                .into_iter()
                .chain(generate_itree_identity_batch(seeds))
            {
                let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step")
                    .unwrap_or_else(|e| panic!("candidate {}: {e}", cand.id));
                for (m, p) in ITREE_CONCOLIC_BASE_INPUTS {
                    for sched in [EnvSchedule::new(), EnvSchedule::new().with_panic_on_call(0)] {
                        ev.run_kernel_step(m, p, &sched, "b0_c0__").unwrap_or_else(|e| {
                            panic!(
                                "candidate {} ({:?}) unsupported on ({m:#x}, {p:#x}): {e}\n{}",
                                cand.id, cand.applied_mutators, cand.source
                            )
                        });
                        evaluated += 1;
                    }
                }
            }
        }
        assert!(evaluated >= 4 * 24 * 8 * 2);
    }

    /// Cross-checks the evaluator against natively compiled candidates
    /// (`rustc -C opt-level=0 -C overflow-checks=on`): every boundary call's
    /// arguments and return, the unwinding call, and the root outcome must match
    /// the prediction on the base inputs and on the concolic argument-negation /
    /// branch-flip trials synthesized from them.
    #[test]
    fn concrete_evaluator_matches_native_rustc_boundary_calls_on_generated_candidates() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let cands: Vec<GeneratedItreeCandidate> = generate_itree_batch(seeds, 20, 0x3333_4444)
            .into_iter()
            .chain(generate_itree_identity_batch(seeds))
            .collect();
        assert_evaluator_matches_native_rustc(&cands);
    }

    /// Compile `cands` natively (`rustc -C opt-level=0 -C overflow-checks=on`)
    /// with every boundary callee wrapped to log its arguments and return, and
    /// compare each run on the base inputs and on the synthesized concolic
    /// inputs against the evaluator's prediction.
    fn assert_evaluator_matches_native_rustc(cands: &[GeneratedItreeCandidate]) {
        assert_evaluator_matches_native_rustc_at_opt_levels(cands, &["0"]);
    }

    fn assert_evaluator_matches_native_rustc_at_opt_levels(
        cands: &[GeneratedItreeCandidate],
        opt_levels: &[&str],
    ) {
        use std::fmt::Write as _;
        let mut program = String::from(
            "#![allow(dead_code, unused_parens, non_snake_case, non_camel_case_types)]\n\
             use std::cell::RefCell;\n\
             thread_local! { static LOG: RefCell<Vec<String>> = RefCell::new(Vec::new()); }\n\
             fn log(s: String) { LOG.with(|l| l.borrow_mut().push(s)); }\n\
             fn run(label: &str, f: impl FnOnce() -> u32 + std::panic::UnwindSafe) {\n\
             LOG.with(|l| l.borrow_mut().clear());\n\
             let res = std::panic::catch_unwind(f);\n\
             let mut line = label.to_string();\n\
             for entry in LOG.with(|l| l.borrow().clone()) { line.push(' '); line.push_str(&entry); }\n\
             match res { Ok(v) => line.push_str(&format!(\" => {v}\")), Err(_) => line.push_str(\" => panic\") }\n\
             println!(\"{line}\");\n}\n",
        );
        let mut main_body = String::new();
        let mut expected: Vec<String> = Vec::new();
        for (ci, cand) in cands.iter().enumerate() {
            let mut file = syn::parse_file(&cand.source).unwrap();
            let mut wrappers: Vec<Item> = Vec::new();
            for item in &mut file.items {
                let Item::Fn(f) = item else { continue };
                if f.sig.ident == "kernel_step" {
                    continue;
                }
                let name = f.sig.ident.clone();
                let name_str = name.to_string();
                let orig = format_ident!("__orig_{}", name);
                let params: Vec<Ident> = f
                    .sig
                    .inputs
                    .iter()
                    .filter_map(|a| match a {
                        FnArg::Typed(pt) => match pt.pat.as_ref() {
                            Pat::Ident(pi) => Some(pi.ident.clone()),
                            _ => None,
                        },
                        FnArg::Receiver(_) => None,
                    })
                    .collect();
                let inputs = f.sig.inputs.clone();
                let output = f.sig.output.clone();
                f.sig.ident = orig.clone();
                wrappers.push(syn::parse_quote! {
                    fn #name(#inputs) #output {
                        let __args: Vec<String> = vec![#(format!("{:?}", #params)),*];
                        log(format!("call {}({})", #name_str, __args.join(", ")));
                        let __r = #orig(#(#params),*);
                        log(format!("ret {:?}", __r));
                        __r
                    }
                });
            }
            file.items.extend(wrappers);
            let _ = writeln!(
                program,
                "mod c{ci} {{\nuse super::log;\n{}\n}}",
                prettyplease::unparse(&file)
            );

            let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step").unwrap();
            let dict = MirInputDictionary::from_rust_source(&cand.source).unwrap();
            let mut inputs: Vec<(u32, u32)> = ITREE_CONCOLIC_BASE_INPUTS.to_vec();
            for t in explore_itree_concolic_trials(
                &cand.source,
                "kernel_step",
                "",
                &ITREE_CONCOLIC_BASE_INPUTS,
                &dict,
                6,
                cand.seed_u64,
            ) {
                if t.schedule == EnvSchedule::new() {
                    inputs.push((t.magic, t.payload_len));
                }
            }
            let u32_of = |b: &[u8]| u32::from_le_bytes(b[..4].try_into().unwrap());
            for (m, p) in inputs {
                let run = ev.run_kernel_step(m, p, &EnvSchedule::new(), "").unwrap();
                let mut line = format!("c{ci} {m} {p}:");
                for e in &run.events {
                    let render = |callee: &str, args: &[Vec<u8>]| {
                        let vals: Vec<String> =
                            args.iter().map(|a| u32_of(a).to_string()).collect();
                        format!(" call {callee}({})", vals.join(", "))
                    };
                    match e {
                        ItreeConcreteEvent::ExtCall { callee, args, ret } => {
                            line.push_str(&render(callee, args));
                            let _ = write!(line, " ret {}", u32_of(ret));
                        }
                        ItreeConcreteEvent::ExtCallPanic { callee, args } => {
                            line.push_str(&render(callee, args));
                        }
                        ItreeConcreteEvent::Branch { .. } => {}
                    }
                }
                match &run.outcome {
                    ItreeConcreteOutcome::Return(b) => {
                        let _ = write!(line, " => {}", u32_of(b));
                    }
                    ItreeConcreteOutcome::Panic => line.push_str(" => panic"),
                }
                expected.push(line);
                let _ = writeln!(
                    main_body,
                    "    run(\"c{ci} {m} {p}:\", || c{ci}::kernel_step({m}u32, {p}u32));"
                );
            }
        }
        let _ = write!(
            program,
            "fn main() {{\nstd::panic::set_hook(Box::new(|_| {{}}));\n{main_body}}}\n"
        );
        let dir = std::env::temp_dir().join(format!(
            "anneal-itree-eval-native-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let src_path = dir.join("native_check.rs");
        std::fs::write(&src_path, &program).unwrap();
        for &opt_level in opt_levels {
            let bin_path = dir.join(format!("native_check_o{opt_level}"));
            let opt_flag = format!("opt-level={opt_level}");
            let compile = std::process::Command::new(crate::miri_eval::resolve_rustc_bin())
                .args([
                    "--edition=2024",
                    "-C",
                    &opt_flag,
                    "-C",
                    "overflow-checks=on",
                    "-A",
                    "warnings",
                ])
                .arg(&src_path)
                .arg("-o")
                .arg(&bin_path)
                .output()
                .expect("invoke rustc");
            assert!(
                compile.status.success(),
                "rustc (-C {opt_flag}) failed:\n{}",
                String::from_utf8_lossy(&compile.stderr)
            );
            let out = std::process::Command::new(&bin_path)
                .output()
                .expect("run native check");
            assert!(
                out.status.success(),
                "native check binary (-C {opt_flag}) failed"
            );
            let native: Vec<String> = String::from_utf8_lossy(&out.stdout)
                .lines()
                .map(str::to_string)
                .collect();
            assert_eq!(native.len(), expected.len());
            for (n, e) in native.iter().zip(&expected) {
                assert_eq!(
                    n, e,
                    "evaluator prediction diverges from native execution at -C {opt_flag}"
                );
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
        assert!(expected.len() >= cands.len() * ITREE_CONCOLIC_BASE_INPUTS.len());
    }

    /// `argPinTerm` negation on `CallBoundaryOutliner` / `ExtOracleInjector`
    /// candidates: every `NegateCallArg` trial re-executes with the base run's
    /// exact prefix (earlier branch decisions and earlier calls with identical
    /// arguments and returns) and reaches the pinned call with a never-seen
    /// argument tuple, whereas return-only perturbation of the same calls keeps
    /// their arguments identical (`arg == prev_arg`) and adds no new
    /// `(callee, arg_tuple)` coverage at the pinned calls.
    #[test]
    fn concolic_arg_pin_negation_preserves_prefix_and_beats_return_only_perturbation() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let mut checked_outliner = 0usize;
        let mut checked_injector = 0usize;
        let mut total_concolic_new = 0usize;
        let mut total_return_only_new = 0usize;
        for batch_seed in [0x3333_4444u64, 0xABCD_1234] {
            for cand in generate_itree_batch(seeds, 24, batch_seed) {
                let has_mutator = |name: &str| cand.applied_mutators.iter().any(|m| m == name);
                let has_outliner = has_mutator("CallBoundaryOutliner");
                let has_injector = has_mutator("ExtOracleInjector");
                if !has_outliner && !has_injector {
                    continue;
                }
                let dict = MirInputDictionary::from_rust_source(&cand.source).unwrap();
                let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step").unwrap();
                let empty = EnvSchedule::new();
                let base_runs: Vec<ItreeConcreteRun> = ITREE_CONCOLIC_BASE_INPUTS
                    .iter()
                    .map(|&(m, p)| ev.run_kernel_step(m, p, &empty, "b0_c0__").unwrap())
                    .collect();
                let trials = explore_itree_concolic_trials(
                    &cand.source,
                    "kernel_step",
                    "b0_c0__",
                    &ITREE_CONCOLIC_BASE_INPUTS,
                    &dict,
                    12,
                    cand.seed_u64,
                );
                // Determinism.
                assert_eq!(
                    trials,
                    explore_itree_concolic_trials(
                        &cand.source,
                        "kernel_step",
                        "b0_c0__",
                        &ITREE_CONCOLIC_BASE_INPUTS,
                        &dict,
                        12,
                        cand.seed_u64,
                    )
                );

                let mut seen_at_pin: BTreeMap<ConcolicArgKey, BTreeSet<Vec<Vec<u8>>>> =
                    BTreeMap::new();
                for r in &base_runs {
                    register_concolic_args(&mut seen_at_pin, r);
                }
                let mut seen_runs: BTreeSet<ItreeConcreteRun> = base_runs.iter().cloned().collect();
                let mut concolic_new = 0usize;
                let mut return_only_new = 0usize;
                let mut return_only_seen = seen_at_pin.clone();
                let mut saw_negation = false;
                let mut saw_return_phase = false;
                for t in &trials {
                    let rerun = ev
                        .run_kernel_step(t.magic, t.payload_len, &t.schedule, "b0_c0__")
                        .unwrap();
                    assert_eq!(rerun, t.predicted, "trial prediction must replay exactly");
                    assert!(seen_runs.insert(rerun.clone()), "duplicate predicted trace");
                    let base = &base_runs[t.base_index];
                    assert!(
                        rerun.shares_prefix_with(base, t.target_event_pos),
                        "candidate {}: trial {:?} broke the prefix guards/pins",
                        cand.id,
                        t.phase
                    );
                    let ItreeConcreteEvent::ExtCall {
                        callee: base_callee,
                        args: base_args,
                        ret: base_ret,
                    } = &base.events[t.target_event_pos]
                    else {
                        assert!(matches!(t.phase, ConcolicTrialPhase::FlipBranchGuard { .. }));
                        continue;
                    };
                    let key = (base.events[..t.target_event_pos].to_vec(), base_callee.clone());
                    match (&t.phase, &rerun.events[t.target_event_pos]) {
                        (
                            ConcolicTrialPhase::NegateCallArg {
                                callee,
                                new_arg_tuple,
                                ..
                            },
                            ItreeConcreteEvent::ExtCall { callee: c, args, .. }
                            | ItreeConcreteEvent::ExtCallPanic { callee: c, args },
                        ) => {
                            assert!(
                                !saw_return_phase,
                                "argument negation must precede return perturbation"
                            );
                            saw_negation = true;
                            assert_eq!((callee, c), (base_callee, base_callee));
                            assert_eq!(args, new_arg_tuple);
                            assert_ne!(args, base_args, "arg != prev_arg");
                            assert!(
                                seen_at_pin.entry(key.clone()).or_default().insert(args.clone()),
                                "negated argument tuple was already exercised at this pin"
                            );
                            concolic_new += 1;
                            register_concolic_args(&mut seen_at_pin, &rerun);

                            // Return-only analogue: same base input, prefix returns pinned,
                            // perturbed return at the same call.
                            let mut sched = EnvSchedule::new();
                            for prior in &base.events[..t.target_event_pos] {
                                if let ItreeConcreteEvent::ExtCall { callee, ret, .. } = prior {
                                    sched.push_callee_response(
                                        &format!("b0_c0__{callee}"),
                                        ret.clone(),
                                    );
                                }
                            }
                            let mut flipped = base_ret.clone();
                            flipped[0] ^= 1;
                            sched.push_callee_response(&format!("b0_c0__{base_callee}"), flipped);
                            let (bm, bp) = ITREE_CONCOLIC_BASE_INPUTS[t.base_index];
                            let ro = ev.run_kernel_step(bm, bp, &sched, "b0_c0__").unwrap();
                            assert!(ro.shares_prefix_with(base, t.target_event_pos));
                            let ItreeConcreteEvent::ExtCall { args: ro_args, .. } =
                                &ro.events[t.target_event_pos]
                            else {
                                panic!("return-only trial must reach the pinned call");
                            };
                            assert_eq!(ro_args, base_args, "return-only keeps arg == prev_arg");
                            if return_only_seen.entry(key).or_default().insert(ro_args.clone()) {
                                return_only_new += 1;
                            }
                        }
                        (
                            ConcolicTrialPhase::PerturbOracleReturn { callee, .. },
                            ItreeConcreteEvent::ExtCall { callee: c, args, ret },
                        ) => {
                            saw_return_phase = true;
                            assert_eq!((callee, c), (base_callee, base_callee));
                            assert_eq!(args, base_args);
                            assert_ne!(ret, base_ret);
                        }
                        (phase, ev_at) => panic!("unexpected trial {phase:?} at {ev_at:?}"),
                    }
                }
                assert!(
                    saw_negation,
                    "candidate {} ({:?}) produced no argument-negating trial",
                    cand.id,
                    cand.applied_mutators
                );
                assert_eq!(return_only_new, 0);
                assert!(concolic_new > return_only_new);
                total_concolic_new += concolic_new;
                total_return_only_new += return_only_new;
                checked_outliner += usize::from(has_outliner);
                checked_injector += usize::from(has_injector);
            }
        }
        assert!(checked_outliner >= 2, "expected >= 2 CallBoundaryOutliner candidates");
        assert!(checked_injector >= 2, "expected >= 2 ExtOracleInjector candidates");
        assert!(total_concolic_new > total_return_only_new);
    }

    #[test]
    fn concolic_handles_zero_arg_calls_multi_call_pin_prefixes_and_bool_domain_saturation() {
        let chain_src = r#"
            pub fn ext_zero() -> u32 { 7 }
            pub fn ext_one(x: u32) -> u32 { (x >> 1) + 3 }
            pub fn ext_two(x: u32, y: u32) -> u32 { (x >> 2) ^ y }
            pub fn ext_three(z: u32) -> u32 { (z >> 3) + 1 }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                if magic == 0x414E_4E4C {
                    let z: u32 = ext_zero();
                    let a: u32 = ext_one(magic);
                    let b: u32 = ext_two(a, payload_len);
                    let c: u32 = ext_three(b);
                    z ^ c
                } else {
                    0
                }
            }
        "#;
        let dict = MirInputDictionary::from_rust_source(chain_src).unwrap();
        let bases = [(0x414E_4E4C, 2048)];
        let trials =
            explore_itree_concolic_trials(chain_src, "kernel_step", "s__", &bases, &dict, 16, 7);
        let ev = ItreeConcreteEvaluator::new(chain_src, "kernel_step").unwrap();
        let base = ev.run_kernel_step(0x414E_4E4C, 2048, &EnvSchedule::new(), "s__").unwrap();
        // pin 0 `ext_zero()`: 0-arg -> `negArgPinTerm` unsatisfiable;
        // pin 1 `ext_one(magic)`: `magic` is fixed by the prefix guard;
        // pin 2 `ext_two(a, payload_len)`: negatable via `payload_len` with pins 0..1 intact;
        // pin 3 `ext_three(b)`: `b` changes only if pin 2's arguments change -> locked.
        let negated: BTreeSet<&str> = trials
            .iter()
            .filter_map(|t| match &t.phase {
                ConcolicTrialPhase::NegateCallArg { callee, .. } => Some(callee.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(negated, BTreeSet::from(["ext_two"]));
        for t in &trials {
            if let ConcolicTrialPhase::NegateCallArg { pin_idx, .. } = &t.phase {
                assert_eq!(*pin_idx, 2);
                // Earlier pins `ext_zero()` and `ext_one(magic)` keep args and returns.
                assert!(t.predicted.shares_prefix_with(&base, t.target_event_pos));
                assert_eq!(&t.predicted.events[1], &ext_call("ext_zero", &[], 7));
                assert_eq!(t.magic, 0x414E_4E4C);
                assert_ne!(t.payload_len, 2048);
            }
        }
        let reasons: BTreeMap<&str, ArgPinFallbackReason> = trials
            .iter()
            .filter_map(|t| match &t.phase {
                ConcolicTrialPhase::PerturbOracleReturn { callee, reason, .. } => {
                    Some((callee.as_str(), *reason))
                }
                _ => None,
            })
            .collect();
        assert_eq!(reasons.get("ext_zero"), Some(&ArgPinFallbackReason::ZeroArgCall));
        assert_eq!(reasons.get("ext_one"), Some(&ArgPinFallbackReason::PrefixLocked));
        assert_eq!(reasons.get("ext_three"), Some(&ArgPinFallbackReason::PrefixLocked));
        let first_ret_idx = trials
            .iter()
            .position(|t| matches!(t.phase, ConcolicTrialPhase::PerturbOracleReturn { .. }))
            .unwrap();
        assert!(
            trials[first_ret_idx..]
                .iter()
                .all(|t| !matches!(t.phase, ConcolicTrialPhase::NegateCallArg { .. })),
            "return perturbation only after argument negation is exhausted"
        );
        // The 0-arg return perturbation pins nothing before it and perturbs `ext_zero`.
        let zero_ret = trials
            .iter()
            .find(|t| {
                matches!(
                    &t.phase,
                    ConcolicTrialPhase::PerturbOracleReturn { callee, .. } if callee == "ext_zero"
                )
            })
            .unwrap();
        assert_eq!(zero_ret.schedule.callee_queues.len(), 1);
        assert_ne!(zero_ret.schedule.callee_queues["s__ext_zero"][0], le32(7));

        // `bool` argument domain {false, true}: exactly one negation, then
        // `DomainExhausted` return perturbation, no duplicates, no loops.
        let flag_src = r#"
            pub fn ext_flag(f: bool) -> u32 { if f { 11 } else { 13 } }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                let f: u32 = ext_flag(payload_len > 5000);
                f ^ magic
            }
        "#;
        let flag_dict = MirInputDictionary::from_rust_source(flag_src).unwrap();
        let flag_trials = explore_itree_concolic_trials(
            flag_src,
            "kernel_step",
            "",
            &ITREE_CONCOLIC_BASE_INPUTS,
            &flag_dict,
            32,
            11,
        );
        let negations: Vec<_> = flag_trials
            .iter()
            .filter(|t| matches!(t.phase, ConcolicTrialPhase::NegateCallArg { .. }))
            .collect();
        assert_eq!(negations.len(), 1, "bool domain admits one alternative: {flag_trials:?}");
        assert_eq!(
            negations[0].phase,
            ConcolicTrialPhase::NegateCallArg {
                pin_idx: 0,
                callee: "ext_flag".to_string(),
                new_arg_tuple: vec![vec![1]],
            }
        );
        assert!(negations[0].payload_len > 5000);
        assert!(flag_trials.iter().any(|t| matches!(
            t.phase,
            ConcolicTrialPhase::PerturbOracleReturn {
                reason: ArgPinFallbackReason::DomainExhausted,
                ..
            }
        )));
        let distinct: BTreeSet<_> = flag_trials.iter().map(|t| t.predicted.clone()).collect();
        assert_eq!(distinct.len(), flag_trials.len());
        assert!(flag_trials.len() < 32, "exploration must terminate below the budget here");

        // `synthesize_itree_concolic_trials` is the deterministic tuple view.
        let tuples =
            synthesize_itree_concolic_trials(flag_src, "kernel_step", "", &flag_dict, 32, 11);
        assert_eq!(
            tuples,
            flag_trials
                .iter()
                .map(|t| (t.magic, t.payload_len, t.schedule.clone()))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn outliner_and_oracle_injector_preserve_downstream_call_negation_freedom() {
        let seed0 = crate::itree_eval::ITREE_SAFE_SEEDS[0];
        let bases = [(0x414E_4E4C, 2048)];

        // 1. Multi-callee `CallBoundaryOutliner` on Seed 0: has 3 boundary calls on
        //    `(0x414E_4E4C, 2048)`: `pin_idx = 0` (`__anneal_itree_outlined_*`),
        //    `pin_idx = 1` (`__anneal_itree_outlined_stage2_*`), and `pin_idx = 2`
        //    (`ext_oracle` inside `if magic == 0x414E_4E4C { if payload_len > 1024 }`).
        let mut multi_src = None;
        for s in 0..32u64 {
            let mut f = syn::parse_file(seed0).unwrap();
            let mut rng = DetRng::new(s);
            CallBoundaryOutliner.mutate(&mut f, &mut rng);
            let src = prettyplease::unparse(&f);
            if src.contains("__anneal_itree_outlined_stage2_") {
                multi_src = Some(src);
                break;
            }
        }
        let multi_src = multi_src.expect("multi-callee outliner source");
        let dict = MirInputDictionary::from_rust_source(&multi_src).unwrap();
        let ev = ItreeConcreteEvaluator::new(&multi_src, "kernel_step").unwrap();
        let base_run = ev
            .run_kernel_step(0x414E_4E4C, 2048, &EnvSchedule::new(), "s__")
            .unwrap();
        assert_eq!(base_run.ext_calls().len(), 3);
        let trials =
            explore_itree_concolic_trials(&multi_src, "kernel_step", "s__", &bases, &dict, 18, 42);
        let negated_pins: BTreeSet<usize> = trials
            .iter()
            .filter_map(|t| match &t.phase {
                ConcolicTrialPhase::NegateCallArg { pin_idx, .. } => Some(*pin_idx),
                _ => None,
            })
            .collect();
        assert_eq!(
            negated_pins,
            BTreeSet::from([0, 1, 2]),
            "all 3 boundary calls (stage1, stage2, ext_oracle) must be negatable under prefix pins"
        );
        for t in &trials {
            if let ConcolicTrialPhase::NegateCallArg { .. } = &t.phase {
                assert!(t.predicted.shares_prefix_with(&base_run, t.target_event_pos));
            }
        }

        // 2. `ExtOracleInjector` on Seed 0: both `pin_idx = 0` (`__anneal_ext_oracle_*`)
        //    and `pin_idx = 1` (`ext_oracle`) must be negatable under prefix pins.
        let mut f_inj = syn::parse_file(seed0).unwrap();
        let mut rng_inj = DetRng::new(7);
        ExtOracleInjector.mutate(&mut f_inj, &mut rng_inj);
        let inj_src = prettyplease::unparse(&f_inj);
        let inj_dict = MirInputDictionary::from_rust_source(&inj_src).unwrap();
        let inj_trials =
            explore_itree_concolic_trials(&inj_src, "kernel_step", "s__", &bases, &inj_dict, 12, 99);
        let inj_negated_pins: BTreeSet<usize> = inj_trials
            .iter()
            .filter_map(|t| match &t.phase {
                ConcolicTrialPhase::NegateCallArg { pin_idx, .. } => Some(*pin_idx),
                _ => None,
            })
            .collect();
        assert_eq!(
            inj_negated_pins,
            BTreeSet::from([0, 1]),
            "both injected oracle and seed ext_oracle must be negatable under prefix pins"
        );
    }

    /// Downstream of the negated call the path is unconstrained, and the coverage
    /// metric ignores call values: among prefix-preserving negations the explorer
    /// must prefer one that reaches an unseen path shape over the first (same-shape)
    /// candidate in pool order.
    #[test]
    fn concolic_arg_negation_prefers_unseen_path_shapes_for_coverage() {
        let src = r#"
            pub fn ext_a(x: u32) -> u32 { x >> 1 }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                let a: u32 = ext_a(payload_len);
                if a > 5000 { magic } else { 2 }
            }
        "#;
        let dict = MirInputDictionary::from_rust_source(src).unwrap();
        let ev = ItreeConcreteEvaluator::new(src, "kernel_step").unwrap();
        let base = ev
            .run_kernel_step(0x414E_4E4C, 2048, &EnvSchedule::new(), "")
            .unwrap();
        assert_eq!(base.events.last(), Some(&branch(0, 0)));
        // The first pool candidate (`payload_len + 1`) negates `ext_a`'s argument but
        // stays on the else-branch; the explorer keeps scanning for the then-branch.
        let first_pool = ev
            .run_kernel_step(0x414E_4E4C, 2049, &EnvSchedule::new(), "")
            .unwrap();
        assert_eq!(concolic_owned_shape(&first_pool), concolic_owned_shape(&base));
        let trials =
            explore_itree_concolic_trials(src, "kernel_step", "", &[(0x414E_4E4C, 2048)], &dict, 1, 5);
        assert_eq!(trials.len(), 1);
        let t = &trials[0];
        assert!(matches!(t.phase, ConcolicTrialPhase::NegateCallArg { .. }));
        assert!(t.predicted.shares_prefix_with(&base, t.target_event_pos));
        assert_ne!(concolic_owned_shape(&t.predicted), concolic_owned_shape(&base));
        assert_eq!(t.predicted.events.last(), Some(&branch(0, 1)));

        // When `max_trials == 2` (`arg_round_cap == 1`), a `bool` argument pin
        // whose 2-element domain `{false, true}` is exhausted by Round 1 must
        // report `ArgPinFallbackReason::DomainExhausted` (not `NegationRoundCapReached`)
        // in Phase 2.
        let bool_src = r#"
            pub fn ext_flag(f: bool) -> u32 { if f { 11 } else { 13 } }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                let f: u32 = ext_flag(payload_len > 5000);
                f ^ magic
            }
        "#;
        let bool_dict = MirInputDictionary::from_rust_source(bool_src).unwrap();
        let cap2_trials = explore_itree_concolic_trials(
            bool_src,
            "kernel_step",
            "",
            &[(0x414E_4E4C, 2048)],
            &bool_dict,
            2,
            11,
        );
        assert_eq!(cap2_trials.len(), 2);
        assert!(matches!(
            cap2_trials[1].phase,
            ConcolicTrialPhase::PerturbOracleReturn {
                reason: ArgPinFallbackReason::DomainExhausted,
                ..
            }
        ));
    }

    /// A negated argument tuple on which the callee itself unwinds is still an
    /// `argPinTerm` negation: the call happened with `arg != prev_arg` under the
    /// preserved prefix (the native recorder logs an unwinding pass-through call
    /// as `ExtCallPanic` with its `raw_args`), and its panic outcome is a new
    /// observable path that only argument steering reaches, so the explorer must
    /// accept it and prefer it over same-shape negations.
    #[test]
    fn concolic_arg_negation_accepts_callee_panics_on_negated_arguments() {
        let src = r#"
            pub fn ext_sub(x: u32) -> u32 { x - 5 }
            pub fn kernel_step(magic: u32, payload_len: u32) -> u32 {
                let r: u32 = ext_sub(payload_len);
                r ^ magic
            }
        "#;
        let dict = MirInputDictionary::from_rust_source(src).unwrap();
        let ev = ItreeConcreteEvaluator::new(src, "kernel_step").unwrap();
        let base = ev
            .run_kernel_step(0x414E_4E4C, 2048, &EnvSchedule::new(), "")
            .unwrap();
        assert!(matches!(base.outcome, ItreeConcreteOutcome::Return(_)));
        let trials =
            explore_itree_concolic_trials(src, "kernel_step", "", &[(0x414E_4E4C, 2048)], &dict, 1, 3);
        assert_eq!(trials.len(), 1);
        let t = &trials[0];
        let ConcolicTrialPhase::NegateCallArg {
            callee,
            new_arg_tuple,
            ..
        } = &t.phase
        else {
            panic!("expected an argument negation, got {:?}", t.phase);
        };
        assert_eq!(callee, "ext_sub");
        assert!(u32::from_le_bytes(new_arg_tuple[0][..4].try_into().unwrap()) < 5);
        assert_eq!(t.predicted.outcome, ItreeConcreteOutcome::Panic);
        assert_eq!(
            t.predicted.events,
            vec![ItreeConcreteEvent::ExtCallPanic {
                callee: "ext_sub".to_string(),
                args: new_arg_tuple.clone(),
            }]
        );
        assert_eq!(
            ev.run_kernel_step(t.magic, t.payload_len, &t.schedule, "")
                .unwrap(),
            t.predicted
        );

        // Reverse direction: when the BASE input itself unwinds inside the callee
        // (`payload_len = 2 < 5` -> `ExtCallPanic`), the explorer still creates a
        // pin for that boundary call, negates `x` in Phase 1 to escape the panic
        // (`Return`), and perturbs its oracle return in Phase 2 so the base input
        // returns normally without panicking.
        let panic_base = ev
            .run_kernel_step(0x414E_4E4C, 2, &EnvSchedule::new(), "")
            .unwrap();
        assert_eq!(panic_base.outcome, ItreeConcreteOutcome::Panic);
        let rev_trials =
            explore_itree_concolic_trials(src, "kernel_step", "", &[(0x414E_4E4C, 2)], &dict, 12, 3);
        assert!(rev_trials.iter().any(|t| {
            matches!(t.phase, ConcolicTrialPhase::NegateCallArg { .. })
                && matches!(t.predicted.outcome, ItreeConcreteOutcome::Return(_))
        }));
        assert!(rev_trials.iter().any(|t| {
            matches!(t.phase, ConcolicTrialPhase::PerturbOracleReturn { .. })
                && (t.magic, t.payload_len) == (0x414E_4E4C, 2)
                && matches!(t.predicted.outcome, ItreeConcreteOutcome::Return(_))
        }));
    }

    /// One [`IndirectDispatchOutliner`] candidate per template and ITree seed.
    fn indirect_dispatch_candidates() -> Vec<(&'static str, GeneratedItreeCandidate)> {
        const TEMPLATES: [(&str, &str); 4] = [
            ("dyn_dispatch", "as &dyn AnnealDynProbe"),
            ("fn_pointer", "anneal_fnptr_mix"),
            ("closures", "let mut bump"),
            ("slice_addr_eq", "lead @ .."),
        ];
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let mut out = Vec::new();
        for (seed_index, seed) in seeds.iter().enumerate() {
            for (label, marker) in TEMPLATES {
                let id = out.len();
                let cand = (0..64u64)
                    .find_map(|s| {
                        let mut file = parse_safe_itree_seed(seed)?;
                        let mut rng = DetRng::new(s);
                        IndirectDispatchOutliner.mutate(&mut file, &mut rng);
                        let source = prettyplease::unparse(&file);
                        source.contains(marker).then(|| GeneratedItreeCandidate {
                            id,
                            seed_index,
                            seed_u64: s,
                            applied_mutators: vec!["IndirectDispatchOutliner".to_string()],
                            source,
                        })
                    })
                    .unwrap_or_else(|| panic!("no `{label}` template for seed {seed_index}"));
                out.push((label, cand));
            }
        }
        out
    }

    #[test]
    fn indirect_dispatch_outliner_templates_are_safe_staged_and_match_native_rustc() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let cands = indirect_dispatch_candidates();
        assert_eq!(cands.len(), 4 * seeds.len());
        let mut combined = String::from("#![forbid(unsafe_code)]\n");
        for (i, (label, cand)) in cands.iter().enumerate() {
            assert!(
                !contains_unsafe_token(&cand.source),
                "{label}:\n{}",
                cand.source
            );
            // Exactly one top-level item is added: the helper function.
            let seed_items = syn::parse_file(seeds[cand.seed_index]).unwrap().items.len();
            let file = syn::parse_file(&cand.source).unwrap();
            assert_eq!(
                file.items.len(),
                seed_items + 1,
                "{label}:\n{}",
                cand.source
            );
            let Some(Item::Fn(helper)) = file.items.last() else {
                panic!("{label}: last item is not the helper function");
            };
            let helper_name = helper.sig.ident.to_string();
            assert!(helper_name.starts_with("__anneal_itree_indirect_"));

            let staged = stage_itree_candidate_items(&cand.source, "b0_c0__", "kernel_step")
                .unwrap_or_else(|e| panic!("{label}: staging failed: {e}"));
            assert!(
                staged
                    .ext_callee_names
                    .contains(&format!("b0_c0__{helper_name}"))
            );
            assert!(syn::parse_file(&staged.staged_source).is_ok());
            let (_, callees) = annotate_itree_external_callees(&cand.source, "kernel_step")
                .unwrap_or_else(|e| panic!("{label}: annotation failed: {e}"));
            assert!(callees.contains(&helper_name));

            // The helper is the root's first boundary call on every input: it
            // takes two `u32`s, never unwinds, and never returns `0`.
            let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step").unwrap();
            for (m, p) in ITREE_CONCOLIC_BASE_INPUTS {
                let run = ev
                    .run_kernel_step(m, p, &EnvSchedule::new(), "")
                    .unwrap_or_else(|e| panic!("{label} unsupported on ({m:#x}, {p:#x}): {e}"));
                match run.events.first() {
                    Some(ItreeConcreteEvent::ExtCall { callee, args, ret }) => {
                        assert_eq!(*callee, helper_name);
                        assert_eq!(args.len(), 2);
                        assert_ne!(*ret, le32(0), "{label} returned 0 on ({m:#x}, {p:#x})");
                    }
                    other => panic!("{label}: first event is {other:?}"),
                }
            }
            combined.push_str(&format!("pub mod c{i} {{\n{}\n}}\n", cand.source));
        }
        for opt_level in ["0", "2"] {
            assert!(
                crate::itree_eval::compile_rust_strict_opt(
                    "indirect_templates",
                    opt_level,
                    &combined
                ),
                "indirect-dispatch templates must compile warning-free under \
                 `#![forbid(unsafe_code)]` at `-C opt-level={opt_level}`:\n{combined}"
            );
        }
        let cands: Vec<GeneratedItreeCandidate> = cands.into_iter().map(|(_, c)| c).collect();
        assert_evaluator_matches_native_rustc_at_opt_levels(&cands, &["0", "2"]);

        // Scheduled batches carry the mutator and replay faithfully.
        let mut scheduled = 0usize;
        for batch_seed in [0x3333_4444u64, 0xABCD_1234, 0x1111_2222] {
            for cand in generate_itree_batch(seeds, 20, batch_seed) {
                if !cand
                    .applied_mutators
                    .iter()
                    .any(|m| m == "IndirectDispatchOutliner")
                {
                    continue;
                }
                scheduled += 1;
                assert_eq!(
                    cand.applied_mutators
                        .iter()
                        .filter(|m| *m == "IndirectDispatchOutliner")
                        .count(),
                    1,
                    "a candidate runs the indirect-dispatch pass at most once"
                );
                let (base, steps) =
                    reconstruct_itree_mutation_steps(&cand, seeds).expect("reconstruct steps");
                assert!(itree_candidate_replay_is_faithful(&cand, &base, &steps));
            }
        }
        assert!(
            scheduled >= 4,
            "expected scheduled indirect-dispatch candidates"
        );
    }

    /// `IndirectDispatchOutliner` stacked with each base mutator, in both
    /// orders, on every ITree seed: the stack stays free of `unsafe`, keeps
    /// every top-level function distinct, stages, is supported by the concrete
    /// evaluator (which sees the indirect-dispatch helper called), and runs
    /// natively as the evaluator predicts.
    #[test]
    fn indirect_dispatch_outliner_stacks_with_every_base_mutator_and_matches_native_rustc() {
        let seeds = crate::itree_eval::ITREE_SAFE_SEEDS;
        let indirect: &dyn ItreeAstMutator = &IndirectDispatchOutliner;
        let mut cands: Vec<GeneratedItreeCandidate> = Vec::new();
        for (seed_index, seed) in seeds.iter().enumerate() {
            for &other in ITREE_AST_MUTATORS.iter().take(ITREE_BASE_MUTATOR_COUNT) {
                for indirect_first in [true, false] {
                    let id = cands.len();
                    let s = 0x57AC_0000u64 + id as u64;
                    let order: [&dyn ItreeAstMutator; 2] = if indirect_first {
                        [indirect, other]
                    } else {
                        [other, indirect]
                    };
                    let mut file = parse_safe_itree_seed(seed).expect("parse ITree seed");
                    let mut rng = DetRng::new(s);
                    for mutator in order {
                        mutator.mutate(&mut file, &mut rng);
                    }
                    let source = prettyplease::unparse(&file);
                    let label = format!(
                        "`{}` then `{}` on seed {seed_index}",
                        order[0].name(),
                        order[1].name()
                    );
                    assert!(!contains_unsafe_token(&source), "{label}:\n{source}");
                    let parsed = syn::parse_file(&source).unwrap();
                    let mut fn_names = BTreeSet::new();
                    for item in &parsed.items {
                        if let Item::Fn(f) = item {
                            assert!(
                                fn_names.insert(f.sig.ident.to_string()),
                                "{label}: `{}` is defined twice:\n{source}",
                                f.sig.ident
                            );
                        }
                    }
                    assert_eq!(
                        fn_names
                            .iter()
                            .filter(|n| n.starts_with("__anneal_itree_indirect_"))
                            .count(),
                        1,
                        "{label}:\n{source}"
                    );
                    let staged = stage_itree_candidate_items(&source, "b0_c0__", "kernel_step")
                        .unwrap_or_else(|e| panic!("{label}: staging failed: {e}"));
                    assert!(syn::parse_file(&staged.staged_source).is_ok());
                    let ev = ItreeConcreteEvaluator::new(&source, "kernel_step")
                        .unwrap_or_else(|e| panic!("{label}: {e}"));
                    let mut helper_called = false;
                    for (m, p) in ITREE_CONCOLIC_BASE_INPUTS {
                        let run = ev
                            .run_kernel_step(m, p, &EnvSchedule::new(), "")
                            .unwrap_or_else(|e| {
                                panic!("{label} unsupported on ({m:#x}, {p:#x}): {e}")
                            });
                        helper_called |= run.events.iter().any(|event| {
                            matches!(
                                event,
                                ItreeConcreteEvent::ExtCall { callee, .. }
                                    if callee.starts_with("__anneal_itree_indirect_")
                            )
                        });
                    }
                    assert!(
                        helper_called,
                        "{label}: no base input calls the indirect-dispatch helper:\n{source}"
                    );
                    cands.push(GeneratedItreeCandidate {
                        id,
                        seed_index,
                        seed_u64: s,
                        applied_mutators: vec![
                            order[0].name().to_string(),
                            order[1].name().to_string(),
                        ],
                        source,
                    });
                }
            }
        }
        assert_eq!(cands.len(), seeds.len() * ITREE_BASE_MUTATOR_COUNT * 2);
        assert_evaluator_matches_native_rustc_at_opt_levels(&cands, &["0", "2"]);
    }

    /// The two PRNG draws of the base schedule also decide the indirect-dispatch
    /// redirect, so a candidate without a redirected pass draws exactly what the
    /// base schedule draws.
    #[test]
    fn indirect_dispatch_pass_is_scheduled_without_extra_draws() {
        let seed = crate::itree_eval::ITREE_SAFE_SEEDS[0];
        let (mut redirected, mut base_only) = (0usize, 0usize);
        for s in 0..2048u64 {
            let id = (s % 9) as usize;
            let mut rng = DetRng::new(s);
            let mut file = parse_safe_itree_seed(seed).unwrap();
            let steps = apply_itree_mutation_passes(&mut file, &mut rng, id);
            let names: Vec<&str> = steps.iter().map(|st| st.mutator_name.as_str()).collect();
            if names.contains(&"IndirectDispatchOutliner") {
                redirected += 1;
                continue;
            }
            base_only += 1;
            // Replay the base schedule by hand from the same PRNG seed.
            let mut base_rng = DetRng::new(s);
            let mut base_file = parse_safe_itree_seed(seed).unwrap();
            let num_passes = 1 + base_rng.gen_range(2);
            let first_idx = id % ITREE_BASE_MUTATOR_COUNT;
            let mut expected = Vec::new();
            for pass in 0..num_passes {
                let m_idx = if pass == 0 {
                    first_idx
                } else {
                    (first_idx + 1 + base_rng.gen_range(ITREE_BASE_MUTATOR_COUNT - 1))
                        % ITREE_BASE_MUTATOR_COUNT
                };
                ITREE_AST_MUTATORS[m_idx].mutate(&mut base_file, &mut base_rng);
                expected.push(ITREE_AST_MUTATORS[m_idx].name());
            }
            assert_eq!(names, expected);
            assert_eq!(
                prettyplease::unparse(&file),
                prettyplease::unparse(&base_file)
            );
            assert_eq!(rng.next_u64(), base_rng.next_u64());
        }
        // One pass in `ITREE_INDIRECT_PASS_DENOMINATOR`, over 1.5 passes per
        // candidate on average.
        let expected = 2048 * 3 / 2 / ITREE_INDIRECT_PASS_DENOMINATOR;
        assert!(
            (expected * 3 / 4..=expected * 5 / 4).contains(&redirected),
            "{redirected} of 2048 candidates redirected, expected about {expected}"
        );
        assert_eq!(redirected + base_only, 2048);
    }

    #[test]
    fn concrete_evaluator_models_indirect_constructs_like_native_rustc_and_rejects_the_rest() {
        const ROOT: &str = "pub fn kernel_step(magic: u32, payload_len: u32) -> u32 { probe(magic, payload_len) }\n";
        // 1. Constructs the evaluator models, checked against native execution.
        let modeled = [
            // A `move` closure keeps the copy it captured; a closure that
            // assigns a captured variable updates it across calls.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let mut x: u32 = a & 0xFFFFu32;
                let frozen = move |d: u32| -> u32 { (x >> 1) ^ d };
                x = x ^ 0x55u32;
                let mut total: u32 = b & 0xFFu32;
                let mut add = |d: u32| {
                    total = total ^ (d << 1);
                };
                add(3u32);
                add(x & 7u32);
                let k: u32 = frozen(total);
                ((k ^ x) >> 1) + 1u32
            }",
            // Arrays, by-value and by-reference array patterns, a bounds-check
            // panic, element addresses, and a method on a by-value receiver.
            "pub fn probe(a: u32, b: u32) -> u32 {
                struct Pair {
                    lo: u32,
                    hi: u32,
                }
                impl Pair {
                    fn mix(&self, k: u32) -> u32 {
                        (self.lo >> 1) ^ (self.hi & k)
                    }
                }
                let arr: [u32; 4] = [a, b, a ^ b, 7];
                let [first, middle @ .., last] = arr;
                let pair = Pair { lo: first ^ middle[1], hi: last };
                let idx: usize = if (b & 3u32) == 3u32 { 4 } else { 1 };
                let picked: u32 = arr[idx];
                let [head, ..] = &arr;
                let same: bool = core::ptr::addr_eq(head, &arr[0]);
                let diff: bool = core::ptr::addr_eq(head, &arr[1]);
                let r: u32 = pair.mix(picked) ^ (*head);
                if same && !diff { (r >> 1) + 1u32 } else { 0u32 }
            }",
            // Function pointers, capture-free closures (including one whose
            // body shadows an outer variable with a local `let`), and safe
            // `FnPtrToPtr` `addr_eq` checks.
            "pub fn probe(a: u32, b: u32) -> u32 {
                fn twice(f: fn(u32) -> u32, v: u32) -> u32 {
                    f(f(v))
                }
                fn halve(v: u32) -> u32 {
                    v >> 1
                }
                let x: u32 = a ^ b;
                let lifted: fn(u32) -> u32 = |v: u32| {
                    let x: u32 = v ^ 0x33u32;
                    x
                };
                let chosen: fn(u32) -> u32 = if a > b { halve } else { lifted };
                let raw: *const () = chosen as *const ();
                let same: bool = core::ptr::addr_eq(raw, chosen as *const ());
                let diff: bool = core::ptr::addr_eq(raw, &x as *const u32);
                let base: u32 = twice(chosen, x);
                if same && !diff { (base >> 1) + 1u32 } else { 0u32 }
            }",
            // Vtable-keyed `&dyn Trait` dispatch when two traits define the
            // same method name on one concrete struct, plus by-ref closure
            // capture address identity (`addr_eq(&captured, outer_ref)`).
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32; }
                trait Right { fn pick(&self) -> u32; }
                struct Both { v: u32 }
                impl Left for Both { fn pick(&self) -> u32 { self.v & 0xFFFFu32 } }
                impl Right for Both { fn pick(&self) -> u32 { 7u32 } }
                let both = Both { v: a };
                let left: &dyn Left = &both;
                let right: &dyn Right = &both;
                let same_obj: bool = core::ptr::addr_eq(left, right);
                let cap: u32 = b & 0xFFu32;
                let cap_ref: &u32 = &cap;
                let check = |x: u32| {
                    if core::ptr::addr_eq(&cap, cap_ref) { x ^ (*cap_ref) } else { 0u32 }
                };
                let res: u32 = check(left.pick() ^ right.pick());
                if same_obj { (res >> 1) + 1u32 } else { 0u32 }
            }",
            // A closure body sees enclosing local `fn`, `struct`, and `impl`
            // items (shadowing any top-level `fn` of the same name).
            "pub fn helper(v: u32) -> u32 { v ^ 999u32 }
             pub fn probe(a: u32, b: u32) -> u32 {
                 fn helper(v: u32) -> u32 { (v >> 1) ^ 0x55u32 }
                 struct Tag { k: u32 }
                 impl Tag { fn mix(&self, x: u32) -> u32 { self.k ^ x } }
                 let f = |x: u32| {
                     let t = Tag { k: b & 0xFFu32 };
                     t.mix(helper(x))
                 };
                 (f(a) >> 1) + 1u32
             }",
        ];
        let cands: Vec<GeneratedItreeCandidate> = modeled
            .iter()
            .enumerate()
            .map(|(id, probe)| GeneratedItreeCandidate {
                id,
                seed_index: 0,
                seed_u64: id as u64,
                applied_mutators: Vec::new(),
                source: format!("{probe}\n{ROOT}"),
            })
            .collect();
        let empty = EnvSchedule::new();
        // `payload_len & 3 == 3` indexes out of bounds: the boundary call unwinds.
        let ev = ItreeConcreteEvaluator::new(&cands[1].source, "kernel_step").unwrap();
        let run = ev.run_kernel_step(9, 3, &empty, "").unwrap();
        assert_eq!(run.outcome, ItreeConcreteOutcome::Panic);
        assert!(matches!(
            run.events[..],
            [ItreeConcreteEvent::ExtCallPanic { .. }]
        ));
        assert_evaluator_matches_native_rustc_at_opt_levels(&cands, &["0", "2"]);

        // 2. Constructs whose result the evaluator cannot determine are rejected.
        let rejected = [
            // A unique borrow: the evaluator's references are read-only.
            "pub fn probe(a: u32, b: u32) -> u32 { let mut x: u32 = a; let r = &mut x; b }",
            // A `let ref` binding must not be silently bound by value.
            "pub fn probe(a: u32, b: u32) -> u32 { let ref r = a; (*r) ^ b }",
            // A pointer to a boundary function bypasses its instrumentation.
            "pub fn ext(v: u32) -> u32 { v }
             pub fn probe(a: u32, b: u32) -> u32 { let f: fn(u32) -> u32 = ext; f(a ^ b) }",
            // Two distinct functions may be merged by ICF, so their address
            // inequality is not assumed.
            "pub fn probe(a: u32, b: u32) -> u32 {
                fn f1(v: u32) -> u32 { v ^ 1u32 }
                fn f2(v: u32) -> u32 { v ^ 2u32 }
                let p1: fn(u32) -> u32 = f1;
                let p2: fn(u32) -> u32 = f2;
                if core::ptr::addr_eq(p1 as *const (), p2 as *const ()) { a } else { b }
            }",
            // Dangling raw pointers: both calls of `leak` place `y` at one
            // address, so the two pointers are equal natively although they
            // name two variables.
            "pub fn probe(a: u32, b: u32) -> u32 {
                fn leak(v: u32) -> *const u32 {
                    let y: u32 = v;
                    &y as *const u32
                }
                let p: *const u32 = leak(a);
                let q: *const u32 = leak(b);
                if core::ptr::addr_eq(p, q) { a } else { b }
            }",
            // A raw pointer that left its referent's scope: the address may be
            // reused for `z`.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let p: *const u32 = {
                    let y: u32 = a;
                    &y as *const u32
                };
                let z: u32 = b;
                if core::ptr::addr_eq(p, &z as *const u32) { a } else { b }
            }",
            // A closure that borrows `cap`, called from another closure's
            // frame, still sees `cap` at its own address, which only the
            // frame that created the closure knows.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let cap: u32 = a & 0xFFu32;
                let cap_ref: &u32 = &cap;
                let inner = |x: u32| if core::ptr::addr_eq(&cap, cap_ref) { x } else { 0u32 };
                let outer = |x: u32| inner(x ^ b);
                outer(1u32)
            }",
            // A struct that the closure body moves is captured by value, so it
            // has a new address inside the closure.
            "pub fn probe(a: u32, b: u32) -> u32 {
                struct Boxed { v: u32 }
                let s = Boxed { v: a };
                let p: *const Boxed = &s as *const Boxed;
                let check = |x: u32| {
                    let same: bool = core::ptr::addr_eq(&s as *const Boxed, p);
                    let moved = s;
                    if same { moved.v ^ x } else { x }
                };
                check(b)
            }",
            // A struct field's offset depends on a layout that is not computed.
            "pub fn probe(a: u32, b: u32) -> u32 {
                struct Pair { lo: u32, hi: u32 }
                let p = Pair { lo: a, hi: b };
                if core::ptr::addr_eq(&p.lo, &p.hi) { 1 } else { 2 }
            }",
            // Two temporaries may or may not share an address.
            "pub fn probe(a: u32, b: u32) -> u32 {
                if core::ptr::addr_eq(&(a ^ 1u32), &(b ^ 1u32)) { 1 } else { 2 }
            }",
            // A zero-sized referent may share its address with anything.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let empty: [u32; 0] = [];
                let other: u32 = a;
                if core::ptr::addr_eq(&empty, &other) { 1 } else { b }
            }",
            // A `move` closure that updates its own captured copy.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let mut n: u32 = a & 0xFFu32;
                let mut bump = move || { n = n ^ 1u32; n };
                bump() ^ bump() ^ b
            }",
            // A captured name that is bound again before the call.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let x: u32 = a;
                let get = || x;
                let x: u32 = b;
                get() ^ x
            }",
            // A trait's default method has no `impl` method to run.
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Twice { fn twice(&self) -> u32 { 2 } }
                struct Unit { v: u32 }
                impl Twice for Unit {}
                let u = Unit { v: a };
                u.twice() ^ u.v ^ b
            }",
            // Ambiguous direct method call on a concrete value when two traits
            // define the same method name without an inherent `impl`.
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32; }
                trait Right { fn pick(&self) -> u32; }
                struct Both { v: u32 }
                impl Left for Both { fn pick(&self) -> u32 { self.v } }
                impl Right for Both { fn pick(&self) -> u32 { 7 } }
                let both = Both { v: a };
                both.pick() ^ b
            }",
            // Multi-bound trait object `&(dyn Left + Send)` must fail closed
            // rather than stripping `dyn` into `Ref` and dispatching to an
            // inherent `impl` of the same name.
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32; }
                struct Both { v: u32 }
                impl Both { fn pick(&self) -> u32 { 999u32 } }
                impl Left for Both { fn pick(&self) -> u32 { self.v } }
                let both = Both { v: a };
                let left: &(dyn Left + Send) = &both;
                left.pick() ^ b
            }",
            // Explicit dereference of `&dyn Left` (`(*left).pick()`) must fail
            // closed rather than dropping `dyn_trait` and dispatching to an
            // inherent `impl`.
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32; }
                struct Both { v: u32 }
                impl Both { fn pick(&self) -> u32 { 999u32 } }
                impl Left for Both { fn pick(&self) -> u32 { self.v } }
                let both = Both { v: a };
                let left: &dyn Left = &both;
                (*left).pick() ^ b
            }",
            // An `else` branch that is unsized to `&dyn Left` implicitly (to
            // the type of the `if` branch) carries no trait-object marker, so
            // `left.pick()` must fail closed rather than dispatch to the
            // inherent `impl` (native Rust calls `<Both as Left>::pick`).
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32; }
                struct Both { v: u32 }
                impl Both { fn pick(&self) -> u32 { 999u32 } }
                impl Left for Both { fn pick(&self) -> u32 { self.v } }
                let both = Both { v: a };
                let other = Both { v: b };
                let left = if a < b { &both as &dyn Left } else { &other };
                left.pick() ^ b
            }",
            // A raw pointer captured in one loop iteration dangles in the next
            // iteration, where native Rust reuses the same stack slot for `y`.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let mut p: *const u32 = &a as *const u32;
                let mut out: u32 = b;
                let mut i: u32 = 0u32;
                while i < 2u32 {
                    let y: u32 = a ^ i;
                    if i == 0u32 {
                        p = &y as *const u32;
                    } else if core::ptr::addr_eq(p, &y as *const u32) {
                        out = a ^ 1u32;
                    }
                    i = i + 1u32;
                }
                out
            }",
            // A macro inside a closure body (even on an untaken branch) may
            // capture outer locals that `syn::Visit` cannot inspect.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let cap: u32 = a;
                let f = |x: u32| {
                    if x == 0u32 {
                        let _ = matches!(cap, 1u32);
                    }
                    x ^ b
                };
                f(1u32)
            }",
            // A closure moving a zero-sized value is itself zero-sized, so `&f`
            // may share an address with another local.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let empty: [u32; 0] = [];
                let f = move || empty;
                let y: u32 = a;
                if core::ptr::addr_eq(&f, &y) { 1u32 } else { b }
            }",
            // Under Rust 2021+ disjoint captures, `let _ = x;` does not capture
            // `x`, so `f` is zero-sized even though `ClosureFreeIdents` sees `x`.
            "pub fn probe(a: u32, b: u32) -> u32 {
                let x: u32 = a;
                let f = || {
                    let _ = x;
                    1u32
                };
                let y: u32 = b;
                if core::ptr::addr_eq(&f, &y) { 1u32 } else { b }
            }",
            // A trait with a default method and an empty `impl Left for Both {}`
            // must fail closed rather than letting an implicitly unsized `else`
            // branch dispatch to an inherent `impl` of the same method name.
            "pub fn probe(a: u32, b: u32) -> u32 {
                trait Left { fn pick(&self) -> u32 { 1u32 } }
                struct Both { v: u32 }
                impl Both { fn pick(&self) -> u32 { 999u32 } }
                impl Left for Both {}
                let both = Both { v: a };
                let other = Both { v: b };
                let left = if a < b { &both as &dyn Left } else { &other };
                left.pick() ^ b
            }",
        ];
        for probe in rejected {
            let source = format!("{probe}\n{ROOT}");
            let ev = ItreeConcreteEvaluator::new(&source, "kernel_step").unwrap();
            assert!(
                ev.run_kernel_step(0x414E_4E4C, 2048, &empty, "").is_err(),
                "evaluator must reject:\n{source}"
            );
        }
    }

    #[test]
    fn closure_free_idents_respects_loop_and_let_chain_binders() {
        let free_of = |expr_src: &str| -> BTreeSet<String> {
            let clos: syn::ExprClosure = syn::parse_str(expr_src).expect("parse closure");
            let mut free = ClosureFreeIdents::default();
            free.visit_expr_closure(&clos);
            free.names
        };
        // `for` binder shadows `i` inside the loop body, while `iter_src` is free.
        assert_eq!(
            free_of("|n: u32| { let mut s = n; for i in iter_src { s = s ^ i; } s }"),
            BTreeSet::from(["iter_src".to_string()])
        );
        // `for i in i { ... }`: RHS `i` is evaluated before the loop binder!
        assert_eq!(
            free_of("|n: u32| { let mut s = n; for i in i { s = s ^ i; } s }"),
            BTreeSet::from(["i".to_string()])
        );
        // `if let` chain: `x` bound in first `let` is in scope in second `let`
        // and `then` branch, but NOT in `else` branch.
        assert_eq!(
            free_of("|a: u32| if let Some(x) = opt && let Some(y) = x { y ^ a } else { x }"),
            BTreeSet::from(["opt".to_string(), "x".to_string()])
        );
        assert_eq!(
            free_of("|a: u32| if let Some(x) = opt && let Some(y) = x { y ^ a } else { a }"),
            BTreeSet::from(["opt".to_string()])
        );
        // `while let` binds `x` inside the loop body; RHS `src` is free.
        assert_eq!(
            free_of("|a: u32| { let mut acc = a; while let Some(x) = src { acc = acc ^ x; } acc }"),
            BTreeSet::from(["src".to_string()])
        );
        // `let ... else`: `x` is NOT bound in `else { ... }`, only after `let`.
        assert_eq!(
            free_of("|a: u32| { let Some(x) = opt else { return x; }; x ^ a }"),
            BTreeSet::from(["opt".to_string(), "x".to_string()])
        );
        assert_eq!(
            free_of("|a: u32| { let Some(x) = opt else { return a; }; x ^ a }"),
            BTreeSet::from(["opt".to_string()])
        );
        // Macros inside closure bodies flag `has_macro` so `make_closure` fails closed.
        let has_macro_of = |expr_src: &str| -> bool {
            let clos: syn::ExprClosure = syn::parse_str(expr_src).expect("parse closure");
            let mut free = ClosureFreeIdents::default();
            free.visit_expr_closure(&clos);
            free.has_macro
        };
        assert!(!has_macro_of("|a: u32| a ^ b"));
        assert!(has_macro_of(
            "|a: u32| { if a == 0u32 { let _ = matches!(cap, 1u32); } a }"
        ));
        assert!(has_macro_of("|a: u32| { assert_eq!(cap, a); a }"));
    }
}
