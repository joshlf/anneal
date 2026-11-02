//! Milestone 5: ITree-strength strictly safe-Rust `syn` AST mutators
//! (`CallBoundaryOutliner`, `LayoutPaddingPerturber`, `BranchLoopWeaver`,
//! `ExtOracleInjector`) plus [`generate_itree_batch`].
//!
//! Enforces a hard zero-`unsafe` invariant: [`contains_unsafe_token`] verifies that
//! **zero** `unsafe` tokens appear anywhere in any emitted candidate program.

use proc_macro2::{TokenStream, TokenTree};
use quote::{format_ident, quote};
use syn::{Block, File, Item, Stmt};

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

/// Trait implemented by all strictly safe ITree AST mutators.
pub trait ItreeAstMutator {
    /// Canonical human-readable name of this mutator pass.
    fn name(&self) -> &'static str;

    /// Mutates `file` in place using strictly safe Rust constructs (`0` `unsafe` tokens).
    fn mutate(&self, file: &mut File, rng: &mut DetRng);
}

/// 1. Outlines computation across a real function call boundary by synthesizing a pure
/// top-level safe helper function and invoking it from each target function body.
#[derive(Debug, Default, Clone, Copy)]
pub struct CallBoundaryOutliner;

impl ItreeAstMutator for CallBoundaryOutliner {
    fn name(&self) -> &'static str {
        "CallBoundaryOutliner"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let tag = rng.next_u64() & 0xFFFF;
        let helper_ident = format_ident!("__anneal_itree_outlined_{}", tag);
        let k_const = ((rng.next_u64() % 251) as u32).wrapping_add(1);

        let helper_item: Item = syn::parse_quote! {
            #[inline(never)]
            pub fn #helper_ident(seed: u32, delta: u32) -> u32 {
                let mixed = seed.wrapping_add(delta).rotate_left(3);
                mixed ^ #k_const
            }
        };

        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let local_ident = format_ident!("__itree_call_res_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #local_ident: u32 = #helper_ident(#k_const, 7u32);
                    let _ = core::hint::black_box(#local_ident);
                };
                prepend_safe_stmts(&mut func.block, injected);
            }
        }

        file.items.push(helper_item);
    }
}

/// 2. Introduces safe `#[repr(C)]` multi-field wrapper structs with natural inter-field
/// alignment padding (`u8`, 3 bytes padding, `u32`, `u8`, 3 bytes padding) and moves values
/// through field construction and pattern matching without a single `unsafe` token.
#[derive(Debug, Default, Clone, Copy)]
pub struct LayoutPaddingPerturber;

impl ItreeAstMutator for LayoutPaddingPerturber {
    fn name(&self) -> &'static str {
        "LayoutPaddingPerturber"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let tag = rng.next_u64() & 0xFFFF;
        let struct_ident = format_ident!("__AnnealSafePadded_{}", tag);
        let init_word = (rng.next_u64() & 0xFFFF_FFFF) as u32;

        let struct_item: Item = syn::parse_quote! {
            #[repr(C)]
            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct #struct_ident {
                pub lead_byte: u8,
                pub aligned_word: u32,
                pub trail_byte: u8,
            }
        };

        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let var_ident = format_ident!("__itree_padded_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #var_ident = #struct_ident {
                        lead_byte: 0x5Au8,
                        aligned_word: #init_word,
                        trail_byte: 0xA5u8,
                    };
                    let #struct_ident {
                        lead_byte: __lb,
                        aligned_word: __aw,
                        trail_byte: __tb,
                    } = #var_ident;
                    let _ = core::hint::black_box((__lb, __aw, __tb));
                };
                prepend_safe_stmts(&mut func.block, injected);
            }
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
        let tag = rng.next_u64() & 0xFFFF;
        let bound: u32 = ((rng.next_u64() % 5) as u32) + 2;

        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let step_ident = format_ident!("__itree_step_{}", tag);
                let acc_ident = format_ident!("__itree_acc_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let mut #step_ident: u32 = 0;
                    let mut #acc_ident: u32 = 1;
                    while #step_ident < #bound {
                        #acc_ident = match #step_ident & 3 {
                            0 => #acc_ident.wrapping_add(3),
                            1 => #acc_ident.wrapping_mul(5),
                            2 => #acc_ident ^ 0x0F0F_0F0Fu32,
                            _ => #acc_ident.rotate_right(1),
                        };
                        #step_ident += 1;
                    }
                    let _ = core::hint::black_box(#acc_ident);
                };
                prepend_safe_stmts(&mut func.block, injected);
            }
        }
    }
}

/// 4. Injects a deterministic safe external oracle function `__anneal_ext_oracle_<tag>` and
/// threads its observable call/return interaction through target functions.
#[derive(Debug, Default, Clone, Copy)]
pub struct ExtOracleInjector;

impl ItreeAstMutator for ExtOracleInjector {
    fn name(&self) -> &'static str {
        "ExtOracleInjector"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng) {
        let tag = rng.next_u64() & 0xFFFF;
        let oracle_ident = format_ident!("__anneal_ext_oracle_{}", tag);
        let mask = ((rng.next_u64() & 0xFF) as u32).wrapping_add(0x100);

        let oracle_item: Item = syn::parse_quote! {
            #[inline(never)]
            pub fn #oracle_ident(query: u32) -> Result<u32, u32> {
                if query & 1 == 0 {
                    Ok(query.wrapping_add(#mask))
                } else {
                    Err(query ^ #mask)
                }
            }
        };

        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let ans_ident = format_ident!("__itree_oracle_ans_{}", tag);
                let injected: Vec<Stmt> = syn::parse_quote! {
                    let #ans_ident: u32 = match #oracle_ident(#mask) {
                        Ok(v) => v,
                        Err(e) => e,
                    };
                    let _ = core::hint::black_box(#ans_ident);
                };
                prepend_safe_stmts(&mut func.block, injected);
            }
        }

        file.items.push(oracle_item);
    }
}

fn prepend_safe_stmts(block: &mut Block, mut new_stmts: Vec<Stmt>) {
    new_stmts.append(&mut block.stmts);
    block.stmts = new_stmts;
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

    let all_mutators: [&dyn ItreeAstMutator; 4] = [
        &CallBoundaryOutliner,
        &LayoutPaddingPerturber,
        &BranchLoopWeaver,
        &ExtOracleInjector,
    ];

    let mut master_rng = DetRng::new(seed_u64);
    let mut out = Vec::with_capacity(count);

    for id in 0..count {
        let seed_index = id % seeds.len();
        let cand_seed = master_rng.next_u64() ^ ((id as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut cand_rng = DetRng::new(cand_seed);

        let Ok(mut parsed) = syn::parse_str::<File>(seeds[seed_index]) else {
            continue;
        };
        sanitize_seed_to_safe_rust(&mut parsed);

        let num_passes = 1 + cand_rng.gen_range(3);
        let mut applied_mutators = Vec::with_capacity(num_passes);

        for pass in 0..num_passes {
            let m_idx = if pass == 0 {
                id % all_mutators.len()
            } else {
                cand_rng.gen_range(all_mutators.len())
            };
            let mutator = all_mutators[m_idx];
            mutator.mutate(&mut parsed, &mut cand_rng);
            applied_mutators.push(mutator.name().to_string());
        }

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
                a.wrapping_sub(b)
            } else {
                b.wrapping_add(a)
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
}
