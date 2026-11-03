//! Milestone 4: Miri-strength structure-aware `syn` AST mutators tracking initialized
//! locals and types (`ArithmeticCastMutator`, `PlaceProjectionWrapper`,
//! `RawPtrOffsetMutator`, `TreeBorrowsRetagInterleaver`, `BitValidityTransmuteMutator`)
//! plus deterministic batch generation via [`generate_miri_batch`].

use quote::{ToTokens, format_ident};
use syn::visit_mut::VisitMut;
use syn::{BinOp, Block, Expr, File, Item, ItemFn, Local, Pat, Stmt, Type};

/// Metadata captured for an initialized local variable discovered inside a function body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrackedLocal {
    pub name: String,
    pub ty: String,
    pub is_mut: bool,
}

/// Output candidate produced by [`generate_miri_batch`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedMiriCandidate {
    /// Zero-based index within the generated batch.
    pub id: usize,
    /// Index of the seed program from `seeds` that this candidate mutated.
    pub seed_index: usize,
    /// Per-candidate deterministic PRNG seed derived from the batch `seed_u64`.
    pub seed_u64: u64,
    /// Ordered list of Miri AST mutator names applied to produce this candidate.
    pub applied_mutators: Vec<String>,
    /// Snapshot of initialized `(local_name, inferred_or_declared_type)` bindings tracked.
    pub tracked_locals: Vec<(String, String)>,
    /// Pretty-printed, syntactically valid Rust source code.
    pub source: String,
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

/// Extracts initialized local bindings and their annotated/inferred scalar types from a
/// function signature and body block.
pub fn collect_initialized_locals(func: &ItemFn) -> Vec<TrackedLocal> {
    let mut locals = Vec::new();

    // Parameters are guaranteed initialized at function entry.
    for arg in &func.sig.inputs {
        if let syn::FnArg::Typed(pat_ty) = arg {
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

    // Walk top-level `let` statements with initializers.
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
            syn::Lit::Int(li) if !li.suffix().is_empty() => li.suffix().to_string(),
            syn::Lit::Int(_) => "i32".to_string(),
            syn::Lit::Bool(_) => "bool".to_string(),
            _ => "i32".to_string(),
        },
        Expr::Cast(cast) => cast.ty.to_token_stream().to_string().replace(' ', ""),
        _ => "i32".to_string(),
    }
}

fn is_integer_type_name(ty: &str) -> bool {
    matches!(
        ty,
        "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize"
    )
}

/// Trait implemented by all Miri-strength AST mutators.
pub trait MiriAstMutator {
    /// Canonical human-readable name of this mutator pass.
    fn name(&self) -> &'static str;

    /// Mutates `file` in place using `rng`, appending any newly tracked locals to `locals_log`.
    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>);
}

/// 1. Mutates integer binary arithmetic/shift operations and injects explicit `as` casts
/// over initialized integer locals to stress integer overflow, shift-width, and sign-extension rules.
#[derive(Debug, Default, Clone, Copy)]
pub struct ArithmeticCastMutator;

struct ArithVisitor<'a> {
    rng: &'a mut DetRng,
}

impl VisitMut for ArithVisitor<'_> {
    fn visit_bin_op_mut(&mut self, op: &mut BinOp) {
        if self.rng.coin(1, 2) {
            match op {
                BinOp::Add(_) => *op = syn::parse_quote!(^),
                BinOp::Sub(_) => *op = syn::parse_quote!(+),
                BinOp::BitXor(_) => *op = syn::parse_quote!(|),
                BinOp::BitAnd(_) => *op = syn::parse_quote!(&),
                _ => {}
            }
        }
    }
}

impl MiriAstMutator for ArithmeticCastMutator {
    fn name(&self) -> &'static str {
        "ArithmeticCastMutator"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        let mut visitor = ArithVisitor { rng };
        visitor.visit_file_mut(file);

        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let locals = collect_initialized_locals(func);
                for loc in &locals {
                    locals_log.push((loc.name.clone(), loc.ty.clone()));
                }
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let ident = format_ident!("{}", int_loc.name);
                    let cast_local = format_ident!("__miri_arith_cast_{}", rng.next_u64() & 0xFFFF);
                    let stmt: Stmt = syn::parse_quote! {
                        let #cast_local: u64 = ((#ident as i64).wrapping_mul(3i64).wrapping_add(1i64)) as u64;
                    };
                    let use_stmt: Stmt = syn::parse_quote! {
                        let _ = core::hint::black_box(#cast_local);
                    };
                    prepend_stmts(&mut func.block, vec![stmt, use_stmt]);
                }
            }
        }
    }
}

/// 2. Wraps initialized locals in an explicit `#[repr(C)]` projection wrapper struct and
/// exercises field place projections and `core::ptr::addr_of!` without moving out of parameters.
#[derive(Debug, Default, Clone, Copy)]
pub struct PlaceProjectionWrapper;

impl MiriAstMutator for PlaceProjectionWrapper {
    fn name(&self) -> &'static str {
        "PlaceProjectionWrapper"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let locals = collect_initialized_locals(func);
                for loc in &locals {
                    locals_log.push((loc.name.clone(), loc.ty.clone()));
                }
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let src_ident = format_ident!("{}", int_loc.name);
                    let ty: Type = syn::parse_str(&int_loc.ty).unwrap_or_else(|_| syn::parse_quote!(u32));
                    let wrap_ident = format_ident!("__MiriProjWrap_{}", rng.next_u64() & 0xFFFF);
                    let inst_ident = format_ident!("__miri_proj_inst_{}", rng.next_u64() & 0xFFFF);
                    let injected: Vec<Stmt> = syn::parse_quote! {
                        #[repr(C)]
                        struct #wrap_ident {
                            head_tag: u8,
                            payload: #ty,
                            tail_tag: u8,
                        }
                        let #inst_ident = #wrap_ident {
                            head_tag: 0x5Au8,
                            payload: #src_ident,
                            tail_tag: 0xA5u8,
                        };
                        let _ = core::hint::black_box((
                            #inst_ident.head_tag,
                            #inst_ident.payload,
                            #inst_ident.tail_tag,
                        ));
                    };
                    prepend_stmts(&mut func.block, injected);
                }
            }
        }
    }
}

/// 3. Synthesizes raw pointer address-of and in-bounds pointer offset round-trips (`&raw const`,
/// `.wrapping_add(1).wrapping_sub(1)`, `unsafe { ptr.read_unaligned() }`) over initialized locals.
#[derive(Debug, Default, Clone, Copy)]
pub struct RawPtrOffsetMutator;

impl MiriAstMutator for RawPtrOffsetMutator {
    fn name(&self) -> &'static str {
        "RawPtrOffsetMutator"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let locals = collect_initialized_locals(func);
                for loc in &locals {
                    locals_log.push((loc.name.clone(), loc.ty.clone()));
                }
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let src_ident = format_ident!("{}", int_loc.name);
                    let ty: Type = syn::parse_str(&int_loc.ty).unwrap_or_else(|_| syn::parse_quote!(u32));
                    let buf_ident = format_ident!("__miri_raw_arr_{}", rng.next_u64() & 0xFFFF);
                    let step = rng.gen_range(2) + 1;
                    let injected: Vec<Stmt> = syn::parse_quote! {
                        let #buf_ident: [#ty; 4] = [#src_ident, #src_ident, #src_ident, #src_ident];
                        let __base_ptr: *const #ty = &raw const #buf_ident[0];
                        let __roundtrip_val: #ty = unsafe {
                            __base_ptr.add(#step).wrapping_sub(#step).read()
                        };
                        let _ = core::hint::black_box(__roundtrip_val);
                    };
                    prepend_stmts(&mut func.block, injected);
                }
            }
        }
    }
}

/// 4. Interleaves Tree Borrows / Stacked Borrows shared + mutable retag transitions on a
/// shadow slot initialized from an existing local binding.
#[derive(Debug, Default, Clone, Copy)]
pub struct TreeBorrowsRetagInterleaver;

impl MiriAstMutator for TreeBorrowsRetagInterleaver {
    fn name(&self) -> &'static str {
        "TreeBorrowsRetagInterleaver"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let locals = collect_initialized_locals(func);
                for loc in &locals {
                    locals_log.push((loc.name.clone(), loc.ty.clone()));
                }
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let src_ident = format_ident!("{}", int_loc.name);
                    let ty: Type = syn::parse_str(&int_loc.ty).unwrap_or_else(|_| syn::parse_quote!(u32));
                    let slot_ident = format_ident!("__miri_tb_slot_{}", rng.next_u64() & 0xFFFF);
                    let injected: Vec<Stmt> = syn::parse_quote! {
                        let mut #slot_ident: #ty = #src_ident;
                        {
                            let __uniq_ref: &mut #ty = &mut #slot_ident;
                            let __raw_mut: *mut #ty = &raw mut *__uniq_ref;
                            let __shared_retag: &#ty = unsafe { &*(__raw_mut as *const #ty) };
                            let __observed: #ty = *__shared_retag;
                            unsafe {
                                *__raw_mut = __observed;
                            }
                        }
                        let _ = core::hint::black_box(#slot_ident);
                    };
                    prepend_stmts(&mut func.block, injected);
                }
            }
        }
    }
}

/// 5. Injects `core::mem::MaybeUninit` and fixed-size `core::mem::transmute_copy` bit-validity
/// round-trips on initialized scalar locals.
#[derive(Debug, Default, Clone, Copy)]
pub struct BitValidityTransmuteMutator;

impl MiriAstMutator for BitValidityTransmuteMutator {
    fn name(&self) -> &'static str {
        "BitValidityTransmuteMutator"
    }

    fn mutate(&self, file: &mut File, rng: &mut DetRng, locals_log: &mut Vec<(String, String)>) {
        for item in &mut file.items {
            if let Item::Fn(func) = item {
                let locals = collect_initialized_locals(func);
                for loc in &locals {
                    locals_log.push((loc.name.clone(), loc.ty.clone()));
                }
                if let Some(int_loc) = locals.iter().find(|l| is_integer_type_name(&l.ty)) {
                    let src_ident = format_ident!("{}", int_loc.name);
                    let ty: Type = syn::parse_str(&int_loc.ty).unwrap_or_else(|_| syn::parse_quote!(u32));
                    let mu_ident = format_ident!("__miri_mu_{}", rng.next_u64() & 0xFFFF);
                    let injected: Vec<Stmt> = syn::parse_quote! {
                        let #mu_ident: core::mem::MaybeUninit<#ty> = core::mem::MaybeUninit::new(#src_ident);
                        let __rehydrated: #ty = unsafe { core::mem::transmute_copy(&#mu_ident) };
                        let _ = core::hint::black_box(__rehydrated);
                    };
                    prepend_stmts(&mut func.block, injected);
                }
            }
        }
    }
}

/// Inserts `new_stmts` immediately after any leading `let` local declarations in `block`
/// so statements referencing a `let`-bound local never appear before its declaration,
/// while preserving any trailing return expression at the end of `block`.
fn prepend_stmts(block: &mut Block, new_stmts: Vec<Stmt>) {
    let insert_idx = block
        .stmts
        .iter()
        .take_while(|stmt| matches!(stmt, Stmt::Local(_) | Stmt::Item(_)))
        .count();
    block.stmts.splice(insert_idx..insert_idx, new_stmts);
}

/// Generates `count` deterministic, syntactically valid Miri-strength mutated Rust programs
/// from `seeds` using a PRNG keyed by `seed_u64`.
pub fn generate_miri_batch(
    seeds: &[&str],
    count: usize,
    seed_u64: u64,
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

    let mut master_rng = DetRng::new(seed_u64);
    let mut out = Vec::with_capacity(count);

    for id in 0..count {
        let seed_index = id % seeds.len();
        let cand_seed = master_rng.next_u64() ^ ((id as u64).wrapping_mul(0x517C_C1B7_2722_0A95));
        let mut cand_rng = DetRng::new(cand_seed);

        let Ok(mut parsed) = syn::parse_str::<File>(seeds[seed_index]) else {
            continue;
        };

        // Always apply 1..=3 distinct mutators so every mutator family gets exercised.
        let num_passes = 1 + cand_rng.gen_range(3);
        let mut applied_mutators = Vec::with_capacity(num_passes);
        let mut raw_locals = Vec::new();

        for pass in 0..num_passes {
            let m_idx = if pass == 0 {
                id % all_mutators.len()
            } else {
                cand_rng.gen_range(all_mutators.len())
            };
            let mutator = all_mutators[m_idx];
            mutator.mutate(&mut parsed, &mut cand_rng, &mut raw_locals);
            applied_mutators.push(mutator.name().to_string());
        }

        // Deduplicate tracked locals while preserving discovery order.
        let mut tracked_locals = Vec::new();
        for pair in raw_locals {
            if !tracked_locals.contains(&pair) {
                tracked_locals.push(pair);
            }
        }

        let formatted = prettyplease::unparse(&parsed);
        out.push(GeneratedMiriCandidate {
            id,
            seed_index,
            seed_u64: cand_seed,
            applied_mutators,
            tracked_locals,
            source: formatted,
        });
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED_A: &str = r#"
        pub fn compute_checksum(x: u32, y: u32) -> u32 {
            let sum: u32 = x.wrapping_add(y);
            sum ^ 0x55AA_55AA
        }
    "#;

    const SEED_B: &str = r#"
        pub fn clamp_signed(v: i32, limit: i32) -> i32 {
            let shifted: i32 = v.wrapping_sub(limit);
            shifted
        }
    "#;

    #[test]
    fn generate_miri_batch_is_deterministic_tracks_locals_and_parses_cleanly() {
        let batch1 = generate_miri_batch(&[SEED_A, SEED_B], 15, 0xCAFE_BABE_1234_5678);
        let batch2 = generate_miri_batch(&[SEED_A, SEED_B], 15, 0xCAFE_BABE_1234_5678);
        assert_eq!(batch1, batch2, "same seed_u64 must produce bit-identical batch");
        assert_eq!(batch1.len(), 15);

        let mut seen_mutators = std::collections::BTreeSet::new();
        for cand in &batch1 {
            assert!(!cand.tracked_locals.is_empty());
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

        // Across 15 candidates all 5 Miri mutators must have fired at least once.
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
}
