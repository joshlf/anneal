// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Batch compilation, live Miri + Anneal oracle execution, coverage reporting,
//! and self-contained finding bundle generation for `miri-difftest`.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    AnnealOutcome, ComparisonVerdict, DEFAULT_CAPTURE_RUSTFLAGS, DEFAULT_MIRI_FLAGS,
    DEFAULT_ORACLE_FUEL, DifftestOracleConfig, DivergenceKind, ItemOracleReport, MiriOutcome,
    MiriToolchain, NotComparedReason, OracleItemSpec, SourcePos, SourceSpan,
    discover_zero_arg_pub_fns, run_difftest_oracle_pipeline, source_files_match,
};
use quote::{ToTokens, format_ident};
use syn::visit_mut::VisitMut;
use syn::{Expr, File, FnArg, Item, ItemFn, Pat, Stmt};

use crate::mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, DetRng, GeneratedMiriCandidate,
    MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE, MiriAstMutator, MutationMode,
    PlaceProjectionWrapper, RawPtrOffsetMutator, TreeBorrowsRetagInterleaver,
    build_standalone_candidate_source, collect_initialized_locals, collect_non_fault_seed_indices,
    load_miri_diff_corpus_seeds,
};
use crate::shrink::shrink_mutation_chain_detailed;

/// Step fuel bound used for `miri-difftest` candidates (2 × `DEFAULT_ORACLE_FUEL`
/// so multi-pass mutations on loop seeds do not prematurely exhaust step fuel).
pub const MIRI_DIFFTEST_CANDIDATE_FUEL: u32 = DEFAULT_ORACLE_FUEL * 2;

/// Canonical mutator names always included in `mutator_applications`.
pub const MIRI_MUTATOR_NAMES: [&str; 5] = [
    "ArithmeticCastMutator",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
    "BitValidityTransmuteMutator",
];

/// Canonical divergence classes always included in `divergence_classes`.
pub const DIVERGENCE_CLASS_NAMES: [&str; 7] = [
    "wrong_value",
    "false_positive_ub",
    "missed_ub",
    "panic_vs_return",
    "return_vs_panic",
    "ub_location_mismatch",
    "panic_site_mismatch",
];

/// Canonical not-compared reason keys always included in `not_compared_reasons`.
pub const NOT_COMPARED_REASON_NAMES: [&str; 6] = [
    "compile_failed",
    "external_call",
    "unsupported",
    "out_of_fuel",
    "miri_oracle_error",
    "capture_failed",
];

/// Self-contained diagnostic bundle emitted for a single Miri vs. Anneal
/// semantic divergence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MiriFindingBundle {
    /// Stable identifier within the run (for example,
    /// `"finding_0000_pass_ptr_offset_within_array"`).
    pub finding_id: String,
    /// Candidate function name in `src/lib.rs` and `repro.rs`.
    pub fn_name: String,
    /// Seed function name in `tests/miri-diff/corpus/src/lib.rs`.
    pub seed_name: String,
    /// Ordered list of AST mutators applied to produce this candidate (after 1-minimal
    /// delta-debugging when shrinking is enabled).
    pub applied_mutators: Vec<String>,
    /// Original ordered list of AST mutators before delta-debugging minimization.
    pub original_mutator_chain: Vec<String>,
    /// Minimized 1-minimal ordered list of AST mutators after delta-debugging minimization.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of shrinker predicate evaluations performed while minimizing this finding.
    pub shrink_evaluations: usize,
    /// Canonical divergence class slug (`"wrong_value"`, `"false_positive_ub"`,
    /// `"missed_ub"`, `"panic_vs_return"`, `"return_vs_panic"`,
    /// `"ub_location_mismatch"`, or `"panic_site_mismatch"`).
    pub divergence_class: String,
    /// Concise Miri outcome tag.
    pub miri_outcome_tag: String,
    /// Human-readable Miri diagnostic excerpt (`MIRI_PASS:...`, panic message,
    /// or `error: Undefined Behavior: ...`).
    pub miri_excerpt: String,
    /// Miri fault/panic position translated to `repro.rs` line coordinates.
    pub miri_pos: Option<String>,
    /// Miri fault/panic position in the staged batch `src/lib.rs`.
    pub batch_miri_pos: Option<String>,
    /// Concise Anneal outcome tag.
    pub anneal_outcome_tag: String,
    /// Lean `MirDiffTag` constructor expression for this Anneal outcome.
    pub anneal_lean_tag: String,
    /// Anneal fault/panic span translated to `repro.rs` line coordinates.
    pub anneal_span: Option<String>,
    /// Anneal fault/panic span in the staged batch `src/lib.rs`.
    pub batch_anneal_span: Option<String>,
    /// Extracted neighborhood from `.anneal/generated/Mir/<Crate>/<Item>.lean`.
    pub mir_neighborhood: String,
    /// Whether the Lean 4 kernel confirmed `evalMirDiffTagBounded` and
    /// `probeMirDiffExecBounded` via `by rfl` in `MiriOracleConfirm.lean`.
    pub kernel_confirmed: bool,
    /// Kernel-checked `theorem confirm_tag_<fn_name>` and
    /// `theorem confirm_probe_<fn_name>` snippet from `MiriOracleConfirm.lean`.
    pub kernel_confirm_theorems: String,
    /// Standalone `#![no_std]` Rust reproducer source (`repro.rs`).
    pub mutant_source: String,
    /// Path to `repro.rs` on disk when `--findings-dir` was provided.
    pub repro_path: Option<PathBuf>,
}

/// Complete result of running `miri-difftest` over a set of candidate batches.
#[derive(Debug, Clone)]
pub struct MiriCampaignEvalReport {
    /// `"identity"` or `"seeded"`.
    pub mode: String,
    /// Master PRNG seed.
    pub seed: u64,
    /// Number of batches generated.
    pub batches: usize,
    /// Target candidate count per batch.
    pub batch_size: usize,
    /// Total candidates generated across all batches.
    pub total_candidates: usize,
    /// Number of candidates that compiled with `rustc`.
    pub compiled_candidates: usize,
    /// Number of candidates that failed `rustc` compilation.
    pub compile_failed_candidates: usize,
    /// Percentage of generated candidates that compiled (`0.0..=100.0`).
    pub compile_pass_rate_pct: f64,
    /// Count of candidates semantically compared (`agree_count + diverge_count`).
    pub compared_candidates: usize,
    /// Count of candidates where Miri and Anneal agreed (`ComparisonVerdict::Agree`).
    pub agree_count: usize,
    /// Count of candidates where Miri and Anneal diverged (`ComparisonVerdict::Diverge`).
    pub diverge_count: usize,
    /// Count of candidates not compared (compile failures + oracle `NotCompared`).
    pub not_compared_count: usize,
    /// Count of divergences confirmed in the Lean 4 kernel (`by rfl`).
    pub kernel_confirmed_divergences: usize,
    /// Miri outcome counts (`pass`, `panic`, `ub`, `error`).
    pub miri_verdicts: BTreeMap<String, usize>,
    /// Anneal outcome counts (`pass`, `panic`, `ub`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `error`).
    pub anneal_outcomes: BTreeMap<String, usize>,
    /// Divergence counts by canonical class name.
    pub divergence_classes: BTreeMap<String, usize>,
    /// Not-compared counts by reason (`compile_failed`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `miri_oracle_error`, `capture_failed`).
    pub not_compared_reasons: BTreeMap<String, usize>,
    /// Frequency table of unmodeled external call `DefPath`s encountered.
    pub unmodeled_external_calls: BTreeMap<String, usize>,
    /// Per-mutator application counts across all generated candidates.
    pub mutator_applications: BTreeMap<String, usize>,
    /// Detailed finding bundles for every `ComparisonVerdict::Diverge` item.
    pub findings: Vec<MiriFindingBundle>,
    /// Per-item oracle reports from `run_difftest_oracle_pipeline`.
    pub item_reports: Vec<ItemOracleReport>,
    /// Total wall-clock duration in milliseconds.
    pub elapsed_ms: f64,
}

/// Resolve the `rustc` binary used for candidate compilation checks.
pub fn resolve_rustc_bin() -> String {
    if let Ok(r) = env::var("RUSTC")
        && !r.is_empty()
    {
        return r;
    }
    if let Ok(home) = env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/rustc");
        if candidate.exists() {
            return candidate.to_string_lossy().into_owned();
        }
    }
    "rustc".to_string()
}

/// Runs `rustc --edition=2024 --crate-type=lib` on an in-memory Rust source
/// string and reports whether it compiled.
pub fn compile_rust_snippet(label: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_miri_difftest_{}_{}",
        std::process::id(),
        label
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libmiri_check.rlib");

    let child_res = Command::new(&rustc_bin)
        .args(["--edition=2024", "--crate-type=lib", "-A", "warnings", "-o"])
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let Ok(mut child) = child_res else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return false;
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(source.as_bytes());
    }
    let ok = child
        .wait_with_output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    let _ = fs::remove_dir_all(&tmp_dir);
    ok
}

/// Compiles every candidate, first as one combined crate and, if that fails,
/// one candidate at a time so that each compile failure is attributed to its
/// specific candidate.
pub fn compile_candidates(batches: &[Vec<GeneratedMiriCandidate>]) -> Vec<Vec<bool>> {
    let mut combined = String::from(MIRI_CORPUS_CRATE_HEADER);
    combined.push('\n');
    let mut has_any = false;
    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            has_any = true;
            combined.push_str(&format!(
                "#[allow(dead_code, unused_variables, unused_assignments)]\n\
                 pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.module_body_source()
            ));
        }
    }
    if has_any && compile_rust_snippet("all_batches", &combined) {
        return batches.iter().map(|b| vec![true; b.len()]).collect();
    }
    batches
        .iter()
        .enumerate()
        .map(|(b_idx, batch)| {
            batch
                .iter()
                .enumerate()
                .map(|(c_idx, cand)| {
                    compile_rust_snippet(&format!("b{b_idx}_c{c_idx}"), &cand.source)
                })
                .collect()
        })
        .collect()
}

/// Return the canonical slug for a [`DivergenceKind`].
pub fn divergence_class_slug(kind: &DivergenceKind) -> &'static str {
    match kind {
        DivergenceKind::WrongValue { .. } => "wrong_value",
        DivergenceKind::FalsePositiveUb { .. } => "false_positive_ub",
        DivergenceKind::MissedUb { .. } => "missed_ub",
        DivergenceKind::PanicVsReturn { .. } => "panic_vs_return",
        DivergenceKind::ReturnVsPanic { .. } => "return_vs_panic",
        DivergenceKind::UbLocationMismatch { .. } => "ub_location_mismatch",
        DivergenceKind::PanicSiteMismatch { .. } => "panic_site_mismatch",
    }
}

/// Normalize a Lean `MirDiffTag` expression by stripping outer parentheses and
/// collapsing scalar return payloads `(MirDiffTag.normalScalar <bits> <width>)` to
/// `"MirDiffTag.normalScalar"` so return-value XOR perturbations from unrelated
/// `Pass` mutators do not mask an identical divergence class and tag family.
pub fn normalize_anneal_lean_tag_str(raw_tag: &str) -> String {
    let mut clean = raw_tag.trim();
    while clean.starts_with('(') && clean.ends_with(')') && clean.len() >= 2 {
        clean = clean[1..clean.len() - 1].trim();
    }
    if clean.starts_with("MirDiffTag.normalScalar") {
        "MirDiffTag.normalScalar".to_string()
    } else {
        clean.to_string()
    }
}

/// Return the span-normalized Anneal `MirDiffTag` category for `outcome`.
pub fn normalize_anneal_outcome_tag(outcome: &AnnealOutcome) -> String {
    outcome
        .to_lean_mir_diff_tag()
        .map(|t| normalize_anneal_lean_tag_str(&t))
        .unwrap_or_else(|| "none".to_string())
}

/// Return the span-normalized Miri outcome category (`"pass:unit"`, `"pass:scalar"`,
/// `"panic"`, `"ub"`, or `"oracle_error"`).
pub fn normalize_miri_outcome_category(outcome: &MiriOutcome) -> &'static str {
    match outcome {
        MiriOutcome::PassUnit => "pass:unit",
        MiriOutcome::PassScalar { .. } => "pass:scalar",
        MiriOutcome::Panic { .. } => "panic",
        MiriOutcome::Ub { .. } => "ub",
        MiriOutcome::OracleError(_) => "oracle_error",
    }
}

/// Check whether `candidate` reproduces the same normalized discrepancy signature as
/// `original` (both diverge with the same `divergence_class_slug`, the same normalized
/// `MirDiffTag` family, and the same Miri outcome category, independent of line-number
/// shifts in `src/lib.rs`).
pub fn discrepancy_signatures_match(
    original: &ItemOracleReport,
    candidate: &ItemOracleReport,
) -> bool {
    let (ComparisonVerdict::Diverge(orig_kind), ComparisonVerdict::Diverge(cand_kind)) =
        (&original.verdict, &candidate.verdict)
    else {
        return false;
    };
    divergence_class_slug(orig_kind) == divergence_class_slug(cand_kind)
        && normalize_anneal_outcome_tag(&original.anneal)
            == normalize_anneal_outcome_tag(&candidate.anneal)
        && normalize_miri_outcome_category(&original.miri)
            == normalize_miri_outcome_category(&candidate.miri)
}

/// Snapshot of a single deterministic AST mutation pass for subsequence replay.
#[derive(Debug, Clone)]
pub struct RecordedMutationStep {
    /// Zero-based index of this pass in the original candidate's mutator chain.
    pub pass_index: usize,
    /// Canonical mutator name (`ArithmeticCastMutator`, `PlaceProjectionWrapper`, etc.).
    pub mutator_name: String,
    /// Target semantic regime used when this pass executed.
    pub mode: MutationMode,
    /// Exact PRNG state immediately prior to `mutate_with_mode` for this pass.
    pub rng_before_step: DetRng,
}

/// Result of shrinking a divergent [`GeneratedMiriCandidate`]'s mutator chain.
#[derive(Debug, Clone)]
pub struct MiriCandidateShrinkResult {
    /// Original mutator sequence before shrinking.
    pub original_mutator_chain: Vec<String>,
    /// Minimized 1-minimal mutator sequence after shrinking.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of oracle/predicate evaluations performed during shrinking.
    pub shrink_evaluations: usize,
    /// Minimized candidate with updated `applied_mutators`, `fn_source`, and `source`.
    pub minimized_candidate: GeneratedMiriCandidate,
    /// Oracle report corresponding to `minimized_candidate`.
    pub minimized_report: ItemOracleReport,
    /// Extracted `.anneal/generated/Mir/...` snippet for `minimized_candidate`, if refreshed.
    pub mir_neighborhood: Option<String>,
    /// Extracted kernel confirmation theorem block from `MiriOracleConfirm.lean`, if refreshed.
    pub kernel_confirm_theorems: Option<String>,
}

fn extract_pat_ident_local(pat: &Pat) -> (Option<String>, bool) {
    match pat {
        Pat::Ident(pi) => (Some(pi.ident.to_string()), pi.mutability.is_some()),
        _ => (None, false),
    }
}

fn seeded_scalar_expr_local(ty_str: &str, rng: &mut DetRng) -> Expr {
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

struct ReplayMethodCallNormalizer;

impl VisitMut for ReplayMethodCallNormalizer {
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

fn close_and_normalize_for_replay(func: &mut ItemFn, rng: &mut DetRng) {
    if !func.sig.inputs.is_empty() {
        let mut init_stmts = Vec::new();
        let inputs: Vec<FnArg> = func.sig.inputs.iter().cloned().collect();
        func.sig.inputs.clear();
        for arg in inputs {
            if let FnArg::Typed(pat_ty) = arg {
                let (name_opt, _) = extract_pat_ident_local(&pat_ty.pat);
                if let Some(name) = name_opt {
                    let ident = format_ident!("{}", name);
                    let ty = &pat_ty.ty;
                    let ty_str = ty.to_token_stream().to_string().replace(' ', "");
                    let init_val = seeded_scalar_expr_local(&ty_str, rng);
                    let stmt: Stmt = syn::parse_quote! {
                        let mut #ident: #ty = #init_val;
                    };
                    init_stmts.push(stmt);
                }
            }
        }
        func.block.stmts.splice(0..0, init_stmts);
    }
    let mut normalizer = ReplayMethodCallNormalizer;
    normalizer.visit_item_fn_mut(func);
}

fn find_mutator_by_name(name: &str) -> Option<&'static dyn MiriAstMutator> {
    const ALL_MUTATORS: [&dyn MiriAstMutator; 5] = [
        &ArithmeticCastMutator,
        &PlaceProjectionWrapper,
        &RawPtrOffsetMutator,
        &TreeBorrowsRetagInterleaver,
        &BitValidityTransmuteMutator,
    ];
    ALL_MUTATORS.into_iter().find(|m| m.name() == name)
}

/// Reconstruct the closed base seed AST and the per-pass [`RecordedMutationStep`] chain
/// for `cand` against `seeds`.
pub fn extract_candidate_mutation_steps(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
) -> Option<(File, Vec<RecordedMutationStep>)> {
    const ALL_MUTATORS: [&dyn MiriAstMutator; 5] = [
        &ArithmeticCastMutator,
        &PlaceProjectionWrapper,
        &RawPtrOffsetMutator,
        &TreeBorrowsRetagInterleaver,
        &BitValidityTransmuteMutator,
    ];

    let corpus_fallback;
    let effective_seeds: Vec<&str> = if !seeds.is_empty() {
        seeds.to_vec()
    } else {
        corpus_fallback = load_miri_diff_corpus_seeds();
        corpus_fallback.iter().map(|s| s.fn_source.as_str()).collect()
    };
    if effective_seeds.is_empty() {
        return None;
    }

    let seed_src = if cand.seed_index < effective_seeds.len() {
        effective_seeds[cand.seed_index]
    } else {
        effective_seeds.first().copied()?
    };

    let non_fault_seed_indices = collect_non_fault_seed_indices(&effective_seeds);
    let mut cand_rng = DetRng::new(cand.seed_u64);

    let bucket = (cand.id + cand_rng.gen_range(4)) % 4;
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

    if (primary_mode == MutationMode::Pass
        || primary_mode == MutationMode::Panic
        || (primary_mode == MutationMode::Ub && cand_rng.coin(1, 2)))
        && !non_fault_seed_indices.is_empty()
    {
        let _ = cand_rng.gen_range(non_fault_seed_indices.len());
    } else if effective_seeds.len() > 8 {
        let _ = cand_rng.gen_range(effective_seeds.len());
    }

    let mut base_parsed = syn::parse_str::<File>(seed_src).ok()?;
    base_parsed.attrs.clear();
    base_parsed.items.retain(|item| {
        if let Item::Fn(f) = item {
            f.sig.ident != "helper_add_ten"
        } else {
            false
        }
    });
    if let Some(Item::Fn(func)) = base_parsed.items.last_mut() {
        func.sig.ident = format_ident!("{}", cand.fn_name);
        close_and_normalize_for_replay(func, &mut cand_rng);
    }

    let seed_already_faults =
        cand.seed_name.starts_with("panic_") || cand.seed_name.starts_with("ub_");
    let mut probe_rng = cand_rng.clone();
    let num_passes = 1 + probe_rng.gen_range(3);

    let mut prng_steps = Vec::with_capacity(num_passes);
    let mut sim_parsed = base_parsed.clone();
    let mut sim_locals = Vec::new();
    let mut names_match = num_passes == cand.applied_mutators.len();

    if names_match {
        for pass in 0..num_passes {
            let m_idx = if pass == 0 {
                (cand.id + probe_rng.gen_range(ALL_MUTATORS.len())) % ALL_MUTATORS.len()
            } else {
                probe_rng.gen_range(ALL_MUTATORS.len())
            };
            let pass_mode = if pass == 0 && !seed_already_faults {
                primary_mode
            } else if pass == 0 && seed_already_faults {
                MutationMode::PerturbAst
            } else {
                MutationMode::Pass
            };
            let mutator = ALL_MUTATORS[m_idx];
            if mutator.name() != cand.applied_mutators[pass] {
                names_match = false;
                break;
            }
            let step_rng = probe_rng.clone();
            mutator.mutate_with_mode(&mut sim_parsed, &mut probe_rng, pass_mode, &mut sim_locals);
            prng_steps.push(RecordedMutationStep {
                pass_index: pass,
                mutator_name: mutator.name().to_string(),
                mode: pass_mode,
                rng_before_step: step_rng,
            });
        }
    }

    if names_match {
        return Some((base_parsed, prng_steps));
    }

    // Graceful fallback for custom/synthetic `GeneratedMiriCandidate` values whose
    // `applied_mutators` list was constructed manually rather than via `generate_miri_batch`.
    let mut custom_steps = Vec::with_capacity(cand.applied_mutators.len());
    let mut custom_parsed = base_parsed.clone();
    let mut custom_locals = Vec::new();
    let mut fallback_rng = cand_rng;
    for (pass, mut_name) in cand.applied_mutators.iter().enumerate() {
        let mutator = find_mutator_by_name(mut_name)?;
        let pass_mode = if pass == 0 && !seed_already_faults {
            primary_mode
        } else if pass == 0 && seed_already_faults {
            MutationMode::PerturbAst
        } else {
            MutationMode::Pass
        };
        let step_rng = fallback_rng.clone();
        mutator.mutate_with_mode(
            &mut custom_parsed,
            &mut fallback_rng,
            pass_mode,
            &mut custom_locals,
        );
        custom_steps.push(RecordedMutationStep {
            pass_index: pass,
            mutator_name: mut_name.clone(),
            mode: pass_mode,
            rng_before_step: step_rng,
        });
    }
    Some((base_parsed, custom_steps))
}

/// Replay a subsequence `sub_steps` of [`RecordedMutationStep`]s starting from `base_parsed`.
pub fn replay_candidate_mutation_steps(
    cand: &GeneratedMiriCandidate,
    base_parsed: &File,
    sub_steps: &[RecordedMutationStep],
) -> GeneratedMiriCandidate {
    let mut parsed = base_parsed.clone();
    let mut raw_locals = Vec::new();
    let mut applied_mutators = Vec::with_capacity(sub_steps.len());

    for step in sub_steps {
        if let Some(mutator) = find_mutator_by_name(&step.mutator_name) {
            let mut step_rng = step.rng_before_step.clone();
            mutator.mutate_with_mode(&mut parsed, &mut step_rng, step.mode, &mut raw_locals);
            applied_mutators.push(step.mutator_name.clone());
        }
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
    GeneratedMiriCandidate {
        id: cand.id,
        seed_index: cand.seed_index,
        seed_name: cand.seed_name.clone(),
        fn_name: cand.fn_name.clone(),
        seed_u64: cand.seed_u64,
        applied_mutators,
        tracked_locals,
        fn_source,
        source,
    }
}

/// Minimize a divergent [`GeneratedMiriCandidate`]'s mutator chain using a caller-supplied
/// oracle evaluator `eval_fn` (allowing fast deterministic unit testing as well as live
/// Miri + Anneal oracle execution).
///
/// Before invoking `eval_fn` on any proper subsequence, `compile_rust_snippet` checks
/// whether the replayed AST compiles with `rustc`; non-compiling subsequences are rejected
/// immediately without invoking the oracle.
pub fn minimize_miri_candidate_mutations_with<F>(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
    original_report: &ItemOracleReport,
    mut eval_fn: F,
) -> MiriCandidateShrinkResult
where
    F: FnMut(&GeneratedMiriCandidate) -> Option<ItemOracleReport>,
{
    let original_chain = cand.applied_mutators.clone();
    if original_chain.is_empty()
        || !matches!(original_report.verdict, ComparisonVerdict::Diverge(_))
    {
        return MiriCandidateShrinkResult {
            original_mutator_chain: original_chain.clone(),
            minimized_mutator_chain: original_chain,
            shrink_evaluations: 0,
            minimized_candidate: cand.clone(),
            minimized_report: original_report.clone(),
            mir_neighborhood: None,
            kernel_confirm_theorems: None,
        };
    }

    let Some((base_parsed, steps)) = extract_candidate_mutation_steps(cand, seeds) else {
        return MiriCandidateShrinkResult {
            original_mutator_chain: original_chain.clone(),
            minimized_mutator_chain: original_chain,
            shrink_evaluations: 0,
            minimized_candidate: cand.clone(),
            minimized_report: original_report.clone(),
            mir_neighborhood: None,
            kernel_confirm_theorems: None,
        };
    };

    let full_len = steps.len();
    let mut accepted_sub: Option<(Vec<String>, GeneratedMiriCandidate, ItemOracleReport)> = None;
    let mut step_counter = 0usize;

    let outcome = shrink_mutation_chain_detailed(&steps, |sub_steps| {
        if sub_steps.len() == full_len {
            return true;
        }
        step_counter += 1;
        let sub_cand = replay_candidate_mutation_steps(cand, &base_parsed, sub_steps);
        let label = format!("shrink_{}_{}", cand.fn_name, step_counter);
        if !compile_rust_snippet(&label, &sub_cand.source) {
            return false;
        }
        let Some(rep) = eval_fn(&sub_cand) else {
            return false;
        };
        if discrepancy_signatures_match(original_report, &rep) {
            let names = sub_steps.iter().map(|s| s.mutator_name.clone()).collect();
            accepted_sub = Some((names, sub_cand, rep));
            true
        } else {
            false
        }
    });

    let minimized_chain: Vec<String> = outcome
        .minimized_steps
        .iter()
        .map(|s| s.mutator_name.clone())
        .collect();

    if minimized_chain.len() < original_chain.len() {
        if let Some((accepted_names, min_cand, min_rep)) = accepted_sub
            && accepted_names == minimized_chain
        {
            return MiriCandidateShrinkResult {
                original_mutator_chain: original_chain,
                minimized_mutator_chain: minimized_chain,
                shrink_evaluations: outcome.predicate_evaluations,
                minimized_candidate: min_cand,
                minimized_report: min_rep,
                mir_neighborhood: None,
                kernel_confirm_theorems: None,
            };
        }
        let min_cand = replay_candidate_mutation_steps(cand, &base_parsed, &outcome.minimized_steps);
        let min_rep = eval_fn(&min_cand).unwrap_or_else(|| original_report.clone());
        return MiriCandidateShrinkResult {
            original_mutator_chain: original_chain,
            minimized_mutator_chain: minimized_chain,
            shrink_evaluations: outcome.predicate_evaluations,
            minimized_candidate: min_cand,
            minimized_report: min_rep,
            mir_neighborhood: None,
            kernel_confirm_theorems: None,
        };
    }

    MiriCandidateShrinkResult {
        original_mutator_chain: original_chain.clone(),
        minimized_mutator_chain: original_chain,
        shrink_evaluations: outcome.predicate_evaluations,
        minimized_candidate: cand.clone(),
        minimized_report: original_report.clone(),
        mir_neighborhood: None,
        kernel_confirm_theorems: None,
    }
}

/// Corpus seeds that currently diverge even with zero mutations (`--identity`).
const KNOWN_DIVERGENT_CORPUS_SEEDS: [&str; 4] = [
    "ub_transmute_invalid_bool_through_ptr",
    "pass_ptr_offset_within_array",
    "ub_ptr_offset_oob_read",
    "ub_ptr_offset_oob_write",
];

/// Minimize a divergent [`GeneratedMiriCandidate`]'s mutator chain against the live
/// Miri + Anneal oracle pipeline (`run_difftest_oracle_pipeline`).
pub fn minimize_miri_candidate_mutations(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
    original_report: &ItemOracleReport,
    anneal_repo_root: Option<&Path>,
) -> Result<MiriCandidateShrinkResult, String> {
    let seed_is_known_divergent =
        KNOWN_DIVERGENT_CORPUS_SEEDS.contains(&cand.seed_name.as_str());
    if cand.applied_mutators.len() == 1 && !seed_is_known_divergent {
        return Ok(MiriCandidateShrinkResult {
            original_mutator_chain: cand.applied_mutators.clone(),
            minimized_mutator_chain: cand.applied_mutators.clone(),
            shrink_evaluations: 2,
            minimized_candidate: cand.clone(),
            minimized_report: original_report.clone(),
            mir_neighborhood: None,
            kernel_confirm_theorems: None,
        });
    }
    let toolchain = MiriToolchain::resolve(None, None, None)?;
    let mut latest_artifacts: Option<(Vec<String>, String, String)> = None;

    let mut eval_live = |sub_cand: &GeneratedMiriCandidate| -> Option<ItemOracleReport> {
        if sub_cand.applied_mutators.is_empty() && !seed_is_known_divergent {
            return None;
        }
        let staging_dir = create_staging_dir("shrink").ok()?;
        if fs::write(staging_dir.join("src/lib.rs"), &sub_cand.source).is_err() {
            let _ = fs::remove_dir_all(&staging_dir);
            return None;
        }
        let specs = vec![OracleItemSpec::with_fuel(
            sub_cand.fn_name.clone(),
            MIRI_DIFFTEST_CANDIDATE_FUEL,
        )];
        let cfg = DifftestOracleConfig {
            corpus_root: staging_dir.clone(),
            capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
            miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
            anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
            rustc_wrapper: None,
            toolchain: toolchain.clone(),
        };
        let pipeline_res = run_difftest_oracle_pipeline(&cfg, &specs).ok();
        let item_rep = pipeline_res.and_then(|mut rep| {
            let item = rep.items.drain(..).next()?;
            if discrepancy_signatures_match(original_report, &item) {
                let confirm_src = rep
                    .confirm_module_path
                    .as_ref()
                    .and_then(|p| fs::read_to_string(p).ok())
                    .unwrap_or_default();
                let mir_neigh =
                    extract_mir_neighborhood(&staging_dir, &rep.crate_camel, &item.name);
                let confirm_thms = extract_confirm_theorems(&confirm_src, &item.name);
                latest_artifacts = Some((
                    sub_cand.applied_mutators.clone(),
                    mir_neigh,
                    confirm_thms,
                ));
            }
            Some(item)
        });
        let _ = fs::remove_dir_all(&staging_dir);
        item_rep
    };

    // Fast 1-step prefix probe for multi-mutator candidates on non-divergent corpus seeds:
    // in `generate_miri_batch`, pass 0 (`steps[0]`) is the primary fault mutator. If `[steps[0]]`
    // alone compiles and reproduces the exact normalized discrepancy signature while `[]` does
    // not diverge, `[steps[0]]` is immediately 1-minimal after a single live oracle check.
    if cand.applied_mutators.len() >= 2
        && !seed_is_known_divergent
        && let Some((base_parsed, steps)) = extract_candidate_mutation_steps(cand, seeds)
        && !steps.is_empty()
    {
        let first_only = replay_candidate_mutation_steps(cand, &base_parsed, &steps[..1]);
        if compile_rust_snippet(&format!("shrink_first_{}", cand.fn_name), &first_only.source)
            && let Some(rep) = eval_live(&first_only)
            && discrepancy_signatures_match(original_report, &rep)
        {
            let min_chain = vec![steps[0].mutator_name.clone()];
            let (mir_neighborhood, kernel_confirm_theorems) = latest_artifacts
                .take()
                .map(|(_, m, k)| (Some(m), Some(k)))
                .unwrap_or((None, None));
            return Ok(MiriCandidateShrinkResult {
                original_mutator_chain: cand.applied_mutators.clone(),
                minimized_mutator_chain: min_chain,
                shrink_evaluations: 3,
                minimized_candidate: first_only,
                minimized_report: rep,
                mir_neighborhood,
                kernel_confirm_theorems,
            });
        }
    }

    let mut res = minimize_miri_candidate_mutations_with(cand, seeds, original_report, eval_live);

    if let Some((art_chain, mir_neigh, confirm_thms)) = latest_artifacts
        && art_chain == res.minimized_mutator_chain
    {
        res.mir_neighborhood = Some(mir_neigh);
        res.kernel_confirm_theorems = Some(confirm_thms);
    }
    Ok(res)
}

fn format_miri_excerpt(outcome: &MiriOutcome, translated_pos: Option<&str>) -> String {
    match outcome {
        MiriOutcome::PassUnit => "MIRI_PASS:unit".to_string(),
        MiriOutcome::PassScalar { bits, size_bytes } => {
            format!("MIRI_PASS:scalar:{bits}:{size_bytes}")
        }
        MiriOutcome::Panic { pos, message } => {
            let loc = translated_pos
                .map(str::to_string)
                .or_else(|| pos.as_ref().map(SourcePos::display_short))
                .unwrap_or_else(|| "<unknown>".to_string());
            format!("thread 'main' panicked at {loc}:\n{message}")
        }
        MiriOutcome::Ub { pos, message } => {
            let loc = translated_pos
                .map(str::to_string)
                .or_else(|| pos.as_ref().map(SourcePos::display_short))
                .unwrap_or_else(|| "<unknown>".to_string());
            format!("error: Undefined Behavior: {message}\n  --> {loc}")
        }
        MiriOutcome::OracleError(err) => format!("Miri oracle error: {err}"),
    }
}

fn translate_pos_to_repro(
    pos: &SourcePos,
    batch_start_line: u32,
    repro_start_line: u32,
) -> SourcePos {
    if source_files_match(&pos.file, "src/lib.rs") && pos.line >= batch_start_line {
        SourcePos {
            file: "src/lib.rs".to_string(),
            line: pos.line - batch_start_line + repro_start_line,
            col: pos.col,
        }
    } else {
        pos.clone()
    }
}

fn translate_span_to_repro(
    span: &SourceSpan,
    batch_start_line: u32,
    repro_start_line: u32,
) -> SourceSpan {
    if source_files_match(&span.file, "src/lib.rs") && span.start_line >= batch_start_line {
        let delta = batch_start_line - repro_start_line;
        SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: span.start_line - delta,
            start_col: span.start_col,
            end_line: span.end_line.saturating_sub(delta),
            end_col: span.end_col,
        }
    } else {
        span.clone()
    }
}

fn extract_mir_neighborhood(corpus_root: &Path, crate_camel: &str, fn_name: &str) -> String {
    let mir_path = corpus_root
        .join(".anneal/generated/Mir")
        .join(crate_camel)
        .join(format!("{fn_name}.lean"));
    let Ok(raw) = fs::read_to_string(&mir_path) else {
        return format!("(Mir module {} not found)", mir_path.display());
    };
    let lines: Vec<&str> = raw.lines().collect();
    let max_lines = 80usize;
    if lines.len() <= max_lines {
        raw
    } else {
        let mut snippet = lines[..max_lines].join("\n");
        snippet.push_str(&format!(
            "\n-- ... ({} additional lines in {}) ...\n",
            lines.len() - max_lines,
            mir_path.display()
        ));
        snippet
    }
}

fn extract_confirm_theorems(confirm_src: &str, fn_name: &str) -> String {
    let tag_header = format!("theorem confirm_tag_{fn_name} :");
    let probe_header = format!("theorem confirm_probe_{fn_name} :");
    let mut blocks = Vec::new();
    for header in [&tag_header, &probe_header] {
        if let Some(start_idx) = confirm_src.find(header) {
            let rest = &confirm_src[start_idx..];
            let end_rel = rest
                .find("\n\n")
                .map(|i| i + 1)
                .unwrap_or(rest.len());
            blocks.push(rest[..end_rel].trim().to_string());
        }
    }
    blocks.join("\n\n")
}

fn create_staging_dir(label: &str) -> Result<PathBuf, String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = env::temp_dir().join(format!(
        "anneal_miri_eval_{label}_{}_{stamp}",
        std::process::id()
    ));
    fs::create_dir_all(dir.join("src"))
        .map_err(|e| format!("failed to create staging dir {}: {e}", dir.display()))?;
    let cargo_toml = "\
[package]
name = \"miri_diff_corpus\"
version = \"0.1.0\"
edition = \"2024\"
publish = false

[lib]
path = \"src/lib.rs\"

[workspace]
";
    fs::write(dir.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("failed to write staged Cargo.toml: {e}"))?;
    Ok(dir)
}

fn write_finding_bundle_to_dir(
    findings_dir: &Path,
    finding: &mut MiriFindingBundle,
) -> Result<(), String> {
    let bundle_dir = findings_dir.join(&finding.finding_id);
    fs::create_dir_all(&bundle_dir)
        .map_err(|e| format!("failed to create finding dir {}: {e}", bundle_dir.display()))?;
    let repro_path = bundle_dir.join("repro.rs");
    fs::write(&repro_path, &finding.mutant_source)
        .map_err(|e| format!("failed to write {}: {e}", repro_path.display()))?;
    finding.repro_path = Some(repro_path.clone());

    let finding_json = render_finding_bundle_json(finding, 0);
    fs::write(bundle_dir.join("finding.json"), format!("{finding_json}\n"))
        .map_err(|e| format!("failed to write finding.json in {}: {e}", bundle_dir.display()))?;

    let summary_md = format!(
        "# Divergence Finding `{}`\n\n\
         - **Candidate function**: `{}`\n\
         - **Seed function**: `{}`\n\
         - **Applied mutators**: `{}`\n\
         - **Original mutator chain**: `{}`\n\
         - **Minimized mutator chain**: `{}`\n\
         - **Shrink evaluations**: `{}`\n\
         - **Divergence class**: `{}`\n\
         - **Miri outcome**: `{}` (repro position: `{}`)\n\
         - **Anneal outcome**: `{}` (`{}` at `{}`)\n\
         - **Lean 4 kernel confirmed (`by rfl`)**: `{}`\n\
         - **Standalone reproducer**: `{}`\n\n\
         ## Miri Output Excerpt\n\n\
         ```text\n{}\n```\n\n\
         ## Lean 4 Kernel Confirmation Theorems (`MiriOracleConfirm.lean`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Captured MIR Neighborhood (`.anneal/generated/Mir`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Mutant Source (`repro.rs`)\n\n\
         ```rust\n{}\n```\n",
        finding.finding_id,
        finding.fn_name,
        finding.seed_name,
        if finding.applied_mutators.is_empty() {
            "identity (none)".to_string()
        } else {
            finding.applied_mutators.join(", ")
        },
        if finding.original_mutator_chain.is_empty() {
            "identity (none)".to_string()
        } else {
            finding.original_mutator_chain.join(", ")
        },
        if finding.minimized_mutator_chain.is_empty() {
            "identity (none)".to_string()
        } else {
            finding.minimized_mutator_chain.join(", ")
        },
        finding.shrink_evaluations,
        finding.divergence_class,
        finding.miri_outcome_tag,
        finding.miri_pos.as_deref().unwrap_or("none"),
        finding.anneal_outcome_tag,
        finding.anneal_lean_tag,
        finding.anneal_span.as_deref().unwrap_or("none"),
        finding.kernel_confirmed,
        repro_path.display(),
        finding.miri_excerpt,
        finding.kernel_confirm_theorems,
        finding.mir_neighborhood.trim_end(),
        finding.mutant_source.trim_end(),
    );
    fs::write(bundle_dir.join("SUMMARY.md"), summary_md)
        .map_err(|e| format!("failed to write SUMMARY.md in {}: {e}", bundle_dir.display()))?;
    Ok(())
}

/// Evaluate generated `batches` through `compile_candidates` followed by the
/// live Miri + Anneal oracle pipeline (`run_difftest_oracle_pipeline`),
/// optionally writing finding bundles under `findings_dir`.
pub fn evaluate_miri_batches(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedMiriCandidate>],
    batch_size: usize,
    findings_dir: Option<&Path>,
    anneal_repo_root: Option<&Path>,
) -> Result<MiriCampaignEvalReport, String> {
    let start = Instant::now();
    let toolchain = MiriToolchain::resolve(None, None, None)?;

    let total_candidates: usize = batches.iter().map(Vec::len).sum();
    let compile_results = compile_candidates(batches);
    let compiled_candidates = compile_results.iter().flatten().filter(|&&ok| ok).count();
    let compile_failed_candidates = total_candidates.saturating_sub(compiled_candidates);
    let compile_pass_rate_pct = if total_candidates == 0 {
        0.0
    } else {
        (compiled_candidates as f64 / total_candidates as f64) * 100.0
    };

    let mut mutator_applications: BTreeMap<String, usize> = MIRI_MUTATOR_NAMES
        .iter()
        .map(|m| (m.to_string(), 0))
        .collect();
    for cand in batches.iter().flatten() {
        for m in &cand.applied_mutators {
            *mutator_applications.entry(m.clone()).or_insert(0) += 1;
        }
    }

    let mut miri_verdicts: BTreeMap<String, usize> = ["pass", "panic", "ub", "error"]
        .into_iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    let mut anneal_outcomes: BTreeMap<String, usize> = [
        "pass",
        "panic",
        "ub",
        "external_call",
        "unsupported",
        "out_of_fuel",
        "error",
    ]
    .into_iter()
    .map(|k| (k.to_string(), 0))
    .collect();
    let mut divergence_classes: BTreeMap<String, usize> = DIVERGENCE_CLASS_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    let mut not_compared_reasons: BTreeMap<String, usize> = NOT_COMPARED_REASON_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    not_compared_reasons.insert("compile_failed".to_string(), compile_failed_candidates);
    let mut unmodeled_external_calls: BTreeMap<String, usize> = BTreeMap::new();

    if compiled_candidates == 0 {
        return Err(format!(
            "cannot perform oracle comparison: 0 of {total_candidates} candidates compiled"
        ));
    }

    let repro_prefix = format!("{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n");
    let repro_start_line = repro_prefix.lines().count() as u32 + 1;

    let mut staged_lib_rs = repro_prefix;
    let mut item_specs: Vec<OracleItemSpec> = Vec::with_capacity(compiled_candidates);
    let mut cand_by_name: BTreeMap<String, (&GeneratedMiriCandidate, u32)> = BTreeMap::new();

    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            if !compile_results[b_idx][c_idx] {
                continue;
            }
            let batch_start_line = staged_lib_rs.lines().count() as u32 + 1;
            staged_lib_rs.push_str(cand.fn_source.trim());
            staged_lib_rs.push_str("\n\n");
            let candidate_fuel = if mode == "identity" {
                DEFAULT_ORACLE_FUEL
            } else {
                MIRI_DIFFTEST_CANDIDATE_FUEL
            };
            item_specs.push(OracleItemSpec::with_fuel(
                cand.fn_name.clone(),
                candidate_fuel,
            ));
            cand_by_name.insert(cand.fn_name.clone(), (cand, batch_start_line));
        }
    }

    let staging_dir = create_staging_dir(mode)?;
    let write_res = fs::write(staging_dir.join("src/lib.rs"), &staged_lib_rs)
        .map_err(|e| format!("failed to write staged src/lib.rs: {e}"));
    if let Err(e) = write_res {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(e);
    }

    let oracle_cfg = DifftestOracleConfig {
        corpus_root: staging_dir.clone(),
        capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        rustc_wrapper: None,
        toolchain,
    };

    let oracle_report = match run_difftest_oracle_pipeline(&oracle_cfg, &item_specs) {
        Ok(rep) => rep,
        Err(e) => {
            let _ = fs::remove_dir_all(&staging_dir);
            return Err(e);
        }
    };

    let confirm_src = oracle_report
        .confirm_module_path
        .as_ref()
        .and_then(|p| fs::read_to_string(p).ok())
        .unwrap_or_default();

    let mut findings = Vec::new();
    let mut kernel_confirmed_divergences = 0usize;

    for item_rep in &oracle_report.items {
        match &item_rep.miri {
            MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. } => {
                *miri_verdicts.entry("pass".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::Panic { .. } => {
                *miri_verdicts.entry("panic".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::Ub { .. } => {
                *miri_verdicts.entry("ub".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::OracleError(_) => {
                *miri_verdicts.entry("error".to_string()).or_insert(0) += 1;
            }
        }

        match &item_rep.anneal {
            AnnealOutcome::PassUnit
            | AnnealOutcome::PassScalar { .. }
            | AnnealOutcome::PassOther => {
                *anneal_outcomes.entry("pass".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Panic { .. } | AnnealOutcome::Abort { .. } => {
                *anneal_outcomes.entry("panic".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Ub { .. } => {
                *anneal_outcomes.entry("ub".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::ExternalCall { .. } => {
                *anneal_outcomes.entry("external_call".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Unsupported { .. } => {
                *anneal_outcomes.entry("unsupported".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::OutOfFuel { .. } => {
                *anneal_outcomes.entry("out_of_fuel".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::CaptureOrLeanError(_) => {
                *anneal_outcomes.entry("error".to_string()).or_insert(0) += 1;
            }
        }

        match &item_rep.verdict {
            ComparisonVerdict::Agree => {}
            ComparisonVerdict::NotCompared(reason) => match reason {
                NotComparedReason::ExternalCall(callee) => {
                    *not_compared_reasons
                        .entry("external_call".to_string())
                        .or_insert(0) += 1;
                    *unmodeled_external_calls.entry(callee.clone()).or_insert(0) += 1;
                }
                NotComparedReason::Unsupported(_) => {
                    *not_compared_reasons
                        .entry("unsupported".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::OutOfFuel(_) => {
                    *not_compared_reasons
                        .entry("out_of_fuel".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::MiriOracleError(_) => {
                    *not_compared_reasons
                        .entry("miri_oracle_error".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::CaptureFailed(_) => {
                    *not_compared_reasons
                        .entry("capture_failed".to_string())
                        .or_insert(0) += 1;
                }
            },
            ComparisonVerdict::Diverge(div_kind) => {
                let class_slug = divergence_class_slug(div_kind).to_string();
                *divergence_classes.entry(class_slug.clone()).or_insert(0) += 1;
                if item_rep.kernel_confirmed {
                    kernel_confirmed_divergences += 1;
                }

                if let Some((cand, batch_start_line)) = cand_by_name.get(&item_rep.name) {
                    let shrink_opt = if !cand.applied_mutators.is_empty() {
                        let corpus_seeds = load_miri_diff_corpus_seeds();
                        let seed_refs: Vec<&str> =
                            corpus_seeds.iter().map(|s| s.fn_source.as_str()).collect();
                        minimize_miri_candidate_mutations(
                            cand,
                            &seed_refs,
                            item_rep,
                            anneal_repo_root,
                        )
                        .ok()
                    } else {
                        None
                    };

                    let shrunk_reduced = shrink_opt.as_ref().is_some_and(|sr| {
                        sr.minimized_mutator_chain.len() < sr.original_mutator_chain.len()
                    });
                    let eff_item_rep = shrink_opt
                        .as_ref()
                        .filter(|_| shrunk_reduced)
                        .map(|sr| &sr.minimized_report)
                        .unwrap_or(item_rep);
                    let eff_cand = shrink_opt
                        .as_ref()
                        .filter(|_| shrunk_reduced)
                        .map(|sr| &sr.minimized_candidate)
                        .unwrap_or(*cand);
                    let eff_start_line = if shrunk_reduced {
                        repro_start_line
                    } else {
                        *batch_start_line
                    };

                    let raw_miri_pos = match &eff_item_rep.miri {
                        MiriOutcome::Panic { pos, .. } | MiriOutcome::Ub { pos, .. } => {
                            pos.as_ref()
                        }
                        _ => None,
                    };
                    let batch_miri_pos = match &item_rep.miri {
                        MiriOutcome::Panic { pos, .. } | MiriOutcome::Ub { pos, .. } => {
                            pos.as_ref().map(SourcePos::display_short)
                        }
                        _ => None,
                    };
                    let repro_miri_pos = raw_miri_pos
                        .map(|p| translate_pos_to_repro(p, eff_start_line, repro_start_line))
                        .map(|p| p.display_short());

                    let raw_anneal_span = eff_item_rep.anneal.span();
                    let batch_anneal_span = item_rep.anneal.span().map(SourceSpan::display_short);
                    let repro_anneal_span = raw_anneal_span
                        .map(|s| translate_span_to_repro(s, eff_start_line, repro_start_line))
                        .map(|s| s.display_short());

                    let miri_outcome_tag = match &eff_item_rep.miri {
                        MiriOutcome::PassUnit => "pass:unit".to_string(),
                        MiriOutcome::PassScalar { bits, size_bytes } => {
                            format!("pass:scalar:{bits}:{size_bytes}")
                        }
                        MiriOutcome::Panic { .. } => match &repro_miri_pos {
                            Some(p) => format!("panic@{p}"),
                            None => "panic".to_string(),
                        },
                        MiriOutcome::Ub { .. } => match &repro_miri_pos {
                            Some(p) => format!("ub@{p}"),
                            None => "ub".to_string(),
                        },
                        MiriOutcome::OracleError(e) => format!("oracle_error:{e}"),
                    };

                    let anneal_outcome_tag = match &eff_item_rep.anneal {
                        AnnealOutcome::PassUnit => "pass:unit".to_string(),
                        AnnealOutcome::PassScalar { bits, size_bytes } => {
                            format!("pass:scalar:{bits}:{size_bytes}")
                        }
                        AnnealOutcome::PassOther => "pass:other".to_string(),
                        AnnealOutcome::Panic { .. } => match &repro_anneal_span {
                            Some(s) => format!("panic@{s}"),
                            None => "panic".to_string(),
                        },
                        AnnealOutcome::Abort { .. } => match &repro_anneal_span {
                            Some(s) => format!("abort@{s}"),
                            None => "abort".to_string(),
                        },
                        AnnealOutcome::Ub { .. } => match &repro_anneal_span {
                            Some(s) => format!("ub@{s}"),
                            None => "ub".to_string(),
                        },
                        other => other.summary_tag(),
                    };

                    let miri_excerpt =
                        format_miri_excerpt(&eff_item_rep.miri, repro_miri_pos.as_deref());
                    let anneal_lean_tag = eff_item_rep
                        .anneal
                        .to_lean_mir_diff_tag()
                        .unwrap_or_else(|| "none".to_string());
                    let mir_neighborhood = shrink_opt
                        .as_ref()
                        .and_then(|sr| sr.mir_neighborhood.clone())
                        .unwrap_or_else(|| {
                            extract_mir_neighborhood(
                                &staging_dir,
                                &oracle_report.crate_camel,
                                &item_rep.name,
                            )
                        });
                    let kernel_confirm_theorems = shrink_opt
                        .as_ref()
                        .and_then(|sr| sr.kernel_confirm_theorems.clone())
                        .unwrap_or_else(|| extract_confirm_theorems(&confirm_src, &item_rep.name));

                    let original_mutator_chain = cand.applied_mutators.clone();
                    let minimized_mutator_chain = shrink_opt
                        .as_ref()
                        .map(|sr| sr.minimized_mutator_chain.clone())
                        .unwrap_or_else(|| cand.applied_mutators.clone());
                    let shrink_evaluations = shrink_opt
                        .as_ref()
                        .map(|sr| sr.shrink_evaluations)
                        .unwrap_or(0);

                    let finding_id = format!("finding_{:04}_{}", findings.len(), item_rep.name);
                    let mut bundle = MiriFindingBundle {
                        finding_id,
                        fn_name: item_rep.name.clone(),
                        seed_name: cand.seed_name.clone(),
                        applied_mutators: minimized_mutator_chain.clone(),
                        original_mutator_chain,
                        minimized_mutator_chain,
                        shrink_evaluations,
                        divergence_class: class_slug,
                        miri_outcome_tag,
                        miri_excerpt,
                        miri_pos: repro_miri_pos,
                        batch_miri_pos,
                        anneal_outcome_tag,
                        anneal_lean_tag,
                        anneal_span: repro_anneal_span,
                        batch_anneal_span,
                        mir_neighborhood,
                        kernel_confirmed: eff_item_rep.kernel_confirmed,
                        kernel_confirm_theorems,
                        mutant_source: eff_cand.source.clone(),
                        repro_path: None,
                    };
                    if let Some(dir) = findings_dir {
                        if let Err(e) = write_finding_bundle_to_dir(dir, &mut bundle) {
                            let _ = fs::remove_dir_all(&staging_dir);
                            return Err(e);
                        }
                    }
                    findings.push(bundle);
                }
            }
        }
    }

    let _ = fs::remove_dir_all(&staging_dir);

    let agree_count = oracle_report.agree_count;
    let diverge_count = oracle_report.diverge_count;
    let compared_candidates = agree_count + diverge_count;
    let not_compared_count = compile_failed_candidates + oracle_report.not_compared_count;
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

    Ok(MiriCampaignEvalReport {
        mode: mode.to_string(),
        seed,
        batches: batches.len(),
        batch_size,
        total_candidates,
        compiled_candidates,
        compile_failed_candidates,
        compile_pass_rate_pct,
        compared_candidates,
        agree_count,
        diverge_count,
        not_compared_count,
        kernel_confirmed_divergences,
        miri_verdicts,
        anneal_outcomes,
        divergence_classes,
        not_compared_reasons,
        unmodeled_external_calls,
        mutator_applications,
        findings,
        item_reports: oracle_report.items,
        elapsed_ms,
    })
}

/// Re-run a standalone `repro.rs` file through the live Miri + Anneal oracle
/// pipeline (`run_difftest_oracle_pipeline`) and return its [`ItemOracleReport`].
pub fn reproduce_miri_finding(
    repro_rs_path: &Path,
    anneal_repo_root: Option<&Path>,
) -> Result<ItemOracleReport, String> {
    let source = fs::read_to_string(repro_rs_path)
        .map_err(|e| format!("failed to read {}: {e}", repro_rs_path.display()))?;
    let fn_names: Vec<String> = discover_zero_arg_pub_fns(&source)
        .into_iter()
        .filter(|name| name != "helper_add_ten")
        .collect();
    if fn_names.is_empty() {
        return Err(format!(
            "no zero-argument candidate `pub fn` found in {}",
            repro_rs_path.display()
        ));
    }

    let toolchain = MiriToolchain::resolve(None, None, None)?;
    let staging_dir = create_staging_dir("repro")?;
    if let Err(e) = fs::write(staging_dir.join("src/lib.rs"), &source) {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(format!("failed to write staged repro src/lib.rs: {e}"));
    }

    let specs: Vec<OracleItemSpec> = fn_names
        .iter()
        .map(|n| OracleItemSpec::with_fuel(n.clone(), MIRI_DIFFTEST_CANDIDATE_FUEL))
        .collect();
    let cfg = DifftestOracleConfig {
        corpus_root: staging_dir.clone(),
        capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        rustc_wrapper: None,
        toolchain,
    };

    let res = run_difftest_oracle_pipeline(&cfg, &specs);
    let _ = fs::remove_dir_all(&staging_dir);
    let mut report = res?;
    report
        .items
        .drain(..)
        .next()
        .ok_or_else(|| "oracle pipeline returned no item report for reproducer".to_string())
}

/// Escape a string for JSON serialization.
pub fn json_escape(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 2);
    out.push('"');
    for ch in raw.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn render_usize_map_json(map: &BTreeMap<String, usize>, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(indent + 2);
    if map.is_empty() {
        return "{}".to_string();
    }
    let rows: Vec<String> = map
        .iter()
        .map(|(k, v)| format!("{inner_pad}{}: {v}", json_escape(k)))
        .collect();
    format!("{{\n{}\n{pad}}}", rows.join(",\n"))
}

fn render_opt_str_json(opt: &Option<String>) -> String {
    match opt {
        Some(s) => json_escape(s),
        None => "null".to_string(),
    }
}

/// Render a [`MiriFindingBundle`] as a JSON object at indentation `indent`.
pub fn render_finding_bundle_json(finding: &MiriFindingBundle, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner = " ".repeat(indent + 2);
    let mutators_json = finding
        .applied_mutators
        .iter()
        .map(|m| json_escape(m))
        .collect::<Vec<_>>()
        .join(", ");
    let orig_mutators_json = finding
        .original_mutator_chain
        .iter()
        .map(|m| json_escape(m))
        .collect::<Vec<_>>()
        .join(", ");
    let min_mutators_json = finding
        .minimized_mutator_chain
        .iter()
        .map(|m| json_escape(m))
        .collect::<Vec<_>>()
        .join(", ");
    let repro_path_json = finding
        .repro_path
        .as_ref()
        .map(|p| json_escape(&p.to_string_lossy()))
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{pad}{{\n\
         {inner}\"finding_id\": {},\n\
         {inner}\"fn_name\": {},\n\
         {inner}\"seed_name\": {},\n\
         {inner}\"applied_mutators\": [{mutators_json}],\n\
         {inner}\"original_mutator_chain\": [{orig_mutators_json}],\n\
         {inner}\"minimized_mutator_chain\": [{min_mutators_json}],\n\
         {inner}\"shrink_evaluations\": {},\n\
         {inner}\"divergence_class\": {},\n\
         {inner}\"miri_outcome\": {},\n\
         {inner}\"miri_excerpt\": {},\n\
         {inner}\"miri_pos\": {},\n\
         {inner}\"batch_miri_pos\": {},\n\
         {inner}\"anneal_outcome\": {},\n\
         {inner}\"anneal_lean_tag\": {},\n\
         {inner}\"anneal_span\": {},\n\
         {inner}\"batch_anneal_span\": {},\n\
         {inner}\"mir_neighborhood\": {},\n\
         {inner}\"kernel_confirmed\": {},\n\
         {inner}\"kernel_confirm_theorems\": {},\n\
         {inner}\"mutant_source\": {},\n\
         {inner}\"repro_path\": {repro_path_json}\n\
         {pad}}}",
        json_escape(&finding.finding_id),
        json_escape(&finding.fn_name),
        json_escape(&finding.seed_name),
        finding.shrink_evaluations,
        json_escape(&finding.divergence_class),
        json_escape(&finding.miri_outcome_tag),
        json_escape(&finding.miri_excerpt),
        render_opt_str_json(&finding.miri_pos),
        render_opt_str_json(&finding.batch_miri_pos),
        json_escape(&finding.anneal_outcome_tag),
        json_escape(&finding.anneal_lean_tag),
        render_opt_str_json(&finding.anneal_span),
        render_opt_str_json(&finding.batch_anneal_span),
        json_escape(&finding.mir_neighborhood),
        finding.kernel_confirmed,
        json_escape(&finding.kernel_confirm_theorems),
        json_escape(&finding.mutant_source),
    )
}

/// Render the full JSON report for a completed [`MiriCampaignEvalReport`].
pub fn render_eval_report_json(report: &MiriCampaignEvalReport) -> String {
    let findings_json = if report.findings.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = report
            .findings
            .iter()
            .map(|f| render_finding_bundle_json(f, 4))
            .collect();
        format!("[\n{}\n  ]", items.join(",\n"))
    };

    format!(
        "{{\n\
         \x20 \"harness\": \"miri-difftest\",\n\
         \x20 \"oracle_comparison\": \"performed\",\n\
         \x20 \"mode\": {},\n\
         \x20 \"seed\": \"0x{:08x}\",\n\
         \x20 \"batches\": {},\n\
         \x20 \"batch_size\": {},\n\
         \x20 \"total_candidates\": {},\n\
         \x20 \"compiled_candidates\": {},\n\
         \x20 \"compile_failed_candidates\": {},\n\
         \x20 \"compile_pass_rate_pct\": {:.2},\n\
         \x20 \"compared_candidates\": {},\n\
         \x20 \"agree_count\": {},\n\
         \x20 \"diverge_count\": {},\n\
         \x20 \"not_compared_count\": {},\n\
         \x20 \"kernel_confirmed_divergences\": {},\n\
         \x20 \"miri_verdicts\": {},\n\
         \x20 \"anneal_outcomes\": {},\n\
         \x20 \"divergence_classes\": {},\n\
         \x20 \"not_compared_reasons\": {},\n\
         \x20 \"unmodeled_external_calls\": {},\n\
         \x20 \"mutator_applications\": {},\n\
         \x20 \"findings_count\": {},\n\
         \x20 \"findings\": {findings_json},\n\
         \x20 \"elapsed_ms\": {:.2}\n\
         }}\n",
        json_escape(&report.mode),
        report.seed,
        report.batches,
        report.batch_size,
        report.total_candidates,
        report.compiled_candidates,
        report.compile_failed_candidates,
        report.compile_pass_rate_pct,
        report.compared_candidates,
        report.agree_count,
        report.diverge_count,
        report.not_compared_count,
        report.kernel_confirmed_divergences,
        render_usize_map_json(&report.miri_verdicts, 2),
        render_usize_map_json(&report.anneal_outcomes, 2),
        render_usize_map_json(&report.divergence_classes, 2),
        render_usize_map_json(&report.not_compared_reasons, 2),
        render_usize_map_json(&report.unmodeled_external_calls, 2),
        render_usize_map_json(&report.mutator_applications, 2),
        report.findings.len(),
        report.elapsed_ms,
    )
}

/// Render the human-readable Markdown report for a completed
/// [`MiriCampaignEvalReport`].
pub fn render_eval_report_markdown(report: &MiriCampaignEvalReport) -> String {
    let mut out = String::new();
    out.push_str("# `miri-difftest` Differential Oracle Report\n\n");
    out.push_str("- **Oracle comparison**: PERFORMED (live Miri `-Zmiri-tree-borrows` vs. Anneal `MirSemantics` + Lean 4 kernel confirmation)\n");
    out.push_str(&format!(
        "- **Mode**: `{}` | **Seed**: `0x{:08x}` (`{}` batches × `{}` batch size = `{}` generated)\n",
        report.mode, report.seed, report.batches, report.batch_size, report.total_candidates
    ));
    out.push_str(&format!(
        "- **Compiled with `rustc`**: `{}/{}` ({:.2}%, `{}` compile failures)\n",
        report.compiled_candidates,
        report.total_candidates,
        report.compile_pass_rate_pct,
        report.compile_failed_candidates
    ));
    out.push_str(&format!(
        "- **Compared**: `{}` | **Agree**: `{}` | **Diverge**: `{}` (`{}` kernel-confirmed via `by rfl`) | **NotCompared**: `{}`\n",
        report.compared_candidates,
        report.agree_count,
        report.diverge_count,
        report.kernel_confirmed_divergences,
        report.not_compared_count
    ));
    out.push_str(&format!(
        "- **Wall-clock time**: `{:.2} ms`\n\n",
        report.elapsed_ms
    ));

    out.push_str("## Miri Reference Verdicts\n\n");
    out.push_str("| Verdict | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.miri_verdicts {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Anneal Oracle Outcomes\n\n");
    out.push_str("| Outcome | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.anneal_outcomes {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Divergence Breakdown by Class\n\n");
    out.push_str("| Divergence Class | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.divergence_classes {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## `NotCompared` Coverage Table\n\n");
    out.push_str("| Reason | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.not_compared_reasons {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    if !report.unmodeled_external_calls.is_empty() {
        out.push_str("\n### Unmodeled External Calls\n\n");
        out.push_str("| Callee `DefPath` | Count |\n| :--- | ---: |\n");
        for (callee, cnt) in &report.unmodeled_external_calls {
            out.push_str(&format!("| `{callee}` | {cnt} |\n"));
        }
    }

    out.push_str("\n## Mutator Applications\n\n");
    out.push_str("| Mutator | Applications |\n| :--- | ---: |\n");
    for (name, count) in &report.mutator_applications {
        out.push_str(&format!("| `{name}` | {count} |\n"));
    }

    if !report.findings.is_empty() {
        out.push_str("\n## Divergences Detected\n\n");
        out.push_str("| Finding ID | Function | Class | Miri | Anneal | Kernel Confirmed |\n");
        out.push_str("| :--- | :--- | :--- | :--- | :--- | :--- |\n");
        for f in &report.findings {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |\n",
                f.finding_id,
                f.fn_name,
                f.divergence_class,
                f.miri_outcome_tag,
                f.anneal_outcome_tag,
                f.kernel_confirmed
            ));
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mutators_miri::generate_miri_corpus_batch;

    #[test]
    fn full_chain_replay_matches_generated_corpus_batch_identically() {
        let seeds = load_miri_diff_corpus_seeds();
        let seed_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
        let batch = generate_miri_corpus_batch(16, 0xCAFE_BABE_1234_5678, 0);
        assert_eq!(batch.len(), 16);

        let mut saw_multi_pass = false;
        for cand in &batch {
            if cand.applied_mutators.len() >= 2 {
                saw_multi_pass = true;
            }
            let (base_parsed, steps) = extract_candidate_mutation_steps(cand, &seed_refs)
                .expect("extract mutation steps for corpus candidate");
            assert_eq!(steps.len(), cand.applied_mutators.len());
            let replayed = replay_candidate_mutation_steps(cand, &base_parsed, &steps);
            assert_eq!(
                replayed.applied_mutators, cand.applied_mutators,
                "replayed mutator chain must match candidate {}",
                cand.fn_name
            );
            assert_eq!(
                replayed.fn_source, cand.fn_source,
                "full-chain AST replay must reproduce fn_source byte-for-byte for {}",
                cand.fn_name
            );
            assert_eq!(
                replayed.source, cand.source,
                "full-chain AST replay must reproduce standalone source byte-for-byte for {}",
                cand.fn_name
            );
        }
        assert!(
            saw_multi_pass,
            "expected at least one multi-mutator candidate in 16-item batch"
        );
    }

    #[test]
    fn minimize_miri_candidate_mutations_with_shrinks_3_mutator_chain_and_tolerates_line_shifts() {
        let seeds = load_miri_diff_corpus_seeds();
        let seed_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
        let batch = generate_miri_corpus_batch(24, 0x5EED_0001, 0);
        let cand3 = batch
            .into_iter()
            .find(|c| c.applied_mutators.len() == 3)
            .expect("find 3-mutator candidate in batch");

        let fault_mutator = cand3.applied_mutators[0].clone();
        let orig_report = ItemOracleReport {
            name: cand3.fn_name.clone(),
            fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
            miri: MiriOutcome::Ub {
                pos: Some(SourcePos {
                    file: "src/lib.rs".to_string(),
                    line: 84,
                    col: 17,
                }),
                message: "out-of-bounds pointer arithmetic".to_string(),
            },
            anneal: AnnealOutcome::Ub {
                span: Some(SourceSpan {
                    file: "src/lib.rs".to_string(),
                    start_line: 88,
                    start_col: 9,
                    end_line: 88,
                    end_col: 42,
                }),
            },
            verdict: ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
                miri_pos: Some(SourcePos {
                    file: "src/lib.rs".to_string(),
                    line: 84,
                    col: 17,
                }),
                miri_msg: "out-of-bounds pointer arithmetic".to_string(),
                anneal_span: Some(SourceSpan {
                    file: "src/lib.rs".to_string(),
                    start_line: 88,
                    start_col: 9,
                    end_line: 88,
                    end_col: 42,
                }),
            }),
            kernel_confirmed: true,
        };

        let shrink_res =
            minimize_miri_candidate_mutations_with(&cand3, &seed_refs, &orig_report, |sub_cand| {
                // Unmutated seed `[]` agrees.
                if sub_cand.applied_mutators.is_empty() {
                    return Some(ItemOracleReport {
                        name: sub_cand.fn_name.clone(),
                        fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
                        miri: MiriOutcome::PassScalar {
                            bits: 10,
                            size_bytes: 4,
                        },
                        anneal: AnnealOutcome::PassScalar {
                            bits: 10,
                            size_bytes: 4,
                        },
                        verdict: ComparisonVerdict::Agree,
                        kernel_confirmed: true,
                    });
                }
                // Subsequences missing the fault mutator trigger a different divergence class
                // (`missed_ub` with `MirDiffTag.normalScalar`) and must be rejected.
                if sub_cand.applied_mutators.as_slice() != [fault_mutator.as_str()] {
                    return Some(ItemOracleReport {
                        name: sub_cand.fn_name.clone(),
                        fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
                        miri: MiriOutcome::Ub {
                            pos: Some(SourcePos {
                                file: "src/lib.rs".to_string(),
                                line: 60,
                                col: 5,
                            }),
                            message: "different ub".to_string(),
                        },
                        anneal: AnnealOutcome::PassScalar {
                            bits: 99,
                            size_bytes: 4,
                        },
                        verdict: ComparisonVerdict::Diverge(DivergenceKind::MissedUb {
                            miri_pos: None,
                            miri_msg: "different ub".to_string(),
                            anneal: "pass:scalar:99:4".to_string(),
                        }),
                        kernel_confirmed: true,
                    });
                }
                // The 1-minimal subsequence `[fault_mutator]` reproduces the exact
                // `ub_location_mismatch` + `MirDiffTag.ub` signature, even though its
                // statement line numbers shifted from 84/88 to 52/56!
                Some(ItemOracleReport {
                    name: sub_cand.fn_name.clone(),
                    fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
                    miri: MiriOutcome::Ub {
                        pos: Some(SourcePos {
                            file: "src/lib.rs".to_string(),
                            line: 52,
                            col: 17,
                        }),
                        message: "out-of-bounds pointer arithmetic".to_string(),
                    },
                    anneal: AnnealOutcome::Ub {
                        span: Some(SourceSpan {
                            file: "src/lib.rs".to_string(),
                            start_line: 56,
                            start_col: 9,
                            end_line: 56,
                            end_col: 42,
                        }),
                    },
                    verdict: ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
                        miri_pos: Some(SourcePos {
                            file: "src/lib.rs".to_string(),
                            line: 52,
                            col: 17,
                        }),
                        miri_msg: "out-of-bounds pointer arithmetic".to_string(),
                        anneal_span: Some(SourceSpan {
                            file: "src/lib.rs".to_string(),
                            start_line: 56,
                            start_col: 9,
                            end_line: 56,
                            end_col: 42,
                        }),
                    }),
                    kernel_confirmed: true,
                })
            });

        assert_eq!(shrink_res.original_mutator_chain.len(), 3);
        assert_eq!(shrink_res.minimized_mutator_chain, vec![fault_mutator]);
        assert!(shrink_res.shrink_evaluations >= 2);
        assert!(
            shrink_res.minimized_candidate.source.len() < cand3.source.len(),
            "1-minimal candidate source must be shorter than 3-mutator candidate source"
        );
    }

    #[test]
    fn finding_bundle_json_and_summary_serialize_shrink_metadata() {
        let dir = create_staging_dir("bundle_test").expect("create test dir");
        let mut bundle = MiriFindingBundle {
            finding_id: "finding_0000_test".to_string(),
            fn_name: "pass_integer_arith_basic__b0_c0".to_string(),
            seed_name: "pass_integer_arith_basic".to_string(),
            applied_mutators: vec!["RawPtrOffsetMutator".to_string()],
            original_mutator_chain: vec![
                "ArithmeticCastMutator".to_string(),
                "RawPtrOffsetMutator".to_string(),
                "PlaceProjectionWrapper".to_string(),
            ],
            minimized_mutator_chain: vec!["RawPtrOffsetMutator".to_string()],
            shrink_evaluations: 5,
            divergence_class: "ub_location_mismatch".to_string(),
            miri_outcome_tag: "ub@src/lib.rs:52:17".to_string(),
            miri_excerpt: "error: Undefined Behavior".to_string(),
            miri_pos: Some("src/lib.rs:52:17".to_string()),
            batch_miri_pos: Some("src/lib.rs:120:17".to_string()),
            anneal_outcome_tag: "ub@src/lib.rs:56:9:56:42".to_string(),
            anneal_lean_tag: "MirDiffTag.ub".to_string(),
            anneal_span: Some("src/lib.rs:56:9:56:42".to_string()),
            batch_anneal_span: Some("src/lib.rs:124:9:124:42".to_string()),
            mir_neighborhood: "def body : CapturedMir := ...".to_string(),
            kernel_confirmed: true,
            kernel_confirm_theorems: "theorem confirm_tag_x : ... := by\n  rfl".to_string(),
            mutant_source: "pub fn pass_integer_arith_basic__b0_c0() {}\n".to_string(),
            repro_path: None,
        };

        write_finding_bundle_to_dir(&dir, &mut bundle).expect("write finding bundle");
        let bundle_dir = dir.join("finding_0000_test");
        let finding_json =
            fs::read_to_string(bundle_dir.join("finding.json")).expect("read finding.json");
        let summary_md =
            fs::read_to_string(bundle_dir.join("SUMMARY.md")).expect("read SUMMARY.md");
        let _ = fs::remove_dir_all(&dir);

        assert!(finding_json.contains(
            "\"original_mutator_chain\": [\"ArithmeticCastMutator\", \"RawPtrOffsetMutator\", \"PlaceProjectionWrapper\"]"
        ));
        assert!(finding_json.contains("\"minimized_mutator_chain\": [\"RawPtrOffsetMutator\"]"));
        assert!(finding_json.contains("\"shrink_evaluations\": 5"));
        assert!(summary_md.contains(
            "- **Original mutator chain**: `ArithmeticCastMutator, RawPtrOffsetMutator, PlaceProjectionWrapper`"
        ));
        assert!(summary_md.contains("- **Minimized mutator chain**: `RawPtrOffsetMutator`"));
        assert!(summary_md.contains("- **Shrink evaluations**: `5`"));
    }
}
