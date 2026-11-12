// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Building blocks for differential testing of Anneal: closed Miri candidate
//! generation and live Miri + Anneal oracle evaluation (`mutators_miri`,
//! `miri_eval`), source instrumentation for external-call traces (`instrument`),
//! layout-aware input builders (`input_gen`), and counterexample shrinking
//! (`shrink`).
//!
//! `miri-difftest` evaluates closed zero-argument candidates against both live
//! Miri (`-Zmiri-tree-borrows`) and Anneal's MIR-in-Lean operational semantics
//! (a helper-linked oracle pipeline over `cargo_anneal`'s Miri and capture
//! stages), confirming divergences via `by rfl` theorems in the Lean 4 kernel
//! (`"oracle_comparison": "performed"`). `itree-difftest` executes safe-Rust
//! candidates natively with `#[anneal_trace::external]` boundary interposition,
//! deduplicates distinct traces, and checks each in the Lean 4 kernel via
//! `TraceCheck` (`"oracle_comparison": "performed"`). When invoked with
//! `--compile-only`, either binary checks candidate compilation without running
//! the oracle (`"oracle_comparison": "not_performed"`).
//!
//! Both harnesses shrink every finding's mutator chain to a 1-minimal chain that
//! reproduces the finding's discrepancy signature
//! ([`shrink::shrink_mutation_chain_detailed`], whose control flow
//! `theory/Anneal/DiffTestShrinker.lean` models and proves 1-minimal), replaying
//! each candidate's recorded mutation passes and re-running the live oracle on
//! every reduction through a [`shrink::MemoizedOracle`].

pub mod input_gen;
pub mod instrument;
pub mod itree_eval;
pub mod miri_eval;
pub mod mutators_itree;
pub mod mutators_miri;
pub mod shrink;

pub use input_gen::{
    EnumVariantLayout, EnvScheduleGenerator, EnvStrategy, FieldLayout, LayoutAwareByteBuilder,
    LayoutSpec, MirInputDictionary, MirObsPathKey, MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
pub use instrument::{
    EnvAction, EnvSchedule, FromScheduleBytes, RecordedEvent, RecordedOutcome, RecordedRawTrace,
    RecordedShadowAlloc, ScheduleError, TraceCapture, TraceRecorder, capture_value_bytes,
    observe_boundary_call, value_as_raw_bytes,
};
pub use itree_eval::{
    CandidateCompile, DEFAULT_ITREE_TRIALS_PER_CANDIDATE, ITREE_CONFIRM_CHUNK_SIZE,
    ITREE_DIAG_TAG_NAMES, ITREE_MUTATOR_NAMES, ITREE_NOT_COMPARED_REASON_NAMES,
    ITREE_PROBE_CHUNK_SIZE, ITREE_SAFE_SEEDS, ITREE_TRACE_CHECK_FUEL, ItreeCampaignEvalReport,
    ItreeCandidateEvaluation, ItreeCandidateShrinkResult, ItreeDiscrepancySignature,
    ItreeEvalOptions, ItreeFindingBundle, ItreeReproReport, ItreeShrinkContext, ItreeShrinkStatus,
    ItreeTraceVerdict, compile_itree_candidates, compile_rust_strict_opt, evaluate_itree_batches,
    evaluate_itree_batches_with_options, evaluate_itree_candidate_live,
    itree_candidate_passes_strict_compile, minimize_itree_candidate_mutations,
    minimize_itree_candidate_mutations_with, minimize_itree_candidate_mutations_with_compile_check,
    minimize_itree_recorded_mutations_with_compile_check, render_itree_eval_report_json,
    render_itree_eval_report_markdown, render_itree_finding_bundle_json, reproduce_itree_finding,
    resolve_itree_lean_jobs,
};
pub use miri_eval::{
    DIVERGENCE_CLASS_NAMES, FMT_ARGUMENTS_CTOR_DEF_PATHS, FMT_ARGUMENTS_CTOR_STUB_LEAN,
    LiveCandidateEvaluation, MIRI_MUTATOR_NAMES, MiriCampaignEvalReport, MiriCandidateShrinkResult,
    MiriEvalOptions, MiriFindingBundle, MiriReconciledPanicSite, MiriShrinkStatus,
    NOT_COMPARED_REASON_NAMES, StagedLibSource, compare_difftest_miri_and_anneal,
    compile_candidates, compile_rust_snippet, discrepancy_signatures_match, divergence_class_slug,
    evaluate_candidate_live, evaluate_miri_batches, evaluate_miri_batches_with_options,
    json_escape, minimize_miri_candidate_mutations, minimize_miri_candidate_mutations_with,
    minimize_miri_candidate_mutations_with_compile_check, miri_report_is_oracle_failure,
    normalize_anneal_outcome_tag, normalize_diagnostic_message, normalize_miri_outcome_family,
    render_eval_report_json, render_eval_report_markdown, render_finding_bundle_json,
    reproduce_miri_finding, resolve_rustc_bin,
};
pub use mutators_itree::{
    BranchLoopWeaver, CallBoundaryOutliner, ExtOracleInjector, GeneratedItreeCandidate,
    ITREE_AST_MUTATORS, ItreeAstMutator, ItreeMutationStep, LayoutPaddingPerturber,
    StagedItreeCandidate, annotate_itree_external_callees, contains_unsafe_token,
    generate_itree_batch, generate_itree_identity_batch, itree_candidate_replay_is_faithful,
    reconstruct_itree_mutation_steps, replay_itree_mutation_steps, stage_itree_candidate_items,
};
pub use mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, GeneratedMiriCandidate, MIRI_AST_MUTATORS,
    MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE, MiriAstMutator, MiriCorpusSeed,
    MutationMode, PlaceProjectionWrapper, RAW_MIRI_DIFF_CORPUS_RS, RawPtrOffsetMutator,
    RecordedMutationStep, TreeBorrowsRetagInterleaver, build_standalone_candidate_source,
    extract_closed_corpus_seeds, generate_miri_batch, generate_miri_corpus_batch,
    generate_miri_identity_batch, load_miri_diff_corpus_seeds, miri_candidate_replay_is_faithful,
    reconstruct_miri_mutation_steps, replay_miri_mutation_steps,
};
pub use shrink::{
    MemoizedOracle, MutationChainShrinkOutcome, MutatorChainShrinkStatus, ShrinkOutcome,
    run_arbtest_and_shrink, shrink_bytes, shrink_mutation_chain, shrink_mutation_chain_detailed,
};
