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
//! (`cargo_anneal::run_difftest_oracle_pipeline`), confirming divergences via
//! `by rfl` theorems in the Lean 4 kernel (`"oracle_comparison": "performed"`).
//! `itree-difftest` executes safe-Rust candidates natively with
//! `#[anneal_trace::external]` boundary interposition, deduplicates distinct
//! traces, and checks each in the Lean 4 kernel via `TraceCheck`
//! (`"oracle_comparison": "performed"`). When invoked with `--compile-only`,
//! either binary checks candidate compilation without running the oracle
//! (`"oracle_comparison": "not_performed"`).

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
    ItreeEvalOptions, ItreeFindingBundle, ItreeReproReport, compile_itree_candidates,
    compile_rust_strict_opt, evaluate_itree_batches, evaluate_itree_batches_with_options,
    render_itree_eval_report_json, render_itree_eval_report_markdown,
    render_itree_finding_bundle_json, reproduce_itree_finding, resolve_itree_lean_jobs,
};
pub use miri_eval::{
    DIVERGENCE_CLASS_NAMES, FMT_ARGUMENTS_CTOR_DEF_PATHS, FMT_ARGUMENTS_CTOR_STUB_LEAN,
    MIRI_MUTATOR_NAMES, MiriCampaignEvalReport, MiriFindingBundle, MiriReconciledPanicSite,
    NOT_COMPARED_REASON_NAMES, StagedLibSource, compare_difftest_miri_and_anneal,
    compile_candidates, compile_rust_snippet, divergence_class_slug, evaluate_miri_batches,
    json_escape, render_eval_report_json, render_eval_report_markdown, render_finding_bundle_json,
    reproduce_miri_finding, resolve_rustc_bin,
};
pub use mutators_itree::{
    BranchLoopWeaver, CallBoundaryOutliner, ExtOracleInjector, GeneratedItreeCandidate,
    ItreeAstMutator, LayoutPaddingPerturber, StagedItreeCandidate,
    annotate_itree_external_callees, contains_unsafe_token, generate_itree_batch,
    generate_itree_identity_batch, stage_itree_candidate_items,
};
pub use mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, GeneratedMiriCandidate,
    MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE, MiriAstMutator, MiriCorpusSeed,
    MutationMode, PlaceProjectionWrapper, RAW_MIRI_DIFF_CORPUS_RS, RawPtrOffsetMutator,
    TreeBorrowsRetagInterleaver, build_standalone_candidate_source, extract_closed_corpus_seeds,
    generate_miri_batch, generate_miri_corpus_batch, generate_miri_identity_batch,
    load_miri_diff_corpus_seeds,
};
pub use shrink::{ShrinkOutcome, run_arbtest_and_shrink, shrink_bytes, shrink_mutation_chain};
