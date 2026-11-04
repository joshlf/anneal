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
//! When invoked with `--compile-only`, it checks candidate compilation without
//! running the oracle (`"oracle_comparison": "not_performed"`).
//! `itree-difftest` currently compiles candidates only and reports
//! `"oracle_comparison": "not_performed"`.

pub mod input_gen;
pub mod instrument;
pub mod miri_eval;
pub mod mutators_itree;
pub mod mutators_miri;
pub mod shrink;

pub use input_gen::{
    EnumVariantLayout, EnvScheduleGenerator, EnvStrategy, FieldLayout, LayoutAwareByteBuilder,
    LayoutSpec, MirInputDictionary, MirObsPathKey, MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
pub use instrument::{
    EnvAction, EnvSchedule, InstrumentConfig, InstrumentationError, InstrumentationResult,
    RecordedEvent, RecordedOutcome, TraceRecorder, emit_runtime_prelude, instrument_source,
    instrument_source_with_config, value_as_raw_bytes,
};
pub use miri_eval::{
    DIVERGENCE_CLASS_NAMES, MIRI_MUTATOR_NAMES, MiriCampaignEvalReport, MiriFindingBundle,
    NOT_COMPARED_REASON_NAMES, compile_candidates, compile_rust_snippet, divergence_class_slug,
    evaluate_miri_batches, json_escape, render_eval_report_json, render_eval_report_markdown,
    render_finding_bundle_json, reproduce_miri_finding, resolve_rustc_bin,
};
pub use mutators_itree::{
    BranchLoopWeaver, CallBoundaryOutliner, ExtOracleInjector, GeneratedItreeCandidate,
    ItreeAstMutator, LayoutPaddingPerturber, contains_unsafe_token, generate_itree_batch,
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
