//! Building blocks intended for differential testing of Anneal: AST mutators
//! that generate candidate programs, a source instrumenter that records
//! external-call traces, layout-aware input builders, and a counterexample
//! shrinker.
//!
//! Nothing in this crate runs Miri, Anneal's Lean model, or the generated
//! programs, so nothing here compares Anneal with another oracle. The
//! `miri-difftest` and `itree-difftest` binaries only generate and compile
//! candidates, and report `"oracle_comparison": "not_performed"`.

pub mod input_gen;
pub mod instrument;
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
pub use mutators_itree::{
    BranchLoopWeaver, CallBoundaryOutliner, ExtOracleInjector, GeneratedItreeCandidate,
    ItreeAstMutator, LayoutPaddingPerturber, contains_unsafe_token, generate_itree_batch,
};
pub use mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, GeneratedMiriCandidate, MiriAstMutator,
    PlaceProjectionWrapper, RawPtrOffsetMutator, TreeBorrowsRetagInterleaver, generate_miri_batch,
};
pub use shrink::{ShrinkOutcome, run_arbtest_and_shrink, shrink_bytes, shrink_mutation_chain};
