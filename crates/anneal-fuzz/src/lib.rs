//! Core fuzzing engine, source auto-instrumenter, MIR-guided layout-aware input
//! generator, Miri AST mutators, and deterministic counterexample shrinker for
//! the Anneal dual-fuzzer infrastructure.

pub mod input_gen;
pub mod instrument;
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
pub use mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, GeneratedMiriCandidate, MiriAstMutator,
    PlaceProjectionWrapper, RawPtrOffsetMutator, TreeBorrowsRetagInterleaver, generate_miri_batch,
};
pub use shrink::{ShrinkOutcome, run_arbtest_and_shrink, shrink_bytes, shrink_mutation_chain};
