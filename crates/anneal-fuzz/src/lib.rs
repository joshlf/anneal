//! Core fuzzing engine, source auto-instrumenter, and MIR-guided layout-aware
//! input generator for the Anneal dual-fuzzer infrastructure.

pub mod input_gen;
pub mod instrument;

pub use input_gen::{
    EnumVariantLayout, EnvScheduleGenerator, EnvStrategy, FieldLayout, LayoutAwareByteBuilder,
    LayoutSpec, MirInputDictionary, MirObsPathKey, MirObsPathSet, PaddingFillPattern, ScalarLayout,
};
pub use instrument::{
    EnvAction, EnvSchedule, InstrumentConfig, InstrumentationError, InstrumentationResult,
    RecordedEvent, RecordedOutcome, TraceRecorder, emit_runtime_prelude, instrument_source,
    instrument_source_with_config, value_as_raw_bytes,
};
