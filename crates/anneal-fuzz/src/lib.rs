//! Core fuzzing engine and source auto-instrumenter for the Anneal dual-fuzzer
//! infrastructure.

pub mod instrument;

pub use instrument::{
    EnvAction, EnvSchedule, InstrumentConfig, InstrumentationError, InstrumentationResult,
    RecordedEvent, RecordedOutcome, TraceRecorder, emit_runtime_prelude, instrument_source,
    instrument_source_with_config, value_as_raw_bytes,
};
