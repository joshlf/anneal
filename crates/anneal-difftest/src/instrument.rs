// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! External-call boundary trace observation and layout-driven byte capture
//! re-exports from [`cargo_anneal::trace_observer`].
//!
//! Environment-boundary functions are annotated with `#[anneal_trace::external]`
//! (and user-defined structs/enums with `#[anneal_trace::capture]`) so that
//! root functions under test execute unchanged while boundary calls record
//! layout-aware argument and return bytes via [`TraceRecorder::observe_root`].

pub use cargo_anneal::trace_observer::{
    EnvAction, EnvSchedule, FromScheduleBytes, RecordedEvent, RecordedOutcome, RecordedRawTrace,
    RecordedShadowAlloc, ScheduleError, TraceCapture, TraceRecorder, capture_value_bytes,
    observe_boundary_call, value_as_raw_bytes,
};
