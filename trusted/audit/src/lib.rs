// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Compatibility API for the repository auditor command and its tests.
//!
//! The publishable CLI package owns the shared auditor implementation so its
//! installed verifier does not depend on an unpublished registry crate.

pub use cargo_anneal::*;
