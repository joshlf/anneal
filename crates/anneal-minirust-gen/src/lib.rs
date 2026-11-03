// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Mechanical translator from pinned upstream MiniRust specification sources
//! to Lean 4.
//!
//! The pipeline is:
//!
//! 1. [`lock`] and [`pipeline::verify_vendor`]: check that `minirust/vendor/<commit>/`
//!    matches the SHA-256 digests pinned in `minirust/minirust.lock.toml`.
//! 2. [`source`] and [`markdown`]: extract every ```` ```rust ```` block of
//!    `spec/**/*.md` and parse it with `syn`.
//! 3. [`deep`]: emit every top-level item as a term of the Lean syntax schema
//!    `MiniRustSpec.Syntax` (complete, one-to-one, with opaque nodes counted).
//! 4. [`shallow`]: additionally emit MiniRust data definitions as Lean types.
//! 5. [`pipeline`]: write the Lean modules and `minirust/coverage.json`.

pub mod deep;
pub mod pipeline;
pub mod lean;
pub mod lock;
pub mod markdown;
pub mod sha256;
pub mod shallow;
pub mod source;
