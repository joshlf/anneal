// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![forbid(unsafe_code)]

//! Pure proof-script template generator (`render_proof_lean`) for
//! `.anneal/Proof.lean`.
//!
//! # Purity and Trust Boundary
//!
//! `render_proof_lean` maps captured MIR function metadata
//! (`&[CapturedFunction]`) to a candidate `.anneal/Proof.lean` source string.
//! Soundness does not rely on the correctness of the generated proof script:
//! `trusted/cargo-anneal/src/audit.rs` and `trusted/audit/TrustedBoundary.lean`
//! check that `Proof.verify_crate` in the compiled `.olean` has the exact
//! kernel type `Trusted.CrateTheorem Mir.crate`, uses zero custom axioms,
//! satisfies Statement-vs.-Proof Origin Separation, and replays cleanly in
//! `base.toKernelEnv.replay`.
//!
//! This module resides in `trusted/rustc-capture` because all Rust code
//! executed during capture and orchestration runs in a trusted process; an
//! arbitrary unreviewed Rust module could otherwise perform effectful side
//! effects (such as spawning background processes or tampering with `.anneal/`
//! files).
//!
//! Architectural note: if the proof-script generator grows unwieldy to review
//! inside `trusted/` in the future, we can investigate moving its source out of
//! `trusted/` into an untrusted crate by mechanically enforcing Rust purity on
//! that crate (for example via `#![no_std]` + `alloc`,
//! `#![forbid(unsafe_code)]`, no `build.rs`, no proc-macros, and no FFI or
//! effectful dependencies).


/// Stub proof generator before `verify` subcommand is introduced.
pub fn proof_gen_ready() -> bool {
    true
}
