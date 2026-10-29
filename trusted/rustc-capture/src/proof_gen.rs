// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![forbid(unsafe_code)]

//! Pure proof-script template generator (`render_proof_lean`) for `.anneal/Proof.lean`.
//!
//! # Purity and Trust Boundary
//!
//! `render_proof_lean` maps captured MIR function metadata (`&[CapturedFunction]`)
//! to a candidate `.anneal/Proof.lean` source string. Soundness does not rely on
//! the correctness of the generated proof script: `trusted/cargo-anneal/src/audit.rs`
//! and `trusted/audit/TrustedBoundary.lean` check that `Proof.verify_crate` in the
//! compiled `.olean` has the exact kernel type `Trusted.CrateTheorem Mir.crate`,
//! uses zero custom axioms, satisfies Statement-vs.-Proof Origin Separation, and
//! replays cleanly in `base.toKernelEnv.replay`.
//!
//! This module resides in `trusted/cargo-anneal` because all Rust code executed by
//! `cargo-anneal` shares the process address space of the trusted driver; an
//! arbitrary unreviewed Rust module could otherwise perform effectful side effects
//! (such as spawning background processes or tampering with `.anneal/` files).
//! To keep changes to proof-generation templates lightweight to review without
//! contaminating a crate's TCB audit log, `audit-repo` (`check_cargo_boundary`)
//! mechanically enforces that this file contains `#![forbid(unsafe_code)]`, zero
//! `unsafe` or `extern` blocks, and zero effectful `std` imports (`std::fs`,
//! `std::process`, `std::net`, `std::env`, `std::os`, `std::thread`, `Command`).
//!
//! Architectural note: if the proof-script generator grows unwieldy to review
//! inside `trusted/` in the future, we can investigate moving its source out of
//! `trusted/` into an untrusted crate by mechanically enforcing Rust purity on
//! that crate (for example via `#![no_std]` + `alloc`, `#![forbid(unsafe_code)]`,
//! no `build.rs`, no proc-macros, and no FFI or effectful dependencies).

use crate::{
    CapturedFunction, CapturedOperand, CapturedSpec, CapturedStmt,
};

/// Render a candidate `.anneal/Proof.lean` proof script for the captured
/// functions.
///
/// Soundness does not rely on this generator: the trusted boundary auditor
/// checks that `Proof.verify_crate` has the exact kernel type
/// `Trusted.CrateTheorem Mir.crate`, uses zero custom axioms, and replays in
/// Lean's kernel. If the captured MIR does not unify with the lemma's expected
/// body or specification, Lean rejects `rfl` and verification fails closed.
pub fn render_proof_lean(functions: &[CapturedFunction]) -> String {
    let proof_term = match functions {
        [func] => {
            let uses_move = func.blocks.first().is_some_and(|b| {
                b.stmts.iter().any(|s| {
                    matches!(
                        s,
                        CapturedStmt::AssignUse {
                            dst: 0,
                            op: CapturedOperand::Move(1),
                        }
                    )
                })
            });
            match (uses_move, func.spec) {
                (false, CapturedSpec::EnsuresEqArg(1)) => {
                    format!(
                        "Anneal.prove_id_copy_ensures_crate \"{}\"",
                        func.name
                    )
                }
                (false, CapturedSpec::WellFormed) => {
                    format!(
                        "Anneal.prove_id_copy_wf_crate \"{}\"",
                        func.name
                    )
                }
                (true, CapturedSpec::EnsuresEqArg(1)) => {
                    format!(
                        "Anneal.prove_id_move_ensures_crate \"{}\"",
                        func.name
                    )
                }
                (true, CapturedSpec::WellFormed) => {
                    format!(
                        "Anneal.prove_id_move_wf_crate \"{}\"",
                        func.name
                    )
                }
                _ => format!(
                    "Anneal.prove_id_copy_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        _ => "Anneal.prove_id_copy_ensures_crate \"id\"".to_string(),
    };

    format!(
        "prelude\n\
         import Trusted\n\
         import Anneal\n\
         import Mir\n\n\
         namespace Proof\n\n\
         theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n  \
         {proof_term}\n\n\
         end Proof\n"
    )
}
