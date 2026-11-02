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
//! `trusted/audit/` and `trusted/audit/TrustedBoundary.lean` check that
//! `Proof.verify_crate` in the compiled `.olean` has the exact kernel type
//! `Trusted.CrateTheorem Mir.crate`, uses only constructive axioms, satisfies
//! Statement-vs.-Proof Origin Separation, and replays cleanly in
//! `base.toKernelEnv.replay`.
//!
//! This module resides in `trusted/rustc-capture` because all Rust code
//! executed during capture and orchestration runs in a trusted process; an
//! arbitrary unreviewed Rust module could otherwise perform effectful side
//! effects (such as spawning background processes or tampering with `.anneal/`
//! files).

use crate::{
    CapturedFunction, CapturedOperand, CapturedSpec, CapturedStmt,
    CapturedTerminator, CapturedTy,
};

/// Check whether `func` is a single-block `usize -> usize` identity function
/// (`_0 = copy _1; return;` or `_0 = move _1; return;`).
fn single_block_id_op(func: &CapturedFunction) -> Option<&CapturedOperand> {
    if func.arg_tys != [CapturedTy::Usize]
        || func.ret_ty != CapturedTy::Usize
        || func.local_count != 2
        || func.blocks.len() != 1
    {
        return None;
    }
    let bb0 = &func.blocks[0];
    if bb0.terminator != CapturedTerminator::Return || bb0.stmts.len() != 1 {
        return None;
    }
    match &bb0.stmts[0] {
        CapturedStmt::AssignUse { dst: 0, op } => Some(op),
        _ => None,
    }
}

/// Render a candidate `.anneal/Proof.lean` proof script for the captured
/// functions.
///
/// Soundness does not rely on this generator: the trusted boundary auditor
/// checks that `Proof.verify_crate` has the exact kernel type
/// `Trusted.CrateTheorem Mir.crate`, uses only constructive axioms, and replays
/// in Lean's kernel. If the captured MIR does not unify with the lemma's
/// expected body or specification, Lean rejects the proof and verification
/// fails closed.
pub fn render_proof_lean(functions: &[CapturedFunction]) -> String {
    let proof_term = match functions {
        [func] => match (single_block_id_op(func), func.spec) {
            (Some(CapturedOperand::Copy(1)), CapturedSpec::EnsuresEqArg(1)) => {
                Some(format!(
                    "Anneal.prove_id_copy_ensures_crate \"{}\"",
                    func.name
                ))
            }
            (Some(CapturedOperand::Copy(1)), CapturedSpec::WellFormed) => {
                Some(format!(
                    "Anneal.prove_id_copy_wf_crate \"{}\"",
                    func.name
                ))
            }
            (Some(CapturedOperand::Move(1)), CapturedSpec::EnsuresEqArg(1)) => {
                Some(format!(
                    "Anneal.prove_id_move_ensures_crate \"{}\"",
                    func.name
                ))
            }
            (Some(CapturedOperand::Move(1)), CapturedSpec::WellFormed) => {
                Some(format!(
                    "Anneal.prove_id_move_wf_crate \"{}\"",
                    func.name
                ))
            }
            _ => None,
        },
        _ => None,
    };

    match proof_term {
        Some(term) => format!(
            "prelude\n\
             import Trusted\n\
             import Anneal\n\
             import Mir\n\n\
             namespace Proof\n\n\
             theorem verify_crate : Trusted.CrateTheorem Mir.crate :=\n  \
             {term}\n\n\
             end Proof\n"
        ),
        None => String::from(
            "prelude\n\
             import Trusted\n\
             import Anneal\n\
             import Mir\n\n\
             namespace Proof\n\n\
             -- Automatic proof generation is not available for this crate shape.\n\
             -- Supply a custom `.anneal/Proof.lean` with `--keep-proof`.\n\n\
             end Proof\n",
        ),
    }
}
