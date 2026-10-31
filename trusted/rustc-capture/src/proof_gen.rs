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
//! `trusted/audit/` (`TrustedBoundary.lean`) checks that `Proof.verify_crate`
//! in the compiled `.olean` has the exact kernel type
//! `Trusted.CrateTheorem Mir.crate`, uses only constructive axioms (`propext`,
//! `Quot.sound`), satisfies Statement-vs.-Proof Origin Separation, and replays
//! cleanly in `base.toKernelEnv.replay`.
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

use crate::{
    CapturedFnKind, CapturedFunction, CapturedOperand, CapturedSpec,
    CapturedStmt, CapturedTerminator, CapturedTy,
};

/// Render a candidate `.anneal/Proof.lean` proof script for the captured
/// functions.
///
/// Soundness does not rely on this generator: the trusted boundary auditor
/// checks that `Proof.verify_crate` has the exact kernel type
/// `Trusted.CrateTheorem Mir.crate`, uses only constructive axioms (`propext`,
/// `Quot.sound`), and replays in Lean's kernel. If the captured MIR does not
/// unify with the lemma's expected body or specification, Lean rejects the
/// proof term and verification fails closed.
pub fn render_proof_lean(functions: &[CapturedFunction]) -> String {
    let runtime_fns: Vec<&CapturedFunction> =
        functions.iter().filter(|f| !f.is_const).collect();
    let proof_term = match runtime_fns.as_slice() {
        [f1, f2] => Some(format!(
            "Anneal.prove_pme_transmute_crate \"{}\" \"{}\"",
            f1.name, f2.name
        )),
        [f1, f2, f3] => Some(format!(
            "Anneal.prove_nonzero_library_crate \"{}\" \"{}\" \"{}\"",
            f1.name, f2.name, f3.name
        )),
        [func] => {
            if !func.required_consts.is_empty()
                || (func.arg_tys == vec![CapturedTy::Param(0)]
                    && func.ret_ty == CapturedTy::Param(1))
            {
                Some(format!(
                    "Anneal.prove_pme_transmute_single_crate \"{}\"",
                    func.name
                ))
            } else {
                let is_id_shape = check_single_fn_body_shape(func);
                match (is_id_shape, func.spec) {
                    (Some(false), CapturedSpec::EnsuresEqArg(1)) => {
                        Some(format!(
                            "Anneal.prove_id_copy_ensures_crate \"{}\"",
                            func.name
                        ))
                    }
                    (Some(false), CapturedSpec::WellFormed) => Some(format!(
                        "Anneal.prove_id_copy_wf_crate \"{}\"",
                        func.name
                    )),
                    (Some(true), CapturedSpec::EnsuresEqArg(1)) => {
                        Some(format!(
                            "Anneal.prove_id_move_ensures_crate \"{}\"",
                            func.name
                        ))
                    }
                    (Some(true), CapturedSpec::WellFormed) => Some(format!(
                        "Anneal.prove_id_move_wf_crate \"{}\"",
                        func.name
                    )),
                    (None, _) | (Some(_), _) => None,
                }
            }
        }
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
        None => "prelude\n\
                 import Trusted\n\
                 import Anneal\n\
                 import Mir\n\n\
                 namespace Proof\n\n\
                 -- Automatic proof generation is not available for this crate shape.\n\n\
                 end Proof\n"
            .to_string(),
    }
}

/// Check whether `func` matches the canonical single-block `idCopyBody`
/// (`Some(false)`) or `idMoveBody` (`Some(true)`). Returns `None` if the body
/// has any other shape.
fn check_single_fn_body_shape(func: &CapturedFunction) -> Option<bool> {
    if func.kind != CapturedFnKind::PubSafe
        || func.arg_tys != vec![CapturedTy::Usize]
        || func.ret_ty != CapturedTy::Usize
        || func.local_count != 2
        || func.blocks.len() != 1
    {
        return None;
    }
    let block = &func.blocks[0];
    if block.terminator != CapturedTerminator::Return || block.stmts.len() != 1
    {
        return None;
    }
    match &block.stmts[0] {
        CapturedStmt::AssignUse {
            dst: 0,
            op: CapturedOperand::Copy(1),
        } => Some(false),
        CapturedStmt::AssignUse {
            dst: 0,
            op: CapturedOperand::Move(1),
        } => Some(true),
        _ => None,
    }
}
