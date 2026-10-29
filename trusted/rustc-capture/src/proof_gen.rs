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
//! This module resides in `trusted/rustc-capture` because all Rust code
//! executed during capture and orchestration runs in a trusted process; an
//! arbitrary unreviewed Rust module could otherwise perform effectful side
//! effects (such as spawning background processes or tampering with `.anneal/`
//! files).
//!
//! Architectural note: if the proof-script generator grows unwieldy to review
//! inside `trusted/` in the future, we can investigate moving its source out of
//! `trusted/` into an untrusted crate by mechanically enforcing Rust purity on
//! that crate (for example via `#![no_std]` + `alloc`, `#![forbid(unsafe_code)]`,
//! no `build.rs`, no proc-macros, and no FFI or effectful dependencies).

use crate::{
    CapturedFunction, CapturedOperand, CapturedSpec, CapturedStmt, CapturedTy,
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
        [func] if func.arg_tys == [CapturedTy::RefAtomicUsize] => {
            match func.spec {
                CapturedSpec::EnsuresAtomicLoad(1) => format!(
                    "Anneal.prove_load_relaxed_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_load_relaxed_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_load_relaxed_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [CapturedTy::RefMutUsize, CapturedTy::Usize] =>
        {
            match func.spec {
                CapturedSpec::EnsuresMaxAssign => format!(
                    "Anneal.prove_max_assign_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_max_assign_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_max_assign_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [
                    CapturedTy::RefMutUsize,
                    CapturedTy::RefMutUsize,
                    CapturedTy::Usize,
                ] =>
        {
            match func.spec {
                CapturedSpec::EnsuresUpdateMin => format!(
                    "Anneal.prove_update_min_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_update_min_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_update_min_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [
                    CapturedTy::RefMutUsize,
                    CapturedTy::Usize,
                    CapturedTy::Usize,
                ] =>
        {
            match func.spec {
                CapturedSpec::EnsuresClampAssign => format!(
                    "Anneal.prove_clamp_assign_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_clamp_assign_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_clamp_assign_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys == [CapturedTy::Usize, CapturedTy::Usize]
                && func.ret_ty == CapturedTy::Bool =>
        {
            match func.spec {
                CapturedSpec::EnsuresIsAlignedMask => format!(
                    "Anneal.prove_is_aligned_mask_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_is_aligned_mask_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_is_aligned_mask_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys == [CapturedTy::Usize, CapturedTy::Usize]
                && func.ret_ty == CapturedTy::Usize =>
        {
            match func.spec {
                CapturedSpec::EnsuresAddBounded => format!(
                    "Anneal.prove_add_bounded_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::EnsuresAbsDiff => format!(
                    "Anneal.prove_abs_diff_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed if func.name == "abs_diff" => format!(
                    "Anneal.prove_abs_diff_wf_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_add_bounded_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_add_bounded_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [CapturedTy::RefSharedUsize, CapturedTy::RefSharedUsize] =>
        {
            match func.spec {
                CapturedSpec::EnsuresSharedMax => format!(
                    "Anneal.prove_shared_max_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_shared_max_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_shared_max_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [CapturedTy::RefMutUsize, CapturedTy::RefSharedUsize] =>
        {
            match func.spec {
                CapturedSpec::EnsuresMaxAssignShared => format!(
                    "Anneal.prove_max_assign_shared_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_max_assign_shared_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_max_assign_shared_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [CapturedTy::RefMutUsize, CapturedTy::RefMutUsize] =>
        {
            match func.spec {
                CapturedSpec::EnsuresSortPair => format!(
                    "Anneal.prove_sort_pair_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_sort_pair_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_sort_pair_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [
                    CapturedTy::RefMutUsize,
                    CapturedTy::RefMutUsize,
                    CapturedTy::Usize,
                    CapturedTy::Usize,
                ] =>
        {
            match func.spec {
                CapturedSpec::EnsuresTwoPhaseReborrow => format!(
                    "Anneal.prove_two_phase_reborrow_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_two_phase_reborrow_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_two_phase_reborrow_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys
                == [
                    CapturedTy::Bool,
                    CapturedTy::RefMutUsize,
                    CapturedTy::RefMutUsize,
                ]
                && func.ret_ty == CapturedTy::RefMutUsize =>
        {
            match func.spec {
                CapturedSpec::EnsuresChooseMut => format!(
                    "Anneal.prove_choose_mut_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_choose_mut_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_choose_mut_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
        [func]
            if func.arg_tys == [CapturedTy::Usize]
                && func.ret_ty == CapturedTy::Usize
                && (func.spec == CapturedSpec::EnsuresCountUp
                    || func.name == "count_up") =>
        {
            match func.spec {
                CapturedSpec::EnsuresCountUp => format!(
                    "Anneal.prove_count_up_ensures_crate \"{}\"",
                    func.name
                ),
                CapturedSpec::WellFormed => format!(
                    "Anneal.prove_count_up_wf_crate \"{}\"",
                    func.name
                ),
                _ => format!(
                    "Anneal.prove_count_up_ensures_crate \"{}\"",
                    func.name
                ),
            }
        }
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
