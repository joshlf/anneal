// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: annotated_id ===
//@ pass
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.int Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.isize false"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    x
}

// === case: unannotated_id ===
//@ pass

pub fn id(x: usize) -> usize {
    x
}

// === case: id_move_via_local ===
//@ pass
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.StatementKind.storageLive 2"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let y = x;
    y
}

// === case: wrong_id_returns_zero ===
//@ fail(proof, id): "mismatch"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: u32_wrapping_add_expr ===
//@ pass
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.MirTy.int Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.IntWidth.i32 false"
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.BinOp.add"

pub fn add(x: u32, y: u32) -> u32 {
    x + y
}

// === case: safe_fn_with_requires ===
//@ pass
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.switchInt"

/// anneal:requires x != 0
/// anneal:spec ensures(ret == x)
pub fn clamp_nonzero(x: usize) -> usize {
    if x == 0 {
        1
    } else {
        x
    }
}

// === case: unsafe_fn_with_requires ===
//@ pass
//@ mir-contains: "isUnsafe := true"
//@ mir-contains: "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst.TerminatorKind.unreachable"

#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

/// # Safety
///
/// `x` must not be zero.
///
/// anneal:requires x != 0
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub unsafe fn nonzero_only(x: usize) -> usize {
    mir! {
        {
            match x {
                0 => bad,
                _ => ok,
            }
        }
        bad = {
            Unreachable()
        }
        ok = {
            RET = x;
            Return()
        }
    }
}

// === case: safe_fn_requires_cannot_guard_ub ===
//@ fail(proof, bad_ub): "mismatch"
//@ mir-contains: "isUnsafe := false"

#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

/// anneal:requires x != 0
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn bad_ub(x: usize) -> usize {
    mir! {
        {
            match x {
                0 => bad,
                _ => ok,
            }
        }
        bad = {
            Unreachable()
        }
        ok = {
            RET = x;
            Return()
        }
    }
}

// === case: unknown_spec_ident_rejected ===
//@ fail(capture): "unknown identifier `y`"

/// anneal:spec ensures(ret == y)
pub fn id(x: usize) -> usize {
    x
}

// === case: known_bug_wrapping_add_one ===
//@ known_bug(#87, capture): "unsupported terminator"

pub fn add_one(x: usize) -> usize {
    x.wrapping_add(1)
}
