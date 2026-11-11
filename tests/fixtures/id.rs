// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: annotated_id ===
//@ pass
//@ mir-contains: "Trusted.PostSpec.ensuresEqArg 1"

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
//@ known_bug(#87, proof, id): "unproved function body"
//@ mir-contains: "Trusted.PostSpec.ensuresEqArg 1"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let y = x;
    y
}

// === case: wrong_id_returns_zero ===
//@ fail(proof, id): "unproved function body"

/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: unsupported_u32_signature ===
//@ fail(proof, add): "unproved function body"
//@ mir-contains: "Trusted.MirTy.uint 32"

pub fn add(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

// === case: safe_fn_with_requires ===
//@ pass
//@ mir-contains: "requires := _root_.Option.some { argLocal := 1, ne := 0 }"

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

/// anneal:requires x != 0
pub unsafe fn id(x: usize) -> usize {
    x
}

// === case: safe_fn_requires_cannot_guard_ub ===
//@ fail(proof, bad_ub): "unexpected requires clause"

/// anneal:requires x != 0
pub fn bad_ub(x: usize) -> usize {
    if x == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x
    }
}

// === case: unknown_spec_ident_rejected ===
//@ fail(capture): "ensures"

/// anneal:spec ensures(ret == y)
pub fn id(x: usize) -> usize {
    x
}

// === case: known_bug_wrapping_add_one ===
//@ known_bug(#87, proof, add_one): "unproved function body"

pub fn add_one(x: usize) -> usize {
    x.wrapping_add(1)
}
