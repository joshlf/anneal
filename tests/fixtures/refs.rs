// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: alloc_passthrough_with_spec ===
//@ pass
//@ mir-contains: "Trusted.PostSpec.ensuresEqArg 1"

/// anneal:spec ensures(ret == x)
pub fn alloc_passthrough(x: usize) -> usize {
    let r = &x;
    *r
}

// === case: alloc_passthrough_unannotated ===
//@ pass

pub fn alloc_passthrough(x: usize) -> usize {
    let r = &x;
    *r
}

// === case: wrong_alloc_passthrough ===
//@ fail(proof, alloc_passthrough): "unproved function body"

/// anneal:spec ensures(ret == x)
pub fn alloc_passthrough(x: usize) -> usize {
    let zero = 0usize;
    let r = &zero;
    let _ = x;
    *r
}
