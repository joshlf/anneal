// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: valid_nonzero_library ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

/// # Safety
///
/// `x` must not be zero.
///
/// anneal:requires x != 0
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: buggy_safe_constructor_returns_zero ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

/// # Safety
///
/// `x` must not be zero.
///
/// anneal:requires x != 0
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: pub_field_violates_invariant ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    pub val: usize,
}

pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

/// # Safety
///
/// `x` must not be zero.
///
/// anneal:requires x != 0
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

pub fn get_unchecked(x: NonZeroUsize) -> usize {
    if x.val == 0 {
        unsafe { core::hint::unreachable_unchecked() }
    } else {
        x.val
    }
}

// === case: buggy_unsafe_constructor ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:requires x != 0
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    let _ = x;
    NonZeroUsize { val: 0 }
}

// === case: unsupported_requires_clause ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:requires x != 1
pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}

// === case: unsupported_spec_on_nonzero_fn ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:invariant val != 0
#[repr(transparent)]
pub struct NonZeroUsize {
    val: usize,
}

/// anneal:spec ensures(ret == x)
pub fn make_nonzero(x: usize) -> NonZeroUsize {
    if x == 0 {
        NonZeroUsize { val: 1 }
    } else {
        NonZeroUsize { val: x }
    }
}

// === case: struct_without_invariant ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

#[repr(transparent)]
pub struct Wrapper {
    val: usize,
}

pub fn id(x: usize) -> usize {
    let w = Wrapper { val: x };
    w.val
}
