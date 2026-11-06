// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: concrete_pme_transmute ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

trait SizeEq<Src, Dst> {
    const ASSERT: ();
}

impl<Src, Dst> SizeEq<Src, Dst> for () {
    const ASSERT: () =
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());
}

fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = <() as SizeEq<Src, Dst>>::ASSERT;
    unsafe { core::mem::transmute_copy(&x) }
}

pub fn f(x: usize) -> usize {
    transmute_checked::<usize, usize>(x)
}

// === case: inline_const_pme_transmute ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

pub fn inline_const_transmute(x: usize) -> usize {
    let () = const {
        assert!(core::mem::size_of::<usize>() == core::mem::size_of::<usize>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: public_generic_assoc_const_transmute ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

pub trait SizeEq<Src, Dst> {
    const ASSERT: ();
}

impl<Src, Dst> SizeEq<Src, Dst> for () {
    const ASSERT: () =
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());
}

pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = <() as SizeEq<Src, Dst>>::ASSERT;
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: public_generic_inline_const_transmute ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

pub fn inline_const_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = const {
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: public_generic_unchecked_transmute ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: concrete_transmute_with_unsupported_spec ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

trait SizeEq<Src, Dst> {
    const ASSERT: ();
}

impl<Src, Dst> SizeEq<Src, Dst> for () {
    const ASSERT: () =
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());
}

fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = <() as SizeEq<Src, Dst>>::ASSERT;
    unsafe { core::mem::transmute_copy(&x) }
}

/// anneal:spec ensures(ret == x)
pub fn f(x: usize) -> usize {
    transmute_checked::<usize, usize>(x)
}

// === case: inline_const_transmute_with_unsupported_spec ===
//@ known_bug(#87, capture): "MIR capture not yet implemented"

/// anneal:spec ensures(ret == x)
pub fn inline_const_transmute(x: usize) -> usize {
    let () = const {
        assert!(core::mem::size_of::<usize>() == core::mem::size_of::<usize>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}
