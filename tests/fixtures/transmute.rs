// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: concrete_pme_transmute ===
//@ pass

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
//@ pass

pub fn inline_const_transmute(x: usize) -> usize {
    let () = const {
        assert!(core::mem::size_of::<usize>() == core::mem::size_of::<usize>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: public_generic_assoc_const_transmute ===
//@ fail(proof, transmute_checked): "unproved function body"

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
//@ fail(proof, inline_const_transmute): "unproved function body"

pub fn inline_const_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = const {
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: public_generic_unchecked_transmute ===
//@ fail(proof, transmute_unchecked): "unproved function body"

pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    unsafe { core::mem::transmute_copy(&x) }
}

// === case: concrete_transmute_with_unsupported_spec ===
//@ fail(proof, f): "unsupported specs on concrete transmute caller"

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
//@ fail(proof, inline_const_transmute): "unsupported specs on inline_const_transmute"

/// anneal:spec ensures(ret == x)
pub fn inline_const_transmute(x: usize) -> usize {
    let () = const {
        assert!(core::mem::size_of::<usize>() == core::mem::size_of::<usize>())
    };
    unsafe { core::mem::transmute_copy(&x) }
}
