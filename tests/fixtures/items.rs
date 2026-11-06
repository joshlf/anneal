// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// === case: empty_crate_no_pub_fns ===
//@ fail(capture): "the crate defines no public functions"

// === case: enum_item_rejected ===
//@ fail(capture): "unsupported item kind Enum"

pub enum E {
    A,
}

pub fn id(x: usize) -> usize {
    x
}

// === case: unsafe_trait_rejected ===
//@ fail(capture): "unsafe trait"

pub unsafe trait Bad {}

pub fn id(x: usize) -> usize {
    x
}

// === case: uncalled_private_fn_rejected ===
//@ fail(capture): "bad"

fn bad(x: usize) -> usize {
    x
}

pub fn id(x: usize) -> usize {
    x
}

// === case: include_str_external_file_rejected ===
//@ fail(capture): "Cargo.toml"

pub fn id(x: usize) -> usize {
    let _ = include_str!("../Cargo.toml");
    x
}

// === case: env_macro_rejected ===
//@ fail(capture): "PATH"

pub fn id(x: usize) -> usize {
    let _ = env!("PATH");
    x
}
