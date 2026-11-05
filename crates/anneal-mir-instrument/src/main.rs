// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Binary entry point for the `anneal-mir-instrument` `rustc` driver.

#![feature(rustc_private)]

use std::env;
use std::process::ExitCode;

fn main() -> ExitCode {
    let raw_args: Vec<String> = env::args().collect();
    anneal_mir_instrument::run_instrument_driver(raw_args)
}
