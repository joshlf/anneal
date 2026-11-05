// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Embeds the active `rustc` sysroot library directory into the binary's
//! `DT_RUNPATH`/`DT_RPATH` so `anneal-mir-instrument` can load
//! `librustc_driver` when invoked directly outside a `cargo`/`rustup` wrapper.

use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    let rustc = env::var_os("RUSTC").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("rustc"));
    if let Ok(out) = Command::new(&rustc).arg("--print").arg("sysroot").output()
        && out.status.success()
    {
        let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_owned();
        if !sysroot.is_empty() {
            let lib_dir = PathBuf::from(&sysroot).join("lib");
            println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir.display());
        }
    }
}
