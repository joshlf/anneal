// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for `cargo anneal setup` and installed `exocrate`
//! toolchain resolution.

use std::process::Command;

use cargo_anneal::setup::Toolchain;

#[test]
fn resolves_and_executes_installed_exocrate_toolchain() {
    let tc = Toolchain::resolve()
        .expect("Anneal toolchain must be installed before running tests");

    assert!(
        tc.lean_bin().is_file(),
        "expected bundled lean binary at {}",
        tc.lean_bin().display()
    );
    assert!(
        tc.rustc_bin().is_file(),
        "expected bundled rustc binary at {}",
        tc.rustc_bin().display()
    );
    assert!(
        tc.rustc_capture_bin().is_file(),
        "expected bundled anneal-rustc-capture binary at {}",
        tc.rustc_capture_bin().display()
    );
    assert!(
        tc.anneal_share_root()
            .join("trusted/lean/foundation-lock.json")
            .is_file(),
        "expected bundled foundation-lock.json inside share/anneal"
    );

    let lean_out = Command::new(tc.lean_bin())
        .arg("--version")
        .output()
        .expect("failed to execute bundled lean --version");
    assert!(
        lean_out.status.success(),
        "bundled lean --version failed: {:?}",
        lean_out
    );
    let lean_stdout = String::from_utf8_lossy(&lean_out.stdout);
    assert!(
        lean_stdout.contains("4.34.1"),
        "expected Lean 4.34.1, got: {lean_stdout}"
    );

    let capture_out = Command::new(tc.rustc_capture_bin())
        .arg("--version")
        .output()
        .expect("failed to execute bundled anneal-rustc-capture --version");
    assert!(
        capture_out.status.success(),
        "bundled anneal-rustc-capture --version failed: {:?}",
        capture_out
    );
}
