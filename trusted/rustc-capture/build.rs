// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Select the MIR dialect of the compiler whose `rustc_private` libraries this
//! driver links, and stop the build for any compiler outside the closed table
//! in `src/compilers.rs`.
//!
//! Cargo passes build scripts `RUSTC`, "the compiler ... that Cargo has
//! resolved to use", and compiles the driver with it. That compiler's sysroot
//! supplies the `rustc_private` crates, and rustc loads crate metadata only
//! when the recorded `rustc_version(cfg_version)` equals its own. So
//! `$RUSTC --version --verbose` identifies the compiler build whose libraries
//! the driver links.
//! https://github.com/rust-lang/cargo/blob/fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef/src/doc/src/reference/environment-variables.md?plain=1#L398-L399
//! https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_metadata/src/rmeta/decoder.rs#L702-L721
//! https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/compiler/rustc_metadata/src/rmeta/decoder.rs#L707-L725
//!
//! The script does not run the compiler through `RUSTC_WRAPPER` or
//! `RUSTC_WORKSPACE_WRAPPER` (`cargo clippy` installs `clippy-driver` as the
//! latter, which reports its own version). A wrapper that substitutes another
//! compiler links that compiler's libraries instead; the driver's run-time
//! `rustc_version_str()` check then refuses to run (see `main.rs`).
//!
//! The selection reaches the crate as:
//! - `cfg(anneal_mir_dialect = "<dialect>")`, which gates code that differs
//!   between `rustc_private` revisions or Lean syntax modules; and
//! - `ANNEAL_LINKED_RUSTC_COMMIT`, `ANNEAL_LINKED_RUSTC_DATE`, and
//!   `ANNEAL_LINKED_MIR_DIALECT`, which the driver reads with `env!` for its
//!   run-time compiler checks and capture manifests.
//!
//! A build system other than Cargo must perform this same identification and
//! supply the same cfg and environment values.
//! https://github.com/rust-lang/cargo/blob/fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef/src/doc/src/reference/build-scripts.md?plain=1#L266-L344

#[path = "src/compilers.rs"]
mod compilers;

use std::env;
use std::process::{Command, ExitCode};

use compilers::{CompilerIdentity, SUPPORTED_COMPILERS, SupportedCompiler};

fn main() -> ExitCode {
    // Only these sources determine the selection. "The script will be re-run
    // after it has been recompiled", which includes a rebuild with another
    // compiler, so a toolchain change still reselects the dialect.
    // https://github.com/rust-lang/cargo/blob/fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef/src/doc/src/reference/build-scripts.md?plain=1#L404-L421
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed=src/compilers.rs");
    println!("cargo::rerun-if-env-changed=RUSTC");
    match identify() {
        Ok(compiler) => {
            emit(compiler);
            ExitCode::SUCCESS
        }
        Err(problem) => {
            // `cargo::error` "tells Cargo to display an error after the build
            // script has finished running, and then fail the build". The exit
            // status fails the build under any other runner as well.
            // https://github.com/rust-lang/cargo/blob/fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef/src/doc/src/reference/build-scripts.md?plain=1#L345-L356
            let message = format!(
                "anneal-rustc-capture cannot be built with this compiler: {problem}. \
                 Set RUSTC to the rustc of a supported toolchain (and RUSTFLAGS \
                 to its lib directory; see docs/mvp.md), or add the compiler to \
                 trusted/rustc-capture/src/compilers.rs together with its \
                 reviewed Trusted.Rustc.<Dialect>.MirAst module."
            );
            // An instruction must stay on one line.
            println!("cargo::error={}", message.replace(['\r', '\n'], " "));
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

fn identify() -> Result<&'static SupportedCompiler, String> {
    let rustc = env::var_os("RUSTC").ok_or("Cargo did not set RUSTC for the build script")?;
    // The driver honors RUSTC_OVERRIDE_VERSION_STRING when printing its first
    // line; drop it so the probe reports the compiler's own version text. The
    // parser ignores that line and refuses repeated fields in any case.
    let output = Command::new(&rustc)
        .args(["--version", "--verbose"])
        .env_remove("RUSTC_OVERRIDE_VERSION_STRING")
        .output()
        .map_err(|error| {
            format!(
                "cannot run {} --version --verbose: {error}",
                rustc.display()
            )
        })?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stderr = stderr.trim();
        let detail = if stderr.is_empty() {
            String::new()
        } else {
            format!(": {stderr}")
        };
        return Err(format!(
            "{} --version --verbose failed with {}{detail}",
            rustc.display(),
            output.status,
        ));
    }
    let text = String::from_utf8(output.stdout).map_err(|_| {
        format!(
            "{} --version --verbose printed non-UTF-8 text",
            rustc.display()
        )
    })?;
    CompilerIdentity::parse(&text)?.supported()
}

fn emit(compiler: &SupportedCompiler) {
    // Declare every dialect the table can select, so a misspelled gate is an
    // `unexpected_cfgs` diagnostic instead of code that silently never builds.
    let values = SUPPORTED_COMPILERS
        .iter()
        .map(|supported| format!("\"{}\"", supported.mir_dialect))
        .collect::<Vec<_>>()
        .join(", ");
    println!("cargo::rustc-check-cfg=cfg(anneal_mir_dialect, values({values}))");
    println!(
        "cargo::rustc-cfg=anneal_mir_dialect=\"{}\"",
        compiler.mir_dialect
    );
    println!(
        "cargo::rustc-env=ANNEAL_LINKED_RUSTC_COMMIT={}",
        compiler.commit
    );
    println!(
        "cargo::rustc-env=ANNEAL_LINKED_RUSTC_DATE={}",
        compiler.commit_date
    );
    println!(
        "cargo::rustc-env=ANNEAL_LINKED_MIR_DIALECT={}",
        compiler.mir_dialect
    );
}
