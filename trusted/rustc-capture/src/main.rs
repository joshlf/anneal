// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone CLI entry point for `anneal-rustc-capture`.
//!
//! Invoked as a subprocess by `cargo-anneal` to compile a target crate, extract
//! its lowered MIR into `.anneal/Mir.lean` and `.anneal/CaptureManifest.json`,
//! and optionally emit a candidate `.anneal/Proof.lean`.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use anneal_rustc_capture::{CaptureError, capture_crate_with_options};

fn main() -> ExitCode {
    let mut emit_proof = false;
    let mut crate_dir: Option<PathBuf> = None;

    for arg in env::args().skip(1) {
        match arg.as_str() {
            "--emit-proof" => emit_proof = true,
            "--help" | "-h" => {
                println!(
                    "usage: anneal-rustc-capture [--version] [--emit-proof] <crate-dir>"
                );
                return ExitCode::SUCCESS;
            }
            "--version" | "-V" => {
                println!("anneal-rustc-capture {}", env!("CARGO_PKG_VERSION"));
                return ExitCode::SUCCESS;
            }
            flag if flag.starts_with('-') => {
                eprintln!(
                    "IO_ERROR: unrecognized flag `{flag}` (usage: anneal-rustc-capture [--emit-proof] <crate-dir>)"
                );
                return ExitCode::from(2);
            }
            pos => {
                if crate_dir.is_some() {
                    eprintln!(
                        "IO_ERROR: unexpected positional argument `{pos}`"
                    );
                    return ExitCode::from(2);
                }
                crate_dir = Some(PathBuf::from(pos));
            }
        }
    }

    let Some(target_dir) = crate_dir else {
        eprintln!(
            "IO_ERROR: missing <crate-dir> argument (usage: anneal-rustc-capture [--emit-proof] <crate-dir>)"
        );
        return ExitCode::from(2);
    };

    match capture_crate_with_options(&target_dir, emit_proof) {
        Ok(_) => ExitCode::SUCCESS,
        Err(CaptureError::Io(msg)) => {
            eprintln!("IO_ERROR: {msg}");
            ExitCode::from(1)
        }
        Err(CaptureError::CompilationFailed(msg)) => {
            eprintln!("COMPILATION_FAILED: {msg}");
            ExitCode::from(1)
        }
        Err(CaptureError::UnsupportedMir(msg)) => {
            eprintln!("UNSUPPORTED_MIR: {msg}");
            ExitCode::from(1)
        }
    }
}
