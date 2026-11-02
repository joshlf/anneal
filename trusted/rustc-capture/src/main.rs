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
//! its lowered MIR into `.anneal/Mir.lean`, print captured function names to
//! stdout, and optionally emit a candidate `.anneal/Proof.lean`.

use std::path::PathBuf;
use std::process::ExitCode;

use anneal_rustc_capture::{
    CaptureError, CaptureOptions, capture_crate_with_config,
};
use clap::Parser;

#[derive(Debug, Parser)]
#[command(name = "anneal-rustc-capture", version, about)]
struct Cli {
    /// Also synthesize a candidate `.anneal/Proof.lean` script.
    #[arg(long)]
    emit_proof: bool,

    /// Optional explicit path to the pinned `rustc` compiler binary.
    #[arg(long)]
    rustc: Option<PathBuf>,

    /// Path to the target Rust crate directory.
    crate_dir: PathBuf,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let options = CaptureOptions {
        emit_proof: cli.emit_proof,
        rustc_bin: cli.rustc,
    };

    match capture_crate_with_config(&cli.crate_dir, &options) {
        Ok(output) => {
            for func in &output.functions {
                println!("{}", func.name);
            }
            ExitCode::SUCCESS
        }
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
