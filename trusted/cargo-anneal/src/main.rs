// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI entry point (`cargo-anneal`).
//!
//! Supports both direct invocation (`cargo-anneal <subcommand>`) and Cargo
//! subcommand invocation (`cargo anneal <subcommand>`).

use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::error::ErrorKind;
use clap::{Parser, Subcommand};

use cargo_anneal::setup;
use cargo_anneal::{ReleaseChannel, VerifyConfig, verify_crate_with_report};

#[derive(Parser)]
#[command(
    name = "cargo-anneal",
    version,
    about = "Deductive verification CLI for Anneal"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Install the pinned Anneal Rust and Lean 4 toolchain bundle.
    Setup {
        /// Optional path to a local toolchain archive.
        #[arg(long)]
        local_archive: Option<PathBuf>,
    },
    /// Capture MIR and verify a Rust crate in the Lean 4 kernel.
    Verify {
        /// Target crate directory (defaults to the current working directory).
        crate_dir: Option<PathBuf>,
        /// Comma-separated candidate-trusted features to allow (or `*`).
        #[arg(long, value_delimiter = ',')]
        allow_candidate_features: Option<Vec<String>>,
        /// Release channel override (`alpha` or `stable`).
        #[arg(long)]
        release_channel: Option<String>,
        /// Anneal toolchain directory (defaults to the installed toolchain).
        #[arg(long)]
        toolchain: Option<PathBuf>,
        /// Path to the Anneal root containing `trusted/lean` and `theory`.
        #[arg(long)]
        anneal_root: Option<PathBuf>,
    },
}

fn default_release_channel() -> ReleaseChannel {
    if env!("CARGO_PKG_VERSION").contains('-') {
        ReleaseChannel::Alpha
    } else {
        ReleaseChannel::Stable
    }
}

fn resolve_default_anneal_root(toolchain_dir: &Path) -> PathBuf {
    let manifest_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    if manifest_root.join("trusted/lean/Trusted.lean").is_file()
        && manifest_root.join("theory/Anneal.lean").is_file()
    {
        if let Ok(canon) = std::fs::canonicalize(&manifest_root) {
            return canon;
        }
        return manifest_root;
    }
    toolchain_dir.join("share/anneal")
}

fn main() -> ExitCode {
    match run(env::args().collect()) {
        Ok(code) => ExitCode::from(code),
        Err((code, msg)) => {
            eprintln!("{msg}");
            ExitCode::from(code)
        }
    }
}

fn run(mut raw_args: Vec<String>) -> Result<u8, (u8, String)> {
    if raw_args.get(1).map(String::as_str) == Some("anneal") {
        raw_args.remove(1);
    }

    let cli = match Cli::try_parse_from(raw_args) {
        Ok(c) => c,
        Err(e) => {
            if matches!(
                e.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) {
                print!("{e}");
                return Ok(0);
            }
            return Err((2, e.to_string().trim_end().to_string()));
        }
    };

    match cli.command {
        Commands::Setup { local_archive } => match setup::install(local_archive)
        {
            Ok(root) => {
                println!("Installed Anneal toolchain at {}", root.display());
                Ok(0)
            }
            Err(err) => Err((1, format!("error: {err}"))),
        },
        Commands::Verify {
            crate_dir,
            allow_candidate_features,
            release_channel,
            toolchain,
            anneal_root,
        } => {
            let release_channel = match release_channel {
                Some(raw) => ReleaseChannel::parse(&raw)
                    .map_err(|e| (2, format!("error: {e}")))?,
                None => default_release_channel(),
            };
            let allow_candidate_features = allow_candidate_features
                .unwrap_or_default()
                .into_iter()
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let toolchain_dir = match toolchain {
                Some(tc) => tc,
                None => setup::resolve_installed().ok_or_else(|| {
                    (
                        1,
                        "error: Anneal toolchain is not installed (run `cargo anneal setup` or pass `--toolchain`)"
                            .to_string(),
                    )
                })?,
            };
            let anneal_root = anneal_root
                .unwrap_or_else(|| resolve_default_anneal_root(&toolchain_dir));
            let target_dir = match crate_dir {
                Some(dir) => dir,
                None => env::current_dir()
                    .map_err(|e| (1, format!("error: no current dir: {e}")))?,
            };
            let config = VerifyConfig {
                crate_dir: target_dir,
                toolchain_dir,
                anneal_root,
                allow_candidate_features,
                release_channel,
            };
            let report = verify_crate_with_report(&config)
                .map_err(|e| (1, format!("error: {e}")))?;
            print!("{}", report.output_text);
            Ok(0)
        }
    }
}
