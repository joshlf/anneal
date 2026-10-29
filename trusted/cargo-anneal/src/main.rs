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
//! subcommand invocation (`cargo anneal <subcommand>`). All effectful stages—
//! `rustc` MIR capture (`anneal-rustc-capture`), repository boundary auditing
//! ([`cargo_anneal::audit`]), and kernel verification—execute inside
//! `trusted/`.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::error::ErrorKind;
use clap::{Parser, Subcommand};

use cargo_anneal::audit::{Checker, Json, ReleaseChannel};
use cargo_anneal::setup;
use cargo_anneal::{
    VerifyOptions, resolve_anneal_root, resolve_lean_bin,
    verify_crate_with_report,
};

#[derive(Parser)]
#[command(
    name = "cargo-anneal",
    version,
    about = "Deductive verification CLI and trusted-boundary auditor for Anneal"
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
        /// Target crate directory (defaults to `.`).
        crate_dir: Option<PathBuf>,
        /// Preserve an existing `.anneal/Proof.lean` instead of regenerating it.
        #[arg(long)]
        keep_proof: bool,
        /// Comma-separated candidate-trusted features to allow (or `*`).
        #[arg(long, value_delimiter = ',')]
        allow_candidate_features: Option<Vec<String>>,
        /// Release channel override (`alpha` or `stable`).
        #[arg(long)]
        release_channel: Option<String>,
        /// Absolute path to the Lean 4 binary.
        #[arg(long)]
        lean: Option<PathBuf>,
        /// Path to the Anneal repository root.
        #[arg(long)]
        anneal_root: Option<PathBuf>,
    },
    /// Audit the Anneal repository's `trusted/` and `theory/` boundaries.
    AuditRepo {
        /// Absolute path to the Lean 4 binary.
        #[arg(long)]
        lean: Option<PathBuf>,
        /// Path to the Anneal repository root.
        #[arg(long)]
        anneal_root: Option<PathBuf>,
    },
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

fn emit_unused_candidate_warnings(report: &Json) {
    if let Some(unused) = report
        .get("crateVerification")
        .and_then(|cv| cv.get("unusedCandidateFeatures"))
        .and_then(Json::as_array)
    {
        for item in unused {
            if let Some(feat) = item.as_str() {
                eprintln!(
                    "warning: candidate-trusted feature `{feat}` in `allow-candidate-features` was not used during verification (it may be unused or may have graduated to @[vetted])"
                );
            }
        }
    }
}

fn active_candidate_features(report: &Json) -> Vec<String> {
    report
        .get("crateVerification")
        .and_then(|cv| cv.get("candidateFeatures"))
        .and_then(Json::as_array)
        .map(|arr| {
            arr.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default()
}

fn validate_lean_path(lean: Option<PathBuf>) -> Result<Option<PathBuf>, (u8, String)> {
    if let Some(ref pb) = lean
        && !pb.is_absolute()
    {
        return Err((2, "error: --lean must be absolute".to_string()));
    }
    Ok(lean)
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
            keep_proof,
            allow_candidate_features,
            release_channel,
            lean,
            anneal_root,
        } => {
            let lean_bin = validate_lean_path(lean)?;
            let release_channel = match release_channel {
                Some(raw) => Some(
                    ReleaseChannel::parse(&raw)
                        .map_err(|e| (2, format!("error: {e}")))?,
                ),
                None => None,
            };
            let allow_candidate_features = allow_candidate_features.map(|list| {
                list.into_iter()
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
                    .collect()
            });
            let options = VerifyOptions {
                anneal_root,
                lean_bin,
                rustc_capture_bin: None,
                keep_proof,
                release_channel,
                allow_candidate_features,
            };
            let target_dir = crate_dir.unwrap_or_else(|| PathBuf::from("."));
            let (output, report) =
                verify_crate_with_report(&target_dir, &options)
                    .map_err(|e| (1, format!("error: {e}")))?;
            emit_unused_candidate_warnings(&report);
            let fn_names: Vec<&str> =
                output.functions.iter().map(|f| f.name.as_str()).collect();
            println!(
                "verified: crate at {} passed Trusted.CrateTheorem ({})",
                target_dir.display(),
                fn_names.join(", ")
            );
            let candidates = active_candidate_features(&report);
            if !candidates.is_empty() {
                println!(
                    "Candidate-Trusted TCB (Unvetted / Alpha): {}",
                    candidates.join(", ")
                );
            }
            Ok(0)
        }
        Commands::AuditRepo { lean, anneal_root } => {
            let lean_bin = validate_lean_path(lean)?;
            let options = VerifyOptions {
                anneal_root,
                lean_bin,
                ..VerifyOptions::default()
            };
            let checkout = resolve_anneal_root(&options)
                .map_err(|e| (2, e.to_string()))?;
            let lean = resolve_lean_bin(&options);
            let mut checker = Checker::new(&checkout, lean.as_deref())
                .map_err(|e| {
                    (
                        2,
                        format!(
                            "Trusted check could not create its private temporary directory: {e}"
                        ),
                    )
                })?;
            match checker.run() {
                Ok(report) => {
                    let guarantee = report
                        .get("guarantee")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    let k_decls = report
                        .get("kernelDeclarations")
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let replayed = report
                        .get("replayedDeclarations")
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let axioms = report
                        .get("axioms")
                        .and_then(|v| serde_json::to_string(v).ok())
                        .unwrap_or_else(|| "[]".to_string());
                    let tc = report
                        .get("toolchain")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    println!(
                        "PASS: {guarantee}\n\
                         {} Trusted modules; {} Theory modules; \
                         {k_decls} Trusted kernel declarations; \
                         {replayed} total replayed declarations; \
                         axioms={axioms}\n\
                         {tc}",
                        checker.modules.len(),
                        checker.theory_modules.len()
                    );
                    Ok(0)
                }
                Err(err) => {
                    let msg = format!(
                        "Trusted check failed ({}): {}\nTarget execution began: {}\nRetry only after resolving/reobserving the reported failure.",
                        err.phase, err.message, checker.execution_began
                    );
                    Err((err.code as u8, msg))
                }
            }
        }
    }
}
