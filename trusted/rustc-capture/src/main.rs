// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone CLI entry point for `anneal-rustc-capture` (`#99`, `#103`, `#109`).
//!
//! Invoked as a subprocess by `cargo-anneal` to compile a target crate, extract
//! its lowered MIR into `.anneal/Mir.lean` and `.anneal/CaptureManifest.json`,
//! and optionally emit a candidate `.anneal/Proof.lean`.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use anneal_rustc_capture::{
    CaptureError, CapturePolicy, capture_crate_with_policy_and_options,
};

fn main() -> ExitCode {
    let mut emit_proof = false;
    let mut crate_dir: Option<PathBuf> = None;
    let mut policy = CapturePolicy::allow_all_alpha();
    let mut custom_policy = false;
    let mut args = env::args().skip(1);

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--emit-proof" => emit_proof = true,
            "--stable-channel" => {
                if !custom_policy {
                    policy = CapturePolicy::vetted_only(true);
                    custom_policy = true;
                } else {
                    policy.is_stable_channel = true;
                }
            }
            "--vetted-only" => {
                policy = CapturePolicy::vetted_only(policy.is_stable_channel);
                custom_policy = true;
            }
            "--allow-all-candidates" => {
                if !custom_policy {
                    policy = CapturePolicy::vetted_only(false);
                    custom_policy = true;
                }
                policy.allow_all_candidates = true;
            }
            "--allow-candidate-feature" => {
                let Some(feat) = args.next() else {
                    eprintln!(
                        "IO_ERROR: --allow-candidate-feature requires a feature name"
                    );
                    return ExitCode::from(2);
                };
                if !custom_policy {
                    policy = CapturePolicy::vetted_only(false);
                    custom_policy = true;
                }
                policy.allowed_candidates.push(feat);
            }
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

    match capture_crate_with_policy_and_options(&target_dir, &policy, emit_proof)
    {
        Ok(_) => ExitCode::SUCCESS,
        Err(CaptureError::CandidateFeatureNotEnabled { feature, reason }) => {
            eprintln!("CANDIDATE_FEATURE_NOT_ENABLED: {feature}: {reason}");
            ExitCode::from(1)
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
