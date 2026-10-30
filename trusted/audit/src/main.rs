// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone CLI entry point (`anneal-audit`) for auditing Anneal's
//! repository trust boundary (`trusted/` vs. `theory/`) and verifying per-crate
//! `.anneal/Mir.lean` and `.anneal/Proof.lean` artifacts in the Lean 4 kernel.

use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::error::ErrorKind;
use clap::Parser;

use anneal_audit::{Checker, Json, ReleaseChannel};

#[derive(Parser)]
#[command(
    name = "anneal-audit",
    version,
    about = "Trusted-boundary and kernel verification auditor for Anneal"
)]
struct Cli {
    /// Target crate directory containing `.anneal/Mir.lean` and
    /// `.anneal/Proof.lean`. When omitted, audits the Anneal repository itself.
    #[arg(long)]
    verify_crate: Option<PathBuf>,

    /// Pre-compile the repository `Trusted.*` and `Anneal.*` prefix into the
    /// specified directory for reuse by subsequent `--verify-crate` calls.
    #[arg(long)]
    build_prefix_cache: Option<PathBuf>,

    /// Reuse a pre-compiled repository prefix directory produced by
    /// `--build-prefix-cache`.
    #[arg(long)]
    prefix_cache_dir: Option<PathBuf>,

    /// Comma-separated candidate-trusted features to allow during
    /// `--verify-crate` (or `*`).
    #[arg(long)]
    allow_candidate_features: Option<String>,

    /// Release channel override (`alpha` or `stable`) for `--verify-crate`.
    #[arg(long)]
    release_channel: Option<String>,

    /// Absolute path to the Lean 4 binary.
    #[arg(long)]
    lean: Option<PathBuf>,

    /// Path to the Anneal repository root.
    #[arg(long)]
    anneal_root: Option<PathBuf>,
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

fn resolve_checkout(explicit: Option<PathBuf>) -> Result<PathBuf, (u8, String)> {
    if let Some(root) = explicit {
        return Ok(root);
    }
    if let Some(env_root) = env::var_os("ANNEAL_ROOT") {
        return Ok(PathBuf::from(env_root));
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(workspace_root) = manifest_dir.parent().and_then(Path::parent)
        && workspace_root
            .join("trusted/lean/foundation-lock.json")
            .is_file()
    {
        return Ok(workspace_root.to_path_buf());
    }
    if let Ok(exe) = env::current_exe()
        && let Some(tc_root) = exe.parent().and_then(Path::parent)
    {
        let share_root = tc_root.join("share/anneal");
        if share_root.join("trusted/lean/foundation-lock.json").is_file() {
            return Ok(share_root);
        }
    }
    Ok(PathBuf::from("."))
}

fn run(raw_args: Vec<String>) -> Result<u8, (u8, String)> {
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

    if let Some(ref pb) = cli.lean
        && !pb.is_absolute()
    {
        return Err((2, "error: --lean must be absolute".to_string()));
    }

    let checkout = resolve_checkout(cli.anneal_root)?;
    let mut checker = Checker::new(&checkout, cli.lean.as_deref()).map_err(|e| {
        (
            2,
            format!(
                "Trusted check could not create its private temporary directory: {e}"
            ),
        )
    })?;

    if let Some(cache_dest) = cli.build_prefix_cache {
        match checker.build_prefix_cache(&cache_dest) {
            Ok(_) => return Ok(0),
            Err(err) => {
                let msg = format!(
                    "Trusted check failed ({}): {}\nTarget execution began: {}\nRetry only after resolving/reobserving the reported failure.",
                    err.phase, err.message, checker.execution_began
                );
                return Err((err.code as u8, msg));
            }
        }
    }

    if let Some(crate_dir) = cli.verify_crate {
        let release_channel = match cli.release_channel {
            Some(raw) => Some(
                ReleaseChannel::parse(&raw)
                    .map_err(|e| (2, format!("error: {e}")))?,
            ),
            None => None,
        };
        let allow_candidate_features: Option<Vec<String>> =
            cli.allow_candidate_features.map(|raw| {
                raw.split(',')
                    .map(|s| s.trim().to_string())
                    .filter(|s| !s.is_empty())
                    .collect()
            });
        checker.set_prefix_cache_dir(cli.prefix_cache_dir);
        match checker.verify_crate_with_policy(
            &crate_dir,
            release_channel,
            allow_candidate_features.as_deref(),
        ) {
            Ok(report) => {
                println!(
                    "{}",
                    serde_json::to_string(&report)
                        .expect("serialize crate verification report")
                );
                return Ok(0);
            }
            Err(err) => {
                let msg = format!(
                    "Trusted check failed ({}): {}\nTarget execution began: {}\nRetry only after resolving/reobserving the reported failure.",
                    err.phase, err.message, checker.execution_began
                );
                return Err((err.code as u8, msg));
            }
        }
    }

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
