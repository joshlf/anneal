// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI orchestration and boundary-audit library for `cargo-anneal`
//! (`#103`, `#109`).
//!
//! `cargo-anneal` resides inside `trusted/` because all effectful code in
//! Anneal—process execution, filesystem I/O, `rustc` MIR capture, and `.olean`
//! boundary auditing—is part of the Trusted Computing Base (TCB). Code outside
//! `trusted/` (`theory/`, `examples/`, `tests/`) is mechanically restricted to
//! pure, effect-free Lean definitions and proofs checked by the Lean kernel.
//!
//! When verifying a target crate, `cargo-anneal` coordinates three stages:
//!
//! 1. **Trusted MIR capture (`anneal-rustc-capture`):** enforces the target
//!    crate's candidate-feature trust policy, invokes the
//!    standalone `anneal-rustc-capture` binary as a subprocess to compile the
//!    target crate, and emits `.anneal/Mir.lean` and
//!    `.anneal/CaptureManifest.json`.
//! 2. **Pure proof script emission (`.anneal/Proof.lean`):** emits a candidate
//!    Lean proof script for `theorem verify_crate : Trusted.CrateTheorem Mir.crate`
//!    (unless the caller supplies `--keep-proof` to test an existing proof
//!    file). Soundness does not depend on the proof generator: the emitted
//!    `Proof.lean` is treated as untrusted input to Stage 3.
//! 3. **Trusted boundary and kernel audit ([`audit::Checker`]):** verifies
//!    `CaptureManifest.json` digests against the on-disk Rust sources and
//!    `.anneal/Mir.lean`, compiles `Trusted`, `Anneal`, `Mir`, and `Proof` with
//!    the pinned Lean 4.34.1 binary, checks that `Proof.verify_crate` has the
//!    exact kernel type `Trusted.CrateTheorem Mir.crate` with zero custom
//!    axioms, enforces the target crate's candidate-feature trust policy, and
//!    replays all declarations in `base.toKernelEnv.replay`.

pub mod audit;
pub mod self_test;
pub mod setup;

use std::env;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use crate::audit::{Checker, Json, ReleaseChannel};

/// Errors returned when `anneal-rustc-capture` rejects a target crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureError {
    /// I/O error invoking `anneal-rustc-capture` or reading `.anneal/` outputs.
    Io(String),
    /// `rustc` exited with a non-zero status code.
    CompilationFailed(String),
    /// The crate or MIR contains a construct outside the supported `#109`
    /// vertical slice.
    UnsupportedMir(String),
    /// A candidate-trusted feature required by capture (`rustc_capture`) is not
    /// enabled by the target crate's trust policy or is forbidden on the active
    /// release channel.
    CandidateFeatureNotEnabled {
        feature: String,
        reason: String,
    },
}

impl fmt::Display for CaptureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(msg) => write!(f, "I/O error during MIR capture: {msg}"),
            Self::CompilationFailed(msg) => {
                write!(f, "rustc compilation failed: {msg}")
            }
            Self::UnsupportedMir(msg) => {
                write!(f, "unsupported MIR construct (fail-closed): {msg}")
            }
            Self::CandidateFeatureNotEnabled { feature, reason } => {
                write!(
                    f,
                    "candidate-trusted feature `{feature}` is not enabled: {reason}"
                )
            }
        }
    }
}

impl std::error::Error for CaptureError {}

/// Summary of a captured function read from `.anneal/CaptureManifest.json`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapturedFunctionSummary {
    pub name: String,
}

/// Summary of `.anneal/Mir.lean` and `.anneal/CaptureManifest.json` produced by
/// `anneal-rustc-capture`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureOutput {
    pub functions: Vec<CapturedFunctionSummary>,
    pub candidate_features: Vec<String>,
    pub mir_lean_path: PathBuf,
    pub manifest_path: PathBuf,
}

/// Configuration options for [`verify_crate`] and repository audit commands.
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    /// Optional explicit path to the Anneal repository root containing
    /// `trusted/lean/` and `trusted/audit/TrustedBoundary.lean`. Defaults to
    /// `ANNEAL_ROOT` or the workspace root of `cargo-anneal`.
    pub anneal_root: Option<PathBuf>,
    /// Optional explicit path to the pinned Lean 4.34.1 binary. Defaults to
    /// `ANNEAL_LEAN_BIN` when set; otherwise [`audit::default_lean_path`] uses
    /// the default pinned toolchain path.
    pub lean_bin: Option<PathBuf>,
    /// Optional explicit path to the `anneal-rustc-capture` binary. Defaults to
    /// `ANNEAL_RUSTC_CAPTURE_BIN` when set.
    pub rustc_capture_bin: Option<PathBuf>,
    /// When `true`, preserve an existing `.anneal/Proof.lean` instead of
    /// overwriting it with a generated proof script.
    pub keep_proof: bool,
    /// Optional release-channel override (`ReleaseChannel::Alpha` by default).
    pub release_channel: Option<ReleaseChannel>,
    /// Optional explicit candidate-feature allowlist (`["*"]` or feature names),
    /// merged with `[package.metadata.anneal.trust-policy] allow-candidate-features`
    /// in the target crate's `Cargo.toml`.
    pub allow_candidate_features: Option<Vec<String>>,
}

/// Errors returned when `cargo-anneal verify` rejects a crate.
#[derive(Debug)]
pub enum VerifyError {
    /// `anneal-rustc-capture` failed to compile or extract the crate's MIR.
    Capture(CaptureError),
    /// I/O error writing `.anneal/Proof.lean` or initializing the audit staging
    /// directory.
    Io(String),
    /// [`audit::Checker::verify_crate_with_policy`] rejected the crate or proof.
    AuditRejected {
        status_code: Option<i32>,
        stdout: String,
        stderr: String,
    },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Capture(err) => write!(f, "{err}"),
            Self::Io(msg) => write!(f, "I/O error during verification: {msg}"),
            Self::AuditRejected {
                status_code,
                stdout,
                stderr,
            } => {
                write!(
                    f,
                    "trusted crate audit exited with {:?}\nstdout: {}\nstderr: {}",
                    status_code,
                    stdout.trim(),
                    stderr.trim()
                )
            }
        }
    }
}

impl std::error::Error for VerifyError {}

impl From<CaptureError> for VerifyError {
    fn from(err: CaptureError) -> Self {
        Self::Capture(err)
    }
}

/// Run only the [`audit::Checker::verify_crate_with_policy`] gate against an
/// already-captured `crate_dir` (used by tests that mutate `.anneal/` artifacts
/// after capture to verify fail-closed audit behavior).
pub fn run_trusted_audit(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<(), VerifyError> {
    let _ = run_trusted_audit_report(crate_dir, options)?;
    Ok(())
}

/// Run [`audit::Checker::verify_crate_with_policy`] against `crate_dir` and
/// return the structured audit report JSON on success.
pub fn run_trusted_audit_report(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<Json, VerifyError> {
    let root = resolve_anneal_root(options)?;
    let lean = resolve_lean_bin(options);
    let mut checker = Checker::new(&root, lean.as_deref(), None).map_err(|e| {
        VerifyError::Io(format!(
            "Trusted check could not create its private temporary directory: {e}"
        ))
    })?;

    match checker.verify_crate_with_policy(
        crate_dir,
        None,
        options.release_channel,
        options.allow_candidate_features.as_deref(),
    ) {
        Ok(report) => {
            let _ = fs::remove_dir_all(&checker.stage);
            Ok(report)
        }
        Err(err) => {
            let stderr = format!(
                "Trusted check failed ({}): {}\nTarget execution began: {}; preserved logs: {}\nRetry only after resolving/reobserving the reported failure.",
                err.phase,
                err.message,
                checker.execution_began,
                checker.stage.display()
            );
            Err(VerifyError::AuditRejected {
                status_code: Some(err.code),
                stdout: String::new(),
                stderr,
            })
        }
    }
}

/// Resolve the Anneal repository or bundled exocrate `share/anneal` root from
/// `options`, `ANNEAL_ROOT`, `CARGO_MANIFEST_DIR`, or the installed exocrate
/// toolchain.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, VerifyError> {
    if let Some(root) = &options.anneal_root {
        return Ok(root.clone());
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
    if let Some(tc_root) = setup::resolve_installed() {
        let share_root = tc_root.join("share/anneal");
        if share_root.join("trusted/lean/foundation-lock.json").is_file() {
            return Ok(share_root);
        }
    }
    Err(VerifyError::Io(
        "Anneal toolchain is not installed; run `cargo anneal setup` first"
            .to_string(),
    ))
}

/// Resolve the optional explicit Lean binary override from `options`,
/// `ANNEAL_LEAN_BIN`, or the installed exocrate toolchain.
pub fn resolve_lean_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(lean) = &options.lean_bin {
        return Some(lean.clone());
    }
    if let Some(env_lean) = env::var_os("ANNEAL_LEAN_BIN") {
        return Some(PathBuf::from(env_lean));
    }
    setup::resolve_installed()
        .map(|tc_root| tc_root.join("lean/bin/lean"))
        .filter(|p| p.is_file())
}

