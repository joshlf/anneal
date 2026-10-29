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
//! 1. **Trusted MIR capture (`anneal-rustc-capture`):** compiles the target
//!    crate with `rustc --emit=mir,metadata` and emits `.anneal/Mir.lean` and
//!    `.anneal/CaptureManifest.json`.
//! 2. **Proof script emission (`.anneal/Proof.lean`):** emits a candidate Lean
//!    proof script for `theorem verify_crate : Trusted.CrateTheorem Mir.crate`
//!    (unless the caller supplies `--keep-proof` to test an existing proof
//!    file). Soundness does not depend on the proof generator: the emitted
//!    `Proof.lean` is treated as untrusted input to Stage 3.
//! 3. **Trusted boundary and kernel audit ([`audit::Checker`]):** verifies
//!    `CaptureManifest.json` digests against the on-disk Rust sources and
//!    `.anneal/Mir.lean`, compiles `Trusted`, `Anneal`, `Mir`, and `Proof` with
//!    the pinned Lean 4.34.1 binary, checks that `Proof.verify_crate` has the
//!    exact kernel type `Trusted.CrateTheorem Mir.crate` with zero custom
//!    axioms, and replays all declarations in `base.toKernelEnv.replay`.

pub mod audit;
pub mod self_test;

use std::env;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};


use crate::audit::{Checker, Json};

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
    /// When `true`, preserve an existing `.anneal/Proof.lean` instead of
    /// overwriting it with a generated proof script.
    pub keep_proof: bool,
}

/// Errors returned when `cargo-anneal verify` rejects a crate.
#[derive(Debug)]
pub enum VerifyError {
    /// I/O error writing `.anneal/Proof.lean` or initializing the audit staging
    /// directory.
    Io(String),
    /// [`audit::Checker::verify_crate`] rejected the crate or proof.
    AuditRejected {
        status_code: Option<i32>,
        stdout: String,
        stderr: String,
    },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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

/// Run only the [`audit::Checker::verify_crate`] gate against an
/// already-captured `crate_dir` (used by tests that mutate `.anneal/` artifacts
/// after capture to verify fail-closed audit behavior).
pub fn run_trusted_audit(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<(), VerifyError> {
    let _ = run_trusted_audit_report(crate_dir, options)?;
    Ok(())
}

/// Run [`audit::Checker::verify_crate`] against `crate_dir` and return the
/// structured audit report JSON on success.
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

    match checker.verify_crate(crate_dir, None) {
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

/// Resolve the Anneal repository root from `options`, `ANNEAL_ROOT`, or
/// `CARGO_MANIFEST_DIR`.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, VerifyError> {
    if let Some(root) = &options.anneal_root {
        return Ok(root.clone());
    }
    if let Some(env_root) = env::var_os("ANNEAL_ROOT") {
        return Ok(PathBuf::from(env_root));
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            VerifyError::Io(
                "cannot determine Anneal repository root from CARGO_MANIFEST_DIR"
                    .to_string(),
            )
        })
}

/// Resolve the optional explicit Lean binary override from `options` or
/// `ANNEAL_LEAN_BIN`.
pub fn resolve_lean_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(lean) = &options.lean_bin {
        return Some(lean.clone());
    }
    env::var_os("ANNEAL_LEAN_BIN").map(PathBuf::from)
}

