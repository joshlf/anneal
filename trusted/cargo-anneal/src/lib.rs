// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI orchestration and boundary-audit library for `cargo-anneal`.
//!
//! `cargo-anneal` resides inside `trusted/` because all effectful code in
//! Anneal—process execution, filesystem I/O, `rustc` MIR capture, and `.olean`
//! boundary auditing—is part of the Trusted Computing Base (TCB). Code outside
//! `trusted/` (`theory/`) is mechanically restricted to pure, effect-free Lean
//! definitions and proofs checked by the Lean kernel.
//!
//! When verifying a target crate, `cargo-anneal` coordinates three stages:
//!
//! 1. **Trusted MIR capture (`anneal-rustc-capture`):** enforces the target
//!    crate's candidate-feature trust policy, invokes the standalone
//!    `anneal-rustc-capture` binary as a subprocess to compile the target
//!    crate, and emits `.anneal/Mir.lean`.
//! 2. **Pure proof script emission (`.anneal/Proof.lean`):** emits a candidate
//!    Lean proof script for `theorem verify_crate : Trusted.CrateTheorem
//!    Mir.crate` (unless the caller supplies `--keep-proof` to test an existing
//!    proof file). Soundness does not depend on the proof generator: the
//!    emitted `Proof.lean` is treated as untrusted input to Stage 3.
//! 3. **Trusted boundary and kernel audit ([`audit::Checker`]):** compiles
//!    `Trusted`, `Anneal`, `Mir`, and `Proof` with the pinned Lean 4.34.1
//!    binary, checks that `Mir.crate : Trusted.Crate` imports only
//!    `foundation ++ trusted`, checks that `Proof.verify_crate` has the
//!    exact kernel type `Trusted.CrateTheorem Mir.crate` with zero custom
//!    axioms, enforces the target crate's candidate-feature trust policy,
//!    and replays all declarations in `base.toKernelEnv.replay`.

pub mod audit;
pub mod setup;

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use crate::audit::{
    Checker, Json, ReleaseChannel, load_crate_trust_policy,
};

/// Errors returned when `anneal-rustc-capture` rejects a target crate.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CaptureError {
    /// I/O error invoking `anneal-rustc-capture` or reading `.anneal/` outputs.
    #[error("I/O error during MIR capture: {0}")]
    Io(String),
    /// `rustc` exited with a non-zero status code.
    #[error("rustc compilation failed: {0}")]
    CompilationFailed(String),
    /// The crate or MIR contains a construct outside the supported MIR subset.
    #[error("unsupported MIR construct (fail-closed): {0}")]
    UnsupportedMir(String),
    /// A candidate-trusted feature required by capture (`rustc_capture`) is not
    /// enabled by the target crate's trust policy or is forbidden on the active
    /// release channel.
    #[error("candidate-trusted feature `{feature}` is not enabled: {reason}")]
    CandidateFeatureNotEnabled {
        feature: String,
        reason: String,
    },
}

/// Summary of a captured function reported by `anneal-rustc-capture`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapturedFunctionSummary {
    pub name: String,
}

/// Summary of `.anneal/Mir.lean` produced by `anneal-rustc-capture`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureOutput {
    pub functions: Vec<CapturedFunctionSummary>,
    pub mir_lean_path: PathBuf,
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
    /// Optional explicit candidate-feature allowlist (`["*"]` or feature
    /// names), merged with `[package.metadata.anneal.trust-policy]
    /// allow-candidate-features` in the target crate's `Cargo.toml`.
    pub allow_candidate_features: Option<Vec<String>>,
}

/// Errors returned when `cargo-anneal verify` rejects a crate.
#[derive(Debug, thiserror::Error)]
pub enum VerifyError {
    /// `anneal-rustc-capture` failed to compile or extract the crate's MIR.
    #[error("{0}")]
    Capture(#[from] CaptureError),
    /// I/O error writing `.anneal/Proof.lean` or initializing the audit staging
    /// directory.
    #[error("I/O error during verification: {0}")]
    Io(String),
    /// [`audit::Checker::verify_crate_with_policy`] rejected the crate or
    /// proof.
    #[error(
        "trusted crate audit exited with {:?}\nstdout: {}\nstderr: {}",
        status_code,
        stdout.trim(),
        stderr.trim()
    )]
    AuditRejected {
        status_code: Option<i32>,
        stdout: String,
        stderr: String,
    },
}

/// Invoke `anneal-rustc-capture` on `crate_dir` without emitting `Proof.lean`.
pub fn capture_crate(crate_dir: &Path) -> Result<CaptureOutput, CaptureError> {
    capture_crate_with_options(crate_dir, false, &VerifyOptions::default())
}

/// Invoke `anneal-rustc-capture` on `crate_dir`, optionally emitting
/// `.anneal/Proof.lean` when `emit_proof` is `true`.
pub fn capture_crate_with_options(
    crate_dir: &Path,
    emit_proof: bool,
    options: &VerifyOptions,
) -> Result<CaptureOutput, CaptureError> {
    let driver_bin = resolve_rustc_capture_bin(options)?;
    let mut cmd = Command::new(&driver_bin);
    if env::var_os("RUSTC").is_none() {
        let driver_toolchain_root = driver_bin
            .parent()
            .and_then(Path::parent)
            .filter(|root| root.join("rust/bin/rustc").is_file())
            .map(Path::to_path_buf)
            .or_else(|| {
                setup::resolve_installed()
                    .filter(|root| root.join("rust/bin/rustc").is_file())
            });
        if let Some(tc_root) = driver_toolchain_root {
            cmd.env("RUSTC", tc_root.join("rust/bin/rustc"));
            let lib_var = if cfg!(target_os = "macos") {
                "DYLD_LIBRARY_PATH"
            } else {
                "LD_LIBRARY_PATH"
            };
            cmd.env(lib_var, tc_root.join("rust/lib"));
        }
    }
    if emit_proof {
        cmd.arg("--emit-proof");
    }
    cmd.arg(crate_dir);
    let output = cmd.output().map_err(|e| {
        CaptureError::Io(format!(
            "failed to invoke {}: {e}",
            driver_bin.display()
        ))
    })?;

    if !output.status.success() {
        let stderr =
            String::from_utf8_lossy(&output.stderr).trim().to_string();
        if let Some(msg) = stderr.strip_prefix("IO_ERROR: ") {
            return Err(CaptureError::Io(msg.to_string()));
        }
        if let Some(msg) = stderr.strip_prefix("COMPILATION_FAILED: ") {
            return Err(CaptureError::CompilationFailed(msg.to_string()));
        }
        if let Some(msg) = stderr.strip_prefix("UNSUPPORTED_MIR: ") {
            return Err(CaptureError::UnsupportedMir(msg.to_string()));
        }
        return Err(CaptureError::Io(format!(
            "anneal-rustc-capture exited with {:?}: {stderr}",
            output.status.code()
        )));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let functions = stdout
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|name| CapturedFunctionSummary {
            name: name.to_string(),
        })
        .collect();
    let canon_dir = crate_dir.canonicalize().map_err(|e| {
        CaptureError::Io(format!("{}: {e}", crate_dir.display()))
    })?;
    let mir_lean_path = canon_dir.join(".anneal/Mir.lean");

    Ok(CaptureOutput {
        functions,
        mir_lean_path,
    })
}

/// Run the end-to-end Anneal verification pipeline on `crate_dir`.
///
/// First checks the crate's candidate-feature trust policy, extracts
/// `.anneal/Mir.lean` (and `.anneal/Proof.lean` unless `options.keep_proof` is
/// set) via the `anneal-rustc-capture` subprocess, and finally runs
/// [`audit::Checker::verify_crate_with_policy`] to check the proof in Lean's
/// kernel.
pub fn verify_crate(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<CaptureOutput, VerifyError> {
    let (capture, _report) = verify_crate_with_report(crate_dir, options)?;
    Ok(capture)
}

/// Run the end-to-end Anneal verification pipeline on `crate_dir` and return
/// both the [`CaptureOutput`] and the structured audit report JSON.
pub fn verify_crate_with_report(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<(CaptureOutput, Json), VerifyError> {
    let channel = options.release_channel.unwrap_or_default();
    let policy = load_crate_trust_policy(
        crate_dir,
        options.allow_candidate_features.as_deref(),
    )
    .map_err(|err| VerifyError::AuditRejected {
        status_code: Some(err.code),
        stdout: String::new(),
        stderr: format!("Trusted check failed ({}): {}", err.phase, err.message),
    })?;
    if channel == ReleaseChannel::Stable {
        return Err(VerifyError::Capture(
            CaptureError::CandidateFeatureNotEnabled {
                feature: "rustc_capture".to_string(),
                reason: "stable release channel forbids candidate-trusted feature `rustc_capture`"
                    .to_string(),
            },
        ));
    }
    if !policy.is_allowed(channel, "rustc_capture") {
        return Err(VerifyError::Capture(
            CaptureError::CandidateFeatureNotEnabled {
                feature: "rustc_capture".to_string(),
                reason: "opt in via `[package.metadata.anneal.trust-policy] allow-candidate-features = [\"rustc_capture\", ...]` in Cargo.toml or `--allow-candidate-features rustc_capture`"
                    .to_string(),
            },
        ));
    }
    let capture =
        capture_crate_with_options(crate_dir, !options.keep_proof, options)?;
    let report = run_trusted_audit_report(crate_dir, options)?;
    Ok((capture, report))
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
    let mut checker = Checker::new(&root, lean.as_deref()).map_err(|e| {
        VerifyError::Io(format!(
            "Trusted check could not create its private temporary directory: {e}"
        ))
    })?;

    match checker.verify_crate_with_policy(
        crate_dir,
        options.release_channel,
        options.allow_candidate_features.as_deref(),
    ) {
        Ok(report) => Ok(report),
        Err(err) => {
            let stderr = format!(
                "Trusted check failed ({}): {}\nTarget execution began: {}\nRetry only after resolving/reobserving the reported failure.",
                err.phase, err.message, checker.execution_began
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

/// Resolve the `anneal-rustc-capture` executable from `options`,
/// `ANNEAL_RUSTC_CAPTURE_BIN`, the local Cargo workspace, the installed
/// exocrate toolchain, or adjacent to the current executable.
pub fn resolve_rustc_capture_bin(
    options: &VerifyOptions,
) -> Result<PathBuf, CaptureError> {
    if let Some(bin) = &options.rustc_capture_bin {
        return Ok(bin.clone());
    }
    if let Some(env_bin) = env::var_os("ANNEAL_RUSTC_CAPTURE_BIN") {
        return Ok(PathBuf::from(env_bin));
    }
    if let Some(root) = &options.anneal_root
        && let Some(tc_root) = root.parent().and_then(Path::parent)
    {
        let bundled = tc_root.join("bin/anneal-rustc-capture");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    static WORKSPACE_DRIVER: OnceLock<Result<PathBuf, String>> =
        OnceLock::new();
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(workspace_root) =
        manifest_dir.parent().and_then(Path::parent)
    {
        let driver_manifest =
            workspace_root.join("trusted/rustc-capture/Cargo.toml");
        if driver_manifest.is_file() {
            return WORKSPACE_DRIVER
                .get_or_init(|| build_workspace_driver(workspace_root))
                .clone()
                .map_err(CaptureError::Io);
        }
    }

    if let Some(tc_root) = setup::resolve_installed() {
        let bundled = tc_root.join("bin/anneal-rustc-capture");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    if let Ok(exe) = env::current_exe()
        && let Some(dir) = exe.parent()
    {
        let sibling = dir.join("anneal-rustc-capture");
        if sibling.is_file() {
            return Ok(sibling);
        }
        if let Some(parent_dir) = dir.parent() {
            let parent_sibling = parent_dir.join("anneal-rustc-capture");
            if parent_sibling.is_file() {
                return Ok(parent_sibling);
            }
        }
    }

    Ok(PathBuf::from("anneal-rustc-capture"))
}

fn build_workspace_driver(workspace_root: &Path) -> Result<PathBuf, String> {
    let cargo_bin = env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let status = Command::new(cargo_bin)
        .arg("build")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(workspace_root.join("Cargo.toml"))
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .status()
        .map_err(|e| {
            format!("failed to build workspace anneal-rustc-capture: {e}")
        })?;
    if !status.success() {
        return Err(
            "cargo build -p anneal-rustc-capture exited with non-zero status"
                .to_string(),
        );
    }
    let bin = workspace_root.join("target/debug/anneal-rustc-capture");
    if bin.is_file() {
        Ok(bin)
    } else {
        Err(format!(
            "expected workspace binary at {} after build",
            bin.display()
        ))
    }
}
