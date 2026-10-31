// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI orchestration library for `cargo-anneal`.
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
//! 3. **Trusted boundary and kernel audit (`anneal-audit`):** invokes the
//!    standalone `anneal-audit` binary to compile `Trusted`, `Anneal`, `Mir`,
//!    and `Proof` with the pinned Lean 4.34.1 binary, check that `Mir.crate :
//!    Trusted.Crate` imports only `foundation ++ trusted`, check that
//!    `Proof.verify_crate` has the exact kernel type `Trusted.CrateTheorem
//!    Mir.crate` with zero custom axioms, enforce the target crate's
//!    candidate-feature trust policy, and replay all declarations in
//!    `base.toKernelEnv.replay`.

pub mod setup;

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// JSON value representation used for structured verification reports.
pub type Json = serde_json::Value;

/// Subsystem candidate-trusted feature identifiers recognized by Anneal.
pub const VALID_CANDIDATE_FEATURES: [&str; 6] = [
    "refinement",
    "step_result",
    "memory",
    "mir_ast",
    "mir_semantics",
    "rustc_capture",
];

/// Release channel governing whether candidate-trusted TCB features may be
/// enabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReleaseChannel {
    /// Alpha release channel: candidate features are supported when explicitly
    /// enabled by the target crate's trust policy or CLI flags, and default to
    /// `VettedOnly` when omitted.
    #[default]
    Alpha,
    /// Stable release channel: hard-locked to `VettedOnly`; candidate features
    /// cannot be enabled.
    Stable,
}

impl ReleaseChannel {
    /// Parse `"alpha"` or `"stable"`.
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "alpha" => Ok(Self::Alpha),
            "stable" => Ok(Self::Stable),
            other => Err(format!(
                "unknown release channel `{other}` (expected `alpha` or `stable`)"
            )),
        }
    }

    /// Return the canonical CLI string (`"alpha"` or `"stable"`).
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Alpha => "alpha",
            Self::Stable => "stable",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct CrateTrustPolicy {
    allow_all: bool,
    allowed_features: BTreeSet<String>,
}

impl CrateTrustPolicy {
    fn from_feature_list<I, S>(features: I) -> Result<Self, String>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut policy = Self::default();
        for raw in features {
            let feat = raw.as_ref().trim();
            if feat == "*" {
                policy.allow_all = true;
            } else if VALID_CANDIDATE_FEATURES.contains(&feat) {
                policy.allowed_features.insert(feat.to_string());
            } else {
                return Err(format!(
                    "unknown candidate feature `{feat}` in allow-candidate-features"
                ));
            }
        }
        Ok(policy)
    }

    fn merge(&mut self, other: Self) {
        self.allow_all |= other.allow_all;
        self.allowed_features.extend(other.allowed_features);
    }

    fn is_allowed(&self, channel: ReleaseChannel, feature: &str) -> bool {
        match channel {
            ReleaseChannel::Stable => false,
            ReleaseChannel::Alpha => {
                self.allow_all || self.allowed_features.contains(feature)
            }
        }
    }
}

fn load_crate_trust_policy(
    crate_dir: &Path,
    cli_override: Option<&[String]>,
) -> Result<CrateTrustPolicy, String> {
    let mut policy = CrateTrustPolicy::default();
    let cargo_toml_path = crate_dir.join("Cargo.toml");
    if cargo_toml_path.is_file() {
        let text = fs::read_to_string(&cargo_toml_path).map_err(|e| {
            format!("cannot read {}: {e}", cargo_toml_path.display())
        })?;
        let toml: toml::Value = toml::from_str(&text).map_err(|e| {
            format!("malformed Cargo.toml in {}: {e}", cargo_toml_path.display())
        })?;
        let allow_val = toml
            .get("package")
            .and_then(|p| p.get("metadata"))
            .and_then(|m| m.get("anneal"))
            .and_then(|a| {
                a.get("trust-policy")
                    .and_then(|tp| tp.get("allow-candidate-features"))
                    .or_else(|| a.get("allow-candidate-features"))
            });
        if let Some(val) = allow_val {
            let arr = val.as_array().ok_or_else(|| {
                "allow-candidate-features in Cargo.toml must be an array of strings"
                    .to_string()
            })?;
            let mut names = Vec::with_capacity(arr.len());
            for item in arr {
                let s = item.as_str().ok_or_else(|| {
                    "allow-candidate-features in Cargo.toml must contain only strings"
                        .to_string()
                })?;
                names.push(s.to_string());
            }
            policy.merge(CrateTrustPolicy::from_feature_list(&names)?);
        }
    }
    if let Some(cli_list) = cli_override {
        policy.merge(CrateTrustPolicy::from_feature_list(cli_list)?);
    }
    Ok(policy)
}

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

/// Configuration options for [`verify_crate`].
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    /// Optional explicit path to the Anneal repository root containing
    /// `trusted/lean/` and `trusted/audit/TrustedBoundary.lean`. Defaults to
    /// `ANNEAL_ROOT` or the workspace root of `cargo-anneal`.
    pub anneal_root: Option<PathBuf>,
    /// Optional explicit path to the pinned Lean 4.34.1 binary. Defaults to
    /// `ANNEAL_LEAN_BIN` when set.
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
    /// I/O error writing `.anneal/Proof.lean` or invoking `anneal-audit`.
    #[error("I/O error during verification: {0}")]
    Io(String),
    /// `anneal-audit` rejected the crate or proof.
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
    .map_err(|msg| VerifyError::AuditRejected {
        status_code: Some(1),
        stdout: String::new(),
        stderr: format!("Trusted check failed (candidate-policy): {msg}"),
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

/// Run only the `anneal-audit` crate verification gate against an
/// already-captured `crate_dir`.
pub fn run_trusted_audit(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<(), VerifyError> {
    let _ = run_trusted_audit_report(crate_dir, options)?;
    Ok(())
}

struct PrefixCacheDir {
    _dir: tempfile::TempDir,
    path: PathBuf,
}

fn default_prefix_cache(
    audit_bin: &Path,
    anneal_root: &Path,
    lean_bin: Option<&Path>,
) -> Result<PathBuf, VerifyError> {
    static PREFIX_CACHE: OnceLock<Result<PrefixCacheDir, String>> =
        OnceLock::new();
    let res = PREFIX_CACHE.get_or_init(|| {
        let dir = tempfile::Builder::new()
            .prefix("anneal-verify-prefix-")
            .tempdir()
            .map_err(|e| format!("failed to create prefix cache dir: {e}"))?;
        let path = dir.path().to_path_buf();
        let mut cmd = Command::new(audit_bin);
        cmd.arg("--build-prefix-cache")
            .arg(&path)
            .arg("--anneal-root")
            .arg(anneal_root);
        if let Some(lean) = lean_bin {
            cmd.arg("--lean").arg(lean);
        }
        let out = cmd.output().map_err(|e| {
            format!("failed to invoke {}: {e}", audit_bin.display())
        })?;
        if !out.status.success() {
            return Err(String::from_utf8_lossy(&out.stderr).trim().to_string());
        }
        Ok(PrefixCacheDir { _dir: dir, path })
    });
    match res {
        Ok(cache) => Ok(cache.path.clone()),
        Err(msg) => Err(VerifyError::Io(msg.clone())),
    }
}

/// Run `anneal-audit --verify-crate` against `crate_dir` and return the
/// structured audit report JSON on success.
pub fn run_trusted_audit_report(
    crate_dir: &Path,
    options: &VerifyOptions,
) -> Result<Json, VerifyError> {
    let audit_bin = resolve_audit_bin(options)?;
    let root = resolve_anneal_root(options)?;
    let lean = resolve_lean_bin(options);

    let mut cmd = Command::new(&audit_bin);
    cmd.arg("--verify-crate")
        .arg(crate_dir)
        .arg("--anneal-root")
        .arg(&root);
    if options.anneal_root.is_none() && options.lean_bin.is_none() {
        let cache_dir =
            default_prefix_cache(&audit_bin, &root, lean.as_deref())?;
        cmd.arg("--prefix-cache-dir").arg(cache_dir);
    }
    if let Some(ref lean_path) = lean {
        cmd.arg("--lean").arg(lean_path);
    }
    if let Some(channel) = options.release_channel {
        cmd.arg("--release-channel").arg(channel.as_str());
    }
    if let Some(ref allowed) = options.allow_candidate_features {
        cmd.arg(format!("--allow-candidate-features={}", allowed.join(",")));
    }

    let output = cmd.output().map_err(|e| {
        VerifyError::Io(format!(
            "failed to invoke {}: {e}",
            audit_bin.display()
        ))
    })?;

    if !output.status.success() {
        return Err(VerifyError::AuditRejected {
            status_code: output.status.code(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }

    let report: Json = serde_json::from_slice(&output.stdout).map_err(|e| {
        VerifyError::Io(format!(
            "malformed JSON report from {}: {e}",
            audit_bin.display()
        ))
    })?;
    Ok(report)
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
                .get_or_init(|| {
                    build_workspace_bin(
                        workspace_root,
                        "anneal-rustc-capture",
                    )
                })
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

    if let Some(sibling) = find_sibling_exe("anneal-rustc-capture") {
        return Ok(sibling);
    }

    Ok(PathBuf::from("anneal-rustc-capture"))
}

/// Resolve the `anneal-audit` executable from `ANNEAL_AUDIT_BIN`, the local
/// Cargo workspace, the installed exocrate toolchain, or adjacent to the
/// current executable.
pub fn resolve_audit_bin(options: &VerifyOptions) -> Result<PathBuf, VerifyError> {
    if let Some(env_bin) = env::var_os("ANNEAL_AUDIT_BIN") {
        return Ok(PathBuf::from(env_bin));
    }
    if let Some(root) = &options.anneal_root
        && let Some(tc_root) = root.parent().and_then(Path::parent)
    {
        let bundled = tc_root.join("bin/anneal-audit");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    static WORKSPACE_AUDITOR: OnceLock<Result<PathBuf, String>> =
        OnceLock::new();
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(workspace_root) =
        manifest_dir.parent().and_then(Path::parent)
    {
        let audit_manifest = workspace_root.join("trusted/audit/Cargo.toml");
        if audit_manifest.is_file() {
            return WORKSPACE_AUDITOR
                .get_or_init(|| {
                    build_workspace_bin(workspace_root, "anneal-audit")
                })
                .clone()
                .map_err(VerifyError::Io);
        }
    }

    if let Some(tc_root) = setup::resolve_installed() {
        let bundled = tc_root.join("bin/anneal-audit");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    if let Some(sibling) = find_sibling_exe("anneal-audit") {
        return Ok(sibling);
    }

    Ok(PathBuf::from("anneal-audit"))
}

fn find_sibling_exe(name: &str) -> Option<PathBuf> {
    let exe = env::current_exe().ok()?;
    let dir = exe.parent()?;
    let sibling = dir.join(name);
    if sibling.is_file() {
        return Some(sibling);
    }
    let parent_sibling = dir.parent()?.join(name);
    if parent_sibling.is_file() {
        return Some(parent_sibling);
    }
    None
}

fn build_workspace_bin(
    workspace_root: &Path,
    bin_name: &str,
) -> Result<PathBuf, String> {
    let cargo_bin = env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let status = Command::new(cargo_bin)
        .arg("build")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(workspace_root.join("Cargo.toml"))
        .arg("-p")
        .arg(bin_name)
        .arg("--bin")
        .arg(bin_name)
        .status()
        .map_err(|e| format!("failed to build workspace {bin_name}: {e}"))?;
    if !status.success() {
        return Err(format!(
            "cargo build -p {bin_name} exited with non-zero status"
        ));
    }
    let bin = workspace_root.join("target/debug").join(bin_name);
    if bin.is_file() {
        Ok(bin)
    } else {
        Err(format!(
            "expected workspace binary at {} after build",
            bin.display()
        ))
    }
}
