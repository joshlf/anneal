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
//! 1. **Trusted MIR capture (`anneal-rustc-capture`):** validates that the
//!    target crate is a single-file library (`src/lib.rs`) free of symlinks,
//!    build scripts, or secondary targets, enforces the target crate's
//!    candidate-feature trust policy, invokes the standalone
//!    `anneal-rustc-capture` binary in a sanitized subprocess environment, and
//!    emits `.anneal/Mir.lean`.
//! 2. **Pure proof script emission (`.anneal/Proof.lean`):** emits a candidate
//!    Lean proof script for `theorem verify_crate : Trusted.CrateTheorem
//!    Mir.crate` (unless the caller supplies `--keep-proof` to test an existing
//!    proof file). Soundness does not depend on the proof generator: the
//!    emitted `Proof.lean` is treated as untrusted input to Stage 3.
//! 3. **Trusted boundary and kernel audit (`anneal-audit`):** invokes the
//!    standalone `anneal-audit` binary in a sanitized subprocess environment to
//!    compile `Trusted`, `Anneal`, `Mir`, and `Proof` with the pinned Lean
//!    4.34.1 binary, check that `Mir.crate : Trusted.Crate` imports only
//!    `foundation ++ trusted`, check that `Proof.verify_crate` has the exact
//!    kernel type `Trusted.CrateTheorem Mir.crate` with only constructive
//!    axioms (`Quot.sound`, `propext`), verify `Mir.crate.artifacts` against
//!    `src/lib.rs` on disk, enforce the target crate's candidate-feature trust
//!    policy, replay all declarations in `base.toKernelEnv.replay`, and
//!    validate the returned JSON report schema.

pub mod setup;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

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

/// Host environment variables preserved across sanitized child-process
/// invocations.
///
/// Clearing the child environment before copying this allowlist prevents
/// ambient `RUSTC_WRAPPER`, `RUSTFLAGS`, `CARGO_BUILD_RUSTFLAGS`, `LEAN_PATH`,
/// `LD_PRELOAD`, or binary-override variables from hijacking compiler or audit
/// execution.
const SANITIZED_ENV_ALLOWLIST: [&str; 10] = [
    "PATH",
    "HOME",
    "TMPDIR",
    "USER",
    "LANG",
    "LC_ALL",
    "TERM",
    "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN",
    "CARGO_HOME",
];

/// Construct a [`Command`] whose environment is cleared and populated only with
/// [`SANITIZED_ENV_ALLOWLIST`].
fn sanitized_command(program: impl AsRef<OsStr>) -> Command {
    let mut cmd = Command::new(program);
    cmd.env_clear();
    for key in SANITIZED_ENV_ALLOWLIST {
        if let Some(val) = env::var_os(key) {
            cmd.env(key, val);
        }
    }
    cmd
}

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

/// Validate that `path` exists, is not a symbolic link, and satisfies `check`.
fn ensure_non_symlink(
    path: &Path,
    expect_dir: bool,
) -> Result<(), CaptureError> {
    let meta = fs::symlink_metadata(path).map_err(|e| {
        CaptureError::Io(format!("cannot stat {}: {e}", path.display()))
    })?;
    if meta.file_type().is_symlink() {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlink at {}",
            path.display()
        )));
    }
    if expect_dir && !meta.is_dir() {
        return Err(CaptureError::Io(format!(
            "expected directory at {}",
            path.display()
        )));
    }
    if !expect_dir && !meta.is_file() {
        return Err(CaptureError::Io(format!(
            "expected regular file at {}",
            path.display()
        )));
    }
    Ok(())
}

/// Validate that `crate_dir` is a single-library crate rooted at `src/lib.rs`
/// with no symlinks, build scripts, binary targets, or proc-macro flags.
///
/// Anneal captures and verifies `src/lib.rs` as a single library compilation
/// unit (`rustc --crate-type=lib src/lib.rs`). Rejecting `build.rs`,
/// `src/main.rs`, `src/bin/`, and extra Cargo targets (`[[bin]]`,
/// `[[example]]`, `[[test]]`, `[[bench]]`, `[package].build`, `[lib].path !=
/// "src/lib.rs"`, `proc-macro = true`) ensures that no unverified code in the
/// package can execute at build time or ship alongside the verified library.
fn validate_target_crate_layout_and_manifest(
    crate_dir: &Path,
) -> Result<Option<toml::Value>, CaptureError> {
    let dir_meta = fs::symlink_metadata(crate_dir).map_err(|e| {
        CaptureError::Io(format!("{}: {e}", crate_dir.display()))
    })?;
    if dir_meta.file_type().is_symlink() {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to verify symlinked crate directory {}",
            crate_dir.display()
        )));
    }
    if !dir_meta.is_dir() {
        return Err(CaptureError::Io(format!(
            "{} is not a directory",
            crate_dir.display()
        )));
    }

    ensure_non_symlink(&crate_dir.join("src"), true)?;
    ensure_non_symlink(&crate_dir.join("src/lib.rs"), false)?;

    let anneal_dir = crate_dir.join(".anneal");
    if let Ok(meta) = fs::symlink_metadata(&anneal_dir)
        && meta.file_type().is_symlink()
    {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlinked .anneal directory at {}",
            anneal_dir.display()
        )));
    }

    for forbidden_rel in ["build.rs", "src/main.rs", "src/bin"] {
        let forbidden = crate_dir.join(forbidden_rel);
        if fs::symlink_metadata(&forbidden).is_ok() {
            return Err(CaptureError::UnsupportedMir(format!(
                "target crate must not contain `{forbidden_rel}`: {}",
                forbidden.display()
            )));
        }
    }

    let cargo_toml_path = crate_dir.join("Cargo.toml");
    let Ok(cargo_meta) = fs::symlink_metadata(&cargo_toml_path) else {
        return Ok(None);
    };
    if cargo_meta.file_type().is_symlink() {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlinked Cargo.toml at {}",
            cargo_toml_path.display()
        )));
    }
    if !cargo_meta.is_file() {
        return Err(CaptureError::Io(format!(
            "expected regular file at {}",
            cargo_toml_path.display()
        )));
    }

    let text = fs::read_to_string(&cargo_toml_path).map_err(|e| {
        CaptureError::Io(format!(
            "cannot read {}: {e}",
            cargo_toml_path.display()
        ))
    })?;
    let toml_val: toml::Value = toml::from_str(&text).map_err(|e| {
        CaptureError::UnsupportedMir(format!(
            "malformed Cargo.toml in {}: {e}",
            cargo_toml_path.display()
        ))
    })?;

    let Some(pkg) = toml_val.get("package").and_then(toml::Value::as_table)
    else {
        return Err(CaptureError::UnsupportedMir(format!(
            "Cargo.toml in {} must contain a [package] table",
            cargo_toml_path.display()
        )));
    };
    if let Some(build_val) = pkg.get("build")
        && build_val.as_bool() != Some(false)
    {
        return Err(CaptureError::UnsupportedMir(
            "Cargo.toml must not specify a [package].build script".to_string(),
        ));
    }

    for forbidden_target in ["bin", "example", "test", "bench"] {
        if toml_val.get(forbidden_target).is_some() {
            return Err(CaptureError::UnsupportedMir(format!(
                "Cargo.toml must not declare [[{forbidden_target}]] targets"
            )));
        }
    }

    if let Some(lib_val) = toml_val.get("lib") {
        let Some(lib_tbl) = lib_val.as_table() else {
            return Err(CaptureError::UnsupportedMir(
                "[lib] in Cargo.toml must be a table".to_string(),
            ));
        };
        if let Some(path_val) = lib_tbl.get("path")
            && path_val.as_str() != Some("src/lib.rs")
        {
            return Err(CaptureError::UnsupportedMir(
                "[lib].path in Cargo.toml must be \"src/lib.rs\"".to_string(),
            ));
        }
        for pm_key in ["proc-macro", "proc_macro"] {
            if let Some(pm_val) = lib_tbl.get(pm_key)
                && pm_val.as_bool() != Some(false)
            {
                return Err(CaptureError::UnsupportedMir(
                    "proc-macro crates are not supported".to_string(),
                ));
            }
        }
        for ct_key in ["crate-type", "crate_type"] {
            if let Some(ct_val) = lib_tbl.get(ct_key) {
                let Some(arr) = ct_val.as_array() else {
                    return Err(CaptureError::UnsupportedMir(
                        "[lib].crate-type must be an array of strings"
                            .to_string(),
                    ));
                };
                for item in arr {
                    match item.as_str() {
                        Some("lib" | "rlib") => {}
                        _ => {
                            return Err(CaptureError::UnsupportedMir(format!(
                                "unsupported [lib].crate-type `{item}` (expected \"lib\" or \"rlib\")"
                            )));
                        }
                    }
                }
            }
        }
    }

    Ok(Some(toml_val))
}

fn load_crate_trust_policy(
    toml_opt: Option<&toml::Value>,
    cli_override: Option<&[String]>,
) -> Result<CrateTrustPolicy, String> {
    let mut policy = CrateTrustPolicy::default();
    if let Some(toml) = toml_opt {
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
    /// `trusted/lean/` and `trusted/audit/TrustedBoundary.lean`.
    pub anneal_root: Option<PathBuf>,
    /// Optional explicit path to the pinned Lean 4.34.1 binary.
    pub lean_bin: Option<PathBuf>,
    /// Optional explicit path to the `anneal-rustc-capture` binary.
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
    let _ = validate_target_crate_layout_and_manifest(crate_dir)?;
    let driver_bin = resolve_rustc_capture_bin(options)?;
    let mut cmd = sanitized_command(&driver_bin);

    let driver_toolchain_root = driver_bin
        .parent()
        .and_then(Path::parent)
        .filter(|root| root.join("rust/bin/rustc").is_file())
        .map(Path::to_path_buf)
        .or_else(setup::resolve_installed_compilers);
    if let Some(tc_root) = driver_toolchain_root {
        let rustc_path = tc_root.join("rust/bin/rustc");
        if rustc_path.is_file() {
            cmd.arg("--rustc").arg(&rustc_path);
        }
        let rust_lib = tc_root.join("rust/lib");
        if rust_lib.is_dir() {
            let lib_var = if cfg!(target_os = "macos") {
                "DYLD_LIBRARY_PATH"
            } else {
                "LD_LIBRARY_PATH"
            };
            cmd.env(lib_var, rust_lib);
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
    let toml_opt = validate_target_crate_layout_and_manifest(crate_dir)?;
    let channel = options.release_channel.unwrap_or_default();
    let policy = load_crate_trust_policy(
        toml_opt.as_ref(),
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

type PrefixCacheKey = (PathBuf, PathBuf, Option<PathBuf>);

/// Build or reuse a precompiled `.olean` prefix cache keyed by
/// `(audit_bin, anneal_root, lean_bin)`.
///
/// Only successful builds are inserted into the cache map so a transient or
/// negative-test failure with an invalid `anneal_root` never poisons
/// subsequent calls in the same process.
fn default_prefix_cache(
    audit_bin: &Path,
    anneal_root: &Path,
    lean_bin: Option<&Path>,
) -> Result<PathBuf, VerifyError> {
    static PREFIX_CACHE: OnceLock<Mutex<BTreeMap<PrefixCacheKey, PrefixCacheDir>>> =
        OnceLock::new();
    let cache_map = PREFIX_CACHE.get_or_init(|| Mutex::new(BTreeMap::new()));
    let key: PrefixCacheKey = (
        audit_bin.to_path_buf(),
        anneal_root.to_path_buf(),
        lean_bin.map(Path::to_path_buf),
    );

    if let Ok(guard) = cache_map.lock()
        && let Some(existing) = guard.get(&key)
        && existing.path.is_dir()
    {
        return Ok(existing.path.clone());
    }

    let dir = tempfile::Builder::new()
        .prefix("anneal-verify-prefix-")
        .tempdir()
        .map_err(|e| {
            VerifyError::Io(format!("failed to create prefix cache dir: {e}"))
        })?;
    let path = dir.path().to_path_buf();
    let mut cmd = sanitized_command(audit_bin);
    cmd.arg("--build-prefix-cache")
        .arg(&path)
        .arg("--anneal-root")
        .arg(anneal_root);
    if let Some(lean) = lean_bin {
        cmd.arg("--lean").arg(lean);
    }
    let out = cmd.output().map_err(|e| {
        VerifyError::Io(format!("failed to invoke {}: {e}", audit_bin.display()))
    })?;
    if !out.status.success() {
        return Err(VerifyError::AuditRejected {
            status_code: out.status.code(),
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        });
    }

    if let Ok(mut guard) = cache_map.lock() {
        guard.insert(
            key,
            PrefixCacheDir {
                _dir: dir,
                path: path.clone(),
            },
        );
    }
    Ok(path)
}

/// Validate the schema and security invariants of the JSON report returned by
/// `anneal-audit --verify-crate`.
fn validate_audit_report_json(
    crate_dir: &Path,
    report: &Json,
) -> Result<(), String> {
    if report.get("replay").and_then(Json::as_bool) != Some(true) {
        return Err("missing or false top-level `replay` field".to_string());
    }
    let Some(cv) = report.get("crateVerification").and_then(Json::as_object)
    else {
        return Err("missing `crateVerification` object in report".to_string());
    };
    if cv.get("verifiedTheorem").and_then(Json::as_str)
        != Some("Proof.verify_crate")
    {
        return Err(format!(
            "unexpected crateVerification.verifiedTheorem: {:?}",
            cv.get("verifiedTheorem")
        ));
    }
    if cv.get("expectedType").and_then(Json::as_str)
        != Some("Trusted.CrateTheorem Mir.crate")
    {
        return Err(format!(
            "unexpected crateVerification.expectedType: {:?}",
            cv.get("expectedType")
        ));
    }
    if cv.get("replay").and_then(Json::as_bool) != Some(true) {
        return Err(
            "missing or false `crateVerification.replay` field".to_string()
        );
    }
    let Some(axioms) = cv.get("axioms").and_then(Json::as_array) else {
        return Err(
            "missing `crateVerification.axioms` array in report".to_string()
        );
    };
    for ax in axioms {
        match ax.as_str() {
            Some("Quot.sound" | "propext") => {}
            other => {
                return Err(format!(
                    "disallowed axiom in crateVerification.axioms: {other:?}"
                ));
            }
        }
    }

    let Some(emitted) = cv.get("emittedArtifacts").and_then(Json::as_array)
    else {
        return Err(
            "missing `crateVerification.emittedArtifacts` array in report"
                .to_string(),
        );
    };
    let lib_rs_path = crate_dir.join("src/lib.rs");
    if let Ok(meta) = fs::symlink_metadata(&lib_rs_path)
        && !meta.file_type().is_symlink()
        && meta.is_file()
    {
        let disk_lib_rs = fs::read_to_string(&lib_rs_path).map_err(|e| {
            format!("cannot read {} for report check: {e}", lib_rs_path.display())
        })?;
        let matched = emitted.iter().any(|entry| {
            entry
                .as_array()
                .is_some_and(|pair| {
                    pair.len() == 2
                        && pair[0].as_str() == Some("src/lib.rs")
                        && pair[1].as_str() == Some(disk_lib_rs.as_str())
                })
        });
        if !matched {
            return Err(
                "`crateVerification.emittedArtifacts` does not contain matching `src/lib.rs` contents"
                    .to_string(),
            );
        }
    } else if emitted.is_empty() {
        return Err(
            "`crateVerification.emittedArtifacts` is empty".to_string()
        );
    }

    Ok(())
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

    let mut cmd = sanitized_command(&audit_bin);
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

    let stdout_str = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr_str = String::from_utf8_lossy(&output.stderr).into_owned();
    if !output.status.success() {
        return Err(VerifyError::AuditRejected {
            status_code: output.status.code(),
            stdout: stdout_str,
            stderr: stderr_str,
        });
    }

    let report: Json = serde_json::from_slice(&output.stdout).map_err(|e| {
        VerifyError::AuditRejected {
            status_code: output.status.code(),
            stdout: stdout_str.clone(),
            stderr: format!(
                "malformed JSON report from {}: {e}",
                audit_bin.display()
            ),
        }
    })?;

    if let Err(reason) = validate_audit_report_json(crate_dir, &report) {
        return Err(VerifyError::AuditRejected {
            status_code: output.status.code(),
            stdout: stdout_str,
            stderr: format!("invalid audit report from {}: {reason}", audit_bin.display()),
        });
    }

    Ok(report)
}

fn is_valid_anneal_root(dir: &Path) -> bool {
    dir.join("trusted/root-manifest.sha256").is_file()
        && dir.join("trusted/lean/foundation-lock.json").is_file()
}

/// Discover the Anneal workspace root by walking ancestors of `current_exe()`
/// and falling back to the compile-time `CARGO_MANIFEST_DIR` parent.
fn discover_checkout_root() -> Option<PathBuf> {
    if let Ok(exe) = env::current_exe() {
        for ancestor in exe.ancestors() {
            if is_valid_anneal_root(ancestor) {
                return Some(ancestor.to_path_buf());
            }
        }
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    if let Some(workspace_root) = manifest_dir.parent().and_then(Path::parent)
        && is_valid_anneal_root(workspace_root)
    {
        return Some(workspace_root.to_path_buf());
    }
    None
}

/// Resolve the Anneal repository or bundled exocrate `share/anneal` root from
/// `options`, `current_exe()` ancestors, `CARGO_MANIFEST_DIR`, or the
/// installed exocrate toolchain.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, VerifyError> {
    if let Some(root) = &options.anneal_root {
        return Ok(root.clone());
    }
    if let Some(checkout) = discover_checkout_root() {
        return Ok(checkout);
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

/// Resolve the pinned Lean binary from `options` or the installed toolchain
/// cache.
pub fn resolve_lean_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(lean) = &options.lean_bin {
        return Some(lean.clone());
    }
    setup::resolve_installed_compilers()
        .map(|tc_root| tc_root.join("lean/bin/lean"))
        .filter(|p| p.is_file())
}

/// Resolve the `anneal-rustc-capture` executable from `options`, a bundled
/// `share/anneal` toolchain layout, the local Cargo workspace, the installed
/// exocrate toolchain, or adjacent to the current executable.
pub fn resolve_rustc_capture_bin(
    options: &VerifyOptions,
) -> Result<PathBuf, CaptureError> {
    if let Some(bin) = &options.rustc_capture_bin {
        return Ok(bin.clone());
    }
    if let Some(root) = &options.anneal_root {
        if root.ends_with("share/anneal")
            && let Some(tc_root) = root.parent().and_then(Path::parent)
        {
            let bundled = tc_root.join("bin/anneal-rustc-capture");
            if bundled.is_file() {
                return Ok(bundled);
            }
        }
        if root.join("trusted/rustc-capture/Cargo.toml").is_file() {
            return resolve_or_build_workspace_bin(root, "anneal-rustc-capture")
                .map_err(CaptureError::Io);
        }
    }

    if let Some(workspace_root) = discover_checkout_root()
        && workspace_root
            .join("trusted/rustc-capture/Cargo.toml")
            .is_file()
    {
        return resolve_or_build_workspace_bin(
            &workspace_root,
            "anneal-rustc-capture",
        )
        .map_err(CaptureError::Io);
    }

    if let Some(tc_root) =
        setup::resolve_installed().or_else(setup::resolve_installed_compilers)
    {
        let bundled = tc_root.join("bin/anneal-rustc-capture");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    if let Some(sibling) = find_sibling_exe("anneal-rustc-capture") {
        return Ok(sibling);
    }

    Err(CaptureError::Io(
        "cannot locate trusted `anneal-rustc-capture` binary".to_string(),
    ))
}

/// Resolve the `anneal-audit` executable from a bundled `share/anneal`
/// toolchain layout, the local Cargo workspace, the installed exocrate
/// toolchain, or adjacent to the current executable.
pub fn resolve_audit_bin(options: &VerifyOptions) -> Result<PathBuf, VerifyError> {
    if let Some(root) = &options.anneal_root {
        if root.ends_with("share/anneal")
            && let Some(tc_root) = root.parent().and_then(Path::parent)
        {
            let bundled = tc_root.join("bin/anneal-audit");
            if bundled.is_file() {
                return Ok(bundled);
            }
        }
        if root.join("trusted/audit/Cargo.toml").is_file() {
            return resolve_or_build_workspace_bin(root, "anneal-audit")
                .map_err(VerifyError::Io);
        }
    }

    if let Some(workspace_root) = discover_checkout_root()
        && workspace_root.join("trusted/audit/Cargo.toml").is_file()
    {
        return resolve_or_build_workspace_bin(&workspace_root, "anneal-audit")
            .map_err(VerifyError::Io);
    }

    if let Some(tc_root) =
        setup::resolve_installed().or_else(setup::resolve_installed_compilers)
    {
        let bundled = tc_root.join("bin/anneal-audit");
        if bundled.is_file() {
            return Ok(bundled);
        }
    }

    if let Some(sibling) = find_sibling_exe("anneal-audit") {
        return Ok(sibling);
    }

    Err(VerifyError::Io(
        "cannot locate trusted `anneal-audit` binary".to_string(),
    ))
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

/// Build `bin_name` in `workspace_root` once per `(workspace_root, bin_name)`
/// pair in the current process, caching only successful builds.
fn resolve_or_build_workspace_bin(
    workspace_root: &Path,
    bin_name: &str,
) -> Result<PathBuf, String> {
    static BUILT_BINS: OnceLock<Mutex<BTreeMap<(PathBuf, String), PathBuf>>> =
        OnceLock::new();
    let map = BUILT_BINS.get_or_init(|| Mutex::new(BTreeMap::new()));
    let key = (workspace_root.to_path_buf(), bin_name.to_string());
    if let Ok(guard) = map.lock()
        && let Some(bin) = guard.get(&key)
        && bin.is_file()
    {
        return Ok(bin.clone());
    }

    let bin = build_workspace_bin(workspace_root, bin_name)?;
    if let Ok(mut guard) = map.lock() {
        guard.insert(key, bin.clone());
    }
    Ok(bin)
}

fn build_workspace_bin(
    workspace_root: &Path,
    bin_name: &str,
) -> Result<PathBuf, String> {
    let tc_root = setup::resolve_installed_compilers();
    let cargo_bin = tc_root
        .as_ref()
        .map(|tc| tc.join("rust/bin/cargo"))
        .filter(|p| p.is_file())
        .unwrap_or_else(|| PathBuf::from("cargo"));
    let mut cmd = sanitized_command(&cargo_bin);
    if let Some(tc) = &tc_root {
        let rustc = tc.join("rust/bin/rustc");
        if rustc.is_file() {
            cmd.env("RUSTC", rustc);
        }
        let rust_lib = tc.join("rust/lib");
        if rust_lib.is_dir() {
            let lib_var = if cfg!(target_os = "macos") {
                "DYLD_LIBRARY_PATH"
            } else {
                "LD_LIBRARY_PATH"
            };
            cmd.env(lib_var, rust_lib);
        }
    }
    let status = cmd
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
