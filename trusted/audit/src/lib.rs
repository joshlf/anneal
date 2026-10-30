// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted boundary and `.olean` environment auditor for Anneal.
//!
//! This module implements the outer host and process boundary gate that pairs
//! with `trusted/audit/TrustedBoundary.lean`. While `TrustedBoundary.lean`
//! inspects Lean syntax trees and compiled `.olean` kernel environments from
//! inside Lean, an inner Lean script cannot verify the host filesystem, Cargo
//! workspace manifests, Lean binary version admission, or the `--setup` flags
//! and environment variables used to invoke `lean` in the first place.
//!
//! Together, `audit.rs` and `TrustedBoundary.lean` enforce Anneal's three-tier
//! trust model:
//!
//! - **Vetted TCB (`trusted/`, `@[vetted]`):** Primitive Lean definitions and
//!   effectful Rust tools audited against the Rust Reference and enabled on
//!   both `alpha` and `stable` release channels.
//! - **Candidate-Trusted TCB (`trusted/`, `@[candidate <feature>]`):** TCB
//!   definitions and `rustc` capture rules whose bugs could cause a false
//!   verification result if used, but which have not yet completed Rust
//!   Reference auditing. Disabled by default (`VettedOnly`), forbidden on
//!   [`ReleaseChannel::Stable`], and usable on [`ReleaseChannel::Alpha`] only
//!   when the target crate explicitly opts in via
//!   `[package.metadata.anneal.trust-policy] allow-candidate-features` or
//!   `--allow-candidate-features`.
//! - **Untrusted (`theory/`, `.anneal/Proof.lean`):** Pure, effect-free Lean
//!   lemmas, symbolic evaluators, and per-crate proof scripts. Bugs in
//!   untrusted code must never cause a false verification result.
//!
//! Specifically, `audit.rs` and `TrustedBoundary.lean` enforce five invariants:
//!
//! 1. **Cargo DAG containment ([`check_cargo_boundary`]):** Because Rust code
//!    (including `build.rs` scripts and proc-macros) is effectful and not
//!    checked by the Lean kernel, every Cargo workspace member must reside
//!    under `trusted/` and no member may declare a `path` dependency outside
//!    `trusted/`.
//! 2. **Toolchain, source-tree, and foundation-lock admission
//!    ([`scan_lean_tree`], [`Checker::tool_admission`]):** Source directories
//!    (`trusted/lean/` and `theory/`) must contain only regular files and zero
//!    pre-existing `.olean`/`.ilean`/`.ir` artifacts (preventing pre-compiled
//!    `.olean` files from shadowing source compilation). The `lean` binary
//!    version must match `trusted/lean/foundation-lock.json` (Lean v4.34.1),
//!    and every `Init.*` module's `.lean` source and `.olean`/`.ir` companion
//!    parts must match the lock's presence/absence specification.
//! 3. **Hermetic preflight and synchronous `--setup` compilation
//!    ([`Checker::new_with_env`], [`Checker::write_setup_json`],
//!    [`Checker::compile_lean_module`]):** Ambient `LEAN_*`, `LAKE_*`,
//!    `ELAN_*`, and `DYLD_*` variables are stripped. Before any `.lean` file is
//!    compiled, `TrustedBoundary.lean` runs in `"preflight"` mode using only
//!    the locked `foundation` parser environment to reject forbidden syntax
//!    (`axiom`, `unsafe`, `partial`, `meta`, `native_decide`, `by_elab`,
//!    `#eval`, `set_option`, compiler-override attributes, etc.). Admitted
//!    modules are then compiled in topological order via `lean --setup
//!    <module>.setup.json -DElab.async=false -Ddebug.skipKernelTC=false`,
//!    binding every import directly to its staged `.olean` path.
//! 4. **Vetted vs. candidate non-contamination and module-origin separation
//!    (`TrustedBoundary.lean` `"audit"` mode):** In `Trusted.*`, `@[vetted]`
//!    types never reference `@[candidate]` constants, and `@[vetted]` bodies
//!    reference `@[candidate <feat>]` constants only inside `Trusted.candidate
//!    "<feat>" (...)` guards coupled one-to-one with matching on a `@[vetted]`
//!    inductive's `@[candidate <feat>]` constructors. Across modules, `Trusted`
//!    imports only `foundation ++ trusted`, `Anneal` (`theory/`) imports only
//!    `foundation ++ trusted ++ theory`, per-crate `Mir.lean` imports only
//!    `foundation ++ trusted` with `Mir.crate : Trusted.Crate`, and
//!    `Proof.lean` imports only `foundation ++ trusted ++ theory ++ #[Mir]`
//!    with `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`.
//! 5. **Zero custom axioms, kernel replay, and candidate-feature gating
//!    ([`Checker::verify_crate_with_policy`]):** All non-foundation constants
//!    are replayed from scratch through `base.toKernelEnv.replay` with only
//!    `{Classical.choice, Quot.sound, propext}` permitted, and any candidate
//!    features reached by `Mir` or `Proof` are checked against the active
//!    [`ReleaseChannel`] and [`CrateTrustPolicy`].

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use serde_json::json;
use walkdir::WalkDir;

/// JSON value representation used for `foundation-lock.json` and the
/// `TrustedBoundary.lean` IPC protocol.
pub type Json = serde_json::Value;

/// Pinned Lean 4 toolchain identifier required by `foundation-lock.json`.
pub const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// Compiled Lean artifact companion suffixes tracked by the foundation lock and
/// module compiler.
///
/// The first three suffixes (`olean`, `olean.server`, `olean.private`) form the
/// `.olean` artifact group passed to `Lean.ImportArtifacts`, and the last two
/// (`ir.sig`, `ir`) form the IR companion group.
pub const PARTS: [&str; 5] = [
    "olean",
    "olean.server",
    "olean.private",
    "ir.sig",
    "ir",
];

/// Subsystem candidate-trusted feature identifiers recognized by Anneal.
///
/// Must stay in sync with `TrustedBoundary.validCandidateFeatures` in
/// `trusted/audit/TrustedBoundary.lean`.
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
}

/// Per-crate candidate-feature trust policy.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CrateTrustPolicy {
    /// When `true` (`allow-candidate-features = ["*"]`), all candidate features
    /// in [`VALID_CANDIDATE_FEATURES`] are permitted on
    /// [`ReleaseChannel::Alpha`].
    pub allow_all: bool,
    /// Explicitly named candidate features permitted on
    /// [`ReleaseChannel::Alpha`].
    pub allowed_features: BTreeSet<String>,
}

impl CrateTrustPolicy {
    /// Default policy permitting only `@[vetted]` TCB declarations.
    pub fn vetted_only() -> Self {
        Self::default()
    }

    /// Parse and validate a list of candidate feature names (or `"*"`),
    /// rejecting any feature identifier outside [`VALID_CANDIDATE_FEATURES`].
    pub fn from_feature_list<I, S>(features: I) -> Result<Self, Failure>
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
                return Err(Failure::new(
                    1,
                    "candidate-policy",
                    format!(
                        "unknown candidate feature `{feat}` in allow-candidate-features"
                    ),
                ));
            }
        }
        Ok(policy)
    }

    /// Merge another [`CrateTrustPolicy`] into `self`.
    pub fn merge(&mut self, other: Self) {
        self.allow_all |= other.allow_all;
        self.allowed_features.extend(other.allowed_features);
    }

    /// Return `true` if `feature` is permitted under `channel` and `self`.
    pub fn is_allowed(&self, channel: ReleaseChannel, feature: &str) -> bool {
        match channel {
            ReleaseChannel::Stable => false,
            ReleaseChannel::Alpha => {
                self.allow_all || self.allowed_features.contains(feature)
            }
        }
    }
}

/// Resolve the target crate's [`CrateTrustPolicy`] from
/// `[package.metadata.anneal.trust-policy] allow-candidate-features` in
/// `crate_dir/Cargo.toml` and any explicit CLI/API override.
///
/// Defaults to [`CrateTrustPolicy::vetted_only`] when `Cargo.toml` is absent or
/// omits `allow-candidate-features`, so candidate TCB features never activate
/// without an explicit opt-in.
pub fn load_crate_trust_policy(
    crate_dir: &Path,
    cli_override: Option<&[String]>,
) -> Result<CrateTrustPolicy, Failure> {
    let mut policy = CrateTrustPolicy::vetted_only();
    let cargo_toml_path = crate_dir.join("Cargo.toml");
    if fs::symlink_metadata(&cargo_toml_path).is_ok() {
        regular(&cargo_toml_path, "candidate-policy")?;
        let text = fs::read_to_string(&cargo_toml_path).map_err(|e| {
            Failure::new(
                1,
                "candidate-policy",
                format!("cannot read {}: {e}", cargo_toml_path.display()),
            )
        })?;
        let toml: toml::Value = toml::from_str(&text).map_err(|e| {
            Failure::new(
                1,
                "candidate-policy",
                format!(
                    "malformed Cargo.toml in {}: {e}",
                    cargo_toml_path.display()
                ),
            )
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
                Failure::new(
                    1,
                    "candidate-policy",
                    "allow-candidate-features in Cargo.toml must be an array of strings",
                )
            })?;
            let mut names = Vec::with_capacity(arr.len());
            for item in arr {
                let s = item.as_str().ok_or_else(|| {
                    Failure::new(
                        1,
                        "candidate-policy",
                        "allow-candidate-features in Cargo.toml must contain only strings",
                    )
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

/// Cache key for [`CachedVerifyPrefix`], binding the canonical repository root,
/// canonical Lean binary path, and exact raw bytes of every `.lean` source file
/// in `trusted/lean/`, `theory/`, and `trusted/audit/TrustedBoundary.lean`.
#[derive(Clone, PartialEq, Eq)]
struct VerifyPrefixKey {
    checkout: PathBuf,
    lean: PathBuf,
    key_sha256: String,
    sources: BTreeMap<String, Vec<u8>>,
}

/// Staged `.olean` or `.ir` file cached in memory across `verify_crate` runs.
#[derive(Clone)]
struct CachedArtifactFile {
    rel_path: String,
    bytes: Vec<u8>,
}

/// In-memory cache of the compiled and audited repository prefix (`Trusted` and
/// `Anneal` modules) so repeated `verify_crate` calls in the same process do
/// not recompile `trusted/lean/` and `theory/` when their sources are
/// unchanged.
#[derive(Clone)]
struct CachedVerifyPrefix {
    key: VerifyPrefixKey,
    report: Json,
    compiled_artifacts_rel: BTreeMap<String, Vec<Vec<String>>>,
    graph: serde_json::Map<String, Json>,
    trust_declarations: Vec<Json>,
    files: Vec<CachedArtifactFile>,
}

static VERIFY_PREFIX_CACHE: Mutex<Option<CachedVerifyPrefix>> =
    Mutex::new(None);

/// Structured audit failure distinguishing policy rejections (`code == 1`)
/// from operational or environment failures (`code == 2`).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct Failure {
    /// Process exit code (`1` for policy rejection, `2` for operational error).
    pub code: i32,
    /// Audit phase in which the failure occurred.
    pub phase: String,
    /// Human-readable diagnostic message.
    pub message: String,
}

impl Failure {
    /// Construct a new [`Failure`].
    pub fn new(
        code: i32,
        phase: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code,
            phase: phase.into(),
            message: message.into(),
        }
    }
}

/// Verify that `path` exists and is a regular file (not a symlink, directory,
/// FIFO, or device node) using `symlink_metadata` so symlinks are never
/// silently followed.
pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot inspect {}: {e}", path.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
        return Err(Failure::new(
            1,
            phase,
            format!("expected a regular file: {}", path.display()),
        ));
    }
    Ok(())
}

/// Compute the lowercase hex-encoded FIPS 180-4 SHA-256 digest of `data`.
pub fn sha256_bytes(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
        0x1f83d9ab, 0x5be0cd19,
    ];
    let bit_len = (data.len() as u64) * 8;
    let mut padded = Vec::with_capacity((data.len() + 72) & !63);
    padded.extend_from_slice(data);
    padded.push(0x80);
    while (padded.len() % 64) != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 =
                w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 =
                w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }
    format!(
        "{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}",
        h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]
    )
}

/// Verify that `path` is a regular file and return its lowercase hex SHA-256
/// digest.
pub fn sha256_file(path: &Path, phase: &str) -> Result<String, Failure> {
    regular(path, phase)?;
    let bytes = fs::read(path).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot read {}: {e}", path.display()),
        )
    })?;
    Ok(sha256_bytes(&bytes))
}

/// Copy a regular source file `src` to `dst`, creating parent directories as
/// needed, and return the SHA-256 digest of the copied bytes.
fn stage_regular_file(
    src: &Path,
    dst: &Path,
    phase: &str,
) -> Result<String, Failure> {
    regular(src, phase)?;
    let bytes = fs::read(src).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot read {}: {e}", src.display()),
        )
    })?;
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::new(
                2,
                phase,
                format!("cannot create {}: {e}", parent.display()),
            )
        })?;
    }
    fs::write(dst, &bytes).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot write {}: {e}", dst.display()),
        )
    })?;
    Ok(sha256_bytes(&bytes))
}

/// Return `true` if `s` is a 64-character ASCII hex digest.
fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Return `true` if `s` is a valid ASCII Lean module identifier component.
fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at the repository root.
fn reject_cargo_toolchain_overrides(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for forbidden in [
        ".cargo",
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        if fs::symlink_metadata(checkout.join(forbidden)).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!("forbidden Cargo/toolchain override at repository root: {forbidden}"),
            ));
        }
    }
    Ok(())
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`] whenever any Cargo or root-manifest TCB file is
/// present.
fn check_checkout_cargo_hygiene(checkout: &Path) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if ["Cargo.toml", "Cargo.lock", "trusted/root-manifest.sha256", "trusted/rustc-capture"]
        .iter()
        .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
    }
    Ok(())
}

/// Verify Cargo workspace DAG containment, root Cargo/toolchain hygiene,
/// `Cargo.lock` dependency provenance, and `trusted/root-manifest.sha256` (when
/// present): all workspace crates must reside under `trusted/`, and no
/// workspace crate may depend on a path outside `trusted/`.
///
/// Unlike Lean modules in `theory/`, which are restricted to pure definitions
/// and checked by the Lean 4 kernel, Rust crates can execute arbitrary code at
/// build time (`build.rs`, proc-macros) and runtime (`std::process`,
/// `std::fs`). Consequently, every Rust crate in the repository is part of the
/// effectful TCB and must live inside `trusted/`.
pub fn check_cargo_boundary(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    reject_cargo_toolchain_overrides(checkout)?;
    let root_toml_path = checkout.join("Cargo.toml");
    let trusted_toml_path = checkout.join("trusted/rustc-capture/Cargo.toml");
    regular(&root_toml_path, phase)?;
    regular(&trusted_toml_path, phase)?;

    let manifest_path = checkout.join("trusted/root-manifest.sha256");
    if fs::symlink_metadata(&manifest_path).is_ok() {
        regular(&manifest_path, phase)?;
        let manifest_text = fs::read_to_string(&manifest_path).map_err(|e| {
            Failure::new(1, phase, format!("cannot read root-manifest.sha256: {e}"))
        })?;
        let mut seen_manifest_paths = BTreeSet::new();
        for raw_line in manifest_text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let Some((expected_hex, rel_path)) = line.split_once("  ") else {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("malformed line in root-manifest.sha256: {line}"),
                ));
            };
            if !is_sha256_hex(expected_hex)
                || !Path::new(rel_path)
                    .components()
                    .all(|c| matches!(c, std::path::Component::Normal(_)))
                || !seen_manifest_paths.insert(rel_path.to_string())
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("invalid or duplicate entry in root-manifest.sha256: {line}"),
                ));
            }
            let actual_hex = sha256_file(&checkout.join(rel_path), phase).map_err(
                |e| Failure::new(1, phase, e.message),
            )?;
            if !actual_hex.eq_ignore_ascii_case(expected_hex) {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "root TCB manifest digest mismatch for {rel_path}: expected {expected_hex}, got {actual_hex}"
                    ),
                ));
            }
        }
        for required_rel in ["Cargo.toml", "flake.nix", "flake.lock"] {
            if !seen_manifest_paths.contains(required_rel) {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("root-manifest.sha256 missing required entry: {required_rel}"),
                ));
            }
        }
    }

    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_ok() {
        regular(&lock_path, phase)?;
        let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
            Failure::new(1, phase, format!("cannot read Cargo.lock: {e}"))
        })?;
        let lock_toml: toml::Value = toml::from_str(&lock_text).map_err(|e| {
            Failure::new(1, phase, format!("malformed Cargo.lock: {e}"))
        })?;
        if let Some(pkgs) = lock_toml.get("package").and_then(toml::Value::as_array) {
            for pkg in pkgs {
                if let Some(src) = pkg.get("source").and_then(toml::Value::as_str) {
                    let pkg_name = pkg
                        .get("name")
                        .and_then(toml::Value::as_str)
                        .unwrap_or("<unknown>");
                    if src != "registry+https://github.com/rust-lang/crates.io-index" {
                        return Err(Failure::new(
                            1,
                            phase,
                            format!(
                                "untrusted dependency source in Cargo.lock for {pkg_name}: {src}"
                            ),
                        ));
                    }
                    let has_checksum = pkg
                        .get("checksum")
                        .and_then(toml::Value::as_str)
                        .is_some_and(is_sha256_hex);
                    if !has_checksum {
                        return Err(Failure::new(
                            1,
                            phase,
                            format!("missing or invalid checksum in Cargo.lock for {pkg_name}"),
                        ));
                    }
                }
            }
        }
    }

    let root_text = fs::read_to_string(&root_toml_path).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;
    let root_toml: toml::Value = toml::from_str(&root_text).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;
    let root_obj = root_toml.as_table().ok_or_else(|| {
        Failure::new(1, phase, "root Cargo.toml must be a TOML table")
    })?;
    if root_obj.keys().any(|k| k != "workspace") {
        return Err(Failure::new(
            1,
            phase,
            "root Cargo.toml may contain only [workspace]",
        ));
    }
    let ws_obj = root_obj
        .get("workspace")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| {
            Failure::new(1, phase, "missing [workspace] table in root Cargo.toml")
        })?;
    if ws_obj.keys().any(|k| k != "members" && k != "resolver") {
        return Err(Failure::new(
            1,
            phase,
            "root [workspace] may contain only `members` and `resolver`",
        ));
    }
    if let Some(res) = ws_obj.get("resolver")
        && res.as_str() != Some("2")
    {
        return Err(Failure::new(
            1,
            phase,
            "root [workspace] resolver must be \"2\"",
        ));
    }

    let members = ws_obj
        .get("members")
        .and_then(toml::Value::as_array)
        .ok_or_else(|| {
            Failure::new(1, phase, "missing workspace.members in root Cargo.toml")
        })?;

    let checkout_canon = fs::canonicalize(checkout).map_err(|e| {
        Failure::new(2, phase, format!("cannot canonicalize checkout: {e}"))
    })?;

    let mut has_rustc_capture = false;

    for member_val in members {
        let member = member_val.as_str().ok_or_else(|| {
            Failure::new(1, phase, "non-string workspace member")
        })?;
        let is_clean_rel = Path::new(member)
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)));
        if !is_clean_rel || !member.starts_with("trusted/") {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace member outside trusted/: {member}"),
            ));
        }
        if member == "trusted/rustc-capture" {
            has_rustc_capture = true;
        }
        let member_toml_path = checkout.join(member).join("Cargo.toml");
        regular(&member_toml_path, phase)?;
        let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("malformed member Cargo.toml in {member}: {e}"),
            )
        })?;
        let member_toml: toml::Value =
            toml::from_str(&member_text).map_err(|e| {
                Failure::new(
                    1,
                    phase,
                    format!("malformed member Cargo.toml in {member}: {e}"),
                )
            })?;
        let _pkg_name = member_toml
            .get("package")
            .and_then(|p| p.get("name"))
            .and_then(toml::Value::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("missing package.name in {member}"),
                )
            })?;

        let member_parent = member_toml_path.parent().unwrap();
        // Canonicalize each `path` dependency before checking its prefix
        // against `checkout_canon` so `..` segments or symlinks cannot escape
        // `trusted/`.
        let check_dep_table = |table_opt: Option<&toml::Value>,
                               section: &str|
         -> Result<(), Failure> {
            let Some(table_val) = table_opt else {
                return Ok(());
            };
            let table = table_val.as_table().ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("invalid {section} in {member}/Cargo.toml"),
                )
            })?;
            for (_dep_name, spec) in table {
                if let Some(spec_obj) = spec.as_table()
                    && let Some(dep_path) =
                        spec_obj.get("path").and_then(toml::Value::as_str)
                {
                    let joined = member_parent.join(dep_path);
                    let resolved = fs::canonicalize(&joined).map_err(|_| {
                        Failure::new(
                            1,
                            phase,
                            format!(
                                "{member} path dependency target does not exist: {dep_path}"
                            ),
                        )
                    })?;
                    let rel = resolved
                        .strip_prefix(&checkout_canon)
                        .map_err(|_| {
                            Failure::new(
                                1,
                                phase,
                                format!(
                                    "{member} path dependency escapes checkout: {dep_path}"
                                ),
                            )
                        })?;
                    let rel_str = rel.to_string_lossy().replace('\\', "/");
                    if !rel_str.starts_with("trusted/") {
                        return Err(Failure::new(
                            1,
                            phase,
                            format!(
                                "{member} path dependency points outside trusted/: {rel_str}"
                            ),
                        ));
                    }
                    regular(&resolved.join("Cargo.toml"), phase)?;
                }
            }
            Ok(())
        };

        // Check `dev-dependencies`, `build-dependencies`, and target-specific
        // dependency tables in addition to `dependencies`, because `cargo test`
        // and `build.rs` compile and execute code from all of them.
        for section in
            ["dependencies", "dev-dependencies", "build-dependencies"]
        {
            check_dep_table(member_toml.get(section), section)?;
        }
        if let Some(targets) =
            member_toml.get("target").and_then(toml::Value::as_table)
        {
            for (cfg_name, cfg_table) in targets {
                if let Some(cfg_obj) = cfg_table.as_table() {
                    for section in [
                        "dependencies",
                        "dev-dependencies",
                        "build-dependencies",
                    ] {
                        let label = format!("target.{cfg_name}.{section}");
                        check_dep_table(cfg_obj.get(section), &label)?;
                    }
                }
            }
        }
    }
    if !has_rustc_capture {
        return Err(Failure::new(
            1,
            phase,
            "trusted/rustc-capture missing from workspace.members",
        ));
    }

    Ok(())
}

/// Scan a Lean directory tree (`trusted/lean` with `"Trusted"` or `theory`
/// with `"Anneal"`), rejecting symlinks, non-`.lean` files, and compiled
/// artifacts in the source tree and returning the map from dot-separated module
/// name to `.lean` path.
///
/// Enforces three filesystem-level invariants:
/// 1. `root` and every directory or file beneath it must be a real directory or
///    regular file (never a symlink), preventing symlink indirection outside
///    the audited tree.
/// 2. No compiled Lean artifacts (`.olean`, `.olean.server`, `.olean.private`,
///    `.ir.sig`, `.ir`, or `.ilean`) or unrecognized non-`.lean` files may
///    exist in the source tree, ensuring that every project module is freshly
///    compiled inside the isolated staging directory after passing
///    `"preflight"`.
/// 3. Every `.lean` file path must map to `<umbrella_prefix>(.<ident>)*`, and
///    `<umbrella_prefix>.lean` must exist, binding `trusted/lean/` to the
///    `Trusted` namespace root and `theory/` to the `Anneal` namespace root.
pub fn scan_lean_tree(
    root: &Path,
    umbrella_prefix: &str,
) -> Result<BTreeMap<String, PathBuf>, Failure> {
    let meta = fs::symlink_metadata(root).map_err(|_| {
        Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        ));
    }

    let mut modules = BTreeMap::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .sort_by_file_name()
        .into_iter()
        .skip(1)
    {
        let entry = entry.map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot read {}: {e}", root.display()),
            )
        })?;
        let path = entry.path().to_path_buf();
        if entry.file_type().is_symlink() {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected symlink in source tree: {}", path.display()),
            ));
        }
        if entry.file_type().is_dir() {
            continue;
        }
        regular(&path, "snapshot")?;

        let rel_path = path.strip_prefix(root).unwrap();
        let relative = rel_path.to_string_lossy().replace('\\', "/");
        if PARTS
            .iter()
            .any(|part| relative.ends_with(&format!(".{part}")))
            || relative.ends_with(".ilean")
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("compiled artifact in source root: {relative}"),
            ));
        }

        if let Some(stem) = relative.strip_suffix(".lean") {
            let components: Vec<&str> = stem.split('/').collect();
            if components.first().copied() != Some(umbrella_prefix)
                || !components.iter().copied().all(is_lean_ident)
            {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("unmappable Lean source: {relative}"),
                ));
            }
            let module = components.join(".");
            if modules.contains_key(&module) {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("duplicate module: {module}"),
                ));
            }
            modules.insert(module, path);
        } else if !(umbrella_prefix == "Trusted"
            && (relative == "lean-toolchain" || relative == "foundation-lock.json"))
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected non-Lean file in source tree: {relative}"),
            ));
        }
    }

    if (umbrella_prefix == "Trusted" || !modules.is_empty())
        && !modules.contains_key(umbrella_prefix)
    {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("missing {umbrella_prefix}.lean umbrella"),
        ));
    }
    Ok(modules)
}

/// Pinned SHA-256 digests of the official Lean 4.34.1 `bin/lean` binaries from
/// `trusted/lean/foundation-lock.json`.
const LOCKED_LEAN_SHA256: [&str; 4] = [
    "79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085",
    "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
    "998f0cc2a5a754cc66df1f33b85e1447528737ff15012db35d8c501754b02f1e",
    "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
];

/// Resolve the default pinned Lean 4.34.1 binary path when none is explicitly
/// provided, selecting a candidate binary whose SHA-256 matches
/// `LOCKED_LEAN_SHA256`.
pub fn default_lean_path() -> PathBuf {
    if let Some(env_lean) = env::var_os("ANNEAL_LEAN_BIN") {
        return PathBuf::from(env_lean);
    }
    let home = dirs::home_dir().unwrap_or_else(|| PathBuf::from("/root"));
    let mut candidate_paths = Vec::new();
    for base in dirs::cache_dir()
        .into_iter()
        .chain(std::iter::once(home.clone()))
    {
        let tc_base = base.join(".anneal/toolchain");
        if let Ok(entries) = fs::read_dir(&tc_base) {
            let mut dirs: Vec<(std::time::SystemTime, PathBuf)> = entries
                .filter_map(Result::ok)
                .map(|e| e.path().join("lean/bin/lean"))
                .filter(|p| p.is_file())
                .map(|p| {
                    let mtime = fs::metadata(&p)
                        .and_then(|m| m.modified())
                        .unwrap_or(std::time::UNIX_EPOCH);
                    (mtime, p)
                })
                .collect();
            dirs.sort_by(|a, b| b.0.cmp(&a.0));
            candidate_paths.extend(dirs.into_iter().map(|(_, p)| p));
        }
    }
    let elan_lean =
        home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
    if elan_lean.is_file() {
        candidate_paths.push(elan_lean.clone());
    }
    for cand in &candidate_paths {
        if let Ok(digest) = sha256_file(cand, "toolchain")
            && LOCKED_LEAN_SHA256.contains(&digest.as_str())
        {
            return cand.clone();
        }
    }
    candidate_paths.into_iter().next().unwrap_or(elan_lean)
}

/// Stateful boundary and crate-verification auditor managing an isolated
/// staging directory (`stage`, owned by `_stage_dir`).
///
/// As [`Checker::run`] and [`Checker::verify_crate_with_policy`] progress,
/// `Checker` populates `artifacts` (mapping each admitted module name to its
/// staged `.olean` and `.ir` file groups) and `graph` (mapping each module name
/// to its `"preflight"`-admitted import list) so that every `lean --setup`
/// invocation and `TrustedBoundary.lean` `"audit"` request operates on a
/// closed, explicitly bound set of module files.
pub struct Checker {
    _stage_dir: tempfile::TempDir,
    pub checkout: PathBuf,
    pub source: PathBuf,
    pub lean: PathBuf,
    pub stage: PathBuf,
    pub phase: String,
    pub execution_began: bool,
    pub counter: usize,
    pub environment: BTreeMap<String, String>,
    pub artifacts: BTreeMap<String, Vec<Vec<String>>>,
    pub graph: serde_json::Map<String, Json>,
    pub modules: BTreeMap<String, PathBuf>,
    pub theory_modules: BTreeMap<String, PathBuf>,
    pub inspector: PathBuf,
    pub lock: Json,
    pub version: String,
    pub prefix: PathBuf,
    pub foundation: Vec<String>,
    pub trust_declarations: Vec<Json>,
    pub prefix_cache_dir: Option<PathBuf>,
}

impl Checker {
    /// Create a new [`Checker`] with a fresh private staging directory.
    pub fn new(checkout: &Path, lean: Option<&Path>) -> io::Result<Self> {
        Self::new_with_env(checkout, lean, env::vars())
    }

    /// Create a new [`Checker`] using a closed environment allowlist.
    ///
    /// Retains only `HOME`, `TMPDIR`, `LANG`, and `LC_ALL` from `ambient_env`
    /// and pins `PATH` to `/usr/bin:/bin` so ambient search paths (`LEAN_PATH`,
    /// `LEAN_SRC_PATH`), toolchain overrides (`ELAN_TOOLCHAIN`), or dynamic
    /// linker preloading (`LD_PRELOAD`, `LD_LIBRARY_PATH`,
    /// `DYLD_INSERT_LIBRARIES`) cannot influence child `lean` invocations.
    pub fn new_with_env<I>(
        checkout: &Path,
        lean: Option<&Path>,
        ambient_env: I,
    ) -> io::Result<Self>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let checkout = fs::canonicalize(checkout)?;
        let source = checkout.join("trusted/lean");
        let lean_raw = match lean {
            Some(p) => p.to_path_buf(),
            None => default_lean_path(),
        };
        let lean = if lean_raw.is_absolute() {
            lean_raw
        } else {
            env::current_dir()?.join(lean_raw)
        };
        let stage_dir = tempfile::Builder::new()
            .prefix("anneal-trusted-")
            .tempdir()?;
        let stage = stage_dir.path().to_path_buf();

        let mut environment = BTreeMap::new();
        for (k, v) in ambient_env {
            if matches!(k.as_str(), "HOME" | "TMPDIR" | "LANG" | "LC_ALL") {
                environment.insert(k, v);
            }
        }
        environment.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

        Ok(Self {
            _stage_dir: stage_dir,
            checkout,
            source,
            lean,
            stage,
            phase: "admission".to_string(),
            execution_began: false,
            counter: 0,
            environment,
            artifacts: BTreeMap::new(),
            graph: serde_json::Map::new(),
            modules: BTreeMap::new(),
            theory_modules: BTreeMap::new(),
            inspector: PathBuf::new(),
            lock: json!({}),
            version: String::new(),
            prefix: PathBuf::new(),
            foundation: Vec::new(),
            trust_declarations: Vec::new(),
            prefix_cache_dir: None,
        })
    }

    /// Execute `self.lean` with `arguments` in the sanitized `self.environment`
    /// with `self.stage` as the working directory.
    pub fn process(
        &mut self,
        label: &str,
        arguments: &[String],
    ) -> Result<String, Failure> {
        self.phase = label.to_string();
        self.counter += 1;
        let output = Command::new(&self.lean)
            .args(arguments)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment)
            .output()
            .map_err(|e| {
                Failure::new(2, label, format!("could not execute Lean: {e}"))
            })?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let detail = if stderr.trim().is_empty() {
                stdout.trim()
            } else {
                stderr.trim()
            };
            return Err(Failure::new(
                2,
                label,
                format!("Lean exited {:?}: {detail}", output.status.code()),
            ));
        }
        String::from_utf8(output.stdout).map_err(|e| {
            Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}"))
        })
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    ///
    /// Passing `--setup` to `lean` binds every module import directly to its
    /// staged `.olean` file path in `importArts` (bypassing `LEAN_PATH` search
    /// directories) and forces `isModule: false`, `dynlibs: []`,
    /// `plugins: []`, and `options: {}` so no native plugins, shared libraries,
    /// or ambient compiler options can be injected.
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[Json],
    ) -> Result<PathBuf, Failure> {
        let setup_obj = json!({
            "name": module,
            "isModule": false,
            "imports": imports,
            "importArts": &self.artifacts,
            "dynlibs": [],
            "plugins": [],
            "options": {},
        });
        let setup_path = self.stage.join(format!("{module}.setup.json"));
        let bytes = serde_json::to_vec(&setup_obj)
            .map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        fs::write(&setup_path, bytes)
            .map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        Ok(setup_path)
    }

    /// Invoke `TrustedBoundary.lean` in `mode` (`"preflight"` or `"audit"`)
    /// with `extra_fields` and validate the structured response envelope.
    ///
    /// Distinguishes policy rejections (exit code 1 accompanied by a valid
    /// `{"ok": false, "category": "policy", "message": "policy:..."}` JSON
    /// payload) from operational or crash failures (exit code 2).
    pub fn inspect(
        &mut self,
        mode: &str,
        extra_fields: BTreeMap<String, Json>,
    ) -> Result<Json, Failure> {
        self.phase = mode.to_string();
        let arts_arr: Vec<Json> = self
            .artifacts
            .iter()
            .map(|(k, parts)| json!([k, parts]))
            .collect();
        let default_graph = if mode == "preflight" {
            self.lock.get("graph").cloned().unwrap_or_else(|| json!({}))
        } else {
            Json::Object(self.graph.clone())
        };
        let axioms = self
            .lock
            .get("axioms")
            .cloned()
            .unwrap_or_else(|| json!([]));
        let mut req = json!({
            "mode": mode,
            "sysroot": self.prefix.to_string_lossy(),
            "artifacts": arts_arr,
            "foundation": &self.foundation,
            "graph": default_graph,
            "axioms": axioms,
        });
        let req_obj = req.as_object_mut().unwrap();
        for (k, v) in extra_fields {
            req_obj.insert(k, v);
        }

        self.counter += 1;
        let stem = self
            .stage
            .join(format!("request-{:03}-{mode}", self.counter));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path =
            PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(&req).map_err(|e| {
            Failure::new(2, mode, format!("cannot serialize request: {e}"))
        })?;
        fs::write(&request_path, req_bytes).map_err(|e| {
            Failure::new(2, mode, format!("cannot write request: {e}"))
        })?;

        let args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "--run".to_string(),
            self.inspector.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        let output = Command::new(&self.lean)
            .args(&args)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment)
            .output()
            .map_err(|e| {
                Failure::new(2, mode, format!("could not execute Lean: {e}"))
            })?;

        if !output.status.success() {
            if output.status.code() == Some(1)
                && result_path.is_file()
                && let Ok(text) = fs::read_to_string(&result_path)
                && let Ok(resp) = serde_json::from_str::<Json>(&text)
                && let Some(obj) = resp.as_object()
                && obj.len() == 3
                && obj.get("ok").and_then(Json::as_bool) == Some(false)
                && obj.get("category").and_then(Json::as_str) == Some("policy")
                && let Some(msg) = obj
                    .get("message")
                    .and_then(Json::as_str)
                    .filter(|s| s.starts_with("policy:"))
            {
                return Err(Failure::new(1, mode, msg));
            }
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::new(
                2,
                mode,
                format!(
                    "Lean exited {:?}: {}",
                    output.status.code(),
                    stderr.trim()
                ),
            ));
        }

        let resp_text = fs::read_to_string(&result_path).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("missing/malformed inspector result: {e}"),
            )
        })?;
        let resp: Json = serde_json::from_str(&resp_text).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("missing/malformed inspector result: {e}"),
            )
        })?;
        let Some(resp_obj) = resp.as_object() else {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        };
        if resp_obj.len() != 2
            || resp_obj.get("ok").and_then(Json::as_bool) != Some(true)
            || !resp_obj
                .get("result")
                .is_some_and(|r| r.as_object().is_some())
        {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        Ok(resp_obj.get("result").unwrap().clone())
    }

    /// Scan `root` via [`scan_lean_tree`] and copy every discovered `.lean`
    /// file into `self.stage.join(stage_subdir)` via [`stage_regular_file`].
    fn scan_and_stage_tree(
        &self,
        root: &Path,
        umbrella_prefix: &str,
        stage_subdir: &str,
    ) -> Result<BTreeMap<String, PathBuf>, Failure> {
        let raw_modules = scan_lean_tree(root, umbrella_prefix)?;
        let mut staged_modules = BTreeMap::new();
        for (mod_name, raw_path) in raw_modules {
            let staged_path = self
                .stage
                .join(stage_subdir)
                .join(format!("{}.lean", mod_name.replace('.', "/")));
            stage_regular_file(&raw_path, &staged_path, "snapshot")?;
            staged_modules.insert(mod_name, staged_path);
        }
        Ok(staged_modules)
    }

    /// Scan and stage `theory/` (when present) into `self.stage/src/theory`.
    fn stage_theory_modules(&mut self) -> Result<(), Failure> {
        let theory_dir = self.checkout.join("theory");
        self.theory_modules = if fs::symlink_metadata(&theory_dir).is_ok() {
            self.scan_and_stage_tree(&theory_dir, "Anneal", "src/theory")?
        } else {
            BTreeMap::new()
        };
        Ok(())
    }

    /// Snapshot and stage `trusted/lean/` and `TrustedBoundary.lean`, and
    /// verify the pinned Lean 4.34.1 binary and `Init.*` artifacts by SHA-256
    /// digest against `foundation-lock.json`.
    ///
    /// Specifically checks:
    /// 1. `trusted/lean/foundation-lock.json` has `schema == 1` and
    ///    `toolchain == "leanprover/lean4:v4.34.1"`, matching
    ///    `trusted/lean/lean-toolchain`.
    /// 2. `self.lean`'s SHA-256 digest matches one of the locked
    ///    `distributions` entries *before* executing `self.lean --version`, and
    ///    `self.lean --version` maps to that exact SHA-256 digest.
    /// 3. Every `Init.*` module in `foundation-lock.json` has a regular `.lean`
    ///    source file under `<prefix>/src/lean/` matching `sourceSha256`, and
    ///    its `.olean`/`.ir` companion parts under `<prefix>/lib/lean/` match
    ///    the lock's SHA-256 digests (`null` parts must not exist on disk).
    pub fn tool_admission(&mut self) -> Result<(), Failure> {
        self.modules =
            self.scan_and_stage_tree(&self.source, "Trusted", "src/trusted")?;

        let inspector_src =
            self.checkout.join("trusted/audit/TrustedBoundary.lean");
        let staged_inspector = self.stage.join("src/TrustedBoundary.lean");
        stage_regular_file(&inspector_src, &staged_inspector, "tool-snapshot")?;
        self.inspector = staged_inspector;

        let lock_path = self.source.join("foundation-lock.json");
        regular(&lock_path, "lock")?;
        let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
            Failure::new(
                2,
                "lock",
                format!("cannot read foundation lock: {e}"),
            )
        })?;
        let lock: Json = serde_json::from_str(&lock_text).map_err(|e| {
            Failure::new(2, "lock", format!("cannot read foundation lock: {e}"))
        })?;
        let Some(lock_obj) = lock.as_object() else {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        };
        if lock_obj.get("schema").and_then(Json::as_i64) != Some(1)
            || lock_obj.get("toolchain").and_then(Json::as_str)
                != Some(TOOLCHAIN)
        {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        }
        self.lock = lock;

        let toolchain_path = self.source.join("lean-toolchain");
        regular(&toolchain_path, "lock")?;
        let toolchain_text =
            fs::read_to_string(&toolchain_path).map_err(|e| {
                Failure::new(
                    2,
                    "lock",
                    format!("cannot read lean-toolchain: {e}"),
                )
            })?;
        if toolchain_text.trim() != TOOLCHAIN {
            return Err(Failure::new(
                1,
                "lock",
                "lean-toolchain differs from lock",
            ));
        }

        let lean_sha = sha256_file(&self.lean, "toolchain")?;
        self.lean = fs::canonicalize(&self.lean).map_err(|e| {
            Failure::new(2, "toolchain", format!("cannot resolve lean: {e}"))
        })?;
        let Some(dist_obj) = self
            .lock
            .get("distributions")
            .and_then(Json::as_object)
            .cloned()
        else {
            return Err(Failure::new(
                2,
                "lock",
                "missing distributions table in foundation lock",
            ));
        };
        if !dist_obj.values().any(|v| {
            v.as_str()
                .is_some_and(|s| is_sha256_hex(s) && s.eq_ignore_ascii_case(&lean_sha))
        }) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean binary SHA-256 differs from lock: {lean_sha}"
                ),
            ));
        }

        let actual_version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
        let Some(expected_lean_sha) =
            dist_obj.get(&actual_version).and_then(Json::as_str)
        else {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean version/commit differs from lock: {actual_version}"
                ),
            ));
        };
        if !expected_lean_sha.eq_ignore_ascii_case(&lean_sha) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean binary SHA-256 mismatch for {actual_version}: expected {expected_lean_sha}, got {lean_sha}"
                ),
            ));
        }
        self.version = actual_version;

        let prefix_raw = self
            .process("prefix", &["--print-prefix".to_string()])?
            .trim()
            .to_string();
        self.prefix = fs::canonicalize(&prefix_raw).map_err(|e| {
            Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}"))
        })?;

        let Some(modules_map) = self
            .lock
            .get("modules")
            .and_then(Json::as_object)
            .cloned()
        else {
            return Err(Failure::new(
                2,
                "lock",
                "missing modules table in foundation lock",
            ));
        };
        let Some(graph_map) = self
            .lock
            .get("graph")
            .and_then(Json::as_object)
            .cloned()
        else {
            return Err(Failure::new(
                2,
                "lock",
                "missing graph table in foundation lock",
            ));
        };
        self.foundation = modules_map.keys().cloned().collect();

        for (module, record) in &modules_map {
            let Some(rec_obj) = record.as_object() else {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            };
            let Some(expected_source_sha) = rec_obj
                .get("sourceSha256")
                .and_then(Json::as_str)
                .filter(|s| is_sha256_hex(s))
            else {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            };
            let Some(parts_obj) =
                rec_obj.get("parts").and_then(Json::as_object)
            else {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            };

            let rel_mod = module.replace('.', "/");
            let source_path =
                self.prefix.join("src/lean").join(format!("{rel_mod}.lean"));
            let actual_source_sha = sha256_file(&source_path, "foundation")?;
            if !actual_source_sha.eq_ignore_ascii_case(expected_source_sha) {
                return Err(Failure::new(
                    2,
                    "foundation",
                    format!(
                        "foundation source SHA-256 mismatch for {module}: expected {expected_source_sha}, got {actual_source_sha}"
                    ),
                ));
            }

            let mut available = BTreeMap::new();
            for (part, expected_val) in parts_obj {
                let relative = format!("{rel_mod}.{part}");
                let installed = self.prefix.join("lib/lean").join(&relative);
                // Verify that companion parts marked `null` in the lock (such
                // as `.olean.private`) do not exist on disk where Lean might
                // load them alongside `.olean`.
                if expected_val.is_null() {
                    if fs::symlink_metadata(&installed).is_ok() {
                        return Err(Failure::new(
                            2,
                            "foundation",
                            format!("unexpected companion part: {relative}"),
                        ));
                    }
                    continue;
                }
                let Some(expected_part_sha) =
                    expected_val.as_str().filter(|s| is_sha256_hex(s))
                else {
                    return Err(Failure::new(
                        2,
                        "lock",
                        format!("invalid part digest for {relative}"),
                    ));
                };
                let actual_part_sha = sha256_file(&installed, "foundation")?;
                if !actual_part_sha.eq_ignore_ascii_case(expected_part_sha) {
                    return Err(Failure::new(
                        2,
                        "foundation",
                        format!(
                            "foundation artifact SHA-256 mismatch for {relative}: expected {expected_part_sha}, got {actual_part_sha}"
                        ),
                    ));
                }
                available.insert(
                    part.clone(),
                    installed.to_string_lossy().into_owned(),
                );
            }

            let olean_group: Vec<String> = PARTS[..3]
                .iter()
                .filter_map(|p| available.get(*p).cloned())
                .collect();
            let ir_group: Vec<String> = PARTS[3..]
                .iter()
                .filter_map(|p| available.get(*p).cloned())
                .collect();
            if olean_group.is_empty() {
                return Err(Failure::new(
                    2,
                    "foundation",
                    format!("missing olean for {module}"),
                ));
            }
            self.artifacts
                .insert(module.clone(), vec![olean_group, ir_group]);
        }

        self.graph = graph_map;
        Ok(())
    }

    /// Compile a single `"preflight"`-admitted `.lean` source file into
    /// `self.stage/<lib_subdir>` using `--setup` and strict kernel flags:
    /// - `-j1 -M2048`: single-threaded deterministic execution with a 2 GiB
    ///   memory cap.
    /// - `-t0`: trust level 0 (never skip kernel checks on imported constants).
    /// - `-DElab.async=false`: synchronous elaboration so all proof tasks
    ///   complete before `lean` exits.
    /// - `-Ddebug.skipKernelTC=false`: forbid disabling the kernel typechecker.
    /// - `-DwarningAsError=true` (when `warn_as_err` is `true`): reject any
    ///   compiler warning on `theory/`, `Mir`, and `Proof` modules.
    fn compile_lean_module(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<Json>,
        lib_subdir: &str,
        warn_as_err: bool,
    ) -> Result<(), Failure> {
        let setup_path = self.write_setup_json(module, &edge_list)?;
        let output = self
            .stage
            .join(lib_subdir)
            .join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::new(2, "compile", e.to_string()))?;
        }
        let mut compile_args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "-t0".to_string(),
            "-DElab.async=false".to_string(),
            "-Ddebug.skipKernelTC=false".to_string(),
        ];
        if warn_as_err {
            compile_args.push("-DwarningAsError=true".to_string());
        }
        compile_args.extend([
            "--setup".to_string(),
            setup_path.to_string_lossy().into_owned(),
            "-o".to_string(),
            output.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ]);
        self.process(&format!("compile-{module}"), &compile_args)?;
        self.record_compiled_artifacts(module, &output, edge_list)
    }

    /// Verify that `compile_lean_module` produced a regular `.olean` file for
    /// `module` and register its `.olean` and `.ir` companion groups in
    /// `self.artifacts` and its import edges in `self.graph`.
    fn record_compiled_artifacts(
        &mut self,
        module: &str,
        output: &Path,
        edge_list: Vec<Json>,
    ) -> Result<(), Failure> {
        let stem = output
            .file_name()
            .unwrap()
            .to_string_lossy()
            .strip_suffix("olean")
            .unwrap()
            .to_string();
        let parent = output.parent().unwrap();
        let mut available = BTreeMap::new();
        for part in PARTS {
            let artifact = parent.join(format!("{stem}{part}"));
            if fs::symlink_metadata(&artifact).is_ok() {
                regular(&artifact, "compile")?;
                available.insert(
                    part.to_string(),
                    artifact.to_string_lossy().into_owned(),
                );
            }
        }
        if !available.contains_key("olean") {
            return Err(Failure::new(
                2,
                "compile",
                format!("compiler omitted output for {module}"),
            ));
        }
        let olean_group: Vec<String> = PARTS[..3]
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        let ir_group: Vec<String> = PARTS[3..]
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        self.artifacts
            .insert(module.to_string(), vec![olean_group, ir_group]);
        self.graph.insert(module.to_string(), Json::Array(edge_list));
        Ok(())
    }

    /// Invoke Phase 2 (`"audit"`) of `TrustedBoundary.lean` over the compiled
    /// `.olean` artifacts in `self.artifacts`.
    fn run_audit_inspector(
        &mut self,
        has_crate: bool,
    ) -> Result<Json, Failure> {
        let mut fields = BTreeMap::new();
        fields.insert(
            "trusted".to_string(),
            json!(self.modules.keys().collect::<Vec<_>>()),
        );
        fields.insert(
            "theory".to_string(),
            json!(self.theory_modules.keys().collect::<Vec<_>>()),
        );
        fields.insert("hasCrate".to_string(), json!(has_crate));
        fields.insert(
            "trustDeclarations".to_string(),
            Json::Array(self.trust_declarations.clone()),
        );
        self.inspect("audit", fields)
    }

    /// Run the repository boundary check (`trusted/lean/` plus `theory/` when
    /// present).
    ///
    /// Executes the full repository audit pipeline:
    /// 1. [`check_checkout_cargo_hygiene`] (and [`check_cargo_boundary`] when
    ///    Cargo/manifest files are present).
    /// 2. [`Self::tool_admission`] and [`scan_lean_tree`] on `theory/`, staging
    ///    all `.lean` sources into `self.stage/src/` before inspection.
    /// 3. Phase 1 (`"preflight"`) via `TrustedBoundary.lean` to validate syntax
    ///    and attributes across all staged `Trusted.*` and `Anneal.*` sources
    ///    before compiling any file, and to enforce that `Trusted.*` imports
    ///    only `foundation ++ trusted` while `Anneal.*` imports only
    ///    `foundation ++ trusted ++ theory`.
    /// 4. Topological sorting (`topo_sort_modules`) and sequential `--setup`
    ///    compilation of the staged `Trusted.*` and `Anneal.*` files.
    /// 5. Phase 2 (`"audit"`) via `TrustedBoundary.lean` to check declaration
    ///    inventories, `@[vetted]` vs. `@[candidate]` non-contamination,
    ///    dependency closures, zero custom axioms, and full kernel replay.
    pub fn run(&mut self) -> Result<Json, Failure> {
        check_checkout_cargo_hygiene(&self.checkout)?;
        self.tool_admission()?;
        self.stage_theory_modules()?;

        let sources: Vec<Json> = self
            .modules
            .iter()
            .chain(self.theory_modules.iter())
            .map(|(n, p)| json!([n, p.to_string_lossy()]))
            .collect();
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert("sources".to_string(), Json::Array(sources));
        let pf_res = self.inspect("preflight", pf_fields)?;
        let Some(headers) = pf_res.get("headers").and_then(Json::as_array) else {
            return Err(Failure::new(
                2,
                "preflight",
                "incomplete source-header inventory",
            ));
        };

        let mut imports_map: BTreeMap<String, Vec<Json>> = BTreeMap::new();
        self.trust_declarations.clear();
        for h in headers {
            let mod_name = h
                .get("module")
                .and_then(Json::as_str)
                .unwrap_or("")
                .to_string();
            if self.modules.contains_key(&mod_name)
                && let Some(decls) =
                    h.get("trustDeclarations").and_then(Json::as_array)
            {
                self.trust_declarations.extend(decls.iter().cloned());
            }
            let edges = h
                .get("imports")
                .and_then(Json::as_array)
                .unwrap()
                .to_vec();
            let is_trusted = self.modules.contains_key(&mod_name);
            // Enforce module-import direction before invoking the compiler:
            // `Trusted` modules may import only `foundation` or `Trusted`,
            // never `Anneal` (`theory/`).
            for edge in &edges {
                let imp_mod = edge
                    .get("module")
                    .and_then(Json::as_str)
                    .unwrap_or("");
                let allowed = if is_trusted {
                    self.artifacts.contains_key(imp_mod)
                        || self.modules.contains_key(imp_mod)
                } else {
                    self.artifacts.contains_key(imp_mod)
                        || self.modules.contains_key(imp_mod)
                        || self.theory_modules.contains_key(imp_mod)
                };
                if !allowed {
                    return Err(Failure::new(
                        1,
                        "preflight",
                        format!("foreign/missing import {imp_mod} in {mod_name}"),
                    ));
                }
            }
            imports_map.insert(mod_name, edges);
        }

        let trusted_order = topo_sort_modules(
            self.modules.keys().cloned().collect(),
            &imports_map,
            "Trusted import cycle",
        )?;
        let theory_order = topo_sort_modules(
            self.theory_modules.keys().cloned().collect(),
            &imports_map,
            "Theory import cycle",
        )?;

        for (k, v) in &imports_map {
            self.graph.insert(k.clone(), Json::Array(v.clone()));
        }

        for module in &trusted_order {
            let edge_list = imports_map[module].clone();
            let staged_src_path = self.modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "lib",
                false,
            )?;
        }

        for module in &theory_order {
            let edge_list = imports_map[module].clone();
            let staged_src_path = self.theory_modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "theory-lib",
                true,
            )?;
        }

        let mut report = self.run_audit_inspector(false)?;

        let rep_obj = report.as_object_mut().unwrap();
        rep_obj.insert("toolchain".to_string(), json!(&self.version));
        rep_obj.insert(
            "guarantee".to_string(),
            json!(
                "kernel dependency closure, module-origin separation, and Cargo DAG boundary"
            ),
        );

        Ok(report)
    }

    /// Audit a captured crate's `Mir.lean` and `Proof.lean` at
    /// `trustLevel := 0` using the default [`ReleaseChannel::Alpha`] and the
    /// crate's `Cargo.toml` trust policy.
    pub fn verify_crate(&mut self, crate_dir: &Path) -> Result<Json, Failure> {
        self.verify_crate_with_policy(crate_dir, None, None)
    }

    /// Audit a captured crate's `Mir.lean` and `Proof.lean` at
    /// `trustLevel := 0`, enforcing `channel_override` and the target crate's
    /// [`CrateTrustPolicy`].
    ///
    /// Executes the per-crate verification pipeline on top of the audited
    /// repository prefix (`load_or_build_verify_prefix`):
    /// 1. Stages `.anneal/Mir.lean` and `.anneal/Proof.lean` into
    ///    `self.stage/src/crate/`, runs Phase 1 (`"preflight"`), and checks
    ///    import containment before compiling either file: `Mir.lean` may
    ///    import only `foundation ++ trusted` (never `Anneal` or `Proof`),
    ///    while `Proof.lean` may import `foundation ++ trusted ++ theory ++
    ///    {Mir}`.
    /// 2. Compiles the staged `Mir` and `Proof` files via
    ///    `compile_lean_module` with `-DwarningAsError=true`.
    /// 3. Runs Phase 2 (`"audit"` with `hasCrate = true`), which verifies in
    ///    the compiled `.olean` environment that `Mir.crate : Trusted.Crate`,
    ///    `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`, zero custom
    ///    axioms are used, all non-foundation declarations replay cleanly
    ///    through `base.toKernelEnv.replay`, and returns the active
    ///    `candidateFeatures` reached by `Mir` and `Proof`.
    /// 4. Enforces release-channel and crate trust-policy gating on the active
    ///    `candidateFeatures` and computes `unusedCandidateFeatures` so callers
    ///    can warn when an opted-in candidate feature is unused or has
    ///    graduated to `@[vetted]`.
    pub fn verify_crate_with_policy(
        &mut self,
        crate_dir: &Path,
        channel_override: Option<ReleaseChannel>,
        cli_allowed_candidates: Option<&[String]>,
    ) -> Result<Json, Failure> {
        let crate_dir = fs::canonicalize(crate_dir).map_err(|e| {
            Failure::new(
                2,
                "crate-input",
                format!("cannot resolve {}: {e}", crate_dir.display()),
            )
        })?;
        let (crate_root, anneal_dir) = if crate_dir
            .file_name()
            .is_some_and(|n| n == ".anneal")
            && let Some(parent) = crate_dir.parent()
        {
            (parent.to_path_buf(), crate_dir.clone())
        } else if fs::symlink_metadata(crate_dir.join(".anneal")).is_ok() {
            (crate_dir.clone(), crate_dir.join(".anneal"))
        } else {
            (crate_dir.clone(), crate_dir.clone())
        };
        let channel = channel_override.unwrap_or_default();
        let policy =
            load_crate_trust_policy(&crate_root, cli_allowed_candidates)?;
        let raw_mir_path = anneal_dir.join("Mir.lean");
        let raw_proof_path = anneal_dir.join("Proof.lean");
        let mir_path = self.stage.join("src/crate/Mir.lean");
        let proof_path = self.stage.join("src/crate/Proof.lean");
        stage_regular_file(&raw_mir_path, &mir_path, "crate-input")?;
        stage_regular_file(&raw_proof_path, &proof_path, "crate-input")?;

        let mut report = self.load_or_build_verify_prefix()?;

        let pf_sources = json!([
            ["Mir", mir_path.to_string_lossy()],
            ["Proof", proof_path.to_string_lossy()],
        ]);
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert("sources".to_string(), pf_sources);
        let pf_res = self.inspect("preflight", pf_fields)?;
        let Some(headers) = pf_res.get("headers").and_then(Json::as_array) else {
            return Err(Failure::new(
                2,
                "preflight",
                "incomplete crate header observation",
            ));
        };

        let mut header_edges: BTreeMap<String, Vec<Json>> = BTreeMap::new();
        for h in headers {
            let m = h
                .get("module")
                .and_then(Json::as_str)
                .unwrap_or("")
                .to_string();
            let edges = h
                .get("imports")
                .and_then(Json::as_array)
                .unwrap()
                .to_vec();
            header_edges.insert(m, edges);
        }

        let mut allowed_mir_imports: BTreeSet<String> =
            self.foundation.iter().cloned().collect();
        allowed_mir_imports.extend(self.modules.keys().cloned());

        let mir_edges = header_edges.remove("Mir").unwrap_or_default();
        if !mir_edges.iter().all(|e| {
            e.get("module")
                .and_then(Json::as_str)
                .is_some_and(|m| allowed_mir_imports.contains(m))
        }) {
            return Err(Failure::new(
                1,
                "preflight",
                "Mir.lean imports disallowed modules",
            ));
        }

        let mut allowed_proof_imports = allowed_mir_imports;
        allowed_proof_imports.extend(self.theory_modules.keys().cloned());
        allowed_proof_imports.insert("Mir".to_string());

        let proof_edges = header_edges.remove("Proof").unwrap_or_default();
        if !proof_edges.iter().all(|e| {
            e.get("module")
                .and_then(Json::as_str)
                .is_some_and(|m| allowed_proof_imports.contains(m))
        }) {
            return Err(Failure::new(
                1,
                "preflight",
                "Proof.lean imports disallowed modules",
            ));
        }

        for (module, src_file, edge_list) in [
            ("Mir", &mir_path, mir_edges),
            ("Proof", &proof_path, proof_edges),
        ] {
            self.compile_lean_module(
                module,
                src_file,
                edge_list,
                "crate-lib",
                true,
            )?;
        }

        let mut crate_audit = self.run_audit_inspector(true)?;

        let mut active_candidates = BTreeSet::new();
        if let Some(arr) =
            crate_audit.get("candidateFeatures").and_then(Json::as_array)
        {
            for item in arr {
                if let Some(feat) = item.as_str() {
                    active_candidates.insert(feat.to_string());
                }
            }
        }

        if channel == ReleaseChannel::Stable && !active_candidates.is_empty() {
            let list: Vec<String> = active_candidates.into_iter().collect();
            return Err(Failure::new(
                1,
                "candidate-policy",
                format!(
                    "stable release channel forbids candidate-trusted features, but verification used: {}",
                    list.join(", ")
                ),
            ));
        }

        for feat in &active_candidates {
            if !policy.is_allowed(channel, feat) {
                return Err(Failure::new(
                    1,
                    "candidate-policy",
                    format!(
                        "candidate-trusted feature `{feat}` is not enabled; opt in via `[package.metadata.anneal.trust-policy] allow-candidate-features = [\"{feat}\"]` or `--allow-candidate-features {feat}`"
                    ),
                ));
            }
        }

        let unused_candidates: Vec<String> = policy
            .allowed_features
            .iter()
            .filter(|f| !active_candidates.contains(*f))
            .cloned()
            .collect();

        if let Some(cv_obj) = crate_audit.as_object_mut() {
            cv_obj.insert(
                "candidateFeatures".to_string(),
                json!(active_candidates),
            );
            cv_obj.insert(
                "unusedCandidateFeatures".to_string(),
                json!(unused_candidates),
            );
        }

        let rep_obj = report.as_object_mut().unwrap();
        rep_obj.insert("crateVerification".to_string(), crate_audit);
        Ok(report)
    }

    /// Configure an optional pre-built repository prefix cache directory.
    pub fn set_prefix_cache_dir(&mut self, dir: Option<PathBuf>) {
        self.prefix_cache_dir = dir;
    }

    /// Compute the [`VerifyPrefixKey`] for the current checkout and toolchain,
    /// enforcing Cargo and source-tree hygiene before consulting any cache.
    fn compute_verify_prefix_key(&self) -> Result<VerifyPrefixKey, Failure> {
        check_checkout_cargo_hygiene(&self.checkout)?;
        let trusted_mods = scan_lean_tree(&self.source, "Trusted")?;
        let theory_dir = self.checkout.join("theory");
        let theory_mods = if fs::symlink_metadata(&theory_dir).is_ok() {
            scan_lean_tree(&theory_dir, "Anneal")?
        } else {
            BTreeMap::new()
        };
        let inspector_src =
            self.checkout.join("trusted/audit/TrustedBoundary.lean");
        regular(&inspector_src, "tool-snapshot")?;
        let lock_src = self.source.join("foundation-lock.json");
        regular(&lock_src, "lock")?;
        let toolchain_src = self.source.join("lean-toolchain");
        regular(&toolchain_src, "lock")?;
        let lean_sha = sha256_file(&self.lean, "toolchain")?;

        let mut sources = BTreeMap::new();
        for p in trusted_mods
            .values()
            .chain(theory_mods.values())
            .chain([&inspector_src, &lock_src, &toolchain_src])
        {
            let bytes = fs::read(p).map_err(|e| {
                Failure::new(
                    2,
                    "io",
                    format!("cannot read {}: {e}", p.display()),
                )
            })?;
            let rel = p
                .strip_prefix(&self.checkout)
                .unwrap_or(p)
                .to_string_lossy()
                .replace('\\', "/");
            sources.insert(rel, bytes);
        }

        let mut key_buf = Vec::new();
        key_buf.extend_from_slice(lean_sha.as_bytes());
        key_buf.push(0);
        for (rel, bytes) in &sources {
            key_buf.extend_from_slice(rel.as_bytes());
            key_buf.push(0);
            key_buf.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
            key_buf.extend_from_slice(bytes);
        }
        let key_sha256 = sha256_bytes(&key_buf);

        Ok(VerifyPrefixKey {
            checkout: self.checkout.clone(),
            lean: self.lean.clone(),
            key_sha256,
            sources,
        })
    }

    /// Audit the repository and populate `dest_dir` with the compiled `Trusted`
    /// and `Anneal` `.olean`/`.ir` prefix and `prefix-metadata.json`.
    pub fn build_prefix_cache(&mut self, dest_dir: &Path) -> Result<Json, Failure> {
        let key = self.compute_verify_prefix_key()?;
        let report = self.run()?;
        fs::create_dir_all(dest_dir)
            .map_err(|e| Failure::new(2, "compile", e.to_string()))?;
        let mut compiled_artifacts_rel = BTreeMap::new();
        let mut artifact_digests = BTreeMap::new();
        for (module, groups) in &self.artifacts {
            if self.foundation.contains(module) {
                continue;
            }
            let mut groups_rel = Vec::new();
            for group in groups {
                let mut g_rel = Vec::new();
                for abs_str in group {
                    let abs_path = Path::new(abs_str);
                    let rel = abs_path
                        .strip_prefix(&self.stage)
                        .map_err(|e| Failure::new(2, "compile", e.to_string()))?
                        .to_string_lossy()
                        .replace('\\', "/");
                    let dest_file = dest_dir.join(&rel);
                    let digest =
                        stage_regular_file(abs_path, &dest_file, "compile")?;
                    artifact_digests.insert(rel.clone(), digest);
                    g_rel.push(rel);
                }
                groups_rel.push(g_rel);
            }
            compiled_artifacts_rel.insert(module.clone(), groups_rel);
        }
        let modules_json: BTreeMap<String, String> = self
            .modules
            .iter()
            .map(|(k, v)| (k.clone(), v.to_string_lossy().into_owned()))
            .collect();
        let theory_json: BTreeMap<String, String> = self
            .theory_modules
            .iter()
            .map(|(k, v)| (k.clone(), v.to_string_lossy().into_owned()))
            .collect();
        let meta = json!({
            "keySha256": key.key_sha256,
            "artifactDigests": artifact_digests,
            "report": report,
            "compiledArtifactsRel": compiled_artifacts_rel,
            "graph": self.graph,
            "modules": modules_json,
            "theoryModules": theory_json,
            "trustDeclarations": self.trust_declarations,
        });
        fs::write(
            dest_dir.join("prefix-metadata.json"),
            serde_json::to_vec(&meta).unwrap(),
        )
        .map_err(|e| Failure::new(2, "compile", e.to_string()))?;
        Ok(report)
    }

    fn load_or_build_verify_prefix(&mut self) -> Result<Json, Failure> {
        let key = self.compute_verify_prefix_key()?;

        if let Some(cache_dir) = self.prefix_cache_dir.clone() {
            let meta_path = cache_dir.join("prefix-metadata.json");
            if fs::symlink_metadata(&meta_path).is_ok()
                && regular(&meta_path, "compile").is_ok()
                && let Ok(meta_text) = fs::read_to_string(&meta_path)
                && let Ok(meta) = serde_json::from_str::<Json>(&meta_text)
                && meta.get("keySha256").and_then(Json::as_str)
                    == Some(key.key_sha256.as_str())
                && let Some(digests_obj) =
                    meta.get("artifactDigests").and_then(Json::as_object)
                && let Some(rel_map) =
                    meta.get("compiledArtifactsRel").and_then(Json::as_object)
            {
                self.tool_admission()?;
                self.stage_theory_modules()?;
                self.execution_began = true;
                let expected_modules: BTreeSet<String> = self
                    .modules
                    .keys()
                    .chain(self.theory_modules.keys())
                    .cloned()
                    .collect();
                let actual_modules: BTreeSet<String> =
                    rel_map.keys().cloned().collect();
                let mut valid_disk_cache = actual_modules == expected_modules;
                let mut staged_artifacts = BTreeMap::new();
                'outer: for (module, groups_val) in rel_map {
                    if !valid_disk_cache {
                        break;
                    }
                    let Some(groups_arr) = groups_val.as_array() else {
                        valid_disk_cache = false;
                        break;
                    };
                    let mut groups_abs = Vec::new();
                    for g in groups_arr {
                        let Some(g_arr) = g.as_array() else {
                            valid_disk_cache = false;
                            break 'outer;
                        };
                        let mut g_abs = Vec::new();
                        for rel_val in g_arr {
                            let Some(rel) = rel_val.as_str() else {
                                valid_disk_cache = false;
                                break 'outer;
                            };
                            let is_clean_rel = Path::new(rel)
                                .components()
                                .all(|c| matches!(c, std::path::Component::Normal(_)));
                            let Some(expected_digest) =
                                digests_obj.get(rel).and_then(Json::as_str)
                            else {
                                valid_disk_cache = false;
                                break 'outer;
                            };
                            if !is_clean_rel || !is_sha256_hex(expected_digest) {
                                valid_disk_cache = false;
                                break 'outer;
                            }
                            let src_file = cache_dir.join(rel);
                            let dest_file = self.stage.join(rel);
                            let Ok(actual_digest) =
                                stage_regular_file(&src_file, &dest_file, "compile")
                            else {
                                valid_disk_cache = false;
                                break 'outer;
                            };
                            if !actual_digest.eq_ignore_ascii_case(expected_digest) {
                                valid_disk_cache = false;
                                break 'outer;
                            }
                            g_abs.push(dest_file.to_string_lossy().into_owned());
                        }
                        groups_abs.push(g_abs);
                    }
                    staged_artifacts.insert(module.clone(), groups_abs);
                }
                if valid_disk_cache
                    && let Some(graph_obj) = meta.get("graph").and_then(Json::as_object)
                    && let Some(decls_arr) =
                        meta.get("trustDeclarations").and_then(Json::as_array)
                    && let Some(rep) = meta.get("report").cloned()
                {
                    self.artifacts.extend(staged_artifacts);
                    self.graph = graph_obj.clone();
                    self.trust_declarations = decls_arr.clone();
                    return Ok(rep);
                }
            }
        }

        let mut guard = VERIFY_PREFIX_CACHE
            .lock()
            .unwrap_or_else(|e| e.into_inner());

        if let Some(cached) = guard
            .as_ref()
            .filter(|c| c.key == key)
            .cloned()
        {
            drop(guard);
            self.tool_admission()?;
            self.stage_theory_modules()?;
            self.execution_began = true;
            for file in &cached.files {
                let dest = self.stage.join(&file.rel_path);
                if let Some(parent) = dest.parent() {
                    fs::create_dir_all(parent).map_err(|e| {
                        Failure::new(2, "compile", e.to_string())
                    })?;
                }
                fs::write(&dest, &file.bytes)
                    .map_err(|e| Failure::new(2, "compile", e.to_string()))?;
            }
            for (module, groups_rel) in &cached.compiled_artifacts_rel {
                let groups_abs: Vec<Vec<String>> = groups_rel
                    .iter()
                    .map(|g| {
                        g.iter()
                            .map(|rel| {
                                self.stage
                                    .join(rel)
                                    .to_string_lossy()
                                    .into_owned()
                            })
                            .collect()
                    })
                    .collect();
                self.artifacts.insert(module.clone(), groups_abs);
            }
            self.graph = cached.graph;
            self.trust_declarations = cached.trust_declarations;
            return Ok(cached.report);
        }

        let report = self.run()?;

        let mut compiled_artifacts_rel = BTreeMap::new();
        let mut files = Vec::new();
        for (module, groups) in &self.artifacts {
            if self.foundation.contains(module) {
                continue;
            }
            let mut groups_rel = Vec::new();
            for group in groups {
                let mut g_rel = Vec::new();
                for abs_str in group {
                    let abs_path = Path::new(abs_str);
                    let rel = abs_path
                        .strip_prefix(&self.stage)
                        .map_err(|e| Failure::new(2, "compile", e.to_string()))?
                        .to_string_lossy()
                        .replace('\\', "/");
                    let bytes = fs::read(abs_path).map_err(|e| {
                        Failure::new(2, "compile", e.to_string())
                    })?;
                    files.push(CachedArtifactFile {
                        rel_path: rel.clone(),
                        bytes,
                    });
                    g_rel.push(rel);
                }
                groups_rel.push(g_rel);
            }
            compiled_artifacts_rel.insert(module.clone(), groups_rel);
        }

        *guard = Some(CachedVerifyPrefix {
            key,
            report: report.clone(),
            compiled_artifacts_rel,
            graph: self.graph.clone(),
            trust_declarations: self.trust_declarations.clone(),
            files,
        });

        Ok(report)
    }
}

/// Topologically sort the module set `pending` according to `imports_map`,
/// returning a policy rejection (`code == 1`) with `cycle_msg` if `pending`
/// contains an import cycle.
fn topo_sort_modules(
    mut pending: BTreeSet<String>,
    imports_map: &BTreeMap<String, Vec<Json>>,
    cycle_msg: &str,
) -> Result<Vec<String>, Failure> {
    let mut order = Vec::new();
    while !pending.is_empty() {
        let ready: Vec<String> = pending
            .iter()
            .filter(|n| {
                imports_map[*n].iter().all(|e| {
                    let m = e.get("module").and_then(Json::as_str).unwrap();
                    !pending.contains(m)
                })
            })
            .cloned()
            .collect();
        if ready.is_empty() {
            return Err(Failure::new(1, "preflight", cycle_msg));
        }
        for r in &ready {
            pending.remove(r);
        }
        order.extend(ready);
    }
    Ok(order)
}
