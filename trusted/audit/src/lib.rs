// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Repository trusted-boundary and `.olean` environment auditor for Anneal.
//!
//! This crate implements the CI repository gate that pairs with
//! `trusted/audit/TrustedBoundary.lean`. While `TrustedBoundary.lean` inspects
//! Lean syntax trees and compiled `.olean` kernel environments from inside
//! Lean, an inner Lean script cannot verify the host filesystem, Cargo
//! workspace manifests, Lean binary version admission, or the `--setup` flags
//! and environment variables used to invoke `lean` in the first place.
//!
//! Together, `trusted/audit` and `TrustedBoundary.lean` enforce five
//! repository-level invariants:
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
//!    version and SHA-256 digest must match `trusted/lean/foundation-lock.json`
//!    (Lean v4.34.1), and every `Init.*` module's `.lean` source and
//!    `.olean`/`.ir` companion parts must match the lock's presence/absence
//!    specification.
//! 3. **Hermetic preflight and synchronous `--setup` compilation
//!    ([`Checker::new_with_env`], [`Checker::write_setup_json`],
//!    [`Checker::compile_lean_module`]):** Ambient `LEAN_*`, `LAKE_*`,
//!    `ELAN_*`, and `LD_*`/`DYLD_*` variables are stripped. Before any `.lean`
//!    file is compiled, `TrustedBoundary.lean` runs in `"preflight"` mode using
//!    only the locked `foundation` parser environment to reject forbidden
//!    syntax (`axiom`, `unsafe`, `partial`, `meta`, `native_decide`, `by_elab`,
//!    `#eval`, `set_option`, compiler-override attributes, etc.) and extract
//!    each `Trusted` module's `-- anneal-trust-tier:` directive. Admitted
//!    modules are then compiled in topological order via `lean --setup
//!    <module>.setup.json -DElab.async=false -Ddebug.skipKernelTC=false`,
//!    binding every import directly to its staged `.olean` path.
//! 4. **Module-level trust-tier separation and namespace hygiene
//!    (`TrustedBoundary.lean` `"audit"` mode):** Each `Trusted` module declares
//!    a single module-level tier (`vetted` or `candidate:<feature>`), and every
//!    constant compiled into that module's `.olean` inherits its origin
//!    module's tier. Constants in `vetted` modules never reference constants in
//!    `candidate:<feature>` modules; `Trusted` modules never import or
//!    reference `theory/` (`Anneal.*`); and non-`Trusted` modules cannot
//!    declare constants in the `Trusted` namespace or `opaque` definitions.
//! 5. **Zero custom axioms and full kernel replay ([`Checker::run`]):** All
//!    non-foundation constants in `Trusted` and `Anneal` are checked against
//!    the foundation axiom allowlist in `foundation-lock.json` and replayed
//!    from scratch through `base.toKernelEnv.replay` with `loadExts := false`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use serde_json::json;
use sha2::{Digest, Sha256};
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
    format!("{:x}", Sha256::digest(data))
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

/// Reject `.cargo*`, `rust-toolchain*`, and `.gitmodules` overrides at the
/// repository root (including case-insensitive directory entries).
fn reject_cargo_toolchain_overrides(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for forbidden in [
        ".cargo",
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
        ".gitmodules",
    ] {
        if fs::symlink_metadata(checkout.join(forbidden)).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "forbidden Cargo/toolchain override at repository root: {forbidden}"
                ),
            ));
        }
    }
    if let Ok(entries) = fs::read_dir(checkout) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_ascii_lowercase();
            if name == ".cargo"
                || name == ".gitmodules"
                || name == "rust-toolchain"
                || name.starts_with("rust-toolchain.")
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "forbidden Cargo/toolchain override at repository root: {}",
                        entry.file_name().to_string_lossy()
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`] whenever any Cargo or root-manifest TCB file is
/// present.
fn check_checkout_cargo_hygiene(checkout: &Path) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if [
        "Cargo.toml",
        "Cargo.lock",
        "trusted/root-manifest.sha256",
        "trusted/rustc-capture",
    ]
    .iter()
    .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockFile {
    version: Option<i64>,
    #[serde(default)]
    package: Vec<CargoLockPackage>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockPackage {
    name: String,
    #[allow(dead_code)]
    version: String,
    source: Option<String>,
    checksum: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    dependencies: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoManifest {
    workspace: RootCargoWorkspace,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoWorkspace {
    members: Vec<String>,
    #[serde(default)]
    exclude: Vec<String>,
    resolver: Option<String>,
}

/// Verify that a relative target path inside a workspace member `Cargo.toml`
/// does not use `..` or an absolute path to escape the member directory.
fn validate_member_target_path(
    member: &str,
    section: &str,
    target_table: &toml::map::Map<String, toml::Value>,
) -> Result<(), Failure> {
    if let Some(path_val) = target_table.get("path") {
        let Some(p) = path_val.as_str() else {
            return Err(Failure::new(
                1,
                "cargo-boundary",
                format!("invalid {section}.path in {member}/Cargo.toml"),
            ));
        };
        let path = Path::new(p);
        if path.is_absolute()
            || path
                .components()
                .any(|c| matches!(c, std::path::Component::ParentDir))
        {
            return Err(Failure::new(
                1,
                "cargo-boundary",
                format!(
                    "{member} target {section}.path escapes member directory: {p}"
                ),
            ));
        }
    }
    Ok(())
}

/// Verify Cargo workspace DAG containment, root Cargo/toolchain hygiene,
/// `Cargo.lock` dependency provenance, and `trusted/root-manifest.sha256` (when
/// present): all workspace crates must reside under `trusted/`, and no
/// workspace crate may depend on a path outside `workspace.members`.
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
            Failure::new(
                1,
                phase,
                format!("cannot read root-manifest.sha256: {e}"),
            )
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
                    format!(
                        "invalid or duplicate entry in root-manifest.sha256: {line}"
                    ),
                ));
            }
            let actual_hex =
                sha256_file(&checkout.join(rel_path), phase).map_err(|e| {
                    Failure::new(1, phase, e.message)
                })?;
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
        for required_rel in
            ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"]
        {
            if !seen_manifest_paths.contains(required_rel) {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "root-manifest.sha256 missing required entry: {required_rel}"
                    ),
                ));
            }
        }
    }

    let root_text = fs::read_to_string(&root_toml_path).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;
    let root_manifest: RootCargoManifest =
        toml::from_str(&root_text).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("root Cargo.toml may contain only [workspace]: {e}"),
            )
        })?;
    if root_manifest.workspace.resolver.as_deref() != Some("2") {
        return Err(Failure::new(
            1,
            phase,
            "root [workspace] resolver must be \"2\"",
        ));
    }

    let checkout_canon = fs::canonicalize(checkout).map_err(|e| {
        Failure::new(2, phase, format!("cannot canonicalize checkout: {e}"))
    })?;

    let member_set: BTreeSet<String> = root_manifest
        .workspace
        .members
        .iter()
        .chain(&root_manifest.workspace.exclude)
        .cloned()
        .collect();
    if !member_set.contains("trusted/rustc-capture") {
        return Err(Failure::new(
            1,
            phase,
            "trusted/rustc-capture missing from workspace.members",
        ));
    }

    let mut member_pkg_names = BTreeSet::new();

    for member in root_manifest
        .workspace
        .members
        .iter()
        .chain(&root_manifest.workspace.exclude)
    {
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
        let pkg_table = member_toml
            .get("package")
            .and_then(toml::Value::as_table)
            .ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("missing [package] in {member}/Cargo.toml"),
                )
            })?;
        let pkg_name = pkg_table
            .get("name")
            .and_then(toml::Value::as_str)
            .filter(|s| !s.is_empty())
            .ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("missing package.name in {member}"),
                )
            })?;
        member_pkg_names.insert(pkg_name.to_string());

        if pkg_table.contains_key("build")
            || pkg_table.contains_key("workspace")
        {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "disallowed package.build or package.workspace in {member}/Cargo.toml"
                ),
            ));
        }
        if fs::symlink_metadata(checkout.join(member).join("build.rs")).is_ok()
        {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed build script {member}/build.rs"),
            ));
        }

        if let Some(lib_table) =
            member_toml.get("lib").and_then(toml::Value::as_table)
        {
            validate_member_target_path(member, "lib", lib_table)?;
        }
        for target_sec in ["bin", "example", "test", "bench"] {
            if let Some(arr) =
                member_toml.get(target_sec).and_then(toml::Value::as_array)
            {
                for item in arr {
                    if let Some(tbl) = item.as_table() {
                        validate_member_target_path(member, target_sec, tbl)?;
                    }
                }
            }
        }

        let member_parent = member_toml_path.parent().unwrap();
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
            for (dep_name, spec) in table {
                if let Some(spec_obj) = spec.as_table() {
                    if spec_obj.contains_key("git")
                        || spec_obj.contains_key("registry")
                    {
                        return Err(Failure::new(
                            1,
                            phase,
                            format!(
                                "disallowed git or custom-registry dependency {dep_name} in {member}/Cargo.toml"
                            ),
                        ));
                    }
                    if let Some(path_val) = spec_obj.get("path") {
                        let Some(dep_path) = path_val.as_str() else {
                            return Err(Failure::new(
                                1,
                                phase,
                                format!(
                                    "non-string path dependency {dep_name} in {member}/Cargo.toml"
                                ),
                            ));
                        };
                        let joined = member_parent.join(dep_path);
                        let resolved =
                            fs::canonicalize(&joined).map_err(|_| {
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
                        let rel_str =
                            rel.to_string_lossy().replace('\\', "/");
                        if !rel_str.starts_with("trusted/") {
                            return Err(Failure::new(
                                1,
                                phase,
                                format!(
                                    "{member} path dependency points outside trusted/: {rel_str}"
                                ),
                            ));
                        }
                        if !member_set.contains(&rel_str) {
                            return Err(Failure::new(
                                1,
                                phase,
                                format!(
                                    "{member} path dependency points to non-member crate: {rel_str}"
                                ),
                            ));
                        }
                        regular(&resolved.join("Cargo.toml"), phase)?;
                    }
                }
            }
            Ok(())
        };

        const DEP_TABLES: [&str; 5] = [
            "dependencies",
            "dev-dependencies",
            "dev_dependencies",
            "build-dependencies",
            "build_dependencies",
        ];
        for section in DEP_TABLES {
            check_dep_table(member_toml.get(section), section)?;
        }
        if let Some(targets) =
            member_toml.get("target").and_then(toml::Value::as_table)
        {
            for (cfg_name, cfg_table) in targets {
                if let Some(cfg_obj) = cfg_table.as_table() {
                    for section in DEP_TABLES {
                        let label = format!("target.{cfg_name}.{section}");
                        check_dep_table(cfg_obj.get(section), &label)?;
                    }
                }
            }
        }
    }

    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_ok() {
        regular(&lock_path, phase)?;
        let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
            Failure::new(1, phase, format!("cannot read Cargo.lock: {e}"))
        })?;
        let lock_file: CargoLockFile =
            toml::from_str(&lock_text).map_err(|e| {
                Failure::new(1, phase, format!("malformed Cargo.lock: {e}"))
            })?;
        if lock_file.version != Some(4) {
            return Err(Failure::new(
                1,
                phase,
                "Cargo.lock must have version = 4",
            ));
        }
        for pkg in &lock_file.package {
            let pkg_name = pkg.name.as_str();
            if let Some(src) = pkg.source.as_deref() {
                if src
                    != "registry+https://github.com/rust-lang/crates.io-index"
                {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!(
                            "untrusted dependency source in Cargo.lock for {pkg_name}: {src}"
                        ),
                    ));
                }
                if !pkg.checksum.as_deref().is_some_and(is_sha256_hex) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!(
                            "missing or invalid checksum in Cargo.lock for {pkg_name}"
                        ),
                    ));
                }
            } else if pkg.checksum.is_some()
                || !member_pkg_names.contains(pkg_name)
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "untrusted local package without source in Cargo.lock: {pkg_name}"
                    ),
                ));
            }
        }
    }

    Ok(())
}

/// Scan a Lean directory tree (`trusted/lean` with `"Trusted"` or `theory`
/// with `"Anneal"`), rejecting symlinks, non-`.lean` files, and compiled
/// artifacts in the source tree and returning the map from dot-separated module
/// name to `.lean` path.
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
            && (relative == "lean-toolchain"
                || relative == "foundation-lock.json"))
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

/// Stateful repository-boundary auditor managing an isolated staging directory
/// (`stage`, owned by `_stage_dir`).
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
    pub module_tiers: BTreeMap<String, String>,
    pub inspector: PathBuf,
    pub lock: Json,
    pub version: String,
    pub prefix: PathBuf,
    pub foundation: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorErrResponse {
    ok: bool,
    category: String,
    message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorOkResponse {
    ok: bool,
    result: serde_json::Map<String, Json>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FoundationModuleRecord {
    #[serde(rename = "sourceSha256")]
    source_sha256: String,
    parts: BTreeMap<String, Option<String>>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FoundationLock {
    schema: i64,
    toolchain: String,
    distributions: BTreeMap<String, String>,
    modules: BTreeMap<String, FoundationModuleRecord>,
    graph: serde_json::Map<String, Json>,
    axioms: Vec<(String, String)>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct PreflightHeader {
    module: String,
    imports: Vec<Json>,
    #[serde(default)]
    trust_tier: Option<String>,
}

#[derive(Deserialize)]
struct PreflightResult {
    headers: Vec<PreflightHeader>,
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
            module_tiers: BTreeMap::new(),
            inspector: PathBuf::new(),
            lock: json!({}),
            version: String::new(),
            prefix: PathBuf::new(),
            foundation: Vec::new(),
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
                && let Ok(resp) =
                    serde_json::from_str::<InspectorErrResponse>(&text)
                && !resp.ok
                && resp.category == "policy"
                && resp.message.starts_with("policy:")
            {
                return Err(Failure::new(1, mode, resp.message));
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
        let resp: InspectorOkResponse =
            serde_json::from_str(&resp_text).map_err(|_| {
                Failure::new(2, mode, "unexpected inspector protocol response")
            })?;
        if !resp.ok {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        Ok(Json::Object(resp.result))
    }

    /// Scan `root` via [`scan_lean_tree`] and copy every discovered `.lean`
    /// file into `self.stage.join(stage_subdir)`.
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

    /// Wipe and recreate `self.stage` and reset per-run staging state.
    fn reset_stage(&mut self) -> Result<(), Failure> {
        if self.stage.exists() {
            fs::remove_dir_all(&self.stage).map_err(|e| {
                Failure::new(
                    2,
                    "snapshot",
                    format!("cannot clean {}: {e}", self.stage.display()),
                )
            })?;
        }
        fs::create_dir_all(&self.stage).map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot recreate {}: {e}", self.stage.display()),
            )
        })?;
        self.artifacts.clear();
        self.graph.clear();
        self.modules.clear();
        self.theory_modules.clear();
        self.module_tiers.clear();
        self.execution_began = false;
        Ok(())
    }

    /// Snapshot and stage `trusted/lean/` and `TrustedBoundary.lean`, and
    /// verify the pinned Lean 4.34.1 binary and `Init.*` artifacts by SHA-256
    /// digest against `foundation-lock.json`.
    pub fn tool_admission(&mut self) -> Result<(), Failure> {
        self.modules =
            self.scan_and_stage_tree(&self.source, "Trusted", "src/trusted")?;

        let inspector_src =
            self.checkout.join("trusted/audit/TrustedBoundary.lean");
        let staged_inspector = self.stage.join("src/TrustedBoundary.lean");
        stage_regular_file(&inspector_src, &staged_inspector, "tool-snapshot")?;
        self.inspector = staged_inspector;

        let lock_path = self.source.join("foundation-lock.json");
        let toolchain_path = self.source.join("lean-toolchain");
        regular(&lock_path, "lock")?;
        regular(&toolchain_path, "lock")?;

        let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
            Failure::new(2, "lock", format!("cannot read foundation lock: {e}"))
        })?;
        let parsed_lock: FoundationLock =
            serde_json::from_str(&lock_text).map_err(|e| {
                Failure::new(
                    2,
                    "lock",
                    format!("cannot read foundation lock: {e}"),
                )
            })?;
        if parsed_lock.schema != 1
            || parsed_lock.toolchain != TOOLCHAIN
            || parsed_lock.distributions.is_empty()
            || !parsed_lock
                .distributions
                .values()
                .all(|s| is_sha256_hex(s))
            || parsed_lock.modules.is_empty()
            || !parsed_lock.modules.keys().eq(parsed_lock.graph.keys())
        {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        }
        for (module, record) in &parsed_lock.modules {
            if !is_sha256_hex(&record.source_sha256)
                || record.parts.len() != PARTS.len()
                || !PARTS.iter().all(|p| record.parts.contains_key(*p))
                || !record
                    .parts
                    .get("olean")
                    .and_then(Option::as_deref)
                    .is_some_and(is_sha256_hex)
            {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            }
            for expected_opt in record.parts.values() {
                if let Some(sha) = expected_opt.as_deref()
                    && !is_sha256_hex(sha)
                {
                    return Err(Failure::new(
                        2,
                        "lock",
                        format!("invalid part digest in {module}"),
                    ));
                }
            }
        }
        self.lock = json!({
            "graph": &parsed_lock.graph,
            "axioms": &parsed_lock.axioms,
        });

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
        if !parsed_lock
            .distributions
            .values()
            .any(|s| s.eq_ignore_ascii_case(&lean_sha))
        {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean binary SHA-256 differs from lock: {lean_sha}"),
            ));
        }

        let actual_version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
        let Some(expected_lean_sha) =
            parsed_lock.distributions.get(&actual_version)
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

        self.foundation = parsed_lock.modules.keys().cloned().collect();

        for (module, record) in &parsed_lock.modules {
            let expected_source_sha = &record.source_sha256;
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
            for part in PARTS {
                let relative = format!("{rel_mod}.{part}");
                let installed = self.prefix.join("lib/lean").join(&relative);
                let expected_opt =
                    record.parts.get(part).and_then(Option::as_deref);
                let Some(expected_part_sha) = expected_opt else {
                    if fs::symlink_metadata(&installed).is_ok() {
                        return Err(Failure::new(
                            2,
                            "foundation",
                            format!("unexpected companion part: {relative}"),
                        ));
                    }
                    continue;
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
                    part.to_string(),
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

        self.graph = parsed_lock.graph;
        Ok(())
    }

    /// Compile a single `"preflight"`-admitted `.lean` source file into
    /// `self.stage/<lib_subdir>` using `--setup` and strict kernel flags.
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
    fn run_audit_inspector(&mut self) -> Result<Json, Failure> {
        let mut fields = BTreeMap::new();
        fields.insert(
            "trusted".to_string(),
            json!(self.modules.keys().collect::<Vec<_>>()),
        );
        fields.insert(
            "theory".to_string(),
            json!(self.theory_modules.keys().collect::<Vec<_>>()),
        );
        let tiers: Vec<Json> = self
            .module_tiers
            .iter()
            .map(|(m, t)| json!([m, t]))
            .collect();
        fields.insert("moduleTiers".to_string(), Json::Array(tiers));
        self.inspect("audit", fields)
    }

    /// Run Phase 1 (`"preflight"`) over all staged `Trusted.*` and `Anneal.*`
    /// repository sources, populating `self.module_tiers` and `self.graph` and
    /// returning the validated module-import map.
    fn preflight_repo_modules(
        &mut self,
    ) -> Result<BTreeMap<String, Vec<Json>>, Failure> {
        let sources: Vec<Json> = self
            .modules
            .iter()
            .chain(self.theory_modules.iter())
            .map(|(n, p)| json!([n, p.to_string_lossy()]))
            .collect();
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert("sources".to_string(), Json::Array(sources));
        let pf_res: PreflightResult =
            serde_json::from_value(self.inspect("preflight", pf_fields)?)
                .map_err(|_| {
                    Failure::new(
                        2,
                        "preflight",
                        "incomplete source-header inventory",
                    )
                })?;

        let mut imports_map: BTreeMap<String, Vec<Json>> = BTreeMap::new();
        self.module_tiers.clear();
        for h in pf_res.headers {
            let mod_name = h.module;
            let is_trusted = self.modules.contains_key(&mod_name);
            if is_trusted {
                let Some(tier) = h.trust_tier else {
                    return Err(Failure::new(
                        1,
                        "preflight",
                        format!("missing trust tier for Trusted module {mod_name}"),
                    ));
                };
                self.module_tiers.insert(mod_name.clone(), tier);
            }
            let edges = h.imports;
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

        let expected_count = self.modules.len() + self.theory_modules.len();
        if imports_map.len() != expected_count
            || !self.modules.keys().all(|m| imports_map.contains_key(m))
            || !self
                .theory_modules
                .keys()
                .all(|m| imports_map.contains_key(m))
        {
            return Err(Failure::new(
                2,
                "preflight",
                "incomplete source-header inventory",
            ));
        }

        for (k, v) in &imports_map {
            self.graph.insert(k.clone(), Json::Array(v.clone()));
        }

        Ok(imports_map)
    }

    /// Run the repository boundary check (`trusted/lean/` plus `theory/` when
    /// present).
    pub fn run(&mut self) -> Result<Json, Failure> {
        check_checkout_cargo_hygiene(&self.checkout)?;
        self.reset_stage()?;
        self.tool_admission()?;
        self.stage_theory_modules()?;
        let imports_map = self.preflight_repo_modules()?;

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

        let mut report = self.run_audit_inspector()?;

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
