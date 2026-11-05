// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Library interface for `cargo-anneal`.
//!
//! Orchestrates end-to-end crate verification:
//! 1. Validates the target crate layout and closed `Cargo.toml` schema
//!    ([`validate_target_crate`]), pinning `Cargo.toml`, `src/lib.rs`, and
//!    optional `anneal-tcb.lock` via `lstat`/`fstat` `(dev, ino)` verification
//!    without ever reading `.anneal/`.
//! 2. Resolves the toolchain andAnneal root directories and verifies the Lean
//!    foundation against `trusted/lean/foundation-lock.json`.
//! 3. Enforces candidate trust-tier opt-in
//!    (`[package.metadata.anneal.trust-policy]` and
//!    `--allow-candidate-features`) and release-channel gating (`alpha` vs.
//!    `stable`).
//! 4. Invokes `anneal-rustc-capture` in a private `/tmp` directory to extract
//!    the target crate's root-anchored first-order `Mir.lean` AST across
//!    `release` and `debug` configurations.
//! 5. Runs the pre-compilation syntax and attribute gate on `Mir.lean`,
//!    verifies 1-to-1 bijection between `/// anneal:trusted` waivers and
//!    `anneal-tcb.lock`, compiles `Mir.lean` (`0444` read-only with SHA-256
//!    verification), and compiles the static 8-line [`PROOF_LEAN_SOURCE`]
//!    against the precompiled `Trusted` and `Anneal` `.olean`s with the Lean 4
//!    kernel (`-Ddebug.skipKernelTC=false -t0`).

pub mod setup;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};

use serde::Deserialize;
use sha2::{Digest, Sha256};
use tempfile::TempDir;
use walkdir::WalkDir;

/// Static, crate-independent `Proof.lean` module compiled for every verified
/// crate.
///
/// Because `Mir.crate` is 100% first-order syntax data (`Trusted.Crate`) and
/// `Anneal.proveCrate` is a total verified decision procedure proved sound in
/// `theory/Anneal/MirLemmas.lean`, every crate's kernel-checked proof script is
/// identical.
pub const PROOF_LEAN_SOURCE: &str = "\
prelude
import Trusted
import Anneal
import Mir

namespace Proof

theorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.proveCrate Mir.crate rfl

end Proof
";

/// Release channel governing whether `candidate:<feature>` TCB modules may be
/// enabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleaseChannel {
    /// Pre-1.0 / alpha channel: candidate TCB features may be enabled via
    /// explicit opt-in.
    Alpha,
    /// Stable channel: any candidate TCB feature is unconditionally rejected.
    Stable,
}

impl ReleaseChannel {
    /// Parses `"alpha"` or `"stable"`.
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "alpha" => Ok(Self::Alpha),
            "stable" => Ok(Self::Stable),
            other => Err(format!(
                "invalid --release-channel `{other}` (expected `alpha` or `stable`)"
            )),
        }
    }
}

/// Configuration for `cargo anneal verify`.
#[derive(Debug, Clone)]
pub struct VerifyConfig {
    /// Path to the user crate directory to verify.
    pub crate_dir: PathBuf,
    /// Path to the unpacked Anneal toolchain root (`lean/`, `rust/`, `bin/`).
    pub toolchain_dir: PathBuf,
    /// Path to the Anneal root containing `trusted/lean/` and `theory/`.
    pub anneal_root: PathBuf,
    /// Candidate TCB features explicitly opted into on the CLI.
    pub allow_candidate_features: Vec<String>,
    /// Active release channel (`alpha` or `stable`).
    pub release_channel: ReleaseChannel,
}

/// Summary returned by a successful [`verify_crate_with_report`] invocation.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Sorted list of candidate TCB features active during verification.
    pub candidate_features: Vec<String>,
    /// Human-readable verification summary (including the
    /// `[candidate-tcb-audit]` report when candidate features are active).
    pub output_text: String,
}

/// The only `PATH` passed to child processes.
const CHILD_PATH: &str = "/usr/bin:/bin";

/// Dynamic library search path environment variable for `rustc` and
/// `anneal-rustc-capture` child processes.
const DYLIB_PATH_VAR: &str = if cfg!(target_os = "macos") {
    "DYLD_LIBRARY_PATH"
} else {
    "LD_LIBRARY_PATH"
};

/// Allowed subdirectories and regular files inside a target crate.
///
/// `.anneal/Mir.lean` and `.anneal/Proof.lean` are permitted to exist on disk
/// so legacy or editor-generated artifacts do not break directory validation,
/// but `cargo-anneal` never reads `.anneal/` as input.
const CRATE_DIRS: [&str; 2] = ["src", ".anneal"];
const CRATE_FILES: [&str; 6] = [
    "Cargo.toml",
    "Cargo.lock",
    "anneal-tcb.lock",
    "src/lib.rs",
    ".anneal/Mir.lean",
    ".anneal/Proof.lean",
];

/// Rust editions accepted by target crate validation (`anneal-rustc-capture`
/// further narrows to `"2024"`).
const EDITIONS: [&str; 4] = ["2015", "2018", "2021", "2024"];

/// Ordered list of `Trusted` Lean source file paths under `trusted/lean/`.
const TRUSTED_LEAN_PATHS: [&str; 5] = [
    "Trusted/Refinement.lean",
    "Trusted/StepResult.lean",
    "Trusted/MirAst.lean",
    "Trusted/MirSemantics.lean",
    "Trusted.lean",
];

/// Ordered list of `Anneal` Lean source file paths under `theory/`.
const THEORY_LEAN_PATHS: [&str; 5] = [
    "Anneal/Refinement.lean",
    "Anneal/StepResult.lean",
    "Anneal/Lowering.lean",
    "Anneal/MirLemmas.lean",
    "Anneal.lean",
];

/// `trusted/rustc-capture` source file paths used to build
/// `anneal-rustc-capture`.
const RUSTC_CAPTURE_PATHS: [&str; 7] = [
    "src/main.rs",
    "src/hook.rs",
    "src/extract.rs",
    "src/items.rs",
    "src/ir.rs",
    "src/lean.rs",
    "src/spec.rs",
];

/// Keywords forbidden in generated `Mir.lean` modules by the pre-compilation
/// syntax gate (`THREAT_MODEL.md` Section 3.1).
const FORBIDDEN_MIR_KEYWORDS: &[&str] = &[
    "open",
    "export",
    "macro",
    "macro_rules",
    "elab",
    "elab_rules",
    "syntax",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "scoped",
    "instance",
    "local",
    "attribute",
    "initialize",
    "builtin_initialize",
    "unsafe",
    "partial",
    "noncomputable",
    "axiom",
    "opaque",
    "sorry",
];

// ---------------------------------------------------------------------------
// Low-level file, hash, and process helpers
// ---------------------------------------------------------------------------

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn has_dot_segment(path: &Path) -> bool {
    path.as_os_str()
        .as_bytes()
        .split(|b| *b == b'/')
        .any(|seg| seg == b"." || seg == b"..")
}

/// Reads a regular file after verifying with `lstat` and `fstat` that `path`
/// is not a symlink and did not change `(dev, ino)` between `lstat` and `open`.
fn read_regular(path: &Path, phase: &str) -> Result<Vec<u8>, String> {
    let lmeta = fs::symlink_metadata(path)
        .map_err(|e| format!("{phase}: cannot stat {}: {e}", path.display()))?;
    if !lmeta.file_type().is_file() {
        return Err(format!(
            "{phase}: expected regular file (not symlink or directory): {}",
            path.display()
        ));
    }
    let mut file = fs::File::open(path)
        .map_err(|e| format!("{phase}: cannot open {}: {e}", path.display()))?;
    let fmeta = file
        .metadata()
        .map_err(|e| format!("{phase}: cannot fstat {}: {e}", path.display()))?;
    if !fmeta.file_type().is_file()
        || (lmeta.dev(), lmeta.ino()) != (fmeta.dev(), fmeta.ino())
    {
        return Err(format!(
            "{phase}: file changed inode or type between lstat and open: {}",
            path.display()
        ));
    }
    let mut buf = Vec::with_capacity(fmeta.len() as usize);
    io::Read::read_to_end(&mut file, &mut buf)
        .map_err(|e| format!("{phase}: cannot read {}: {e}", path.display()))?;
    Ok(buf)
}

fn sha256_file(path: &Path, phase: &str) -> Result<String, String> {
    Ok(sha256_bytes(&read_regular(path, phase)?))
}

fn set_readonly(path: &Path, phase: &str) -> Result<(), String> {
    fs::set_permissions(path, fs::Permissions::from_mode(0o444)).map_err(|e| {
        format!("{phase}: cannot mark {} read-only (0444): {e}", path.display())
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ExpectedKind {
    RegularFile,
    Directory,
}

fn beneath(
    root: &Path,
    rel: &str,
    phase: &str,
    expected: ExpectedKind,
) -> Result<PathBuf, String> {
    let bad = || format!("{phase}: invalid relative path: {rel}");
    let components: Vec<_> = Path::new(rel).components().collect();
    if components.is_empty()
        || rel.contains('\\')
        || has_dot_segment(Path::new(rel))
    {
        return Err(bad());
    }
    let mut cur = root.to_path_buf();
    for (i, comp) in components.iter().enumerate() {
        let Component::Normal(seg) = comp else {
            return Err(bad());
        };
        cur.push(seg);
        let meta = fs::symlink_metadata(&cur)
            .map_err(|e| format!("{phase}: cannot inspect {rel}: {e}"))?;
        let is_last = i + 1 == components.len();
        let file_expected = is_last && expected == ExpectedKind::RegularFile;
        if (file_expected && !meta.is_file())
            || (!file_expected && !meta.is_dir())
        {
            return Err(format!(
                "{phase}: {rel} must be a regular file beneath real directories"
            ));
        }
    }
    Ok(cur)
}

fn private_tempdir(prefix: &str) -> Result<TempDir, String> {
    tempfile::Builder::new()
        .prefix(prefix)
        .tempdir_in("/tmp")
        .map_err(|e| format!("failed to create private /tmp directory: {e}"))
}

fn child_command(program: &Path) -> Command {
    let mut cmd = Command::new(program);
    cmd.env_clear().env("PATH", CHILD_PATH).current_dir("/");
    cmd
}

// ---------------------------------------------------------------------------
// Toolchain and Anneal root resolution
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Toolchain {
    root: PathBuf,
    lean: PathBuf,
    rustc: PathBuf,
    rust_lib: PathBuf,
    sysroot: PathBuf,
}

fn resolve_toolchain(root: &Path) -> Result<Toolchain, String> {
    let phase = "toolchain";
    let canonical = fs::canonicalize(root).map_err(|e| {
        format!("{phase}: cannot resolve toolchain {}: {e}", root.display())
    })?;
    let lean =
        beneath(&canonical, "lean/bin/lean", phase, ExpectedKind::RegularFile)?;
    let rustc =
        beneath(&canonical, "rust/bin/rustc", phase, ExpectedKind::RegularFile)?;
    let rust_lib =
        beneath(&canonical, "rust/lib", phase, ExpectedKind::Directory)?;
    let sysroot = beneath(&canonical, "rust", phase, ExpectedKind::Directory)?;
    Ok(Toolchain {
        root: canonical,
        lean,
        rustc,
        rust_lib,
        sysroot,
    })
}

/// Source buffers loaded from `--anneal-root`.
struct AnnealRootSources {
    foundation_lock: Vec<u8>,
    trusted_lean: Vec<(&'static str, Vec<u8>)>,
    theory_lean: Vec<(&'static str, Vec<u8>)>,
    rustc_capture: Option<Vec<(&'static str, Vec<u8>)>>,
}

fn load_anneal_root(anneal_root: &Path) -> Result<AnnealRootSources, String> {
    let phase = "anneal-root";
    let canonical = fs::canonicalize(anneal_root).map_err(|e| {
        format!(
            "{phase}: cannot resolve anneal root {}: {e}",
            anneal_root.display()
        )
    })?;
    let load_file = |rel: &str| -> Result<Vec<u8>, String> {
        let path = beneath(&canonical, rel, phase, ExpectedKind::RegularFile)?;
        read_regular(&path, phase)
    };

    let foundation_lock = load_file("trusted/lean/foundation-lock.json")?;
    let mut trusted_lean = Vec::with_capacity(TRUSTED_LEAN_PATHS.len());
    for rel in TRUSTED_LEAN_PATHS {
        trusted_lean.push((rel, load_file(&format!("trusted/lean/{rel}"))?));
    }
    let mut theory_lean = Vec::with_capacity(THEORY_LEAN_PATHS.len());
    for rel in THEORY_LEAN_PATHS {
        theory_lean.push((rel, load_file(&format!("theory/{rel}"))?));
    }
    let rustc_capture = if canonical.join("trusted/rustc-capture").exists() {
        let mut sources = Vec::with_capacity(RUSTC_CAPTURE_PATHS.len());
        for rel in RUSTC_CAPTURE_PATHS {
            sources.push((rel, load_file(&format!("trusted/rustc-capture/{rel}"))?));
        }
        Some(sources)
    } else {
        None
    };

    Ok(AnnealRootSources {
        foundation_lock,
        trusted_lean,
        theory_lean,
        rustc_capture,
    })
}

// ---------------------------------------------------------------------------
// Target crate validation
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetManifest {
    package: TargetPackage,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetPackage {
    name: String,
    edition: String,
    #[serde(default)]
    #[allow(dead_code)]
    version: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    authors: Option<Vec<String>>,
    #[serde(default)]
    #[allow(dead_code)]
    description: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    license: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    repository: Option<String>,
    #[serde(default)]
    metadata: Option<TargetMetadata>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetMetadata {
    anneal: TargetAnnealMetadata,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetAnnealMetadata {
    #[serde(rename = "trust-policy")]
    trust_policy: TargetTrustPolicy,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TargetTrustPolicy {
    #[serde(rename = "allow-candidate-features")]
    allow_candidate_features: Vec<String>,
}

#[derive(Debug, Clone)]
struct ValidatedTargetCrate {
    crate_name: String,
    edition: String,
    allow_candidate_features: Vec<String>,
    lib_rs_bytes: Vec<u8>,
    tcb_lock_bytes: Option<Vec<u8>>,
}

fn validate_target_crate(path: &Path) -> Result<ValidatedTargetCrate, String> {
    let phase = "target-crate";
    if has_dot_segment(path) {
        return Err(format!(
            "{phase}: crate path must not contain `.` or `..`: {}",
            path.display()
        ));
    }
    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir()
            .map_err(|e| format!("{phase}: no current dir: {e}"))?
            .join(path)
    };
    let root = fs::canonicalize(&abs).map_err(|e| {
        format!("{phase}: cannot resolve {}: {e}", abs.display())
    })?;
    if root != abs || !root.is_dir() {
        return Err(format!(
            "{phase}: crate path must be a directory with no symlinked component: {}",
            abs.display()
        ));
    }

    for anc in root.ancestors() {
        if anc.file_name().is_some_and(|n| n == ".gemini") {
            break;
        }
        for rel in [
            ".cargo/config",
            ".cargo/config.toml",
            "rust-toolchain",
            "rust-toolchain.toml",
        ] {
            let candidate = anc.join(rel);
            if fs::symlink_metadata(&candidate).is_ok() {
                return Err(format!(
                    "{phase}: disallowed toolchain or Cargo config at {}",
                    candidate.display()
                ));
            }
        }
    }

    for entry in WalkDir::new(&root).min_depth(1).follow_links(false) {
        let entry = entry
            .map_err(|e| format!("{phase}: cannot walk target crate: {e}"))?;
        let rel = entry.path().strip_prefix(&root).unwrap_or(entry.path());
        let rel_str = rel.to_string_lossy();
        let ft = entry.file_type();
        let ok = (ft.is_dir() && CRATE_DIRS.contains(&rel_str.as_ref()))
            || (ft.is_file() && CRATE_FILES.contains(&rel_str.as_ref()));
        if !ok {
            return Err(format!(
                "{phase}: target crate may contain only {CRATE_FILES:?} as regular \
                 files; found {rel_str}"
            ));
        }
    }

    let lib_rs_bytes = read_regular(&root.join("src/lib.rs"), phase)?;
    let cargo_toml_bytes = read_regular(&root.join("Cargo.toml"), phase)?;
    let tcb_lock_path = root.join("anneal-tcb.lock");
    let tcb_lock_bytes = if fs::symlink_metadata(&tcb_lock_path).is_ok() {
        Some(read_regular(&tcb_lock_path, phase)?)
    } else {
        None
    };
    let text = String::from_utf8(cargo_toml_bytes)
        .map_err(|_| format!("{phase}: Cargo.toml is not UTF-8"))?;
    let manifest: TargetManifest = toml::from_str(&text).map_err(|e| {
        format!("{phase}: Cargo.toml outside the allowed schema: {e}")
    })?;
    let pkg = manifest.package;
    let mut name_chars = pkg.name.chars();
    let name_ok = name_chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name_chars
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-');
    if !name_ok {
        return Err(format!("{phase}: invalid package.name `{}`", pkg.name));
    }
    if !EDITIONS.contains(&pkg.edition.as_str()) {
        return Err(format!(
            "{phase}: unsupported package.edition `{}`",
            pkg.edition
        ));
    }
    Ok(ValidatedTargetCrate {
        crate_name: pkg.name.replace('-', "_"),
        edition: pkg.edition,
        allow_candidate_features: pkg
            .metadata
            .map(|m| m.anneal.trust_policy.allow_candidate_features)
            .unwrap_or_default(),
        lib_rs_bytes,
        tcb_lock_bytes,
    })
}

// ---------------------------------------------------------------------------
// Pre-compilation `Mir.lean` AST gate and `anneal-tcb.lock` waiver enforcement
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(deny_unknown_fields)]
struct TcbWaiverEntry {
    item: String,
    kind: String,
    reason: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TcbLockFile {
    #[serde(default)]
    waivers: Vec<TcbWaiverEntry>,
}

/// Strips double-quoted string literals (`"..."`) and trailing line comments
/// (`-- ...`) from a single line of Lean source so identifier scanning does not
/// inspect string or comment contents.
fn strip_lean_strings_and_line_comment(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();
    let mut in_str = false;
    while let Some(c) = chars.next() {
        if in_str {
            if c == '\\' {
                let _ = chars.next();
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        if c == '"' {
            in_str = true;
            out.push(' ');
            continue;
        }
        if c == '-' && chars.peek() == Some(&'-') {
            break;
        }
        out.push(c);
    }
    out
}

fn parse_waiver_comment(line: &str) -> Result<Option<TcbWaiverEntry>, String> {
    let Some(rest) = line.trim().strip_prefix("-- anneal-waiver:") else {
        return Ok(None);
    };
    let rest = rest.trim();
    let Some(rest) = rest.strip_prefix("fnBody ") else {
        return Err(format!("tcb-lock: malformed waiver header `{line}`"));
    };
    let Some((item_lit, reason_lit)) = rest.split_once(" reason = ") else {
        return Err(format!("tcb-lock: malformed waiver header `{line}`"));
    };
    let item: String = serde_json::from_str(item_lit.trim()).map_err(|e| {
        format!("tcb-lock: invalid waiver item literal `{item_lit}`: {e}")
    })?;
    let reason: String =
        serde_json::from_str(reason_lit.trim()).map_err(|e| {
            format!(
                "tcb-lock: invalid waiver reason literal `{reason_lit}`: {e}"
            )
        })?;
    Ok(Some(TcbWaiverEntry {
        item,
        kind: "trusted_fn".to_string(),
        reason,
    }))
}

/// Validates that `mir_lean_src` obeys the pre-compilation syntax and attribute
/// gate (`THREAT_MODEL.md` Section 3.1) and that its `/// anneal:trusted`
/// waivers match `tcb_lock_bytes` in 1-to-1 bijection.
fn validate_mir_lean_and_waivers(
    mir_lean_src: &str,
    tcb_lock_bytes: Option<&[u8]>,
) -> Result<(), String> {
    let mut waivers = Vec::new();
    let mut code_lines = Vec::new();
    for line in mir_lean_src.lines() {
        if let Some(w) = parse_waiver_comment(line)? {
            waivers.push(w);
        }
        let stripped = strip_lean_strings_and_line_comment(line);
        let trimmed = stripped.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.contains("@[") {
            return Err(format!(
                "mir-syntax-gate: forbidden attribute syntax `@[` in Mir.lean: {line}"
            ));
        }
        for tok in
            trimmed.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        {
            if !tok.is_empty() && FORBIDDEN_MIR_KEYWORDS.contains(&tok) {
                return Err(format!(
                    "mir-syntax-gate: forbidden keyword `{tok}` in Mir.lean: {line}"
                ));
            }
        }
        code_lines.push(trimmed.to_string());
    }
    if code_lines.first().map(String::as_str) != Some("prelude")
        || code_lines.get(1).map(String::as_str) != Some("import Trusted")
    {
        return Err(
            "mir-syntax-gate: Mir.lean must begin with `prelude` and `import Trusted`"
                .into(),
        );
    }

    waivers.sort();
    match (waivers.is_empty(), tcb_lock_bytes) {
        (true, None) => Ok(()),
        (false, None) => Err(format!(
            "tcb-lock: crate uses `/// anneal:trusted` waivers ({:?}) but \
             `anneal-tcb.lock` is missing",
            waivers.iter().map(|w| &w.item).collect::<Vec<_>>()
        )),
        (_, Some(bytes)) => {
            let text = std::str::from_utf8(bytes)
                .map_err(|_| "tcb-lock: anneal-tcb.lock is not UTF-8")?;
            let mut lock: TcbLockFile = toml::from_str(text).map_err(|e| {
                format!("tcb-lock: invalid anneal-tcb.lock schema: {e}")
            })?;
            lock.waivers.sort();
            if lock.waivers != waivers {
                return Err(format!(
                    "tcb-lock: `anneal-tcb.lock` waivers {:?} do not match \
                     crate waivers {:?}",
                    lock.waivers, waivers
                ));
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// Candidate TCB feature discovery & policy check
// ---------------------------------------------------------------------------

/// Trust tier declared by a `Trusted` Lean module via
/// `-- anneal-trust-tier: <tier>`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ModuleTrustTier {
    Vetted,
    Candidate(String),
}

/// Parses the `-- anneal-trust-tier:` header from a `Trusted` Lean module.
fn parse_module_trust_tier(
    source: &str,
    rel_path: &str,
) -> Result<ModuleTrustTier, String> {
    let mut found: Option<ModuleTrustTier> = None;
    for line in source.lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix("-- anneal-trust-tier:") else {
            continue;
        };
        if found.is_some() {
            return Err(format!(
                "duplicate `-- anneal-trust-tier:` header in {rel_path}"
            ));
        }
        let tier = rest.trim();
        if tier == "vetted" {
            found = Some(ModuleTrustTier::Vetted);
        } else if let Some(feat) = tier.strip_prefix("candidate:") {
            let valid = !feat.is_empty()
                && feat
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_');
            if !valid {
                return Err(format!(
                    "invalid candidate feature name `{feat}` in {rel_path}"
                ));
            }
            found = Some(ModuleTrustTier::Candidate(feat.to_string()));
        } else {
            return Err(format!(
                "invalid `-- anneal-trust-tier: {tier}` header in {rel_path}"
            ));
        }
    }
    found.ok_or_else(|| {
        format!("missing `-- anneal-trust-tier:` header in {rel_path}")
    })
}

/// Discovers all candidate TCB features in `TRUSTED_LEAN_PATHS` plus
/// `rustc_capture`, and verifies that the target crate and release channel
/// permit them.
///
/// Returns a map from candidate feature name to the list of TCB components
/// gated by that feature.
fn check_candidate_policy(
    trusted_lean: &[(&'static str, Vec<u8>)],
    crate_allowed: &[String],
    cli_allowed: &[String],
    release_channel: ReleaseChannel,
) -> Result<BTreeMap<String, Vec<String>>, String> {
    let phase = "trust-policy";
    let mut required: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (rel, bytes) in trusted_lean {
        let src = std::str::from_utf8(bytes)
            .map_err(|_| format!("{phase}: {rel} is not UTF-8"))?;
        let display_rel = format!("trusted/lean/{rel}");
        match parse_module_trust_tier(src, &display_rel)? {
            ModuleTrustTier::Vetted => {}
            ModuleTrustTier::Candidate(feat) => {
                required.entry(feat).or_default().push(display_rel);
            }
        }
    }
    required
        .entry("rustc_capture".to_string())
        .or_default()
        .push("trusted/rustc-capture".to_string());

    let mut allowed: BTreeSet<String> = BTreeSet::new();
    for feat in crate_allowed.iter().chain(cli_allowed.iter()) {
        allowed.insert(feat.clone());
    }

    if release_channel == ReleaseChannel::Stable {
        if !required.is_empty() || !allowed.is_empty() {
            return Err(format!(
                "{phase}: candidate features are not permitted on the stable \
                 release channel (active candidate TCB features: {:?})",
                required.keys().collect::<Vec<_>>()
            ));
        }
        return Ok(required);
    }

    let wildcard = allowed.contains("*");
    for feat in &allowed {
        if feat == "*" {
            continue;
        }
        if !required.contains_key(feat) {
            return Err(format!(
                "{phase}: unknown candidate feature `{feat}` in allow-candidate-features \
                 (known candidate features: {:?})",
                required.keys().collect::<Vec<_>>()
            ));
        }
    }

    if !wildcard {
        let missing: Vec<String> = required
            .keys()
            .filter(|feat| !allowed.contains(*feat))
            .cloned()
            .collect();
        if !missing.is_empty() {
            return Err(format!(
                "{phase}: verification requires candidate TCB features {missing:?}; \
                 opt in via `--allow-candidate-features {}` or \
                 `[package.metadata.anneal.trust-policy] allow-candidate-features`",
                missing.join(",")
            ));
        }
    }

    Ok(required)
}

/// Validated and policy-checked inputs for a single capture or verification
/// invocation.
struct PreparedVerify {
    target: ValidatedTargetCrate,
    tc: Toolchain,
    root: AnnealRootSources,
    active_candidates: BTreeMap<String, Vec<String>>,
}

fn prepare_verify(config: &VerifyConfig) -> Result<PreparedVerify, String> {
    let target = validate_target_crate(&config.crate_dir)?;
    let tc = resolve_toolchain(&config.toolchain_dir)?;
    let root = load_anneal_root(&config.anneal_root)?;
    let active_candidates = check_candidate_policy(
        &root.trusted_lean,
        &target.allow_candidate_features,
        &config.allow_candidate_features,
        config.release_channel,
    )?;
    Ok(PreparedVerify {
        target,
        tc,
        root,
        active_candidates,
    })
}

// ---------------------------------------------------------------------------
// Building and running `anneal-rustc-capture`
// ---------------------------------------------------------------------------

/// Builds (or resolves) the `anneal-rustc-capture` binary for `tc` from the
/// [`AnnealRootSources`] sources in a process-cached private `/tmp` directory
/// (or uses `tc.root/bin/anneal-rustc-capture` when running from an installed
/// archive without `trusted/rustc-capture` sources).
fn ensure_rustc_capture_bin(
    tc: &Toolchain,
    root: &AnnealRootSources,
) -> Result<PathBuf, String> {
    static BUILT_CAPTURE: Mutex<BTreeMap<PathBuf, (Arc<TempDir>, PathBuf)>> =
        Mutex::new(BTreeMap::new());

    let Some(rustc_capture_sources) = &root.rustc_capture else {
        let prebuilt = tc.root.join("bin/anneal-rustc-capture");
        if prebuilt.is_file() {
            return Ok(prebuilt);
        }
        return Err(format!(
            "missing both trusted/rustc-capture sources and {}",
            prebuilt.display()
        ));
    };

    let mut cache = BUILT_CAPTURE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, bin)) = cache.get(&tc.root) {
        return Ok(bin.clone());
    }

    let stage = Arc::new(private_tempdir("anneal-capture-build-")?);
    let src_stage = stage.path().join("rustc-capture");
    fs::create_dir_all(src_stage.join("src"))
        .map_err(|e| format!("cannot create capture staging dir: {e}"))?;

    for (rel, bytes) in rustc_capture_sources {
        fs::write(src_stage.join(rel), bytes)
            .map_err(|e| format!("cannot write staged {rel}: {e}"))?;
    }

    let bin = stage.path().join("anneal-rustc-capture");
    let out = child_command(&tc.rustc)
        .arg("--edition=2024")
        .arg("--crate-name")
        .arg("anneal_rustc_capture")
        .arg("--sysroot")
        .arg(&tc.sysroot)
        .arg(src_stage.join("src/main.rs"))
        .arg("-o")
        .arg(&bin)
        .env(DYLIB_PATH_VAR, &tc.rust_lib)
        .output()
        .map_err(|e| format!("failed to spawn rustc for rustc-capture: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "failed to build anneal-rustc-capture:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        ));
    }

    if !bin.is_file() {
        return Err(format!(
            "rustc build succeeded but {} is missing",
            bin.display()
        ));
    }
    cache.insert(tc.root.clone(), (stage, bin.clone()));
    Ok(bin)
}

fn capture_prepared(prep: &PreparedVerify) -> Result<String, String> {
    let capture_bin = ensure_rustc_capture_bin(&prep.tc, &prep.root)?;
    let stage = private_tempdir("anneal-capture-run-")?;
    let staged_src_dir = stage.path().join("src");
    fs::create_dir_all(&staged_src_dir)
        .map_err(|e| format!("cannot create staged src dir: {e}"))?;
    let staged_lib_rs = staged_src_dir.join("lib.rs");
    fs::write(&staged_lib_rs, &prep.target.lib_rs_bytes)
        .map_err(|e| format!("cannot write staged src/lib.rs: {e}"))?;

    let out_mir = stage.path().join("Mir.lean");

    let out = child_command(&capture_bin)
        .arg("--sysroot")
        .arg(&prep.tc.sysroot)
        .arg("--edition")
        .arg(&prep.target.edition)
        .arg("--crate-name")
        .arg(&prep.target.crate_name)
        .arg("--src")
        .arg(&staged_lib_rs)
        .arg("--out")
        .arg(&out_mir)
        .env(DYLIB_PATH_VAR, &prep.tc.rust_lib)
        .output()
        .map_err(|e| format!("failed to run anneal-rustc-capture: {e}"))?;

    if !out.status.success() {
        return Err(format!(
            "anneal-rustc-capture failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        ));
    }

    let mir_bytes = read_regular(&out_mir, "capture-output")?;
    String::from_utf8(mir_bytes)
        .map_err(|_| "generated Mir.lean is not UTF-8".to_string())
}

/// Validates the target crate, runs `anneal-rustc-capture` in a private `/tmp`
/// directory on the pinned `src/lib.rs` bytes, and returns the captured
/// `Mir.lean` source string.
pub fn capture(config: &VerifyConfig) -> Result<String, String> {
    let prep = prepare_verify(config)?;
    capture_prepared(&prep)
}

// ---------------------------------------------------------------------------
// Lean foundation & prefix compilation and crate verification
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct FoundationLock {
    distributions: BTreeMap<String, String>,
    modules: BTreeMap<String, FoundationModule>,
}

#[derive(Deserialize)]
struct FoundationModule {
    parts: BTreeMap<String, String>,
}

fn verify_foundation_lock(
    tc: &Toolchain,
    foundation_lock_bytes: &[u8],
) -> Result<(), String> {
    let phase = "foundation-lock";
    let lock: FoundationLock = serde_json::from_slice(foundation_lock_bytes)
        .map_err(|e| format!("{phase}: invalid JSON: {e}"))?;

    let ver_out = child_command(&tc.lean)
        .arg("--version")
        .output()
        .map_err(|e| format!("{phase}: failed to run lean --version: {e}"))?;
    if !ver_out.status.success() {
        return Err(format!("{phase}: lean --version exited with error"));
    }
    let ver_line = String::from_utf8_lossy(&ver_out.stdout)
        .lines()
        .next()
        .unwrap_or("")
        .trim()
        .to_string();
    let expected_lean_sha = lock.distributions.get(&ver_line).ok_or_else(|| {
        format!(
            "{phase}: Lean version string `{ver_line}` not found in foundation-lock.json"
        )
    })?;
    let actual_lean_sha = sha256_file(&tc.lean, phase)?;
    if &actual_lean_sha != expected_lean_sha {
        return Err(format!(
            "{phase}: lean binary SHA-256 mismatch ({actual_lean_sha} != {expected_lean_sha})"
        ));
    }

    let lean_lib = tc.root.join("lean/lib/lean");
    for (mod_name, mod_entry) in &lock.modules {
        let rel_base = mod_name.replace('.', "/");
        for (ext, expected_sha) in &mod_entry.parts {
            let rel = format!("{rel_base}.{ext}");
            let path =
                beneath(&lean_lib, &rel, phase, ExpectedKind::RegularFile)?;
            let actual_sha = sha256_file(&path, phase)?;
            if &actual_sha != expected_sha {
                return Err(format!(
                    "{phase}: foundation artifact {rel} SHA-256 mismatch \
                     ({actual_sha} != {expected_sha})"
                ));
            }
        }
    }
    Ok(())
}

fn compile_lean_file(
    tc: &Toolchain,
    lean_path: &str,
    src_file: &Path,
    out_olean: &Path,
) -> Result<(), String> {
    if let Some(parent) = out_olean.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            format!("cannot create parent directory {}: {e}", parent.display())
        })?;
    }
    let out = child_command(&tc.lean)
        .env("LEAN_PATH", lean_path)
        .arg("-DwarningAsError=true")
        .arg("-DElab.async=false")
        .arg("-Ddebug.skipKernelTC=false")
        .arg("-t0")
        .arg("-o")
        .arg(out_olean)
        .arg(src_file)
        .output()
        .map_err(|e| {
            format!("failed to invoke lean on {}: {e}", src_file.display())
        })?;
    if !out.status.success() {
        return Err(format!(
            "lean failed on {}:\nstdout:\n{}\nstderr:\n{}",
            src_file.display(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        ));
    }
    Ok(())
}

/// Compiles `Trusted` and `Anneal` `.olean`s into a process-cached private
/// `/tmp` directory from [`AnnealRootSources`].
fn ensure_compiled_prefix(
    tc: &Toolchain,
    root: &AnnealRootSources,
) -> Result<Arc<TempDir>, String> {
    static PREFIX_CACHE: Mutex<BTreeMap<PathBuf, Arc<TempDir>>> =
        Mutex::new(BTreeMap::new());

    let mut cache = PREFIX_CACHE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(dir) = cache.get(&tc.root) {
        return Ok(dir.clone());
    }

    verify_foundation_lock(tc, &root.foundation_lock)?;

    let prefix_dir = Arc::new(private_tempdir("anneal-lean-prefix-")?);
    let lean_sys_lib = tc.root.join("lean/lib/lean");
    let lean_path = format!(
        "{}:{}",
        prefix_dir.path().display(),
        lean_sys_lib.display()
    );

    for (rel, bytes) in root
        .trusted_lean
        .iter()
        .chain(root.theory_lean.iter())
    {
        let staged_src = prefix_dir.path().join("src").join(rel);
        if let Some(parent) = staged_src.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "cannot create staged Lean source dir {}: {e}",
                    parent.display()
                )
            })?;
        }
        fs::write(&staged_src, bytes).map_err(|e| {
            format!("cannot write staged Lean source {rel}: {e}")
        })?;
        let out_olean = prefix_dir
            .path()
            .join(rel.strip_suffix(".lean").unwrap_or(rel))
            .with_extension("olean");
        compile_lean_file(tc, &lean_path, &staged_src, &out_olean)?;
    }

    cache.insert(tc.root.clone(), prefix_dir.clone());
    Ok(prefix_dir)
}

/// Verifies the crate described by `config` and returns a [`VerifyReport`]
/// including any active `[candidate-tcb-audit]` details.
pub fn verify_crate_with_report(
    config: &VerifyConfig,
) -> Result<VerifyReport, String> {
    let prep = prepare_verify(config)?;
    let mir_lean_src = capture_prepared(&prep)?;
    validate_mir_lean_and_waivers(
        &mir_lean_src,
        prep.target.tcb_lock_bytes.as_deref(),
    )?;
    let prefix_dir = ensure_compiled_prefix(&prep.tc, &prep.root)?;

    let verify_dir = private_tempdir("anneal-verify-")?;
    let mir_lean_path = verify_dir.path().join("Mir.lean");
    let mir_olean_path = verify_dir.path().join("Mir.olean");
    let proof_lean_path = verify_dir.path().join("Proof.lean");
    fs::write(&mir_lean_path, &mir_lean_src)
        .map_err(|e| format!("cannot write staged Mir.lean: {e}"))?;
    fs::write(&proof_lean_path, PROOF_LEAN_SOURCE)
        .map_err(|e| format!("cannot write staged Proof.lean: {e}"))?;

    let lean_sys_lib = prep.tc.root.join("lean/lib/lean");
    let lean_path = format!(
        "{}:{}:{}",
        verify_dir.path().display(),
        prefix_dir.path().display(),
        lean_sys_lib.display()
    );

    compile_lean_file(&prep.tc, &lean_path, &mir_lean_path, &mir_olean_path)?;
    set_readonly(&mir_lean_path, "verify")?;
    set_readonly(&mir_olean_path, "verify")?;
    let mir_olean_sha = sha256_file(&mir_olean_path, "verify")?;

    compile_lean_file(
        &prep.tc,
        &lean_path,
        &proof_lean_path,
        &verify_dir.path().join("Proof.olean"),
    )?;
    let post_mir_olean_sha = sha256_file(&mir_olean_path, "verify")?;
    if post_mir_olean_sha != mir_olean_sha {
        return Err(
            "verify: Mir.olean was modified during Proof.lean compilation"
                .into(),
        );
    }

    let candidate_features: Vec<String> =
        prep.active_candidates.keys().cloned().collect();
    let mut output_text = format!(
        "verified crate `{}` (Proof.verify_crate : Trusted.CrateTheorem Mir.crate)\n",
        prep.target.crate_name
    );
    if !prep.active_candidates.is_empty() {
        output_text.push_str(&format!(
            "Candidate-Trusted TCB (Unvetted / Alpha): {}\n",
            candidate_features.join(", ")
        ));
        output_text.push_str("[candidate-tcb-audit]\n");
        for (feat, origins) in &prep.active_candidates {
            output_text.push_str(&format!(
                "  candidate:{feat} -> {}\n",
                origins.join(", ")
            ));
        }
    }

    Ok(VerifyReport {
        candidate_features,
        output_text,
    })
}

/// Verifies the crate described by `config`.
pub fn verify_crate(config: &VerifyConfig) -> Result<(), String> {
    verify_crate_with_report(config).map(|_| ())
}
