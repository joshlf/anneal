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
//!    ([`validate_target_crate`]), pinning `Cargo.toml` and `src/lib.rs` via
//!    `lstat`/`fstat` `(dev, ino)` verification without ever reading `.anneal/`.
//! 2. Authenticates the toolchain directory against the compiled-in
//!    `toolchain-lock.sha256` manifest ([`authenticate_toolchain`]) and
//!    `trusted/lean/foundation-lock.json`.
//! 3. Enforces candidate trust-tier opt-in (`[package.metadata.anneal.trust-policy]`
//!    and `--allow-candidate-features`) and release-channel gating (`alpha` vs.
//!    `stable`).
//! 4. Invokes `anneal-rustc-capture` in a private `/tmp` directory to extract
//!    the target crate's first-order `Mir.lean` AST and verifies from `rustc`'s
//!    escaped dep-info that `src/lib.rs` was the sole source file read.
//! 5. Compiles `Mir.lean` and the static 8-line [`PROOF_LEAN_SOURCE`] against
//!    the precompiled `Trusted` and `Anneal` `.olean`s with the Lean 4 kernel
//!    (`-Ddebug.skipKernelTC=false -t0`).

pub mod setup;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io;
use std::ops::Deref;
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
/// identical. Evaluating `Anneal.checkCrate Mir.crate` before `verify_crate`
/// prints `[]` on passing crates and `["<message>", "<scope>"]` on failing
/// crates so `cargo-anneal` can report the exact failing item and cause from
/// the single `lean Proof.lean` invocation.
pub const PROOF_LEAN_SOURCE: &str = "\
prelude
import Trusted
import Anneal
import Mir

#eval Anneal.checkCrate Mir.crate

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
    /// Returns the default release channel for this `cargo-anneal` binary
    /// (`Alpha` when `CARGO_PKG_VERSION` carries a pre-release suffix such as
    /// `-alpha`, `Stable` otherwise).
    pub fn default_for_binary() -> Self {
        if env!("CARGO_PKG_VERSION").contains('-') {
            Self::Alpha
        } else {
            Self::Stable
        }
    }

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

    /// Resolves the active release channel from an optional `--release-channel`
    /// CLI override, enforcing that a `Stable` binary cannot be downgraded to
    /// `Alpha`.
    pub fn resolve(override_str: Option<&str>) -> Result<Self, String> {
        let default_channel = Self::default_for_binary();
        let Some(raw) = override_str else {
            return Ok(default_channel);
        };
        let parsed = Self::parse(raw)?;
        if default_channel == Self::Stable && parsed == Self::Alpha {
            return Err(
                "`--release-channel alpha` is not permitted in a stable cargo-anneal release"
                    .to_string(),
            );
        }
        Ok(parsed)
    }
}

/// Pipeline stage and item scope for a structured verification failure.
///
/// Modeling `Capture` and `Proof` as distinct variants ensures that `Capture`
/// failures never carry a proof item scope and `Proof` failures always carry
/// `scope` (`"crate"` or `<fn_name>`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailureStage {
    /// `anneal-rustc-capture` rejected the target crate during MIR extraction.
    Capture,
    /// `Anneal.checkCrate` / `Anneal.proveCrate` failed on `scope` (`"crate"`
    /// or `<fn_name>`).
    Proof {
        /// Item scope (`"crate"` or `<fn_name>`) reported by `Anneal.checkCrate`.
        scope: String,
    },
}

/// Structured stage and diagnostic payload for a capture or proof failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StageFailure {
    /// Pipeline stage (and item scope for `Proof`) where verification failed.
    pub stage: FailureStage,
    /// Diagnostic text for the failing stage (`anneal-rustc-capture` stderr or
    /// `Anneal.checkCrate` diagnostic message).
    pub diagnostic: String,
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

/// Summary returned by a successful [`verify_crate`] invocation.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Captured first-order `Mir.lean` module source for the target crate.
    pub mir_lean: String,
    /// Human-readable verification summary (including the
    /// `[candidate-tcb-audit]` report when candidate features are active).
    pub output_text: String,
}

/// Error returned by [`verify_crate`], preserving structured stage attribution
/// and the captured `Mir.lean` module source when verification fails after MIR
/// capture succeeds.
#[derive(Debug, Clone)]
pub struct VerifyError {
    /// Human-readable error message.
    pub message: String,
    /// Structured pipeline stage and diagnostic when the failure occurred in
    /// crate capture or proof checking (as opposed to host configuration,
    /// manifest validation, or toolchain authentication).
    pub failure: Option<StageFailure>,
    /// Captured `Mir.lean` module source, if MIR capture succeeded before the
    /// failure occurred.
    pub mir_lean: Option<String>,
}

impl VerifyError {
    fn new(message: String) -> Self {
        Self {
            message,
            failure: None,
            mir_lean: None,
        }
    }

    fn capture(stdout: &str, stderr: &str) -> Self {
        let message = format!(
            "anneal-rustc-capture failed:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        Self {
            message,
            failure: Some(StageFailure {
                stage: FailureStage::Capture,
                diagnostic: stderr.to_string(),
            }),
            mir_lean: None,
        }
    }

    fn with_mir(
        message: String,
        mir_lean: String,
        failure: Option<StageFailure>,
    ) -> Self {
        Self {
            message,
            failure,
            mir_lean: Some(mir_lean),
        }
    }
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl Deref for VerifyError {
    type Target = str;

    fn deref(&self) -> &str {
        &self.message
    }
}

/// Compiled-in SHA-256 lock of the toolchain's `lean/` and `rust/` trees.
const TOOLCHAIN_LOCK: &str = include_str!("toolchain-lock.sha256");

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
const CRATE_FILES: [&str; 5] = [
    "Cargo.toml",
    "Cargo.lock",
    "src/lib.rs",
    ".anneal/Mir.lean",
    ".anneal/Proof.lean",
];

/// Compiled-in SHA-256 manifest authenticating `trusted/lean/`, `theory/`, and
/// `trusted/rustc-capture/` under `--anneal-root`.
///
/// The entry order in `anneal-sources.sha256` is also the canonical compilation
/// order for `trusted/lean/*.lean` and `theory/*.lean`.
const LOCKED_ANNEAL_SOURCES: &str = include_str!("anneal-sources.sha256");

// ---------------------------------------------------------------------------
// Low-level file, hash, and process helpers
// ---------------------------------------------------------------------------

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

fn has_dot_segment(path: &Path) -> bool {
    path.as_os_str()
        .as_bytes()
        .split(|b| *b == b'/')
        .any(|seg| seg == b"." || seg == b"..")
}

/// Inode and timestamp fingerprint captured via `fstat`/`lstat` to detect
/// post-authentication replacement or in-place modification.
///
/// Note: `ctime` is intentionally excluded because creating or dropping a
/// private hardlink snapshot increments/decrements `st_nlink` on the shared
/// inode, which updates `st_ctime` across concurrent processes without
/// altering file contents or permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FileFingerprint {
    dev: u64,
    ino: u64,
    mode: u32,
    len: u64,
    mtime: i64,
    mtime_nsec: i64,
}

impl FileFingerprint {
    fn from_meta(meta: &fs::Metadata) -> Self {
        Self {
            dev: meta.dev(),
            ino: meta.ino(),
            mode: meta.mode(),
            len: meta.len(),
            mtime: meta.mtime(),
            mtime_nsec: meta.mtime_nsec(),
        }
    }
}

/// Reads a regular file after verifying with `lstat` and `fstat` that `path`
/// is not a symlink and did not change `(dev, ino)` between `lstat` and `open`,
/// returning both the bytes read from the open descriptor and its `fstat`
/// [`FileFingerprint`].
fn read_regular_with_fp(
    path: &Path,
    phase: &str,
) -> Result<(Vec<u8>, FileFingerprint), String> {
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
    let fp = FileFingerprint::from_meta(&fmeta);
    let mut buf = Vec::with_capacity(fmeta.len() as usize);
    io::Read::read_to_end(&mut file, &mut buf)
        .map_err(|e| format!("{phase}: cannot read {}: {e}", path.display()))?;
    Ok((buf, fp))
}

fn read_regular(path: &Path, phase: &str) -> Result<Vec<u8>, String> {
    Ok(read_regular_with_fp(path, phase)?.0)
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

fn join_env_paths<'a>(
    paths: impl IntoIterator<Item = &'a Path>,
    var_name: &str,
) -> Result<OsString, String> {
    env::join_paths(paths).map_err(|e| {
        format!(
            "cannot construct {var_name} (path contains path-list separator): {e}"
        )
    })
}

fn write_staged(
    base: &Path,
    rel: &str,
    bytes: &[u8],
) -> Result<PathBuf, String> {
    let dst = base.join(rel);
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            format!("cannot create staged directory {}: {e}", parent.display())
        })?;
    }
    fs::write(&dst, bytes)
        .map_err(|e| format!("cannot write staged {rel}: {e}"))?;
    Ok(dst)
}

fn child_command(program: &Path) -> Command {
    let mut cmd = Command::new(program);
    cmd.env_clear().env("PATH", CHILD_PATH).current_dir("/");
    cmd
}

// ---------------------------------------------------------------------------
// Toolchain authentication and private snapshot isolation
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct LockedFileRecord {
    src: PathBuf,
    src_fp: FileFingerprint,
    dst: PathBuf,
    dst_fp: FileFingerprint,
}

#[derive(Debug, Clone)]
struct Toolchain {
    /// Canonical source toolchain path used as the in-process cache key.
    source_root: PathBuf,
    /// Private snapshot directory holding only SHA-256-authenticated files.
    _snapshot: Arc<TempDir>,
    snapshot_root: PathBuf,
    lean: PathBuf,
    rustc: PathBuf,
    rust_lib: PathBuf,
    sysroot: PathBuf,
    locked_files: Arc<Vec<LockedFileRecord>>,
    locked_dirs: Arc<Vec<(PathBuf, String)>>,
}

impl Toolchain {
    /// Verifies that every authenticated file and directory listing in both
    /// the source toolchain and the private snapshot still matches the exact
    /// `(dev, ino, mode, len, mtime_nsec, ctime_nsec)` fingerprint recorded
    /// when its bytes were SHA-256-verified.
    fn verify_unchanged(&self, phase: &str) -> Result<(), String> {
        for rec in self.locked_files.iter() {
            let src_meta = fs::symlink_metadata(&rec.src).map_err(|e| {
                format!(
                    "{phase}: toolchain file disappeared {}: {e}",
                    rec.src.display()
                )
            })?;
            if !src_meta.file_type().is_file()
                || FileFingerprint::from_meta(&src_meta) != rec.src_fp
            {
                return Err(format!(
                    "{phase}: toolchain file modified after authentication: {}",
                    rec.src.display()
                ));
            }
            let dst_meta = fs::symlink_metadata(&rec.dst).map_err(|e| {
                format!(
                    "{phase}: snapshot file disappeared {}: {e}",
                    rec.dst.display()
                )
            })?;
            if !dst_meta.file_type().is_file()
                || FileFingerprint::from_meta(&dst_meta) != rec.dst_fp
            {
                return Err(format!(
                    "{phase}: toolchain snapshot modified after authentication: {}",
                    rec.dst.display()
                ));
            }
        }
        for (dir, want_sha) in self.locked_dirs.iter() {
            let got_sha = listing_digest(dir, phase)?;
            if &got_sha != want_sha {
                return Err(format!(
                    "{phase}: toolchain directory listing modified after authentication: {}",
                    dir.display()
                ));
            }
        }
        Ok(())
    }
}

fn parse_digest_lines(
    text: &str,
    phase: &str,
) -> Result<Vec<(String, String)>, String> {
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let bad = || format!("{phase}: malformed lock line: {line}");
        let (hex, rel) = line.split_once("  ").ok_or_else(bad)?;
        if !is_sha256_hex(hex)
            || has_dot_segment(Path::new(rel))
            || !seen.insert(rel.to_string())
        {
            return Err(bad());
        }
        entries.push((rel.to_string(), hex.to_string()));
    }
    Ok(entries)
}

fn listing_digest(dir: &Path, phase: &str) -> Result<String, String> {
    let mut names = fs::read_dir(dir)
        .and_then(|it| {
            it.map(|e| Ok(e?.file_name().as_bytes().to_vec()))
                .collect::<io::Result<Vec<_>>>()
        })
        .map_err(|e| format!("{phase}: cannot list {}: {e}", dir.display()))?;
    names.sort();
    let mut text = Vec::new();
    for name in names {
        text.extend(name);
        text.push(b'\n');
    }
    Ok(sha256_bytes(&text))
}

/// Reads and hashes a single regular file at `rel` beneath `src_root`, stages
/// it into `snapshot_root/rel` via a verified same-inode hardlink (or direct
/// write of the hashed buffer when across filesystems), and records its
/// [`LockedFileRecord`].
fn stage_locked_file(
    src_root: &Path,
    snapshot_root: &Path,
    rel: &str,
    phase: &str,
    locked_files: &mut Vec<LockedFileRecord>,
) -> Result<String, String> {
    let src = beneath(src_root, rel, phase, ExpectedKind::RegularFile)?;
    let (bytes, src_fp) = read_regular_with_fp(&src, phase)?;
    let sha = sha256_bytes(&bytes);
    let dst = snapshot_root.join(rel);
    if !dst.exists() {
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "{phase}: cannot create snapshot dir {}: {e}",
                    parent.display()
                )
            })?;
        }
        let dst_fp = if fs::hard_link(&src, &dst).is_ok() {
            let meta = fs::symlink_metadata(&dst).map_err(|e| {
                format!("{phase}: cannot stat snapshot {}: {e}", dst.display())
            })?;
            let fp = FileFingerprint::from_meta(&meta);
            if fp != src_fp {
                return Err(format!(
                    "{phase}: snapshot hardlink fingerprint mismatch on {}",
                    dst.display()
                ));
            }
            fp
        } else {
            fs::write(&dst, &bytes).map_err(|e| {
                format!("{phase}: cannot write snapshot {}: {e}", dst.display())
            })?;
            let mode = if src_fp.mode & 0o111 != 0 {
                0o500
            } else {
                0o400
            };
            fs::set_permissions(&dst, fs::Permissions::from_mode(mode))
                .map_err(|e| {
                    format!(
                        "{phase}: cannot chmod snapshot {}: {e}",
                        dst.display()
                    )
                })?;
            let meta = fs::symlink_metadata(&dst).map_err(|e| {
                format!("{phase}: cannot stat snapshot {}: {e}", dst.display())
            })?;
            FileFingerprint::from_meta(&meta)
        };
        locked_files.push(LockedFileRecord {
            src,
            src_fp,
            dst,
            dst_fp,
        });
    }
    Ok(sha)
}

fn stage_tree_digest(
    src_root: &Path,
    snapshot_root: &Path,
    dir_rel: &str,
    phase: &str,
    locked_files: &mut Vec<LockedFileRecord>,
) -> Result<String, String> {
    let dir = beneath(src_root, dir_rel, phase, ExpectedKind::Directory)?;
    let mut lines = Vec::new();
    for entry in WalkDir::new(&dir)
        .follow_links(false)
        .follow_root_links(false)
    {
        let entry = entry.map_err(|e| {
            format!("{phase}: cannot walk {}: {e}", dir.display())
        })?;
        if entry.file_type().is_dir() {
            continue;
        }
        if !entry.file_type().is_file() {
            return Err(format!(
                "{phase}: symlink or special file in toolchain: {}",
                entry.path().display()
            ));
        }
        let rel_in_dir = entry.path().strip_prefix(&dir).unwrap_or(entry.path());
        let rel_in_root = entry
            .path()
            .strip_prefix(src_root)
            .unwrap_or(entry.path())
            .to_str()
            .ok_or_else(|| {
                format!(
                    "{phase}: non-UTF-8 path in toolchain: {}",
                    entry.path().display()
                )
            })?;
        let file_sha = stage_locked_file(
            src_root,
            snapshot_root,
            rel_in_root,
            phase,
            locked_files,
        )?;
        let mut line = file_sha.into_bytes();
        line.extend_from_slice(b"  ");
        line.extend_from_slice(rel_in_dir.as_os_str().as_bytes());
        line.push(b'\n');
        lines.push((rel_in_dir.as_os_str().as_bytes().to_vec(), line));
    }
    lines.sort();
    Ok(sha256_bytes(
        &lines.into_iter().flat_map(|(_, l)| l).collect::<Vec<_>>(),
    ))
}

fn create_toolchain_snapshot_dir(canonical_root: &Path) -> Result<TempDir, String> {
    if let Some(cache_dir) = canonical_root.parent().and_then(Path::parent)
        && let Ok(dir) = tempfile::Builder::new()
            .prefix(".anneal-tc-snapshot-")
            .tempdir_in(cache_dir)
        && join_env_paths([dir.path()], "toolchain").is_ok()
    {
        return Ok(dir);
    }
    private_tempdir("anneal-tc-snapshot-")
}

fn authenticate_toolchain(
    root: &Path,
    anneal_root: &AuthenticatedRoot,
) -> Result<Toolchain, String> {
    static AUTHENTICATED: Mutex<BTreeMap<PathBuf, Toolchain>> =
        Mutex::new(BTreeMap::new());
    let phase = "toolchain";
    let canonical = fs::canonicalize(root).map_err(|e| {
        format!("{phase}: cannot resolve toolchain {}: {e}", root.display())
    })?;
    join_env_paths([canonical.as_path()], phase)?;

    let mut cache = AUTHENTICATED.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(tc) = cache.get(&canonical)
        && tc.verify_unchanged(phase).is_ok()
    {
        return Ok(tc.clone());
    }

    let tc = authenticate_toolchain_uncached(
        &canonical,
        &anneal_root.foundation_lock,
    )?;
    tc.verify_unchanged(phase)?;
    cache.insert(canonical, tc.clone());
    Ok(tc)
}

fn authenticate_toolchain_uncached(
    root: &Path,
    foundation_lock_bytes: &[u8],
) -> Result<Toolchain, String> {
    let phase = "toolchain";
    let snapshot = Arc::new(create_toolchain_snapshot_dir(root)?);
    let snapshot_root = snapshot.path().to_path_buf();
    join_env_paths([snapshot_root.as_path()], phase)?;

    let mut locked_files = Vec::new();
    let mut locked_dirs = Vec::new();

    // FIXME(#87): Add aarch64-linux, x86_64-macos, and aarch64-macos entries to
    // `toolchain-lock.sha256` once those platform toolchain archives are pinned.
    let platform = format!("{}-{}/", env::consts::ARCH, env::consts::OS);
    let lock = parse_digest_lines(TOOLCHAIN_LOCK, phase)?;
    let mut saw_platform = false;
    for (key, want) in &lock {
        let Some(rel) = key.strip_prefix(&platform) else {
            continue;
        };
        saw_platform = true;
        let got = if let Some(dir) = rel.strip_suffix("/**") {
            stage_tree_digest(
                root,
                &snapshot_root,
                dir,
                phase,
                &mut locked_files,
            )?
        } else if let Some(dir) = rel.strip_suffix('/') {
            let dir_path = beneath(root, dir, phase, ExpectedKind::Directory)?;
            let digest = listing_digest(&dir_path, phase)?;
            locked_dirs.push((dir_path, want.clone()));
            digest
        } else {
            stage_locked_file(
                root,
                &snapshot_root,
                rel,
                phase,
                &mut locked_files,
            )?
        };
        if &got != want {
            return Err(format!(
                "{phase}: toolchain entry {rel} has SHA-256 {got}, locked {want}"
            ));
        }
    }
    if !saw_platform {
        return Err(format!(
            "{phase}: toolchain-lock.sha256 has no entries for platform `{}`",
            platform.trim_end_matches('/')
        ));
    }

    verify_and_stage_foundation_lock(
        root,
        &snapshot_root,
        foundation_lock_bytes,
        &mut locked_files,
    )?;

    Ok(Toolchain {
        source_root: root.to_path_buf(),
        lean: beneath(
            &snapshot_root,
            "lean/bin/lean",
            phase,
            ExpectedKind::RegularFile,
        )?,
        rustc: beneath(
            &snapshot_root,
            "rust/bin/rustc",
            phase,
            ExpectedKind::RegularFile,
        )?,
        rust_lib: snapshot_root.join("rust/lib"),
        sysroot: snapshot_root.join("rust"),
        _snapshot: snapshot,
        snapshot_root,
        locked_files: Arc::new(locked_files),
        locked_dirs: Arc::new(locked_dirs),
    })
}

/// Authenticated source buffers read from `--anneal-root` after verifying
/// every file against [`LOCKED_ANNEAL_SOURCES`].
struct AuthenticatedRoot {
    foundation_lock: Vec<u8>,
    trusted_lean: Vec<(String, Vec<u8>)>,
    theory_lean: Vec<(String, Vec<u8>)>,
    rustc_capture: Vec<(String, Vec<u8>)>,
}

/// Authenticates `anneal_root` (`trusted/lean/foundation-lock.json`,
/// `trusted/lean/*.lean`, `theory/*.lean`, and `trusted/rustc-capture/src/*.rs`)
/// against [`LOCKED_ANNEAL_SOURCES`] and returns the verified in-memory source
/// buffers.
fn authenticate_anneal_root(
    anneal_root: &Path,
) -> Result<Arc<AuthenticatedRoot>, String> {
    let phase = "anneal-root";
    let canonical = fs::canonicalize(anneal_root).map_err(|e| {
        format!(
            "{phase}: cannot resolve anneal root {}: {e}",
            anneal_root.display()
        )
    })?;
    join_env_paths([canonical.as_path()], phase)?;

    let entries = parse_digest_lines(LOCKED_ANNEAL_SOURCES, phase)?;
    let mut foundation_lock: Option<Vec<u8>> = None;
    let mut trusted_lean = Vec::new();
    let mut theory_lean = Vec::new();
    let mut rustc_capture = Vec::new();

    for (rel, expected_sha) in entries {
        let path = beneath(&canonical, &rel, phase, ExpectedKind::RegularFile)?;
        let actual = read_regular(&path, phase)?;
        let actual_sha = sha256_bytes(&actual);
        if actual_sha != expected_sha {
            return Err(format!(
                "{phase}: {rel} in {} does not match compiled-in sources \
                 ({actual_sha} != {expected_sha})",
                canonical.display()
            ));
        }
        if rel == "trusted/lean/foundation-lock.json" {
            foundation_lock = Some(actual);
        } else if let Some(sub) = rel.strip_prefix("trusted/lean/") {
            trusted_lean.push((sub.to_string(), actual));
        } else if let Some(sub) = rel.strip_prefix("theory/") {
            theory_lean.push((sub.to_string(), actual));
        } else if let Some(sub) = rel.strip_prefix("trusted/rustc-capture/") {
            rustc_capture.push((sub.to_string(), actual));
        } else {
            return Err(format!(
                "{phase}: unrecognized path `{rel}` in anneal-sources.sha256"
            ));
        }
    }

    let foundation_lock = foundation_lock.ok_or_else(|| {
        format!(
            "{phase}: trusted/lean/foundation-lock.json missing from anneal-sources.sha256"
        )
    })?;
    if rustc_capture.is_empty() {
        return Err(format!(
            "{phase}: trusted/rustc-capture sources missing from anneal-sources.sha256"
        ));
    }

    Ok(Arc::new(AuthenticatedRoot {
        foundation_lock,
        trusted_lean,
        theory_lean,
        rustc_capture,
    }))
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct ValidatedTargetCrate {
    crate_name: String,
    allow_candidate_features: Vec<String>,
    cargo_toml_bytes: Vec<u8>,
    lib_rs_bytes: Vec<u8>,
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
    let text = std::str::from_utf8(&cargo_toml_bytes)
        .map_err(|_| format!("{phase}: Cargo.toml is not UTF-8"))?;
    let manifest: TargetManifest = toml::from_str(text).map_err(|e| {
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
    if pkg.edition != "2024" {
        return Err(format!(
            "{phase}: unsupported package.edition `{}` (only edition `2024` is supported)",
            pkg.edition
        ));
    }
    Ok(ValidatedTargetCrate {
        crate_name: pkg.name.replace('-', "_"),
        allow_candidate_features: pkg
            .metadata
            .map(|m| m.anneal.trust_policy.allow_candidate_features)
            .unwrap_or_default(),
        cargo_toml_bytes,
        lib_rs_bytes,
    })
}

fn revalidate_target_crate(
    path: &Path,
    expected: &ValidatedTargetCrate,
) -> Result<(), String> {
    let current = validate_target_crate(path)?;
    if &current != expected {
        return Err(
            "target-crate: Cargo.toml or src/lib.rs changed during verification"
                .to_string(),
        );
    }
    Ok(())
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

/// Discovers all candidate TCB features in `TRUSTED_LEAN_MODULES` plus
/// `rustc_capture`, and verifies that the target crate and release channel
/// permit them.
///
/// Returns a map from candidate feature name to the list of TCB components
/// gated by that feature.
fn check_candidate_policy(
    trusted_lean: &[(String, Vec<u8>)],
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

// ---------------------------------------------------------------------------
// Building and running `anneal-rustc-capture`
// ---------------------------------------------------------------------------

/// Builds the `anneal-rustc-capture` binary for `tc` from the authenticated
/// [`AuthenticatedRoot`] sources inside a process-private `/tmp` directory.
fn ensure_rustc_capture_bin(
    tc: &Toolchain,
    root: &AuthenticatedRoot,
) -> Result<PathBuf, String> {
    static BUILT_CAPTURE: Mutex<BTreeMap<PathBuf, Arc<TempDir>>> =
        Mutex::new(BTreeMap::new());

    tc.verify_unchanged("rustc-capture-build")?;
    let mut cache = BUILT_CAPTURE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(stage) = cache.get(&tc.source_root) {
        return Ok(stage.path().join("anneal-rustc-capture"));
    }

    let stage = Arc::new(private_tempdir("anneal-capture-build-")?);
    let bin = stage.path().join("anneal-rustc-capture");
    let src_stage = stage.path().join("rustc-capture");
    for (rel, bytes) in &root.rustc_capture {
        write_staged(&src_stage, rel, bytes)?;
    }

    let dylib_path =
        join_env_paths([tc.rust_lib.as_path()], DYLIB_PATH_VAR)?;
    let out = child_command(&tc.rustc)
        .arg("--edition=2024")
        .arg("--crate-name")
        .arg("anneal_rustc_capture")
        .arg("--sysroot")
        .arg(&tc.sysroot)
        .arg(src_stage.join("src/main.rs"))
        .arg("-o")
        .arg(&bin)
        .env("CARGO_PKG_VERSION", "0.1.0")
        .env(DYLIB_PATH_VAR, dylib_path)
        .output()
        .map_err(|e| format!("failed to spawn rustc for rustc-capture: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "failed to build anneal-rustc-capture:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        ));
    }
    tc.verify_unchanged("rustc-capture-build")?;

    cache.insert(tc.source_root.clone(), stage);
    Ok(bin)
}

/// Verifies from `rustc`'s `--emit=dep-info` output that `staged_lib_rs` was
/// the sole source file read while expanding the target crate (rejecting
/// `#[path = "..."]`, `include!`, `include_str!`, and `include_bytes!`).
fn verify_sole_source_dep_info(
    deps_d: &Path,
    staged_lib_rs: &Path,
) -> Result<(), VerifyError> {
    let dep_bytes =
        read_regular(deps_d, "capture-dep-info").map_err(VerifyError::new)?;
    let dep_text = std::str::from_utf8(&dep_bytes).map_err(|_| {
        VerifyError::new("capture-dep-info: deps.d is not UTF-8".to_string())
    })?;
    let expected = format!(
        "{}: {}\n\n{}:",
        deps_d.display(),
        staged_lib_rs.display(),
        staged_lib_rs.display(),
    );
    if dep_text.trim() != expected.trim() {
        let diag = format!(
            "error: target crate read source files or environment variables \
             outside staged src/lib.rs (dep-info: {})",
            dep_text.trim().replace('\n', " ")
        );
        return Err(VerifyError::capture("", &diag));
    }
    Ok(())
}

fn capture_mir(
    tc: &Toolchain,
    root: &AuthenticatedRoot,
    target: &ValidatedTargetCrate,
) -> Result<String, VerifyError> {
    let capture_bin =
        ensure_rustc_capture_bin(tc, root).map_err(VerifyError::new)?;
    let stage =
        private_tempdir("anneal-capture-run-").map_err(VerifyError::new)?;
    let staged_lib_rs =
        write_staged(stage.path(), "src/lib.rs", &target.lib_rs_bytes)
            .map_err(VerifyError::new)?;
    let deps_d = stage.path().join("deps.d");
    let out_mir = stage.path().join("Mir.lean");
    let dylib_path = join_env_paths([tc.rust_lib.as_path()], DYLIB_PATH_VAR)
        .map_err(VerifyError::new)?;

    tc.verify_unchanged("capture").map_err(VerifyError::new)?;
    let dep_out = child_command(&tc.rustc)
        .arg("--edition=2024")
        .arg("--crate-type=lib")
        .arg("--crate-name")
        .arg(&target.crate_name)
        .arg("--sysroot")
        .arg(&tc.sysroot)
        .arg(format!("--emit=dep-info={}", deps_d.display()))
        .arg("-Z")
        .arg("no-codegen")
        .arg(&staged_lib_rs)
        .env(DYLIB_PATH_VAR, &dylib_path)
        .output()
        .map_err(|e| {
            VerifyError::new(format!("failed to run rustc dep-info check: {e}"))
        })?;
    if deps_d.exists() {
        verify_sole_source_dep_info(&deps_d, &staged_lib_rs)?;
    }

    let out = child_command(&capture_bin)
        .arg("--sysroot")
        .arg(&tc.sysroot)
        .arg("--edition")
        .arg("2024")
        .arg("--crate-name")
        .arg(&target.crate_name)
        .arg("--src")
        .arg(&staged_lib_rs)
        .arg("--out")
        .arg(&out_mir)
        .env(DYLIB_PATH_VAR, &dylib_path)
        .output()
        .map_err(|e| {
            VerifyError::new(format!("failed to run anneal-rustc-capture: {e}"))
        })?;
    tc.verify_unchanged("capture").map_err(VerifyError::new)?;

    if !out.status.success() {
        return Err(VerifyError::capture(
            &String::from_utf8_lossy(&out.stdout),
            &String::from_utf8_lossy(&out.stderr),
        ));
    }
    if !dep_out.status.success() {
        return Err(VerifyError::capture(
            &String::from_utf8_lossy(&dep_out.stdout),
            &String::from_utf8_lossy(&dep_out.stderr),
        ));
    }
    verify_sole_source_dep_info(&deps_d, &staged_lib_rs)?;

    let mir_bytes =
        read_regular(&out_mir, "capture-output").map_err(VerifyError::new)?;
    String::from_utf8(mir_bytes).map_err(|_| {
        VerifyError::new("generated Mir.lean is not UTF-8".to_string())
    })
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

fn verify_and_stage_foundation_lock(
    src_root: &Path,
    snapshot_root: &Path,
    foundation_lock_bytes: &[u8],
    locked_files: &mut Vec<LockedFileRecord>,
) -> Result<(), String> {
    let phase = "foundation-lock";
    let lock: FoundationLock = serde_json::from_slice(foundation_lock_bytes)
        .map_err(|e| format!("{phase}: invalid JSON: {e}"))?;

    let actual_lean_sha = stage_locked_file(
        src_root,
        snapshot_root,
        "lean/bin/lean",
        phase,
        locked_files,
    )?;
    let staged_lean = snapshot_root.join("lean/bin/lean");
    let ver_out = child_command(&staged_lean)
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
    if &actual_lean_sha != expected_lean_sha {
        return Err(format!(
            "{phase}: lean binary SHA-256 mismatch ({actual_lean_sha} != {expected_lean_sha})"
        ));
    }

    for (mod_name, mod_entry) in &lock.modules {
        let rel_base = mod_name.replace('.', "/");
        for (ext, expected_sha) in &mod_entry.parts {
            let rel = format!("lean/lib/lean/{rel_base}.{ext}");
            let actual_sha = stage_locked_file(
                src_root,
                snapshot_root,
                &rel,
                phase,
                locked_files,
            )?;
            if &actual_sha != expected_sha {
                return Err(format!(
                    "{phase}: foundation artifact {rel_base}.{ext} SHA-256 mismatch \
                     ({actual_sha} != {expected_sha})"
                ));
            }
        }
    }
    Ok(())
}

fn compile_lean_file(
    tc: &Toolchain,
    lean_path: &OsString,
    src_file: &Path,
    out_olean: &Path,
) -> Result<(), (String, Option<StageFailure>)> {
    if let Some(parent) = out_olean.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            (
                format!("cannot create parent directory {}: {e}", parent.display()),
                None,
            )
        })?;
    }
    tc.verify_unchanged("lean-compile")
        .map_err(|e| (e, None))?;
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
            (
                format!("failed to invoke lean on {}: {e}", src_file.display()),
                None,
            )
        })?;
    tc.verify_unchanged("lean-compile")
        .map_err(|e| (e, None))?;
    if !out.status.success() {
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        let stage_failure = stdout
            .lines()
            .next()
            .and_then(|line| {
                serde_json::from_str::<[String; 2]>(line.trim()).ok()
            })
            .map(|[diagnostic, scope]| StageFailure {
                stage: FailureStage::Proof { scope },
                diagnostic,
            });
        let prefix = match &stage_failure {
            Some(StageFailure {
                stage: FailureStage::Proof { scope },
                diagnostic,
            }) => format!("proof [{scope}]: {diagnostic}\n"),
            _ => String::new(),
        };
        return Err((
            format!(
                "{prefix}lean failed on {}:\nstdout:\n{stdout}\nstderr:\n{stderr}",
                src_file.display(),
            ),
            stage_failure,
        ));
    }
    Ok(())
}

/// Compiles `Trusted` and `Anneal` `.olean`s into a process-cached private
/// `/tmp` directory from the authenticated [`AuthenticatedRoot`] sources.
fn ensure_compiled_prefix(
    tc: &Toolchain,
    root: &AuthenticatedRoot,
) -> Result<Arc<TempDir>, String> {
    static PREFIX_CACHE: Mutex<BTreeMap<PathBuf, Arc<TempDir>>> =
        Mutex::new(BTreeMap::new());

    tc.verify_unchanged("lean-prefix")?;
    let mut cache = PREFIX_CACHE.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(dir) = cache.get(&tc.source_root) {
        return Ok(dir.clone());
    }

    let prefix_dir = Arc::new(private_tempdir("anneal-lean-prefix-")?);
    let lean_sys_lib = tc.snapshot_root.join("lean/lib/lean");
    let lean_path = join_env_paths(
        [prefix_dir.path(), lean_sys_lib.as_path()],
        "LEAN_PATH",
    )?;

    for (rel, bytes) in root.trusted_lean.iter().chain(&root.theory_lean) {
        let rel_olean =
            format!("{}.olean", rel.strip_suffix(".lean").unwrap_or(rel));
        let staged_src =
            write_staged(&prefix_dir.path().join("src"), rel, bytes)?;
        let out_olean = prefix_dir.path().join(&rel_olean);
        compile_lean_file(tc, &lean_path, &staged_src, &out_olean)
            .map_err(|(msg, _)| msg)?;
    }

    cache.insert(tc.source_root.clone(), prefix_dir.clone());
    Ok(prefix_dir)
}

/// Verifies the crate described by `config` and returns a [`VerifyReport`]
/// including any active `[candidate-tcb-audit]` details.
pub fn verify_crate(config: &VerifyConfig) -> Result<VerifyReport, VerifyError> {
    let target =
        validate_target_crate(&config.crate_dir).map_err(VerifyError::new)?;
    let root =
        authenticate_anneal_root(&config.anneal_root).map_err(VerifyError::new)?;
    let tc = authenticate_toolchain(&config.toolchain_dir, &root)
        .map_err(VerifyError::new)?;
    let active_candidates = check_candidate_policy(
        &root.trusted_lean,
        &target.allow_candidate_features,
        &config.allow_candidate_features,
        config.release_channel,
    )
    .map_err(VerifyError::new)?;

    let prefix_dir =
        ensure_compiled_prefix(&tc, &root).map_err(VerifyError::new)?;
    let mir_lean_src = capture_mir(&tc, &root, &target)?;

    let verify_dir =
        private_tempdir("anneal-verify-").map_err(VerifyError::new)?;
    let mir_lean_path =
        write_staged(verify_dir.path(), "Mir.lean", mir_lean_src.as_bytes())
            .map_err(VerifyError::new)?;
    let proof_lean_path = write_staged(
        verify_dir.path(),
        "Proof.lean",
        PROOF_LEAN_SOURCE.as_bytes(),
    )
    .map_err(VerifyError::new)?;

    let lean_sys_lib = tc.snapshot_root.join("lean/lib/lean");
    let lean_path = join_env_paths(
        [
            verify_dir.path(),
            prefix_dir.path(),
            lean_sys_lib.as_path(),
        ],
        "LEAN_PATH",
    )
    .map_err(VerifyError::new)?;

    compile_lean_file(
        &tc,
        &lean_path,
        &mir_lean_path,
        &verify_dir.path().join("Mir.olean"),
    )
    .map_err(|(msg, failure)| {
        VerifyError::with_mir(msg, mir_lean_src.clone(), failure)
    })?;
    compile_lean_file(
        &tc,
        &lean_path,
        &proof_lean_path,
        &verify_dir.path().join("Proof.olean"),
    )
    .map_err(|(msg, failure)| {
        VerifyError::with_mir(msg, mir_lean_src.clone(), failure)
    })?;

    revalidate_target_crate(&config.crate_dir, &target)
        .map_err(|e| VerifyError::with_mir(e, mir_lean_src.clone(), None))?;
    tc.verify_unchanged("verify")
        .map_err(|e| VerifyError::with_mir(e, mir_lean_src.clone(), None))?;

    let mut output_text = format!(
        "verified crate `{}` (Proof.verify_crate : Trusted.CrateTheorem Mir.crate)\n",
        target.crate_name
    );
    if !active_candidates.is_empty() {
        let candidate_features: Vec<&str> =
            active_candidates.keys().map(String::as_str).collect();
        output_text.push_str(&format!(
            "Candidate-Trusted TCB (Unvetted / Alpha): {}\n",
            candidate_features.join(", ")
        ));
        output_text.push_str("[candidate-tcb-audit]\n");
        for (feat, origins) in &active_candidates {
            output_text.push_str(&format!(
                "  candidate:{feat} -> {}\n",
                origins.join(", ")
            ));
        }
    }

    Ok(VerifyReport {
        mir_lean: mir_lean_src,
        output_text,
    })
}
