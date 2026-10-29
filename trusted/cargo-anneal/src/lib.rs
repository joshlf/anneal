//! Trusted CLI orchestration library for `cargo-anneal`.

pub mod setup;

use std::env;
use std::path::{Path, PathBuf};

/// Configuration options for `cargo-anneal` commands.
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    /// Optional explicit path to the Anneal repository or toolchain root.
    pub anneal_root: Option<PathBuf>,
    /// Optional explicit path to the pinned Lean 4.34.1 binary.
    pub lean_bin: Option<PathBuf>,
    /// Optional explicit path to the `anneal-rustc-capture` binary.
    pub rustc_capture_bin: Option<PathBuf>,
}

/// Resolve the Anneal repository or installed exocrate toolchain root from
/// `options`, `ANNEAL_ROOT`, an installed `exocrate` toolchain, or
/// `CARGO_MANIFEST_DIR`.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, String> {
    if let Some(root) = &options.anneal_root {
        return Ok(root.clone());
    }
    if let Some(env_root) = env::var_os("ANNEAL_ROOT") {
        return Ok(PathBuf::from(env_root));
    }
    if let Some(tc) = setup::resolve_installed_toolchain() {
        let share_root = tc.anneal_share_root();
        if share_root.is_dir() {
            return Ok(share_root);
        }
    }
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            "cannot determine Anneal repository root from CARGO_MANIFEST_DIR"
                .to_string()
        })
}

/// Resolve the Lean binary from `options`, `ANNEAL_LEAN_BIN`, or an installed
/// `exocrate` toolchain.
pub fn resolve_lean_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(lean) = &options.lean_bin {
        return Some(lean.clone());
    }
    if let Some(env_lean) = env::var_os("ANNEAL_LEAN_BIN") {
        return Some(PathBuf::from(env_lean));
    }
    if let Some(tc) = setup::resolve_installed_toolchain() {
        let bin = tc.lean_bin();
        if bin.is_file() {
            return Some(bin);
        }
    }
    None
}

/// Resolve the `anneal-rustc-capture` binary from `options`,
/// `ANNEAL_RUSTC_CAPTURE_BIN`, or an installed `exocrate` toolchain.
pub fn resolve_rustc_capture_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(bin) = &options.rustc_capture_bin {
        return Some(bin.clone());
    }
    if let Some(env_bin) = env::var_os("ANNEAL_RUSTC_CAPTURE_BIN") {
        return Some(PathBuf::from(env_bin));
    }
    if let Some(tc) = setup::resolve_installed_toolchain() {
        let bin = tc.rustc_capture_bin();
        if bin.is_file() {
            return Some(bin);
        }
    }
    None
}
