// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI orchestration library for `cargo-anneal`.

use std::env;
use std::path::{Path, PathBuf};

/// Configuration options for `cargo-anneal` commands.
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    /// Explicit path to the Anneal repository or toolchain root.
    pub anneal_root: Option<PathBuf>,
    /// Explicit path to the pinned Lean 4.34.1 binary.
    pub lean_bin: Option<PathBuf>,
    /// Explicit path to the `anneal-rustc-capture` binary.
    pub rustc_capture_bin: Option<PathBuf>,
}

/// Resolves the Anneal repository root from `options.anneal_root`, the
/// `ANNEAL_ROOT` environment variable, or the workspace ancestor of
/// `CARGO_MANIFEST_DIR`.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, String> {
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
            "cannot determine Anneal repository root from CARGO_MANIFEST_DIR"
                .to_string()
        })
}

/// Resolves an explicit Lean binary override from `options.lean_bin` or the
/// `ANNEAL_LEAN_BIN` environment variable.
pub fn resolve_lean_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(lean) = &options.lean_bin {
        return Some(lean.clone());
    }
    env::var_os("ANNEAL_LEAN_BIN").map(PathBuf::from)
}

/// Resolves an explicit `anneal-rustc-capture` binary override from
/// `options.rustc_capture_bin` or the `ANNEAL_RUSTC_CAPTURE_BIN` environment
/// variable.
pub fn resolve_rustc_capture_bin(options: &VerifyOptions) -> Option<PathBuf> {
    if let Some(bin) = &options.rustc_capture_bin {
        return Some(bin.clone());
    }
    env::var_os("ANNEAL_RUSTC_CAPTURE_BIN").map(PathBuf::from)
}
