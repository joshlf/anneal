// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI orchestration and boundary-audit library for `cargo-anneal`
//! (`#103`).

pub mod audit;
pub mod self_test;
pub mod setup;

use std::env;
use std::path::{Path, PathBuf};

/// Configuration options for repository audit commands.
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    pub anneal_root: Option<PathBuf>,
    pub lean_bin: Option<PathBuf>,
}

/// Resolve the Anneal repository or bundled exocrate `share/anneal` root.
pub fn resolve_anneal_root(options: &VerifyOptions) -> Result<PathBuf, String> {
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
    Err(
        "Anneal toolchain is not installed; run `cargo anneal setup` first"
            .to_string(),
    )
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
