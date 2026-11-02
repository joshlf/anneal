// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation via `exocrate` (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::env;
use std::fs;
use std::path::PathBuf;

// Include both the workspace manifest and `trusted/root-manifest.sha256` in the
// `exocrate` cache key so any change to `trusted/lean/` or `trusted/audit/`
// invalidates stale cached `share/anneal` foundation snapshots.
exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml", "../../root-manifest.sha256"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml";
}

/// Installs or resolves the Anneal toolchain archive in the user-global cache.
///
/// Uses `local_archive` when set, falling back to the remote archive recorded
/// in `[[package.metadata.exocrate]]` for the current platform.
pub fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
    let source = match local_archive {
        Some(path) => exocrate::Source::Local(path),
        None => exocrate::Source::Remote(REMOTE_ARCHIVE),
    };
    CONFIG
        .resolve_installation_dir_or_install(
            exocrate::Location::UserGlobal,
            source,
        )
        .map(|(dir, _)| dir)
        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))
}

/// Resolves the exact version-matched Anneal toolchain directory in the
/// user-global cache without attempting installation.
///
/// This function is intentionally strict on the `CONFIG` slug (which hashes
/// `../Cargo.toml` and `../root-manifest.sha256`) so callers resolving
/// `share/anneal` never load a stale `trusted/lean/` snapshot from an older
/// archive.
pub fn resolve_installed() -> Option<PathBuf> {
    CONFIG
        .resolve_installation_dir(exocrate::Location::UserGlobal)
        .ok()
}

/// Resolves the pinned `lean/` and `rust/` compiler binaries in the user-global
/// toolchain cache.
///
/// Checks the exact `CONFIG` slug first via [`resolve_installed`]. When
/// `trusted/root-manifest.sha256` has been updated locally in a repository
/// checkout without re-archiving the omnibus tarball, falls back to scanning
/// `~/.cache/.anneal/toolchain/*` for an extracted toolchain containing both
/// `lean/bin/lean` and `rust/bin/rustc`. Callers must only use this fallback
/// for compiler binaries (`lean`, `lake`, `rustc`, `cargo`), never for
/// `share/anneal` foundation source files.
pub fn resolve_installed_compilers() -> Option<PathBuf> {
    if let Some(dir) = resolve_installed()
        && dir.join("lean/bin/lean").is_file()
        && dir.join("rust/bin/rustc").is_file()
    {
        return Some(dir);
    }

    let cache_base = env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    let toolchain_root = cache_base.join(".anneal").join("toolchain");
    let entries = fs::read_dir(toolchain_root).ok()?;
    let mut dirs: Vec<PathBuf> = entries
        .filter_map(|e| e.ok().map(|entry| entry.path()))
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    dirs.into_iter().find(|dir| {
        dir.join("lean/bin/lean").is_file()
            && dir.join("rust/bin/rustc").is_file()
    })
}

#[cfg(test)]
mod tests {
    use std::process::Command;

    use super::*;

    #[test]
    fn resolves_and_executes_installed_exocrate_toolchain() {
        let root = resolve_installed_compilers()
            .expect("Anneal toolchain must be installed before running tests");

        assert!(
            root.join("share/anneal/trusted/lean/foundation-lock.json")
                .is_file(),
            "expected bundled foundation-lock.json inside share/anneal"
        );

        let lean_out = Command::new(root.join("lean/bin/lean"))
            .arg("--version")
            .output()
            .expect("failed to execute bundled lean --version");
        assert!(
            lean_out.status.success(),
            "bundled lean --version failed: {lean_out:?}"
        );
        let lean_stdout = String::from_utf8_lossy(&lean_out.stdout);
        assert!(
            lean_stdout.contains("4.34.1"),
            "expected Lean 4.34.1, got: {lean_stdout}"
        );

        let rust_lib = root.join("rust/lib");
        for rel_bin in ["rust/bin/rustc", "bin/anneal-rustc-capture"] {
            let mut cmd = Command::new(root.join(rel_bin));
            if rust_lib.is_dir() {
                cmd.env("LD_LIBRARY_PATH", &rust_lib);
            }
            let out = cmd
                .arg("--version")
                .output()
                .unwrap_or_else(|e| panic!("failed to execute {rel_bin}: {e}"));
            assert!(out.status.success(), "{rel_bin} --version failed: {out:?}");
        }
    }
}
