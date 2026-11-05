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
//! - `share/anneal/`, the `trusted/lean/` foundation metadata and `theory/`
//!   proof automation.

use std::path::PathBuf;

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
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

/// Resolves an already-installed Anneal toolchain directory in the user-global
/// cache without attempting a network download.
pub fn resolve_installed() -> Option<PathBuf> {
    if let Ok(dir) =
        CONFIG.resolve_installation_dir(exocrate::Location::UserGlobal)
    {
        return Some(dir);
    }
    if let Ok(env_tc) = std::env::var("ANNEAL_TOOLCHAIN") {
        let dir = PathBuf::from(env_tc);
        if is_valid_toolchain_dir(&dir) {
            return Some(dir);
        }
    }
    let home = std::env::var_os("HOME").map(PathBuf::from)?;
    for base in [
        home.join(".cache/.anneal/toolchain"),
        home.join(".anneal/toolchain"),
    ] {
        let Ok(entries) = std::fs::read_dir(&base) else {
            continue;
        };
        let mut candidates = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if is_valid_toolchain_dir(&path) {
                let mtime = entry.metadata().and_then(|m| m.modified()).ok();
                candidates.push((mtime, path));
            }
        }
        candidates.sort_by(|a, b| b.0.cmp(&a.0));
        if let Some((_, dir)) = candidates.into_iter().next() {
            return Some(dir);
        }
    }
    None
}

fn is_valid_toolchain_dir(dir: &std::path::Path) -> bool {
    dir.join("lean/bin/lean").is_file()
        && dir.join("rust/bin/rustc").is_file()
        && dir
            .join("share/anneal/trusted/lean/foundation-lock.json")
            .is_file()
}

#[cfg(test)]
mod tests {
    use std::process::Command;

    use super::*;

    #[test]
    fn resolves_and_executes_installed_exocrate_toolchain() {
        let root = resolve_installed()
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

        for rel_bin in ["rust/bin/rustc", "bin/anneal-rustc-capture"] {
            let out = Command::new(root.join(rel_bin))
                .arg("--version")
                .output()
                .unwrap_or_else(|e| panic!("failed to execute {rel_bin}: {e}"));
            assert!(out.status.success(), "{rel_bin} --version failed: {out:?}");
        }
    }
}
