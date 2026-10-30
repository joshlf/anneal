// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation and resolution via `exocrate` (`cargo anneal setup`).
//!
//! This module manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean 4.34.1 toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::path::PathBuf;

exocrate::config! {
    pub const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE_ARCHIVE: RemoteArchive = "Cargo.toml" [
        (linux, x86_64),
        (linux, aarch64),
        (macos, x86_64),
        (macos, aarch64),
    ];
}

/// Options for `cargo anneal setup`.
#[derive(Debug, Clone, Default)]
pub struct SetupOptions {
    /// Path to a locally built `.tar.zst` omnibus archive to install instead of
    /// downloading the remote release archive.
    pub local_archive: Option<PathBuf>,
}

/// Resolved Anneal `exocrate` toolchain installation directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Toolchain {
    /// Root directory of the extracted omnibus toolchain archive.
    pub root: PathBuf,
}

impl Toolchain {
    /// Installs or resolves the Anneal toolchain archive according to
    /// `options`.
    ///
    /// Uses `options.local_archive` when set, falling back to the remote
    /// archive recorded in `[package.metadata.exocrate.<os>.<arch>]` for the
    /// current platform.
    pub fn install(options: &SetupOptions) -> Result<Self, String> {
        let source = match &options.local_archive {
            Some(path) => exocrate::Source::Local(path.clone()),
            None => exocrate::Source::Remote(REMOTE_ARCHIVE),
        };
        let root = CONFIG
            .resolve_installation_dir_or_install(
                exocrate::Location::UserGlobal,
                source,
            )
            .map_err(|e| format!("failed to install Anneal toolchain: {e}"))?;
        Ok(Self { root })
    }

    /// Resolves the installed Anneal toolchain directory matching the current
    /// `Cargo.toml` version.
    pub fn resolve() -> Result<Self, String> {
        let root = CONFIG
            .resolve_installation_dir(exocrate::Location::UserGlobal)
            .map_err(|e| {
                format!(
                    "Anneal toolchain is not installed (run `cargo anneal setup` first): {e}"
                )
            })?;
        Ok(Self { root })
    }

    /// Returns the path to the bundled Lean 4.34.1 executable
    /// (`<root>/lean/bin/lean`).
    pub fn lean_bin(&self) -> PathBuf {
        self.root.join("lean/bin/lean")
    }

    /// Returns the path to the bundled `rustc` executable
    /// (`<root>/rust/bin/rustc`).
    pub fn rustc_bin(&self) -> PathBuf {
        self.root.join("rust/bin/rustc")
    }

    /// Returns the path to the bundled Rust shared library directory
    /// (`<root>/rust/lib`).
    pub fn rust_lib(&self) -> PathBuf {
        self.root.join("rust/lib")
    }

    /// Returns the path to the bundled `anneal-rustc-capture` executable
    /// (`<root>/bin/anneal-rustc-capture`).
    pub fn rustc_capture_bin(&self) -> PathBuf {
        self.root.join("bin/anneal-rustc-capture")
    }

    /// Returns the path to the bundled Anneal Lean foundation root
    /// (`<root>/share/anneal`).
    pub fn anneal_share_root(&self) -> PathBuf {
        self.root.join("share/anneal")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn toolchain_paths_match_omnibus_archive_layout() {
        let tc = Toolchain {
            root: PathBuf::from("/tmp/anneal-tc"),
        };
        assert_eq!(tc.lean_bin(), PathBuf::from("/tmp/anneal-tc/lean/bin/lean"));
        assert_eq!(
            tc.rustc_bin(),
            PathBuf::from("/tmp/anneal-tc/rust/bin/rustc")
        );
        assert_eq!(tc.rust_lib(), PathBuf::from("/tmp/anneal-tc/rust/lib"));
        assert_eq!(
            tc.rustc_capture_bin(),
            PathBuf::from("/tmp/anneal-tc/bin/anneal-rustc-capture")
        );
        assert_eq!(
            tc.anneal_share_root(),
            PathBuf::from("/tmp/anneal-tc/share/anneal")
        );
    }

    #[test]
    fn parses_remote_archive_at_compile_time() {
        assert!(!REMOTE_ARCHIVE.url.is_empty());
    }
}
