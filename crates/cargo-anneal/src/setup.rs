// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Toolchain installation and resolution (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive under `~/.anneal/toolchain/` containing:
//! - `bin/anneal-rustc-capture`, the standalone MIR capture driver;
//! - `lean/`, the pinned Lean toolchain;
//! - `rust/`, the pinned Rust toolchain (`rustc`, `rust-std`, and `rustc-dev`);
//!   and
//! - `share/anneal/`, the `trusted/lean/` foundation metadata.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anneal_rustc_capture::sha256_hex;

/// Environment variable overriding the root directory of an installed Anneal
/// omnibus toolchain archive.
pub const ANNEAL_TOOLCHAIN_DIR_ENV: &str = "ANNEAL_TOOLCHAIN_DIR";

const CARGO_TOML_TEXT: &str = include_str!("../Cargo.toml");
const ROOT_CARGO_TOML_TEXT: &str = include_str!("../../../Cargo.toml");

/// Platform archive entry parsed from `[[package.metadata.exocrate]]` in
/// `crates/cargo-anneal/Cargo.toml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExocrateArchiveEntry {
    /// Target operating system (`"linux"`, `"macos"`).
    pub os: String,
    /// Target CPU architecture (`"x86_64"`, `"aarch64"`).
    pub arch: String,
    /// Expected SHA-256 hex digest of the `.tar.zst` archive.
    pub sha256: String,
    /// Remote download URL for the `.tar.zst` archive.
    pub url: String,
}

/// Parse all `[[package.metadata.exocrate]]` entries from a `Cargo.toml`
/// manifest string.
pub fn parse_exocrate_metadata(cargo_toml: &str) -> Result<Vec<ExocrateArchiveEntry>, String> {
    let mut entries = Vec::new();
    let mut in_exocrate = false;
    let mut os: Option<String> = None;
    let mut arch: Option<String> = None;
    let mut sha256: Option<String> = None;
    let mut url: Option<String> = None;

    let flush = |entries: &mut Vec<ExocrateArchiveEntry>,
                 os: &mut Option<String>,
                 arch: &mut Option<String>,
                 sha256: &mut Option<String>,
                 url: &mut Option<String>|
     -> Result<(), String> {
        if os.is_none() && arch.is_none() && sha256.is_none() && url.is_none() {
            return Ok(());
        }
        let entry = ExocrateArchiveEntry {
            os: os
                .take()
                .ok_or_else(|| "missing `os` in [[package.metadata.exocrate]]".to_string())?,
            arch: arch
                .take()
                .ok_or_else(|| "missing `arch` in [[package.metadata.exocrate]]".to_string())?,
            sha256: sha256
                .take()
                .ok_or_else(|| "missing `sha256` in [[package.metadata.exocrate]]".to_string())?,
            url: url
                .take()
                .ok_or_else(|| "missing `url` in [[package.metadata.exocrate]]".to_string())?,
        };
        entries.push(entry);
        Ok(())
    };

    for raw_line in cargo_toml.lines() {
        let line = raw_line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            if in_exocrate {
                flush(&mut entries, &mut os, &mut arch, &mut sha256, &mut url)?;
            }
            in_exocrate = line == "[[package.metadata.exocrate]]";
            continue;
        }
        if !in_exocrate {
            continue;
        }
        if let Some((key, val)) = line.split_once('=') {
            let key = key.trim();
            let val = val.trim().trim_matches('"').to_string();
            match key {
                "os" => os = Some(val),
                "arch" => arch = Some(val),
                "sha256" => sha256 = Some(val),
                "url" => url = Some(val),
                _ => {}
            }
        }
    }
    if in_exocrate {
        flush(&mut entries, &mut os, &mut arch, &mut sha256, &mut url)?;
    }
    Ok(entries)
}

/// Return the `ExocrateArchiveEntry` for the current `(OS, ARCH)` target.
pub fn current_platform_archive_metadata() -> Result<ExocrateArchiveEntry, String> {
    let entries = parse_exocrate_metadata(CARGO_TOML_TEXT)?;
    let target_os = env::consts::OS;
    let target_arch = env::consts::ARCH;
    entries
        .into_iter()
        .find(|e| e.os == target_os && e.arch == target_arch)
        .ok_or_else(|| {
            format!(
                "no [[package.metadata.exocrate]] entry configured for os='{target_os}', arch='{target_arch}'"
            )
        })
}

/// Compute the deterministic installation directory under `~/.anneal/toolchain/`
/// keyed by the versioned `Cargo.toml` manifests.
pub fn versioned_installation_dir() -> Result<PathBuf, String> {
    if let Ok(override_dir) = env::var(ANNEAL_TOOLCHAIN_DIR_ENV)
        && !override_dir.trim().is_empty()
    {
        return Ok(PathBuf::from(override_dir.trim()));
    }
    let home = env::var("HOME")
        .map(PathBuf::from)
        .map_err(|_| "HOME environment variable is not set".to_string())?;
    let mut combined = Vec::new();
    combined.extend_from_slice(CARGO_TOML_TEXT.as_bytes());
    combined.extend_from_slice(ROOT_CARGO_TOML_TEXT.as_bytes());
    let digest = sha256_hex(&combined);
    let short_hash = &digest[..16];
    Ok(home
        .join(".anneal")
        .join("toolchain")
        .join(format!("v{}-{short_hash}", env!("CARGO_PKG_VERSION"))))
}

/// Check whether `dir` contains a complete extracted Anneal omnibus archive.
pub fn is_valid_toolchain_dir(dir: &Path) -> bool {
    dir.join("bin/anneal-rustc-capture").is_file()
        && dir.join("lean/bin/lean").is_file()
        && dir.join("rust/bin/rustc").is_file()
        && dir
            .join("share/anneal/trusted/lean/foundation-lock.json")
            .is_file()
}

/// Resolve an already-installed Anneal omnibus toolchain directory if present.
///
/// Checks in order:
/// 1. `ANNEAL_TOOLCHAIN_DIR` environment variable;
/// 2. The version-pinned directory under `~/.anneal/toolchain/v<ver>-<hash>`;
/// 3. `~/.anneal/toolchain/current` or `~/.anneal/toolchain` directly.
pub fn resolve_installed_toolchain() -> Option<PathBuf> {
    if let Ok(override_dir) = env::var(ANNEAL_TOOLCHAIN_DIR_ENV)
        && !override_dir.trim().is_empty()
    {
        let p = PathBuf::from(override_dir.trim());
        if is_valid_toolchain_dir(&p) {
            return Some(p);
        }
    }
    if let Ok(pinned) = versioned_installation_dir()
        && is_valid_toolchain_dir(&pinned)
    {
        return Some(pinned);
    }
    if let Ok(home) = env::var("HOME") {
        let base = PathBuf::from(home).join(".anneal").join("toolchain");
        let current = base.join("current");
        if is_valid_toolchain_dir(&current) {
            return Some(current);
        }
        if is_valid_toolchain_dir(&base) {
            return Some(base);
        }
    }
    None
}

/// Install or resolve the Anneal toolchain archive in the user-global cache
/// (`~/.anneal/toolchain/`).
///
/// Uses `local_archive` when set (`cargo anneal setup --local-archive <PATH>`),
/// falling back to the remote archive recorded in `[[package.metadata.exocrate]]`
/// for the current platform.
pub fn install(local_archive: Option<PathBuf>) -> Result<PathBuf, String> {
    let target_dir = versioned_installation_dir()?;
    if local_archive.is_none() && is_valid_toolchain_dir(&target_dir) {
        return Ok(target_dir);
    }

    let parent_dir = target_dir
        .parent()
        .ok_or_else(|| format!("invalid target toolchain path {}", target_dir.display()))?;
    fs::create_dir_all(parent_dir).map_err(|err| {
        format!(
            "failed to create toolchain parent directory {}: {}",
            parent_dir.display(),
            err
        )
    })?;

    let staging_dir = parent_dir.join(format!(".staging-{}", std::process::id()));
    let _ = fs::remove_dir_all(&staging_dir);
    fs::create_dir_all(&staging_dir).map_err(|err| {
        format!(
            "failed to create staging directory {}: {}",
            staging_dir.display(),
            err
        )
    })?;

    let archive_path = match local_archive {
        Some(path) => {
            if !path.is_file() {
                let _ = fs::remove_dir_all(&staging_dir);
                return Err(format!(
                    "local toolchain archive does not exist: {}",
                    path.display()
                ));
            }
            path
        }
        None => {
            let meta = current_platform_archive_metadata()?;
            let dl_path = staging_dir.join("omnibus.tar.zst");
            let status = Command::new("curl")
                .args(["-fsSL", "-o"])
                .arg(&dl_path)
                .arg(&meta.url)
                .status()
                .map_err(|err| format!("failed to execute curl to download {}: {err}", meta.url))?;
            if !status.success() {
                let _ = fs::remove_dir_all(&staging_dir);
                return Err(format!(
                    "failed to download Anneal toolchain archive from {} (status {status})",
                    meta.url
                ));
            }
            let bytes = fs::read(&dl_path).map_err(|err| {
                let _ = fs::remove_dir_all(&staging_dir);
                format!(
                    "failed to read downloaded archive {}: {err}",
                    dl_path.display()
                )
            })?;
            let actual_sha = sha256_hex(&bytes);
            if actual_sha != meta.sha256 {
                let _ = fs::remove_dir_all(&staging_dir);
                return Err(format!(
                    "Anneal toolchain archive SHA-256 mismatch for {}: expected {}, got {}",
                    meta.url, meta.sha256, actual_sha
                ));
            }
            dl_path
        }
    };

    let extract_dir = staging_dir.join("extracted");
    fs::create_dir_all(&extract_dir)
        .map_err(|err| format!("failed to create extract directory: {err}"))?;

    let tar_status = Command::new("tar")
        .arg("--zstd")
        .arg("-xf")
        .arg(&archive_path)
        .arg("-C")
        .arg(&extract_dir)
        .status()
        .map_err(|err| format!("failed to execute `tar --zstd -xf`: {err}"))?;
    if !tar_status.success() {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(format!(
            "tar extraction failed with status {tar_status} for {}",
            archive_path.display()
        ));
    }

    if !is_valid_toolchain_dir(&extract_dir) {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(format!(
            "extracted archive {} is missing required entries (bin/anneal-rustc-capture, lean/bin/lean, rust/bin/rustc, or share/anneal/trusted/lean/foundation-lock.json)",
            archive_path.display()
        ));
    }

    let _ = fs::remove_dir_all(&target_dir);
    fs::rename(&extract_dir, &target_dir).map_err(|err| {
        let _ = fs::remove_dir_all(&staging_dir);
        format!(
            "failed to move extracted toolchain into {}: {}",
            target_dir.display(),
            err
        )
    })?;
    let _ = fs::remove_dir_all(&staging_dir);

    #[cfg(unix)]
    {
        let current_link = parent_dir.join("current");
        let _ = fs::remove_file(&current_link);
        let _ = std::os::unix::fs::symlink(&target_dir, &current_link);
    }

    Ok(target_dir)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_cargo_toml_exocrate_metadata_for_all_four_platforms() {
        let entries =
            parse_exocrate_metadata(CARGO_TOML_TEXT).expect("parse [[package.metadata.exocrate]]");
        assert_eq!(entries.len(), 4);
        assert!(entries.iter().any(|e| e.os == "linux" && e.arch == "x86_64"));
        assert!(entries
            .iter()
            .any(|e| e.os == "linux" && e.arch == "aarch64"));
        assert!(entries.iter().any(|e| e.os == "macos" && e.arch == "x86_64"));
        assert!(entries
            .iter()
            .any(|e| e.os == "macos" && e.arch == "aarch64"));
    }
}
