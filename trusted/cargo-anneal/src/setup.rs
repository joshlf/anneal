//! Toolchain installation and resolution via `exocrate` (`cargo anneal setup`).
//!
//! Manages the versioned omnibus archive containing:
//! - `bin/anneal-rustc-capture`: standalone MIR capture driver
//! - `lean/`: pinned Lean 4.34.1 toolchain
//! - `rust/`: pinned Rust toolchain (`rustc` + `rust-std` + `rustc-dev`)
//! - `share/anneal/`: `trusted/lean/` foundation metadata

use std::collections::BTreeMap;
use std::env;
use std::path::{Path, PathBuf};

exocrate::config! {
    pub const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml"],
    };
}

/// Options for `cargo anneal setup`.
#[derive(Debug, Clone, Default)]
pub struct SetupOptions {
    /// Optional path to a locally built `.tar.zst` omnibus archive.
    pub local_archive: Option<PathBuf>,
}

/// Resolved Anneal exocrate toolchain installation directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Toolchain {
    pub root: PathBuf,
}

impl Toolchain {
    /// Path to the bundled Lean 4.34.1 executable (`<root>/lean/bin/lean`).
    pub fn lean_bin(&self) -> PathBuf {
        self.root.join("lean/bin/lean")
    }

    /// Path to the bundled `rustc` executable (`<root>/rust/bin/rustc`).
    pub fn rustc_bin(&self) -> PathBuf {
        self.root.join("rust/bin/rustc")
    }

    /// Path to the bundled Rust shared library directory (`<root>/rust/lib`).
    pub fn rust_lib(&self) -> PathBuf {
        self.root.join("rust/lib")
    }

    /// Path to the bundled `anneal-rustc-capture` executable
    /// (`<root>/bin/anneal-rustc-capture`).
    pub fn rustc_capture_bin(&self) -> PathBuf {
        self.root.join("bin/anneal-rustc-capture")
    }

    /// Path to the bundled Anneal Lean foundation & theory root
    /// (`<root>/share/anneal`).
    pub fn anneal_share_root(&self) -> PathBuf {
        self.root.join("share/anneal")
    }
}

/// Returns the platform dynamic library search path variable name used by
/// `rustc` and `anneal-rustc-capture`.
pub fn rust_library_path_env_var() -> &'static str {
    if cfg!(target_os = "macos") {
        "DYLD_LIBRARY_PATH"
    } else {
        "LD_LIBRARY_PATH"
    }
}

/// Install or resolve the Anneal toolchain archive according to `options`.
pub fn run_setup(options: &SetupOptions) -> Result<Toolchain, String> {
    let local_archive = options.local_archive.clone().or_else(|| {
        env::var_os("ANNEAL_SETUP_LOCAL_ARCHIVE").map(PathBuf::from)
    });
    let source = match local_archive {
        Some(path) => exocrate::Source::Local(path),
        None => exocrate::Source::Remote(remote_archive()?),
    };

    let root = CONFIG
        .resolve_installation_dir_or_install(setup_location(), source)
        .map_err(|e| format!("failed to install Anneal toolchain: {e}"))?;
    Ok(Toolchain { root })
}

/// Resolve an already-installed Anneal toolchain directory if present on disk.
pub fn resolve_installed_toolchain() -> Option<Toolchain> {
    if let Some(custom_dir) = env::var_os("ANNEAL_TOOLCHAIN_DIR") {
        let root = CONFIG
            .resolve_installation_dir(exocrate::Location::Custom(PathBuf::from(
                custom_dir,
            )))
            .ok()?;
        return Some(Toolchain { root });
    }

    let manifest_target = Path::new(env!("CARGO_MANIFEST_DIR")).join("target");
    let workspace_target = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(|p| p.join("target"));

    let mut candidates = Vec::new();
    if env::var_os("__ANNEAL_LOCAL_DEV").is_some() {
        candidates.push(exocrate::Location::LocalDev);
        candidates.push(exocrate::Location::Custom(manifest_target));
        if let Some(wt) = workspace_target {
            candidates.push(exocrate::Location::Custom(wt));
        }
    } else {
        candidates.push(exocrate::Location::LocalDev);
        candidates.push(exocrate::Location::Custom(manifest_target));
        if let Some(wt) = workspace_target {
            candidates.push(exocrate::Location::Custom(wt));
        }
        candidates.push(exocrate::Location::UserGlobal);
    }

    for loc in candidates {
        if let Ok(root) = CONFIG.resolve_installation_dir(loc) {
            return Some(Toolchain { root });
        }
    }
    None
}

fn setup_location() -> exocrate::Location {
    if let Some(dir) = env::var_os("ANNEAL_TOOLCHAIN_DIR") {
        exocrate::Location::Custom(PathBuf::from(dir))
    } else if env::var_os("__ANNEAL_LOCAL_DEV").is_some() {
        exocrate::Location::LocalDev
    } else {
        exocrate::Location::UserGlobal
    }
}

/// Parse the [`exocrate::RemoteArchive`] entry for `(OS, ARCH)` from the
/// embedded `trusted/cargo-anneal/Cargo.toml`.
pub fn remote_archive() -> Result<exocrate::RemoteArchive, String> {
    remote_archive_for_platform(
        include_str!("../Cargo.toml"),
        env::consts::OS,
        env::consts::ARCH,
    )
}

fn parse_exocrate_entries(
    cargo_toml_text: &str,
) -> Result<Vec<BTreeMap<String, String>>, String> {
    let mut entries = Vec::new();
    let mut current: Option<BTreeMap<String, String>> = None;

    for (idx, raw_line) in cargo_toml_text.lines().enumerate() {
        let line_no = idx + 1;
        let line = match raw_line.split_once('#') {
            Some((before, _)) => before.trim(),
            None => raw_line.trim(),
        };
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            if let Some(prev) = current.take() {
                entries.push(prev);
            }
            if line == "[[package.metadata.exocrate]]" {
                current = Some(BTreeMap::new());
            }
            continue;
        }
        if let Some(map) = current.as_mut() {
            let (key, val) = line.split_once('=').ok_or_else(|| {
                format!("malformed key-value on line {line_no} of Cargo.toml")
            })?;
            let key = key.trim().to_string();
            let val = val.trim();
            let unquoted = val
                .strip_prefix('"')
                .and_then(|s| s.strip_suffix('"'))
                .ok_or_else(|| {
                    format!(
                        "expected quoted string for `{key}` on line {line_no} of Cargo.toml"
                    )
                })?;
            map.insert(key, unquoted.to_string());
        }
    }
    if let Some(prev) = current.take() {
        entries.push(prev);
    }
    if entries.is_empty() {
        return Err(
            "missing [[package.metadata.exocrate]] in Cargo.toml".to_string()
        );
    }
    Ok(entries)
}

fn remote_archive_for_platform(
    cargo_toml_text: &str,
    target_os: &str,
    target_arch: &str,
) -> Result<exocrate::RemoteArchive, String> {
    let entries = parse_exocrate_entries(cargo_toml_text)?;

    for entry in entries {
        let os = entry.get("os").map(String::as_str).unwrap_or("");
        let arch = entry.get("arch").map(String::as_str).unwrap_or("");
        if os == target_os && arch == target_arch {
            let sha_str =
                entry.get("sha256").map(String::as_str).ok_or_else(|| {
                    format!(
                        "missing sha256 in [[package.metadata.exocrate]] for {target_os}-{target_arch}"
                    )
                })?;
            let url_str =
                entry.get("url").map(String::as_str).ok_or_else(|| {
                    format!(
                        "missing url in [[package.metadata.exocrate]] for {target_os}-{target_arch}"
                    )
                })?;
            let sha256 = exocrate::macro_util::decode_hex(sha_str).ok_or_else(
                || {
                    format!(
                        "invalid 64-character hex sha256 in [[package.metadata.exocrate]] for {target_os}-{target_arch}"
                    )
                },
            )?;
            let leaked_url: &'static str =
                Box::leak(url_str.to_string().into_boxed_str());
            return Ok(exocrate::RemoteArchive {
                url: leaked_url,
                sha256,
            });
        }
    }

    Err(format!(
        "unsupported platform `{target_os}-{target_arch}` in [[package.metadata.exocrate]]"
    ))
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
    fn parses_remote_archive_for_all_four_supported_platforms() {
        let manifest = include_str!("../Cargo.toml");
        for (os, arch) in [
            ("linux", "x86_64"),
            ("linux", "aarch64"),
            ("macos", "x86_64"),
            ("macos", "aarch64"),
        ] {
            let remote =
                remote_archive_for_platform(manifest, os, arch).unwrap();
            assert!(!remote.url.is_empty());
        }
    }
}
