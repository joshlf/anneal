// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Run the pinned compiler or explicitly capture one configured compilation.
//! Typed capture does not verify a crate; the host must check the generated
//! subject against its authored specifications and exact root.

#![feature(normalize_lexically, rustc_private)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod capture;
mod compilers;
mod driver;
mod extract;
mod ir;
mod lean;
mod publication;

// `build.rs` selects exactly one dialect from `compilers::SUPPORTED_COMPILERS`.
// Code that differs between `rustc_private` revisions or Lean syntax modules
// is gated on `anneal_mir_dialect` and names every dialect it covers. This
// guard lists the dialects those gates classify; a new table entry stops the
// build here until each gate has been reviewed for it.
#[cfg(not(any(
    anneal_mir_dialect = "V2026_10_22_R7189d39d9",
    anneal_mir_dialect = "V2026_05_31_R14210df0e",
    anneal_mir_dialect = "V2026_05_30_Rf8a08b688",
)))]
compile_error!(
    "build.rs selected no MIR dialect classified by this crate's anneal_mir_dialect gates"
);

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::{ArgGroup, Parser};
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Debug, Parser)]
#[command(name = "anneal-rustc-capture capture", version, about = "Capture pinned Runtime(PostCleanup) MIR", group(
    ArgGroup::new("selection").required(true).args(["select", "scope"])
))]
pub struct Args {
    #[arg(long)]
    crate_root: PathBuf,
    #[arg(long)]
    crate_name: String,
    #[arg(long, default_value = "2024", value_parser = ["2015", "2018", "2021", "2024"])]
    edition: String,
    #[arg(long)]
    target: String,
    /// Publish into a new directory with a UTF-8 resolved path.
    /// An existing destination is refused.
    #[arg(long)]
    out_dir: PathBuf,
    // Capture these callable roots without claiming coverage of other items.
    #[arg(long, action = clap::ArgAction::Append)]
    select: Vec<String>,
    // Require admission of every required item in the compiler census.
    #[arg(long, value_parser = ["crate"])]
    scope: Option<String>,
    #[arg(long, action = clap::ArgAction::Append)]
    cfg: Vec<String>,
    /// Override the sysroot resolved from the pinned compiler distribution.
    #[arg(long)]
    sysroot: Option<PathBuf>,
    /// Compiler executable that must report the linked compiler's commit and
    /// date; defaults to `bin/rustc` in the session's sysroot.
    #[arg(long)]
    rustc: Option<PathBuf>,
    /// Declare an allowed compiler input; repeat for every staged source file.
    /// An explicit allowlist prevents omitted declarations from authorizing
    /// ambient module or include-file reads.
    #[arg(long, required = true, action = clap::ArgAction::Append)]
    source_file: Vec<PathBuf>,
    /// Bind an ASCII crate identifier to a `.rmeta` or `.rlib` file
    /// (`<crate_name>=<path>`).
    #[arg(long = "extern", value_name = "NAME=PATH", action = clap::ArgAction::Append)]
    externs: Vec<String>,
    /// Add a dependency search directory (`dependency=<dir>`) whose crate
    /// artifacts are hashed into the capture configuration.
    #[arg(short = 'L', value_name = "dependency=DIR", action = clap::ArgAction::Append)]
    search_paths: Vec<String>,
}

pub(crate) struct PreparedExterns {
    pub(crate) externs: Vec<ir::ExternFile>,
    pub(crate) dependency_dirs: Vec<PathBuf>,
    pub(crate) dependency_artifacts: Vec<ir::DependencyArtifact>,
    pub(crate) allowed_artifacts: BTreeMap<PathBuf, String>,
}

#[derive(Debug, Serialize)]
pub struct Failure {
    status: &'static str,
    diagnostics: Vec<String>,
    unsupported: Vec<ir::Unsupported>,
}

impl Failure {
    fn tool(message: impl Into<String>) -> Self {
        Self {
            status: "tool_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn io(error: std::io::Error) -> Self {
        Self::tool(error.to_string())
    }
    fn compiler(message: impl Into<String>) -> Self {
        Self {
            status: "compiler_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported(message: impl Into<String>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported_items(items: Vec<ir::Unsupported>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![format!(
                "{} required obligations are unsupported",
                items.len()
            )],
            unsupported: items,
        }
    }
}

/// Return the linked compiler libraries' version string if it names the commit
/// that `build.rs` selected.
///
/// `rustc_version_str` returns the `CFG_VERSION` compiled into the linked
/// `rustc_interface`, the "version string for `rustc` itself". Upstream builds
/// print the nine-digit short commit there, and Fuchsia's builds print the
/// commit inside their `git_revisions:` description, so the prefix check
/// accepts both. A driver built or run against another compiler's libraries
/// reports another commit. This is a consistency check; authenticating the
/// distribution remains the calling host's responsibility.
/// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/compiler/rustc_interface/src/util.rs#L716-L724
/// https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_interface/src/util.rs#L683-L691
pub(crate) fn linked_compiler_version() -> Option<&'static str> {
    rustc_interface::util::rustc_version_str()
        .filter(|version| version.contains(&ir::LINKED_COMPILER.commit[..9]))
}

/// Check that `rustc` is the compiler whose libraries this driver links.
///
/// Two observations must agree with the identity that `build.rs` selected:
/// the linked libraries' version string ([`linked_compiler_version`]), and the
/// full `commit-hash` and `commit-date` that `rustc --version --verbose`
/// reports. The second comparison uses the full commit, not its prefix.
///
/// `rustc` is the explicit `--rustc` or, without one, `<sysroot>/bin/rustc`:
/// a distribution may keep its compiler executable outside the sysroot it
/// compiles against. The probe runs with a cleared environment, so variables
/// such as `RUSTC_OVERRIDE_VERSION_STRING` cannot change its report. Neither
/// check replaces authentication of the distribution by the calling host.
fn check_compiler(rustc: &Path) -> Result<(), Failure> {
    if rustc.to_str().is_none() {
        return Err(Failure::tool(format!(
            "compiler path must be UTF-8: {rustc:?}"
        )));
    }
    let linked = &ir::LINKED_COMPILER;
    if linked_compiler_version().is_none() {
        return Err(Failure::tool(format!(
            "capture was linked against compiler libraries that do not report commit {}",
            &linked.commit[..9]
        )));
    }
    let mut probe = Command::new(rustc);
    probe
        .args(["--version", "--verbose"])
        .env_clear()
        .env("PATH", "/usr/bin:/bin");
    if let Some(tmpdir) = env::var_os("TMPDIR") {
        probe.env("TMPDIR", tmpdir);
    }
    let output = probe.output().map_err(|error| {
        Failure::tool(format!(
            "cannot run {} --version --verbose: {error}",
            rustc.display()
        ))
    })?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stderr = stderr.trim();
        let detail = if stderr.is_empty() {
            String::new()
        } else {
            format!(": {stderr}")
        };
        return Err(Failure::tool(format!(
            "{} --version --verbose failed with {}{detail}",
            rustc.display(),
            output.status
        )));
    }
    let text = String::from_utf8(output.stdout).map_err(|_| {
        Failure::tool(format!(
            "{} --version --verbose printed non-UTF-8 text",
            rustc.display()
        ))
    })?;
    let identity = compilers::CompilerIdentity::parse(&text)
        .map_err(|error| Failure::tool(format!("{}: {error}", rustc.display())))?;
    if identity.commit != linked.commit || identity.commit_date != linked.commit_date {
        // Name the probed dialect when it is another supported compiler. Any
        // other identity cannot run these libraries either.
        let probed = identity.supported().map_or_else(
            |_| format!("unsupported {}", compilers::mir_dialect_name(&identity)),
            |compiler| compiler.mir_dialect.to_owned(),
        );
        return Err(Failure::tool(format!(
            "{} is {probed} (commit-hash {}, commit-date {}), but this capture driver links {} (commit-hash {}, commit-date {})",
            rustc.display(),
            identity.commit,
            identity.commit_date,
            linked.mir_dialect,
            linked.commit,
            linked.commit_date
        )));
    }
    Ok(())
}

fn prepare_externs(args: &Args) -> Result<PreparedExterns, Failure> {
    let mut externs = Vec::new();
    let mut seen_names = BTreeSet::new();
    let mut allowed_artifacts = BTreeMap::new();
    for spec in &args.externs {
        let Some((name, raw_path)) = spec.split_once('=') else {
            return Err(Failure::unsupported(format!(
                "--extern {spec:?} must have the form <crate_name>=<path>"
            )));
        };
        if !compilers::is_ascii_crate_ident(name) {
            return Err(Failure::unsupported(format!(
                "invalid --extern crate name {name:?}; expected an ASCII Rust crate identifier"
            )));
        }
        if !seen_names.insert(name.to_owned()) {
            return Err(Failure::unsupported(format!(
                "duplicate --extern crate name {name:?}"
            )));
        }
        if raw_path.is_empty() {
            return Err(Failure::unsupported(format!(
                "--extern {name} path must not be empty"
            )));
        }
        let given = Path::new(raw_path);
        if !matches!(
            given.extension().and_then(|ext| ext.to_str()),
            Some("rmeta" | "rlib")
        ) {
            return Err(Failure::unsupported(format!(
                "--extern {name} path must end in .rmeta or .rlib: {raw_path:?}"
            )));
        }
        let given_meta = fs::symlink_metadata(given).map_err(Failure::io)?;
        if given_meta.file_type().is_symlink() || !given_meta.is_file() {
            return Err(Failure::unsupported(format!(
                "--extern {name} must be a regular file (not a symlink): {}",
                given.display()
            )));
        }
        let canon = fs::canonicalize(given).map_err(Failure::io)?;
        if canon.to_str().is_none() {
            return Err(Failure::unsupported(format!(
                "--extern {name} target path must be UTF-8: {canon:?}"
            )));
        }
        if !matches!(
            canon.extension().and_then(|ext| ext.to_str()),
            Some("rmeta" | "rlib")
        ) {
            return Err(Failure::unsupported(format!(
                "--extern {name} target path must end in .rmeta or .rlib: {}",
                canon.display()
            )));
        }
        let meta = fs::symlink_metadata(&canon).map_err(Failure::io)?;
        if meta.file_type().is_symlink() || !meta.is_file() {
            return Err(Failure::unsupported(format!(
                "--extern {name} target is not a regular file: {}",
                canon.display()
            )));
        }
        let bytes = fs::read(&canon).map_err(Failure::io)?;
        let sha256 = format!("{:x}", Sha256::digest(&bytes));
        if let Some(prev) = allowed_artifacts.insert(canon.clone(), sha256.clone())
            && prev != sha256
        {
            return Err(Failure::unsupported(format!(
                "external crate input changed while staging: {}",
                canon.display()
            )));
        }
        externs.push(ir::ExternFile {
            crate_name: name.to_owned(),
            path: canon,
            sha256,
        });
    }
    externs.sort_by(|a, b| a.crate_name.cmp(&b.crate_name));

    let mut dependency_dirs = Vec::new();
    let mut seen_dirs = BTreeSet::new();
    let mut dep_artifact_map = BTreeMap::new();
    for raw_search in &args.search_paths {
        let Some(raw_dir) = raw_search.strip_prefix("dependency=") else {
            return Err(Failure::unsupported(format!(
                "unsupported -L search path {raw_search:?}; only dependency=<dir> is supported"
            )));
        };
        if raw_dir.is_empty() {
            return Err(Failure::unsupported(
                "-L dependency=<dir> directory path must not be empty",
            ));
        }
        let given_dir = Path::new(raw_dir);
        let given_dir_meta = fs::symlink_metadata(given_dir).map_err(Failure::io)?;
        if given_dir_meta.file_type().is_symlink() || !given_dir_meta.is_dir() {
            return Err(Failure::unsupported(format!(
                "-L dependency path must be a regular directory (not a symlink): {}",
                given_dir.display()
            )));
        }
        let canon_dir = fs::canonicalize(given_dir).map_err(Failure::io)?;
        if canon_dir.to_str().is_none() {
            return Err(Failure::unsupported(format!(
                "-L dependency directory path must be UTF-8: {canon_dir:?}"
            )));
        }
        let dir_meta = fs::symlink_metadata(&canon_dir).map_err(Failure::io)?;
        if dir_meta.file_type().is_symlink() || !dir_meta.is_dir() {
            return Err(Failure::unsupported(format!(
                "-L dependency path is not a directory: {}",
                canon_dir.display()
            )));
        }
        if !seen_dirs.insert(canon_dir.clone()) {
            continue;
        }
        dependency_dirs.push(canon_dir.clone());
        for entry in fs::read_dir(&canon_dir).map_err(Failure::io)? {
            let entry = entry.map_err(Failure::io)?;
            let path = entry.path();
            let ft = entry.file_type().map_err(Failure::io)?;
            if ft.is_symlink() {
                return Err(Failure::unsupported(format!(
                    "symlink forbidden in -L dependency directory: {}",
                    path.display()
                )));
            }
            let ext = path.extension().and_then(|e| e.to_str());
            if matches!(ext, Some("dylib" | "dll")) {
                return Err(Failure::unsupported(format!(
                    "unsupported dynamic library in -L dependency directory: {}",
                    path.display()
                )));
            }
            if !matches!(ext, Some("rmeta" | "rlib" | "so")) {
                continue;
            }
            if !ft.is_file() || fs::canonicalize(&path).map_err(Failure::io)? != path {
                return Err(Failure::unsupported(format!(
                    "non-regular crate artifact in -L dependency directory: {}",
                    path.display()
                )));
            }
            if path.to_str().is_none() {
                return Err(Failure::unsupported(format!(
                    "crate artifact path in -L dependency directory must be UTF-8: {path:?}"
                )));
            }
            let bytes = fs::read(&path).map_err(Failure::io)?;
            let sha256 = format!("{:x}", Sha256::digest(&bytes));
            if let Some(prev) = allowed_artifacts.insert(path.clone(), sha256.clone())
                && prev != sha256
            {
                return Err(Failure::unsupported(format!(
                    "dependency artifact changed while staging: {}",
                    path.display()
                )));
            }
            dep_artifact_map.insert(path.clone(), ir::DependencyArtifact { path, sha256 });
        }
    }
    let dependency_artifacts = dep_artifact_map.into_values().collect();
    Ok(PreparedExterns {
        externs,
        dependency_dirs,
        dependency_artifacts,
        allowed_artifacts,
    })
}

fn run(mut args: Args) -> Result<serde_json::Value, Failure> {
    if !compilers::is_supported_target(&args.target) {
        return Err(Failure::unsupported(format!(
            "unsupported target {:?}; supported 64-bit little-endian targets are: {}",
            args.target,
            compilers::SUPPORTED_TARGETS.join(", ")
        )));
    }
    // Declarations, selectors, and cfgs are sets. A declared alias selects its
    // canonical filename; it does not expose other ambient aliases to rustc.
    // The recording loader uses those names and their ancestor directories as
    // its source namespace, independently checking the exact bytes read.
    // Sorting keeps manifests stable; normalization alone proves no read.
    args.crate_root = args.crate_root.canonicalize().map_err(Failure::io)?;
    for path in &mut args.source_file {
        *path = path.canonicalize().map_err(Failure::io)?;
    }
    args.source_file.sort();
    args.source_file.dedup();
    args.select.sort();
    args.select.dedup();
    args.cfg.sort();
    args.cfg.dedup();
    let prepared_externs = prepare_externs(&args)?;
    if let Some(sysroot) = &mut args.sysroot {
        if sysroot.to_str().is_none() {
            return Err(Failure::tool(format!(
                "--sysroot path must be UTF-8: {sysroot:?}"
            )));
        }
        *sysroot = sysroot.canonicalize().map_err(Failure::io)?;
        if sysroot.to_str().is_none() {
            return Err(Failure::tool(format!(
                "sysroot path must be UTF-8: {sysroot:?}"
            )));
        }
    }
    if let Some(rustc) = &mut args.rustc {
        if rustc.to_str().is_none() {
            return Err(Failure::tool(format!(
                "--rustc path must be UTF-8: {rustc:?}"
            )));
        }
        *rustc = rustc.canonicalize().map_err(|error| {
            Failure::tool(format!(
                "cannot resolve --rustc {}: {error}",
                rustc.display()
            ))
        })?;
    }
    // Check the linked libraries and any compiler named by the arguments
    // before reserving output or starting rustc. `collect` checks again
    // against the session's effective sysroot, which also covers the packaged
    // default's `bin/rustc`.
    if let Some(rustc) = args.rustc.clone().or_else(|| {
        args.sysroot
            .as_ref()
            .map(|sysroot| sysroot.join("bin/rustc"))
    }) {
        check_compiler(&rustc)?;
    } else if linked_compiler_version().is_none() {
        return Err(Failure::tool(format!(
            "capture was linked against compiler libraries that do not report commit {}",
            &ir::LINKED_COMPILER.commit[..9]
        )));
    }
    // Keep compiler side effects outside the public artifact pair. The
    // publication owner cleans up staging on every error and unwind; only its
    // completed directory rename permits a captured status below.
    let publication = publication::Publication::new(&args.out_dir).map_err(Failure::io)?;
    args.out_dir = publication.compiler_dir();
    let manifest = capture::run(&args, &prepared_externs)?;
    let json =
        serde_json::to_vec_pretty(&manifest).map_err(|error| Failure::tool(error.to_string()))?;
    let lean = lean::render(&manifest.program);
    let destination = publication
        .publish(&json, lean.as_bytes())
        .map_err(Failure::io)?;
    let json_path = destination.join("capture.json");
    let lean_path = destination.join("Captured.lean");
    Ok(serde_json::json!({
        "status": "captured", "capture": json_path, "lean": lean_path,
        "selected_count": manifest.selected.len(), "census_count": manifest.census.len(),
        "source_count": manifest.source_files.len(),
        "extern_count": manifest.externs.len(),
    }))
}

fn run_capture(args: Vec<OsString>) -> ExitCode {
    let args = match Args::try_parse_from(
        std::iter::once(OsString::from("anneal-rustc-capture capture")).chain(args),
    ) {
        Ok(args) => args,
        Err(error)
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) =>
        {
            print!("{error}");
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            println!(
                "{}",
                serde_json::to_string(&Failure::tool(error.to_string()))
                    .expect("serializable failure")
            );
            return ExitCode::from(2);
        }
    };
    // A callback or adapter panic must become an explicit failed capture,
    // never an apparently successful receipt for an incomplete compiler run.
    // rustc's own ICE hook still supplies the detailed stderr diagnostic.
    let result = std::panic::catch_unwind(|| run(args)).unwrap_or_else(|_| {
        Err(Failure::tool(
            "capture or compiler panicked; see stderr diagnostics",
        ))
    });
    match result {
        Ok(success) => {
            println!("{success}");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!(
                "{}",
                serde_json::to_string(&failure).expect("serializable failure")
            );
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    let mut args: Vec<_> = env::args_os().skip(1).collect();
    if args.is_empty() || (args.len() == 1 && matches!(args[0].to_str(), Some("--help" | "-h"))) {
        println!(
            "Usage: anneal-rustc-capture [--] <rustc arguments>\n\
             \n\
             Run the pinned compiler and report a successful analysis callback on stderr.\n\
             Verification is not performed.\n\
             \n\
             Pass compiler options unchanged, including --sysroot for an unbundled\n\
             development binary. Installed binaries use the adjacent rust/ sysroot.\n\
             Use -- before compiler --help, --version, or an input named capture.\n\
             \n\
             Use anneal-rustc-capture capture --help for typed MIR capture."
        );
        return ExitCode::SUCCESS;
    }
    if args.len() == 1 && matches!(args[0].to_str(), Some("--version" | "-V")) {
        println!("anneal-rustc-capture {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    // Only the explicit command selects typed capture. Inspect it before
    // removing the raw compiler escape, so `-- capture` remains a rustc input.
    if args.first().is_some_and(|arg| arg == "capture") {
        args.remove(0);
        return run_capture(args);
    }
    if args.first().is_some_and(|arg| arg == "--") {
        args.remove(0);
    }
    driver::run(args)
}

#[cfg(test)]
mod tests {
    #[test]
    fn linked_libraries_report_the_commit_selected_by_the_build_script() {
        let version = super::linked_compiler_version().expect("linked compiler version");
        assert!(version.contains(&super::ir::LINKED_COMPILER.commit[..9]));
    }
}
