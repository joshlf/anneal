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

use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::{ArgGroup, Parser};
use serde::Serialize;

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
    let linked = &ir::LINKED_COMPILER;
    if linked_compiler_version().is_none() {
        return Err(Failure::tool(format!(
            "capture was linked against compiler libraries that do not report commit {}",
            &linked.commit[..9]
        )));
    }
    let output = Command::new(rustc)
        .args(["--version", "--verbose"])
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .output()
        .map_err(|error| {
            Failure::tool(format!(
                "cannot run {} --version --verbose: {error}",
                rustc.display()
            ))
        })?;
    if !output.status.success() {
        return Err(Failure::tool(format!(
            "{} --version --verbose failed with {}",
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

fn run(mut args: Args) -> Result<serde_json::Value, Failure> {
    if args.target != "x86_64-unknown-linux-gnu" {
        return Err(Failure::unsupported(
            "the initial adapter supports only x86_64-unknown-linux-gnu",
        ));
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
    if let Some(sysroot) = &mut args.sysroot {
        *sysroot = sysroot.canonicalize().map_err(Failure::io)?;
    }
    if let Some(rustc) = &mut args.rustc {
        *rustc = rustc.canonicalize().map_err(|error| {
            Failure::tool(format!(
                "cannot resolve --rustc {}: {error}",
                rustc.display()
            ))
        })?;
    }
    // Check a compiler named by the arguments before reserving output or
    // starting rustc. `collect` checks again against the session's effective
    // sysroot, which also covers the packaged default.
    if let Some(rustc) = args.rustc.clone().or_else(|| {
        args.sysroot
            .as_ref()
            .map(|sysroot| sysroot.join("bin/rustc"))
    }) {
        check_compiler(&rustc)?;
    }
    // Keep compiler side effects outside the public artifact pair. The
    // publication owner cleans up staging on every error and unwind; only its
    // completed directory rename permits a captured status below.
    let publication = publication::Publication::new(&args.out_dir).map_err(Failure::io)?;
    args.out_dir = publication.compiler_dir();
    let manifest = capture::run(&args)?;
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
