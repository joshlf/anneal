// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trusted CLI entry point (`cargo-anneal`).
//!
//! Supports both direct invocation (`cargo-anneal <subcommand>`) and Cargo
//! subcommand invocation (`cargo anneal <subcommand>`). All effectful stages—
//! `rustc` MIR capture (`anneal-rustc-capture`), repository boundary auditing
//! ([`cargo_anneal::audit`]), and kernel verification—execute inside
//! `trusted/`.

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use cargo_anneal::audit::{Checker, Json};
use cargo_anneal::setup;
use cargo_anneal::{VerifyOptions, resolve_anneal_root, resolve_lean_bin};

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(code) => ExitCode::from(code),
        Err((code, msg)) => {
            eprintln!("{msg}");
            ExitCode::from(code)
        }
    }
}

fn run_setup_cli(args: &[String]) -> Result<u8, (u8, String)> {
    let mut local_archive: Option<PathBuf> = None;
    let mut iter = args.iter().map(String::as_str);
    while let Some(arg) = iter.next() {
        match arg {
            "--local-archive" => {
                let Some(val) = iter.next() else {
                    return Err((
                        2,
                        "error: --local-archive requires a path".to_string(),
                    ));
                };
                local_archive = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: cargo anneal setup [--local-archive <path>]"
                );
                return Ok(0);
            }
            other => {
                return Err((
                    2,
                    format!("error: unknown setup argument `{other}`"),
                ));
            }
        }
    }

    match setup::install(local_archive) {
        Ok(root) => {
            println!("Installed Anneal toolchain at {}", root.display());
            Ok(0)
        }
        Err(err) => Err((1, format!("error: {err}"))),
    }
}

fn run(mut args: Vec<String>) -> Result<u8, (u8, String)> {
    if args.first().map(String::as_str) == Some("anneal") {
        args.remove(0);
    }

    let Some(subcmd) = args.first().map(String::as_str) else {
        return Err((1, format!("error: {}", usage())));
    };
    if subcmd == "--help" || subcmd == "-h" || subcmd == "help" {
        println!("{}", usage());
        return Ok(0);
    }
    if subcmd == "--version" || subcmd == "-V" {
        println!("cargo-anneal {}", env!("CARGO_PKG_VERSION"));
        return Ok(0);
    }
    if subcmd == "setup" {
        return run_setup_cli(&args[1..]);
    }
    let subcmd = subcmd.to_string();
    if subcmd != "audit-repo" {
        return Err((
            1,
            format!("error: unknown subcommand `{subcmd}`\n{}", usage()),
        ));
    }

    let mut options = VerifyOptions::default();
    let mut iter = args.into_iter().skip(1);

    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--lean" => {
                let Some(path) = iter.next() else {
                    return Err((
                        2,
                        "error: --lean requires a path argument".to_string(),
                    ));
                };
                let pb = PathBuf::from(path);
                if !pb.is_absolute() {
                    return Err((
                        2,
                        "error: --lean must be absolute".to_string(),
                    ));
                }
                options.lean_bin = Some(pb);
            }
            "--anneal-root" => {
                let Some(path) = iter.next() else {
                    return Err((
                        2,
                        "error: --anneal-root requires a path argument"
                            .to_string(),
                    ));
                };
                options.anneal_root = Some(PathBuf::from(path));
            }
            "--help" | "-h" => {
                println!("{}", usage());
                return Ok(0);
            }
            flag if flag.starts_with('-') => {
                return Err((
                    1,
                    format!("error: unrecognized flag `{flag}`\n{}", usage()),
                ));
            }
            pos => {
                return Err((
                    1,
                    format!(
                        "error: unexpected positional argument `{pos}`\n{}",
                        usage()
                    ),
                ));
            }
        }
    }

    match subcmd.as_str() {
        "audit-repo" => {
            let checkout = resolve_anneal_root(&options)
                .map_err(|e| (2, e.to_string()))?;
            let lean = resolve_lean_bin(&options);
            let mut checker = Checker::new(&checkout, lean.as_deref(), None)
                .map_err(|e| {
                    (
                        2,
                        format!(
                            "Trusted check could not create its private temporary directory: {e}"
                        ),
                    )
                })?;
            match checker.run() {
                Ok(report) => {
                    let guarantee = report
                        .get("guarantee")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    let k_decls = report
                        .get("kernelDeclarations")
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let replayed = report
                        .get("replayedDeclarations")
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let axioms = report
                        .get("axioms")
                        .map(Json::to_compact_string)
                        .unwrap_or_else(|| "[]".to_string());
                    let tc = report
                        .get("toolchain")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    println!(
                        "PASS: {guarantee}\n\
                         {} Trusted modules; {} Theory modules; \
                         {k_decls} Trusted kernel declarations; \
                         {replayed} total replayed declarations; \
                         axioms={axioms}\n\
                         {tc}",
                        checker.modules.len(),
                        checker.theory_modules.len()
                    );
                    let _ = fs::remove_dir_all(&checker.stage);
                    Ok(0)
                }
                Err(err) => {
                    let msg = format!(
                        "Trusted check failed ({}): {}\nTarget execution began: {}; preserved logs: {}\nRetry only after resolving/reobserving the reported failure.",
                        err.phase,
                        err.message,
                        checker.execution_began,
                        checker.stage.display()
                    );
                    Err((err.code as u8, msg))
                }
            }
        }
        _ => unreachable!(),
    }
}

fn usage() -> String {
    "usage: cargo-anneal [anneal] <setup|audit-repo> [--lean <path>] [--anneal-root <path>]".to_string()
}
