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
//! `trusted/` (`#103`, `#109`).

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use cargo_anneal::audit::{Checker, Json, ReleaseChannel};
use cargo_anneal::self_test::run_self_test;
use cargo_anneal::setup;
use cargo_anneal::{
    VerifyOptions, resolve_anneal_root, resolve_lean_bin,
    run_trusted_audit_report,
};

fn main() -> ExitCode {
    match run(env::args().skip(1).collect()) {
        Ok(code) => ExitCode::from(code),
        Err((code, msg)) => {
            eprintln!("{msg}");
            ExitCode::from(code)
        }
    }
}

fn emit_unused_candidate_warnings(report: &Json) {
    if let Some(unused) = report
        .get("crateVerification")
        .and_then(|cv| cv.get("unusedCandidateFeatures"))
        .and_then(Json::as_arr)
    {
        for item in unused {
            if let Some(feat) = item.as_str() {
                eprintln!(
                    "warning: candidate-trusted feature `{feat}` in `allow-candidate-features` was not used during verification (it may be unused or may have graduated to @[vetted])"
                );
            }
        }
    }
}

fn active_candidate_features(report: &Json) -> Vec<String> {
    report
        .get("crateVerification")
        .and_then(|cv| cv.get("candidateFeatures"))
        .and_then(Json::as_arr)
        .map(|arr| {
            arr.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default()
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
    if !matches!(
        subcmd.as_str(),
        "verify-crate" | "audit-repo" | "audit-self-test"
    ) {
        return Err((
            1,
            format!("error: unknown subcommand `{subcmd}`\n{}", usage()),
        ));
    }

    let mut crate_dir: Option<PathBuf> = None;
    let mut options = VerifyOptions::default();
    let mut iter = args.into_iter().skip(1);

    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--allow-candidate-features"
                if matches!(subcmd.as_str(), "verify" | "verify-crate") =>
            {
                let Some(raw) = iter.next() else {
                    return Err((
                        2,
                        "error: --allow-candidate-features requires a feature list argument"
                            .to_string(),
                    ));
                };
                let list = options
                    .allow_candidate_features
                    .get_or_insert_with(Vec::new);
                for part in raw.split(',') {
                    let trimmed = part.trim();
                    if !trimmed.is_empty() {
                        list.push(trimmed.to_string());
                    }
                }
            }
            "--release-channel"
                if matches!(subcmd.as_str(), "verify" | "verify-crate") =>
            {
                let Some(raw) = iter.next() else {
                    return Err((
                        2,
                        "error: --release-channel requires `alpha` or `stable`"
                            .to_string(),
                    ));
                };
                let ch = ReleaseChannel::parse(&raw)
                    .map_err(|e| (2, format!("error: {e}")))?;
                options.release_channel = Some(ch);
            }
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
            pos if subcmd == "verify-crate" => {
                if crate_dir.is_some() {
                    return Err((
                        1,
                        format!(
                            "error: unexpected positional argument `{pos}`\n{}",
                            usage()
                        ),
                    ));
                }
                crate_dir = Some(PathBuf::from(pos));
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
        "verify-crate" => {
            let Some(target_dir) = crate_dir else {
                return Err((
                    2,
                    format!(
                        "error: `verify-crate` requires a crate directory\n{}",
                        usage()
                    ),
                ));
            };
            let report = run_trusted_audit_report(&target_dir, &options)
                .map_err(|e| (1, e.to_string()))?;
            emit_unused_candidate_warnings(&report);
            let cv = report.get("crateVerification").unwrap();
            let targets: Vec<&str> = report
                .get("manifest")
                .and_then(|m| m.get("targets"))
                .and_then(Json::as_arr)
                .map(|arr| {
                    arr.iter()
                        .filter_map(|t| t.get("def_id")?.as_str())
                        .collect()
                })
                .unwrap_or_default();
            let verified_thm = cv
                .get("verifiedTheorem")
                .and_then(Json::as_str)
                .unwrap_or("");
            let expected_ty = cv
                .get("expectedType")
                .and_then(Json::as_str)
                .unwrap_or("");
            let replayed = cv
                .get("replayedDeclarations")
                .and_then(Json::as_i64)
                .unwrap_or(0);
            let axioms = cv
                .get("axioms")
                .map(Json::to_compact_string)
                .unwrap_or_else(|| "[]".to_string());
            let candidates = active_candidate_features(&report);
            let cand_summary = if candidates.is_empty() {
                "none".to_string()
            } else {
                candidates.join(", ")
            };
            println!(
                "VERIFIED: {verified_thm} : {expected_ty}\n\
                 Targets: {}\n\
                 TCB audit log: rustcLowering Permitted ({} item(s))\n\
                 Candidate-Trusted TCB (Unvetted / Alpha): {cand_summary}\n\
                 {replayed} replayed declarations; axioms={axioms}",
                targets.join(", "),
                targets.len()
            );
            Ok(0)
        }
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
            match checker.run(true) {
                Ok(report) => {
                    let guarantee = report
                        .get("guarantee")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    let k_decls = report
                        .get("kernelDeclarations")
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let downstream = report.get("downstream");
                    let replayed = downstream
                        .and_then(|d| d.get("replayedDeclarations"))
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let claims = downstream
                        .and_then(|d| d.get("claimTheoremsChecked"))
                        .and_then(Json::as_i64)
                        .unwrap_or(0);
                    let axioms = report
                        .get("axioms")
                        .map(Json::to_compact_string)
                        .unwrap_or_else(|| "[]".to_string());
                    let src_sha = report
                        .get("sourceSha256")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    let tools_sha = report
                        .get("toolsSha256")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    let tc = report
                        .get("toolchain")
                        .and_then(Json::as_str)
                        .unwrap_or("");
                    println!(
                        "PASS: {guarantee}\n\
                         {} Trusted modules; {k_decls} Trusted kernel declarations; \
                         {replayed} total replayed declarations; \
                         {claims} claim theorem statements origin-checked; \
                         axioms={axioms}\n\
                         Source {src_sha}; tools/policy {tools_sha}\n\
                         {tc}",
                        checker.modules.len()
                    );
                    if k_decls == 0 {
                        println!("0 Trusted declarations; no semantics");
                    }
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
        "audit-self-test" => {
            let checkout = resolve_anneal_root(&options)
                .map_err(|e| (2, e.to_string()))?;
            let lean = resolve_lean_bin(&options);
            let rc = run_self_test(&checkout, lean.as_deref());
            Ok(rc as u8)
        }
        _ => unreachable!(),
    }
}

fn usage() -> String {
    "usage: cargo-anneal [anneal] <setup|verify-crate|audit-repo|audit-self-test> [crate-dir] [--lean <path>] [--anneal-root <path>] [--keep-proof] [--allow-candidate-features <feat,...>] [--release-channel <alpha|stable>]".to_string()
}
