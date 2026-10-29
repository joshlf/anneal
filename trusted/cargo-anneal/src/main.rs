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

use cargo_anneal::audit::{Checker, Json};
use cargo_anneal::self_test::run_self_test;
use cargo_anneal::setup::{SetupOptions, run_setup};
use cargo_anneal::{
    VerifyOptions, resolve_anneal_root, resolve_lean_bin,
    run_trusted_audit_report, verify_crate,
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

fn run(mut args: Vec<String>) -> Result<u8, (u8, String)> {
    if args.first().map(String::as_str) == Some("anneal") {
        args.remove(0);
    }

    let Some(subcmd) = args.first().map(String::as_str) else {
        return Err((1, format!("error: {}", usage())));
    };
    if subcmd == "--help" || subcmd == "-h" {
        println!("{}", usage());
        return Ok(0);
    }
    let subcmd = subcmd.to_string();
    if !matches!(
        subcmd.as_str(),
        "setup"
            | "verify"
            | "verify-crate"
            | "audit-repo"
            | "audit-self-test"
            | "build-verify-prefix"
    ) {
        return Err((
            1,
            format!("error: unknown subcommand `{subcmd}`\n{}", usage()),
        ));
    }

    let mut crate_dir: Option<PathBuf> = None;
    let mut options = VerifyOptions::default();
    let mut setup_options = SetupOptions::default();
    let mut iter = args.into_iter().skip(1);

    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--local-archive" if subcmd == "setup" => {
                let Some(path) = iter.next() else {
                    return Err((
                        2,
                        "error: --local-archive requires a path argument"
                            .to_string(),
                    ));
                };
                setup_options.local_archive = Some(PathBuf::from(path));
            }
            "--keep-proof" if subcmd == "verify" => {
                options.keep_proof = true;
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
            pos if matches!(
                subcmd.as_str(),
                "verify" | "verify-crate" | "build-verify-prefix"
            ) => {
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
        "setup" => {
            let tc = run_setup(&setup_options)
                .map_err(|e| (1, format!("error: {e}")))?;
            println!(
                "installed Anneal toolchain at {}",
                tc.root.display()
            );
            Ok(0)
        }
        "verify" => {
            let target_dir = crate_dir.unwrap_or_else(|| PathBuf::from("."));
            let output = verify_crate(&target_dir, &options)
                .map_err(|e| (1, format!("error: {e}")))?;
            let fn_names: Vec<&str> =
                output.functions.iter().map(|f| f.name.as_str()).collect();
            println!(
                "verified: crate at {} passed Trusted.CrateTheorem ({})",
                target_dir.display(),
                fn_names.join(", ")
            );
            Ok(0)
        }
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
            println!(
                "VERIFIED: {verified_thm} : {expected_ty}\n\
                 Targets: {}\n\
                 TCB audit log: rustcLowering Permitted ({} item(s))\n\
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
        "build-verify-prefix" => {
            let checkout = resolve_anneal_root(&options)
                .map_err(|e| (2, e.to_string()))?;
            let lean = resolve_lean_bin(&options);
            let out_dir = crate_dir
                .unwrap_or_else(|| checkout.join("precompiled-prefix"));
            let mut checker = Checker::new(&checkout, lean.as_deref(), None)
                .map_err(|e| (2, format!("error: {e}")))?;
            let manifest_path = checker
                .write_verify_prefix(&out_dir)
                .map_err(|e| (e.code as u8, format!("error: {e}")))?;
            let _ = fs::remove_dir_all(&checker.stage);
            println!(
                "built precompiled verify prefix at {}",
                manifest_path.display()
            );
            Ok(0)
        }
        _ => unreachable!(),
    }
}

fn usage() -> String {
    "usage: cargo-anneal [anneal] <setup|verify|verify-crate|audit-repo|audit-self-test|build-verify-prefix> [crate-dir] [--local-archive <path>] [--lean <path>] [--anneal-root <path>] [--keep-proof]".to_string()
}
