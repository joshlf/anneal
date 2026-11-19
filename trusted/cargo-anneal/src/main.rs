// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI entrypoint for `cargo-anneal`.

mod compilers;
#[cfg(feature = "setup")]
mod setup;
mod verify;

use std::env;
use std::ffi::OsString;
#[cfg(feature = "setup")]
use std::path::PathBuf;
use std::process::ExitCode;

use clap::error::ErrorKind;
use clap::{CommandFactory, Parser, Subcommand};

#[derive(Parser)]
#[command(
    name = "cargo-anneal",
    bin_name = "cargo anneal",
    version,
    about = "Formally verify Rust programs in Lean 4",
    after_help = "Also accepts direct invocation as cargo-anneal <COMMAND>."
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Install the pinned Anneal toolchain archive.
    #[cfg(feature = "setup")]
    Setup {
        /// Install a local archive instead of downloading the pinned archive.
        #[arg(long, value_name = "path")]
        local_archive: Option<PathBuf>,
    },
    /// Capture a configured compilation and check its authored source proof.
    // Boxed so the parsed command stays small beside `Setup`
    // (`clippy::large_enum_variant`).
    Verify(Box<verify::VerifyArgs>),
}

enum Action {
    Print(String),
    Verify(Box<verify::VerifyArgs>),
}

#[derive(Debug)]
enum Failure {
    Arguments(clap::Error),
    #[cfg(feature = "setup")]
    Operation(String),
}

fn parse(mut args: Vec<OsString>) -> Result<Cli, clap::Error> {
    // Cargo passes its subcommand name as the first argument. Both invocation
    // routes use the same parser after removing that one Cargo-owned argument.
    if args.get(1).is_some_and(|arg| arg == "anneal") {
        args.remove(1);
    }
    Cli::try_parse_from(args)
}

#[cfg(feature = "setup")]
fn dispatch(
    cli: Cli,
    install: impl FnOnce(Option<PathBuf>) -> Result<PathBuf, String>,
) -> Result<Action, String> {
    match cli.command {
        None => Ok(Action::Print(format!("{}\n", Cli::command().render_help()))),
        Some(Command::Setup { local_archive }) => {
            let root = install(local_archive)?;
            Ok(Action::Print(format!(
                "Installed Anneal toolchain at {}\n",
                root.display()
            )))
        }
        Some(Command::Verify(args)) => Ok(Action::Verify(args)),
    }
}

#[cfg(not(feature = "setup"))]
fn dispatch(cli: Cli) -> Action {
    match cli.command {
        None => Action::Print(format!("{}\n", Cli::command().render_help())),
        Some(Command::Verify(args)) => Action::Verify(args),
    }
}

#[cfg(feature = "setup")]
fn run(
    args: Vec<OsString>,
    install: impl FnOnce(Option<PathBuf>) -> Result<PathBuf, String>,
) -> Result<Action, Failure> {
    let cli = match parse(args) {
        Ok(cli) => cli,
        Err(error)
            if matches!(
                error.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) =>
        {
            return Ok(Action::Print(error.to_string()));
        }
        Err(error) => return Err(Failure::Arguments(error)),
    };
    dispatch(cli, install).map_err(Failure::Operation)
}

#[cfg(not(feature = "setup"))]
fn run(args: Vec<OsString>) -> Result<Action, Failure> {
    let cli = match parse(args) {
        Ok(cli) => cli,
        Err(error)
            if matches!(
                error.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) =>
        {
            return Ok(Action::Print(error.to_string()));
        }
        Err(error) => return Err(Failure::Arguments(error)),
    };
    Ok(dispatch(cli))
}

fn main() -> ExitCode {
    #[cfg(feature = "setup")]
    let outcome = run(env::args_os().collect(), setup::install);
    #[cfg(not(feature = "setup"))]
    let outcome = run(env::args_os().collect());

    match outcome {
        Ok(Action::Print(output)) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Ok(Action::Verify(args)) => verify::main(*args),
        Err(Failure::Arguments(error)) => {
            eprint!("{error}");
            ExitCode::from(2)
        }
        #[cfg(feature = "setup")]
        Err(Failure::Operation(error)) => {
            eprintln!("error: {error}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }

    #[cfg(feature = "setup")]
    fn must_not_install(_: Option<PathBuf>) -> Result<PathBuf, String> {
        panic!("argument handling must not install a toolchain")
    }

    fn output(action: Action) -> String {
        match action {
            Action::Print(output) => output,
            Action::Verify(_) => panic!("expected printable output"),
        }
    }

    #[cfg(feature = "setup")]
    #[test]
    fn help_and_version_do_not_install() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &[][..],
                &["help"],
                &["-h"],
                &["--help"],
                &["setup", "-h"],
                &["setup", "--help"],
                &["help", "setup"],
                &["verify", "-h"],
                &["verify", "--help"],
                &["help", "verify"],
            ] {
                let output = output(
                    run(args(&[prefix, suffix].concat()), must_not_install)
                        .expect("help must succeed"),
                );
                assert!(output.contains("Usage:"), "{output}");
                if suffix.is_empty() {
                    assert!(output.contains("setup"), "{output}");
                    assert!(output.contains("verify"), "{output}");
                }
            }
            for suffix in ["-V", "--version"] {
                let output = output(
                    run(args(&[prefix, &[suffix]].concat()), must_not_install)
                        .expect("version must succeed"),
                );
                assert_eq!(
                    output,
                    format!("cargo-anneal {}\n", env!("CARGO_PKG_VERSION"))
                );
            }
        }
    }

    #[cfg(not(feature = "setup"))]
    #[test]
    fn help_and_version_omit_setup_subcommand() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &[][..],
                &["help"],
                &["-h"],
                &["--help"],
                &["verify", "-h"],
                &["verify", "--help"],
                &["help", "verify"],
            ] {
                let output =
                    output(run(args(&[prefix, suffix].concat())).expect("help must succeed"));
                assert!(output.contains("Usage:"), "{output}");
                if suffix.is_empty() {
                    assert!(!output.contains("setup"), "{output}");
                    assert!(output.contains("verify"), "{output}");
                }
            }
            for suffix in ["-V", "--version"] {
                let output =
                    output(run(args(&[prefix, &[suffix]].concat())).expect("version must succeed"));
                assert_eq!(
                    output,
                    format!("cargo-anneal {}\n", env!("CARGO_PKG_VERSION"))
                );
            }
        }
    }

    #[cfg(feature = "setup")]
    #[test]
    fn malformed_arguments_are_argument_failures() {
        for suffix in [
            &["unknown"][..],
            &["--unknown"],
            &["setup", "--unknown"],
            &["setup", "--local-archive"],
            &["setup", "--local-archive", "--unknown"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &[
                "verify",
                "--request",
                "request.json",
                "--manifest-path",
                "Cargo.toml",
            ],
        ] {
            let failure = run(
                args(&[&["cargo-anneal"], suffix].concat()),
                must_not_install,
            )
            .err()
            .expect("malformed arguments must fail");
            let Failure::Arguments(error) = failure else {
                panic!("expected an argument failure, got {failure:?}");
            };
            assert_eq!(error.exit_code(), 2);
            assert!(error.to_string().contains("error:"));
        }
    }

    #[cfg(not(feature = "setup"))]
    #[test]
    fn setup_and_missing_hermetic_tool_flags_are_argument_failures() {
        for (suffix, expected_substr) in [
            (&["setup"][..], "unrecognized subcommand 'setup'"),
            (
                &["verify", "--request", "request.json"],
                "--capture <CAPTURE>",
            ),
            (
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--capture",
                    "capture",
                    "--sysroot",
                    "sysroot",
                ],
                "--lean <LEAN>",
            ),
            (
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--capture",
                    "capture",
                    "--lean",
                    "lean",
                ],
                "--sysroot <SYSROOT>",
            ),
            (
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--manifest-path",
                    "Cargo.toml",
                    "--capture",
                    "capture",
                    "--lean",
                    "lean",
                    "--sysroot",
                    "sysroot",
                ],
                "cannot be used with",
            ),
        ] {
            let Failure::Arguments(error) = run(args(&[&["cargo-anneal"], suffix].concat()))
                .err()
                .expect("malformed or incomplete arguments must fail");
            assert_eq!(error.exit_code(), 2);
            let rendered = error.to_string();
            assert!(
                rendered.contains(expected_substr),
                "expected {expected_substr:?} in:\n{rendered}"
            );
        }
    }

    #[cfg(feature = "setup")]
    #[test]
    fn setup_dispatch_preserves_archive_and_operation_result() {
        for archive in [None, Some(PathBuf::from("local archive.tar.zst"))] {
            let mut input = args(&["cargo-anneal", "setup"]);
            if let Some(path) = &archive {
                input.push("--local-archive".into());
                input.push(path.as_os_str().into());
            }
            let output = output(
                run(input.clone(), |actual| {
                    assert_eq!(actual, archive);
                    Ok(PathBuf::from("installed toolchain"))
                })
                .expect("setup must return the operation's success"),
            );
            assert_eq!(
                output,
                "Installed Anneal toolchain at installed toolchain\n"
            );

            let failure = run(input, |_| Err("archive unavailable".into()))
                .err()
                .expect("setup must return the operation's failure");
            assert!(matches!(
                failure,
                Failure::Operation(message) if message == "archive unavailable"
            ));
        }
    }

    #[cfg(feature = "setup")]
    #[test]
    fn verify_dispatch_preserves_both_invocation_routes() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &["verify", "--request", "request.json"][..],
                &[
                    "verify",
                    "--manifest-path",
                    "Cargo.toml",
                    "--proof-dir",
                    "proof",
                    "--select",
                    "subject::function",
                ],
            ] {
                let action = run(args(&[prefix, suffix].concat()), must_not_install)
                    .expect("verify arguments must parse and dispatch");
                assert!(matches!(action, Action::Verify(_)));
            }
        }
    }

    #[cfg(not(feature = "setup"))]
    #[test]
    fn verify_dispatch_accepts_explicit_hermetic_tool_flags() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--capture",
                    "capture",
                    "--lean",
                    "lean",
                    "--sysroot",
                    "sysroot",
                ][..],
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--capture",
                    "capture",
                    "--lean",
                    "lean",
                    "--rustc",
                    "rustc",
                    "--rustc-version",
                    "V2026_05_31_R14210df0e",
                ],
            ] {
                let action = run(args(&[prefix, suffix].concat()))
                    .expect("hermetic verify arguments must parse and dispatch");
                assert!(matches!(action, Action::Verify(_)));
            }
        }
    }

    #[cfg(all(feature = "setup", unix))]
    #[test]
    fn archive_paths_do_not_require_utf8() {
        use std::os::unix::ffi::OsStringExt as _;

        let path = OsString::from_vec(b"archive-\xff.tar.zst".to_vec());
        let cli = parse(vec![
            "cargo-anneal".into(),
            "setup".into(),
            "--local-archive".into(),
            path.clone(),
        ])
        .expect("OS-native archive path must parse");
        assert!(matches!(
            cli.command,
            Some(Command::Setup { local_archive: Some(actual) })
                if actual.as_os_str() == path
        ));
    }
}
