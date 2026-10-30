//! Untrusted CLI entry point (`cargo-anneal`).
//!
//! All semantic extraction is performed by `anneal-rustc-capture` in
//! `trusted/rustc-capture/`, and final proof acceptance is gated by
//! `trusted/audit/` (#103 §2, §5).

use std::env;
use std::process::ExitCode;

use cargo_anneal::{execute_cli, parse_cli_args};

fn main() -> ExitCode {
    let options = match parse_cli_args(env::args()) {
        Ok(opts) => opts,
        Err(err) => {
            eprintln!("cargo-anneal error: {err}");
            return ExitCode::from(1);
        }
    };
    if let Err(err) = execute_cli(&options) {
        eprintln!("cargo-anneal error: {err}");
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}
