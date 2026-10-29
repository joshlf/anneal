//! CLI entrypoint for `anneal-rustc-capture`.

use std::env;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        if arg == "--help" || arg == "-h" {
            println!("Usage: anneal-rustc-capture [--version] <crate-dir>");
            return ExitCode::SUCCESS;
        }
        if arg == "--version" || arg == "-V" {
            let ver = option_env!("CARGO_PKG_VERSION").unwrap_or("0.1.0");
            println!("anneal-rustc-capture {ver}");
            return ExitCode::SUCCESS;
        }
    }
    eprintln!("anneal-rustc-capture: MIR capture not yet implemented");
    ExitCode::from(1)
}
