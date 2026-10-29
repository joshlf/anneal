//! CLI entrypoint for `cargo-anneal`.

use std::env;
use std::process::ExitCode;

fn print_help() {
    println!(
        "\
cargo-anneal {}

USAGE:
    cargo anneal <SUBCOMMAND>
    cargo-anneal <SUBCOMMAND>

OPTIONS:
    -h, --help       Print help information
    -V, --version    Print version information",
        env!("CARGO_PKG_VERSION")
    );
}

fn main() -> ExitCode {
    let mut args: Vec<String> = env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("anneal") {
        args.remove(0);
    }

    match args.first().map(String::as_str) {
        None | Some("--help") | Some("-h") | Some("help") => {
            print_help();
            ExitCode::SUCCESS
        }
        Some("--version") | Some("-V") => {
            println!("cargo-anneal {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("error: unknown subcommand `{other}`");
            print_help();
            ExitCode::from(2)
        }
    }
}
