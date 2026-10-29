//! Zero-dependency standalone builder for `precompiled-prefix/prefix-manifest.json`.
//!
//! Compiled directly with `rustc` inside the Nix derivation (`flake.nix`) to
//! audit `trusted/lean` (`Trusted.*`) and precompile `theory` (`Anneal.*`)
//! into `<anneal-root>/precompiled-prefix/` during exocrate archive creation.

#[allow(dead_code)]
#[path = "../audit.rs"]
mod audit;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use audit::Checker;

fn main() -> ExitCode {
    let mut anneal_root: Option<PathBuf> = None;
    let mut lean_bin: Option<PathBuf> = None;
    let mut out_dir: Option<PathBuf> = None;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--anneal-root" => {
                anneal_root = args.next().map(PathBuf::from);
            }
            "--lean" => {
                lean_bin = args.next().map(PathBuf::from);
            }
            "--out-dir" => {
                out_dir = args.next().map(PathBuf::from);
            }
            other => {
                eprintln!("unrecognized argument: {other}");
                return ExitCode::from(2);
            }
        }
    }

    let Some(root) = anneal_root else {
        eprintln!("missing --anneal-root <path>");
        return ExitCode::from(2);
    };
    let prefix_out = out_dir.unwrap_or_else(|| root.join("precompiled-prefix"));

    let mut checker = match Checker::new(&root, lean_bin.as_deref(), None) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("failed to initialize Checker: {e}");
            return ExitCode::from(2);
        }
    };

    match checker.write_verify_prefix(&prefix_out) {
        Ok(manifest) => {
            let _ = fs::remove_dir_all(&checker.stage);
            println!(
                "built precompiled verify prefix at {}",
                manifest.display()
            );
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("failed to build verify prefix ({}): {}", err.phase, err);
            ExitCode::from(err.code as u8)
        }
    }
}
