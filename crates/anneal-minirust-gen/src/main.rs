// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command-line entry point for the mechanical MiniRust-to-Lean translator.
//!
//! ```text
//! anneal-minirust-gen vendor --tarball <minirust-<sha>.tar.gz> --commit <sha>
//!                            [--commit-date <iso>] [--commit-subject <text>]
//! anneal-minirust-gen verify-tarball --tarball <path>
//! anneal-minirust-gen generate [--check]
//! ```
//!
//! All commands accept `--minirust-dir <dir>` (default: the repository's
//! `minirust/` directory).

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;

use anneal_minirust_gen::pipeline::{self, Layout};

fn usage() -> ExitCode {
    eprintln!(
        "usage:\n  anneal-minirust-gen vendor --tarball <path> --commit <sha> [--commit-date <iso>] [--commit-subject <text>]\n  anneal-minirust-gen verify-tarball --tarball <path>\n  anneal-minirust-gen generate [--check]\n(all commands accept --minirust-dir <dir>)"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return usage();
    }
    let cmd = args.remove(0);
    let mut opts: BTreeMap<String, String> = BTreeMap::new();
    let mut flags: Vec<String> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if a == "--check" {
            flags.push(a.clone());
            i += 1;
        } else if let Some(k) = a.strip_prefix("--") {
            let Some(v) = args.get(i + 1) else { return usage() };
            opts.insert(k.to_string(), v.clone());
            i += 2;
        } else {
            return usage();
        }
    }
    let root = opts
        .get("minirust-dir")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../minirust"));
    let layout = Layout { root };
    let result = match cmd.as_str() {
        "vendor" => {
            let Some(t) = opts.get("tarball") else { return usage() };
            let mut meta = BTreeMap::new();
            for k in ["commit", "commit-date", "commit-subject"] {
                if let Some(v) = opts.get(k) {
                    meta.insert(k.replace('-', "_"), v.clone());
                }
            }
            pipeline::vendor(&layout, &PathBuf::from(t), &meta).map(|text| {
                println!("wrote {}:\n{text}", layout.lock_path().display());
            })
        }
        "verify-tarball" => {
            let Some(t) = opts.get("tarball") else { return usage() };
            pipeline::verify_tarball(&layout, &PathBuf::from(t)).map(|msg| println!("{msg}"))
        }
        "generate" => match pipeline::generate(&layout) {
            Err(e) => Err(e),
            Ok(g) => {
                print!("{}", g.summary);
                if flags.iter().any(|f| f == "--check") {
                    check(&layout, &g)
                } else {
                    pipeline::write(&layout, &g).map(|()| {
                        println!("wrote {} files under {}", g.files.len(), layout.root.display());
                    })
                }
            }
        },
        _ => return usage(),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

/// Compares freshly generated output with the files on disk.
fn check(layout: &Layout, g: &pipeline::Generated) -> Result<(), String> {
    let mut problems = Vec::new();
    for (rel, text) in &g.files {
        match std::fs::read_to_string(layout.root.join(rel)) {
            Ok(on_disk) if &on_disk == text => {}
            Ok(_) => problems.push(format!("differs: {rel}")),
            Err(_) => problems.push(format!("missing: {rel}")),
        }
    }
    let gen_dir = layout.generated_dir();
    if gen_dir.exists() {
        for rel in anneal_minirust_gen::source::list_files(&gen_dir)? {
            let full = format!("lean/MiniRustSpec/Generated/{rel}");
            if !g.files.contains_key(&full) {
                problems.push(format!("stale: {full}"));
            }
        }
    }
    if problems.is_empty() {
        println!("check: {} generated files are up to date", g.files.len());
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}
