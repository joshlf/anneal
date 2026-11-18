// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Keep the closed compiler tables of the capture driver and the verifier,
//! and everything each supported MIR dialect selects, consistent.
//!
//! The two tables live in separate packages because the packaged verifier
//! cannot read the driver's sources. Disagreement fails closed at run time,
//! but only for the affected compiler; this repository check reports it for
//! every compiler before release.

use std::fs;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn read(relative: &str) -> String {
    let path = repo_root().join(relative);
    fs::read_to_string(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

/// Extract `(mir_dialect, commit, commit_date)` from each entry of the
/// `SUPPORTED_COMPILERS` table in `relative`, in order.
fn table(relative: &str) -> Vec<(String, String, String)> {
    let text = read(relative);
    let start = text
        .find("SUPPORTED_COMPILERS: &[SupportedCompiler] = &[")
        .unwrap_or_else(|| panic!("{relative} has no SUPPORTED_COMPILERS table"));
    let end = start + text[start..].find("\n];").expect("end of table");
    let field = |entry: &str, name: &str| {
        let prefix = format!("{name}: \"");
        entry
            .lines()
            .find_map(|line| line.trim().strip_prefix(&prefix)?.strip_suffix("\","))
            .unwrap_or_else(|| panic!("{relative}: entry lacks {name}: {entry}"))
            .to_owned()
    };
    text[start..end]
        .split("SupportedCompiler {")
        .skip(1)
        .map(|entry| {
            (
                field(entry, "mir_dialect"),
                field(entry, "commit"),
                field(entry, "commit_date"),
            )
        })
        .collect()
}

#[test]
fn compiler_tables_agree_and_every_dialect_has_its_lean_model_and_gates() {
    let driver = table("trusted/rustc-capture/src/compilers.rs");
    let verifier = table("trusted/cargo-anneal/src/compilers.rs");
    assert!(!driver.is_empty());
    assert_eq!(
        driver, verifier,
        "capture driver and verifier tables differ"
    );

    let semantics = read("trusted/lean/Trusted/MirSemantics.lean");
    let bundle = read("trusted/cargo-anneal/examples/regenerate_bundle.rs");
    let guard = read("trusted/rustc-capture/src/main.rs");
    let emission = read("trusted/rustc-capture/src/lean.rs");
    for (dialect, commit, date) in &driver {
        assert_eq!(
            *dialect,
            format!("V{}_R{}", date.replace('-', "_"), &commit[..9])
        );
        let syntax = format!("trusted/lean/Trusted/Rustc/{dialect}/MirAst.lean");
        assert!(repo_root().join(&syntax).is_file(), "missing {syntax}");
        assert!(
            bundle.contains(&format!("    \"{syntax}\",\n")),
            "the verifier bundle omits {syntax}"
        );
        assert!(
            semantics.contains(&format!("\nimport Trusted.Rustc.{dialect}.MirAst\n"))
                && semantics.contains(&format!("\nnamespace {dialect}\n")),
            "Trusted.MirSemantics lacks the {dialect} roots"
        );
        // The driver's central dialect guard and its syntax-module selection
        // must both classify the dialect; a build for an unlisted dialect
        // stops at the guard.
        assert!(
            guard.contains(&format!("    anneal_mir_dialect = \"{dialect}\",\n")),
            "rustc-capture's dialect guard omits {dialect}"
        );
        assert!(
            emission.contains(&format!(
                "#[cfg(anneal_mir_dialect = \"{dialect}\")]\nconst MIR_AST: &str = \"Trusted.Rustc.{dialect}.MirAst\";\n"
            )),
            "rustc-capture does not select Trusted.Rustc.{dialect}.MirAst"
        );
    }
}
