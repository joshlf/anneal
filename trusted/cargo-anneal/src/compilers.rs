// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The closed set of compilers whose captures `cargo anneal verify` accepts,
//! and how a compiler executable identifies itself.
//!
//! This table mirrors `trusted/rustc-capture/src/compilers.rs`. The packaged
//! CLI cannot read that file, so the two copies are kept separately and
//! `trusted/audit/tests/compiler_tables.rs` compares them in the repository.
//! Drift fails closed: a capture from a compiler missing here is refused, and
//! so is a dialect without a bundled `MirAst` module (see `verify.rs`).

/// A compiler whose captured MIR this CLI can check.
///
/// `mir_dialect` selects both `Trusted.Rustc.<mir_dialect>.MirAst`, the syntax
/// of the captured program, and `Trusted.MirSemantics.<mir_dialect>`, the
/// namespace of its canonical theorem roots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SupportedCompiler {
    pub(crate) mir_dialect: &'static str,
    /// Full 40-hex `commit-hash` reported by `rustc --version --verbose`.
    pub(crate) commit: &'static str,
    /// `commit-date` (`YYYY-MM-DD`) reported by `rustc --version --verbose`.
    pub(crate) commit_date: &'static str,
}

pub(crate) const SUPPORTED_COMPILERS: &[SupportedCompiler] = &[
    // Fuchsia's live in-tree rustc pin (distributed in nightly-2026-10-23).
    SupportedCompiler {
        mir_dialect: "V2026_10_22_R7189d39d9",
        commit: "7189d39d9ce936881b8132c6addeaf3e295cd455",
        commit_date: "2026-10-22",
    },
    // Team Capsule nightly-2026-06-01 toolchain pin.
    SupportedCompiler {
        mir_dialect: "V2026_05_31_R14210df0e",
        commit: "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
        commit_date: "2026-05-31",
    },
    // Prior pin (#267), distributed in nightly-2026-05-31.
    SupportedCompiler {
        mir_dialect: "V2026_05_30_Rf8a08b688",
        commit: "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
        commit_date: "2026-05-30",
    },
];

/// Every target triple whose 64-bit little-endian compilation profile
/// `cargo anneal verify` and `Trusted.MirSemantics` admit.
///
/// Mirrors `trusted/rustc-capture/src/compilers.rs` (checked by
/// `trusted/audit/tests/compiler_tables.rs`).
pub(crate) const SUPPORTED_TARGETS: &[&str] = &[
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "riscv64gc-unknown-linux-gnu",
    "x86_64-unknown-fuchsia",
    "aarch64-unknown-fuchsia",
    "riscv64gc-unknown-fuchsia",
];

/// Whether `target` belongs to [`SUPPORTED_TARGETS`].
pub(crate) fn is_supported_target(target: &str) -> bool {
    SUPPORTED_TARGETS.contains(&target)
}

/// Whether `name` is a strict ASCII Rust crate identifier
/// (`[a-zA-Z_][a-zA-Z0-9_]*`, excluding bare `_`).
///
/// Rejecting leading `-`, `@`, `:`, `=`, and non-ASCII characters prevents
/// `--extern` crate names from injecting compiler flags, `@file` response-file
/// expansions, or unstable `--extern opts:name=path` modifiers.
/// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/compiler/rustc_session/src/config.rs#L2600-L2695
/// https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_session/src/config.rs#L2287-L2382
pub(crate) fn is_ascii_crate_ident(name: &str) -> bool {
    if name.is_empty() || name == "_" {
        return false;
    }
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

/// Resolve a `--rustc-version` value: a MIR dialect name such as
/// `V2026_10_22_R7189d39d9`, or the compiler's full 40-hex commit. Only exact
/// spellings match; an abbreviated commit does not identify a compiler.
pub(crate) fn resolve(id: &str) -> Option<&'static SupportedCompiler> {
    SUPPORTED_COMPILERS
        .iter()
        .find(|compiler| compiler.mir_dialect == id || compiler.commit == id)
}

/// Return the supported compiler with this full commit.
pub(crate) fn by_commit(commit: &str) -> Option<&'static SupportedCompiler> {
    SUPPORTED_COMPILERS
        .iter()
        .find(|compiler| compiler.commit == commit)
}

/// List the accepted `--rustc-version` values for diagnostics.
pub(crate) fn supported_list() -> String {
    SUPPORTED_COMPILERS
        .iter()
        .map(|compiler| format!("{} (commit {})", compiler.mir_dialect, compiler.commit))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The `rustc --version --verbose` fields that identify a compiler build.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CompilerIdentity<'a> {
    pub(crate) commit: &'a str,
    pub(crate) commit_date: &'a str,
}

impl<'a> CompilerIdentity<'a> {
    /// Read the `commit-hash` and `commit-date` lines of
    /// `rustc --version --verbose`, under the same rules as the capture
    /// driver's parser.
    ///
    /// Both pinned driver revisions print one `key: value` line per field:
    /// `safe_println!("commit-hash: {commit_hash}")` and
    /// `safe_println!("commit-date: {commit_date}")`. The first line carries
    /// `CFG_VERSION`; a distribution may extend it (Fuchsia's builds print
    /// `rustc 1.101.0-dev (git_revisions:...)`) and the driver replaces it
    /// with `RUSTC_OVERRIDE_VERSION_STRING`, so it is ignored. Without git
    /// information the driver prints `unknown`, which identifies no compiler.
    /// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/compiler/rustc_driver_impl/src/lib.rs#L893-L924
    /// https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_driver_impl/src/lib.rs#L882-L913
    ///
    /// A missing, repeated, or malformed field is refused, so an override
    /// string containing a newline cannot supply a second `commit-hash` line.
    pub(crate) fn parse(text: &'a str) -> Result<Self, String> {
        let mut commit = None;
        let mut commit_date = None;
        for line in text.lines() {
            let (field, name, value) = if let Some(value) = line.strip_prefix("commit-hash: ") {
                (&mut commit, "commit-hash", value)
            } else if let Some(value) = line.strip_prefix("commit-date: ") {
                (&mut commit_date, "commit-date", value)
            } else {
                continue;
            };
            if field.replace(value).is_some() {
                return Err(format!("rustc --version --verbose repeats {name}"));
            }
        }
        let commit = commit.ok_or("rustc --version --verbose reports no commit-hash")?;
        let commit_date = commit_date.ok_or("rustc --version --verbose reports no commit-date")?;
        if commit.len() != 40
            || !commit
                .bytes()
                .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
        {
            return Err(format!(
                "commit-hash is not a full lowercase hexadecimal commit: {commit:?}"
            ));
        }
        let date = commit_date.as_bytes();
        let date_shape = date.len() == 10
            && date.iter().enumerate().all(|(index, byte)| match index {
                4 | 7 => *byte == b'-',
                _ => byte.is_ascii_digit(),
            });
        if !date_shape {
            return Err(format!("commit-date is not YYYY-MM-DD: {commit_date:?}"));
        }
        Ok(Self {
            commit,
            commit_date,
        })
    }

    /// Whether this is exactly `compiler`'s build: same full commit and date.
    pub(crate) fn is(&self, compiler: &SupportedCompiler) -> bool {
        self.commit == compiler.commit && self.commit_date == compiler.commit_date
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verbose(version: &str, commit: &str, date: &str) -> String {
        format!(
            "rustc {version}\nbinary: rustc\ncommit-hash: {commit}\ncommit-date: {date}\n\
             host: x86_64-unknown-linux-gnu\nrelease: 1.101.0-dev\nLLVM version: 22.1.6\n"
        )
    }

    #[test]
    fn dialect_names_derive_from_commit_dates_and_short_commits() {
        for (index, compiler) in SUPPORTED_COMPILERS.iter().enumerate() {
            assert_eq!(
                compiler.mir_dialect,
                format!(
                    "V{}_R{}",
                    compiler.commit_date.replace('-', "_"),
                    &compiler.commit[..9]
                )
            );
            let text = verbose("1.0.0", compiler.commit, compiler.commit_date);
            assert!(CompilerIdentity::parse(&text).unwrap().is(compiler));
            assert_eq!(resolve(compiler.mir_dialect), Some(compiler));
            assert_eq!(resolve(compiler.commit), Some(compiler));
            assert_eq!(by_commit(compiler.commit), Some(compiler));
            for other in &SUPPORTED_COMPILERS[index + 1..] {
                assert_ne!(compiler.commit, other.commit);
                assert_ne!(compiler.mir_dialect, other.mir_dialect);
            }
        }
        for unknown in [
            "",
            "7189d39d9",
            "V2026_10_22_R7189D39D9",
            "7189D39D9CE936881B8132C6ADDEAF3E295CD455",
            "Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst",
        ] {
            assert_eq!(resolve(unknown), None, "{unknown:?}");
        }
    }

    // A capture driver entry missing here, or one with another date or
    // dialect, would make every capture it produces unverifiable.
    // `trusted/audit/tests/compiler_tables.rs` compares this table with the
    // driver's in the source checkout; the packaged crate cannot read it.
    #[test]
    fn upstream_and_fuchsia_version_lines_both_identify_by_their_fields() {
        let commit = "7189d39d9ce936881b8132c6addeaf3e295cd455";
        for version in [
            "1.101.0-nightly (7189d39d9 2026-10-22)",
            "1.101.0-dev (git_revisions:7189d39d9ce936881b8132c6addeaf3e295cd455,llvm:0123456789abcdef)",
        ] {
            let text = verbose(version, commit, "2026-10-22");
            for text in [text.clone(), text.replace('\n', "\r\n")] {
                let identity = CompilerIdentity::parse(&text).unwrap();
                assert!(identity.is(resolve("V2026_10_22_R7189d39d9").unwrap()));
                assert!(!identity.is(resolve("V2026_05_31_R14210df0e").unwrap()));
            }
        }
    }

    #[test]
    fn missing_repeated_and_malformed_fields_are_refused() {
        let commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65";
        let good = verbose(
            "1.98.0-nightly (14210df0e 2026-05-31)",
            commit,
            "2026-05-31",
        );
        let injected = verbose(
            &format!("1.98.0\ncommit-hash: {commit}"),
            commit,
            "2026-05-31",
        );
        for (text, diagnostic) in [
            (good.replace("commit-hash", "commit_hash"), "no commit-hash"),
            (good.replace("commit-date", "commit_date"), "no commit-date"),
            (injected, "repeats commit-hash"),
            (
                format!("{good}commit-date: 2026-05-31\n"),
                "repeats commit-date",
            ),
            (good.replace(commit, "unknown"), "full lowercase"),
            (good.replace(commit, &commit[..39]), "full lowercase"),
            (
                good.replace(commit, &commit.to_uppercase()),
                "full lowercase",
            ),
            (
                good.replace(commit, &format!("{commit} ")),
                "full lowercase",
            ),
            (good.replace("2026-05-31\n", "unknown\n"), "YYYY-MM-DD"),
            (good.replace("2026-05-31\n", "2026/05/31\n"), "YYYY-MM-DD"),
        ] {
            let error = CompilerIdentity::parse(&text).unwrap_err();
            assert!(error.contains(diagnostic), "{error}\n{text}");
        }
        // A known commit with another date is a different build.
        let rebuilt = verbose("1.98.0", commit, "2026-06-01");
        assert!(
            !CompilerIdentity::parse(&rebuilt)
                .unwrap()
                .is(by_commit(commit).unwrap())
        );
    }

    #[test]
    fn target_allowlist_and_crate_ident_rules_hold() {
        for allowed in [
            "x86_64-unknown-linux-gnu",
            "aarch64-unknown-linux-gnu",
            "riscv64gc-unknown-linux-gnu",
            "x86_64-unknown-fuchsia",
            "aarch64-unknown-fuchsia",
            "riscv64gc-unknown-fuchsia",
        ] {
            assert!(is_supported_target(allowed), "{allowed}");
        }
        for rejected in [
            "",
            "i686-unknown-linux-gnu",
            "s390x-unknown-linux-gnu",
            "wasm32-unknown-unknown",
            "x86_64-apple-darwin",
        ] {
            assert!(!is_supported_target(rejected), "{rejected}");
        }
        for valid in ["dep_types", "_dep", "x1"] {
            assert!(is_ascii_crate_ident(valid), "{valid}");
        }
        for invalid in ["", "_", "--bad", "-v", "@rsp", "priv:dep", "my-crate", "9x"] {
            assert!(!is_ascii_crate_ident(invalid), "{invalid}");
        }
    }
}
