// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The closed set of compilers this driver can link, and how a compiler
//! executable identifies itself.
//!
//! `build.rs` includes this file through `#[path]` to identify `$RUSTC`, whose
//! sysroot supplies the `rustc_private` crates the driver links. The driver
//! includes it as an ordinary module to identify the `rustc` executable named
//! by a capture run. Both users compile it with only `std`, so it must not
//! import `rustc_private` crates, external crates, or other driver modules.

/// A compiler whose MIR this driver can capture.
///
/// `mir_dialect` names the `Trusted.Rustc.<mir_dialect>.MirAst` Lean module
/// that renders this compiler's captured MIR. It is derived from the other two
/// fields by [`mir_dialect_name`]; [`CompilerIdentity::supported`] rechecks
/// that derivation for every match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SupportedCompiler {
    pub mir_dialect: &'static str,
    /// Full 40-hex `commit-hash` reported by `rustc --version --verbose`.
    pub commit: &'static str,
    /// `commit-date` (`YYYY-MM-DD`) reported by `rustc --version --verbose`.
    pub commit_date: &'static str,
}

/// Every compiler this driver can link; `build.rs` stops a build against any
/// other compiler.
///
/// Adding an entry also requires a reviewed
/// `trusted/lean/Trusted/Rustc/<Dialect>/MirAst.lean`, the matching entry in
/// `trusted/cargo-anneal/src/compilers.rs`, and a decision at every
/// `anneal_mir_dialect` gate in this crate. `main.rs` refuses to compile a
/// dialect that its gates do not list.
pub const SUPPORTED_COMPILERS: &[SupportedCompiler] = &[
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

/// The `rustc --version --verbose` fields that identify a compiler build.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompilerIdentity<'a> {
    pub commit: &'a str,
    pub commit_date: &'a str,
}

impl<'a> CompilerIdentity<'a> {
    /// Read the `commit-hash` and `commit-date` lines of
    /// `rustc --version --verbose`.
    ///
    /// Both pinned driver revisions print one `key: value` line per field:
    /// `safe_println!("commit-hash: {commit_hash}")` and
    /// `safe_println!("commit-date: {commit_date}")`.
    /// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/compiler/rustc_driver_impl/src/lib.rs#L893-L924
    /// https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_driver_impl/src/lib.rs#L882-L913
    ///
    /// Bootstrap records the hash from `git rev-parse HEAD` and the date from
    /// `git log -1 --date=short --pretty=format:%cd`. Without that information
    /// the driver prints `unknown`, which identifies no compiler.
    /// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/src/bootstrap/src/utils/channel.rs#L63-L91
    /// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/src/bootstrap/src/core/build_steps/compile.rs#L1337-L1342
    ///
    /// The first line is ignored. It carries `CFG_VERSION`, which a
    /// distribution may extend with a configured description (Fuchsia's builds
    /// print `rustc 1.101.0-dev (git_revisions:...)`), and the driver replaces
    /// it with `RUSTC_OVERRIDE_VERSION_STRING` when that variable is set.
    /// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/src/bootstrap/src/core/session.rs#L1359-L1374
    ///
    /// A missing, repeated, or malformed field is refused. In particular, an
    /// override string containing a newline cannot supply a second
    /// `commit-hash` line ahead of the real one.
    pub fn parse(text: &'a str) -> Result<Self, String> {
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

    /// Return the supported compiler with exactly this commit and date.
    ///
    /// The full commit selects the entry; matching only the dialect name would
    /// accept any build that shares its nine-digit prefix and date.
    pub fn supported(&self) -> Result<&'static SupportedCompiler, String> {
        let Some(compiler) = SUPPORTED_COMPILERS
            .iter()
            .find(|compiler| compiler.commit == self.commit)
        else {
            return Err(format!(
                "unsupported rustc: commit-hash {} with commit-date {} would be MIR dialect {}, which is not one of: {}",
                self.commit,
                self.commit_date,
                mir_dialect_name(self),
                supported_list()
            ));
        };
        if compiler.commit_date != self.commit_date {
            return Err(format!(
                "rustc commit-hash {} reports commit-date {}, but the supported build of that commit has commit-date {}",
                self.commit, self.commit_date, compiler.commit_date
            ));
        }
        if compiler.mir_dialect != mir_dialect_name(self) {
            return Err(format!(
                "supported compiler entry {} does not name its derived dialect {}",
                compiler.mir_dialect,
                mir_dialect_name(self)
            ));
        }
        Ok(compiler)
    }
}

/// Name a compiler's MIR dialect `VYYYY_MM_DD_R<first nine commit digits>`.
///
/// Nine digits match the short hash that bootstrap places in `CFG_VERSION`
/// (`git rev-parse --short=9 HEAD`), so the name reads like upstream's own
/// version string.
/// https://github.com/rust-lang/rust/blob/7189d39d9ce936881b8132c6addeaf3e295cd455/src/bootstrap/src/utils/channel.rs#L79-L85
pub fn mir_dialect_name(identity: &CompilerIdentity<'_>) -> String {
    format!(
        "V{}_R{}",
        identity.commit_date.replace('-', "_"),
        &identity.commit[..9]
    )
}

fn supported_list() -> String {
    SUPPORTED_COMPILERS
        .iter()
        .map(|compiler| {
            format!(
                "{} (commit-hash {}, commit-date {})",
                compiler.mir_dialect, compiler.commit, compiler.commit_date
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
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
    fn table_entries_are_unique_and_name_their_derived_dialects() {
        for (index, compiler) in SUPPORTED_COMPILERS.iter().enumerate() {
            let text = verbose("1.0.0", compiler.commit, compiler.commit_date);
            let identity = CompilerIdentity::parse(&text).unwrap();
            assert_eq!(mir_dialect_name(&identity), compiler.mir_dialect);
            assert_eq!(identity.supported().unwrap(), compiler);
            for other in &SUPPORTED_COMPILERS[index + 1..] {
                assert_ne!(compiler.commit, other.commit);
                assert_ne!(compiler.mir_dialect, other.mir_dialect);
            }
        }
    }

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
                assert_eq!(identity.commit, commit);
                assert_eq!(identity.commit_date, "2026-10-22");
                assert_eq!(
                    identity.supported().unwrap().mir_dialect,
                    "V2026_10_22_R7189d39d9"
                );
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
    }

    #[test]
    fn unknown_commits_and_dates_are_refused() {
        let unknown = verbose("1.0.0", &"0".repeat(40), "2026-05-31");
        let error = CompilerIdentity::parse(&unknown)
            .unwrap()
            .supported()
            .unwrap_err();
        assert!(error.contains("V2026_05_31_R000000000"), "{error}");
        assert!(error.contains("V2026_05_31_R14210df0e"), "{error}");

        let commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65";
        let wrong_date = verbose("1.0.0", commit, "2026-06-01");
        let error = CompilerIdentity::parse(&wrong_date)
            .unwrap()
            .supported()
            .unwrap_err();
        assert!(error.contains("has commit-date 2026-05-31"), "{error}");
    }
}
