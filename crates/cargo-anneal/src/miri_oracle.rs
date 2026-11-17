// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared Miri and Anneal differential oracle pipeline.
//!
//! Evaluates a corpus crate of closed, zero-argument Rust functions against
//! both live Miri (`-Zmiri-tree-borrows`) and Anneal's MIR-in-Lean operational
//! semantics (`Trusted.Rustc.V2026_06_01.MirSemantics`), comparing return
//! values, panic sites, and Undefined Behavior fault locations.

use std::collections::BTreeMap;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use anneal_rustc_capture::{ANNEAL_CAPTURE_DIR_ENV, CapturedItemKind, UnitTargetRecord};

use crate::driver::{
    ANNEAL_CAPTURE_FILTER_ENV, CaptureDriverConfig, aggregate_unit_manifests, resolve_rustc_wrapper,
};
use crate::obligations::derive_item_module_suffix;
use crate::scaffold::{ScaffoldConfig, scaffold_workspace_with_config};
use crate::{normalize_path_against, resolve_lake_binary, run_lake_verify_targets};

/// Environment variable that callers in test suites may set to `"1"` to
/// explicitly opt out when Miri or its sysroot is not installed.
pub const ALLOW_MISSING_MIRI_ENV: &str = "ANNEAL_ALLOW_MISSING_MIRI";

/// Environment variable overriding the `cargo` binary used by
/// [`ensure_miri_sysroot_initialized`] when running
/// `cargo +nightly-2026-06-01 miri setup`.
pub const MIRI_SETUP_BIN_ENV: &str = "ANNEAL_MIRI_SETUP_BIN";

/// Environment variable bounding, in whole seconds, how long
/// [`ensure_miri_sysroot_initialized`] lets `cargo miri setup` run before it is
/// killed and provisioning fails closed (default
/// [`DEFAULT_MIRI_SETUP_TIMEOUT_SECS`]).
pub const MIRI_SETUP_TIMEOUT_ENV: &str = "ANNEAL_MIRI_SETUP_TIMEOUT_SECS";

/// Default `cargo miri setup` timeout in seconds (a cold `std` sysroot check
/// build normally takes a few minutes).
pub const DEFAULT_MIRI_SETUP_TIMEOUT_SECS: u64 = 1800;

/// Environment variable bounding, in whole seconds, how long
/// [`ensure_miri_sysroot_initialized`] waits for `<sysroot>/.setup.lock` while
/// another `miri setup` holds it (default: the setup timeout plus 60 seconds).
pub const MIRI_SETUP_LOCK_TIMEOUT_ENV: &str = "ANNEAL_MIRI_SETUP_LOCK_TIMEOUT_SECS";

/// Default fuel bound per item when evaluating `evalMirDiffTagBounded` and
/// `probeMirDiffExecBounded`.
pub const DEFAULT_ORACLE_FUEL: u32 = 128;

/// Default `rustc` flags used for both Miri `.rlib` compilation and
/// `anneal-rustc-capture` MIR extraction.
pub const DEFAULT_CAPTURE_RUSTFLAGS: &[&str] = &[
    "-Zmir-opt-level=0",
    "-C",
    "debug-assertions=off",
    "-C",
    "overflow-checks=on",
    "--cfg",
    "anodized_embed_specs",
];

/// Default flags passed to `miri` when evaluating the reference oracle.
pub const DEFAULT_MIRI_FLAGS: &[&str] = &["-Zmiri-tree-borrows"];

/// Single source position (`<file>:<line>:<col>`) reported by `rustc` or Miri.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourcePos {
    /// File path as reported by the compiler or Miri.
    pub file: String,
    /// 1-based line number.
    pub line: u32,
    /// 1-based column number.
    pub col: u32,
}

impl SourcePos {
    /// Parse a `<file>:<line>:<col>` position string from `rustc` or Miri
    /// diagnostic output.
    pub fn parse_rustc_pos(raw: &str) -> Option<Self> {
        let trimmed = raw.trim().trim_end_matches(':');
        let mut parts = trimmed.rsplitn(3, ':');
        let col_str = parts.next()?.trim();
        let line_str = parts.next()?.trim();
        let file_str = parts.next()?.trim();
        if file_str.is_empty() {
            return None;
        }
        let line = line_str.parse::<u32>().ok()?;
        let col = col_str.parse::<u32>().ok()?;
        if line == 0 || col == 0 {
            return None;
        }
        Some(Self {
            file: file_str.to_string(),
            line,
            col,
        })
    }

    /// Format as `"<file>:<line>:<col>"`.
    pub fn display_short(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.col)
    }
}

/// Half-inclusive source span
/// (`<file>:<start_line>:<start_col>: <end_line>:<end_col>`) recorded on a
/// captured MIR statement or terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceSpan {
    /// Source file path recorded in the captured MIR.
    pub file: String,
    /// 1-based start line.
    pub start_line: u32,
    /// 1-based start column.
    pub start_col: u32,
    /// 1-based end line.
    pub end_line: u32,
    /// 1-based end column.
    pub end_col: u32,
}

impl SourceSpan {
    /// Parse an Anneal MIR span string of the form
    /// `"<file>:<start_line>:<start_col>: <end_line>:<end_col>"` (or a single
    /// point `"<file>:<line>:<col>"`).
    pub fn parse_anneal_span(raw: &str) -> Option<Self> {
        let trimmed = raw.trim();
        if trimmed.is_empty() || trimmed == "none" {
            return None;
        }
        if let Some((left, right)) = trimmed.split_once(": ") {
            let start = SourcePos::parse_rustc_pos(left)?;
            let mut end_parts = right.trim().split(':');
            let end_line = end_parts.next()?.trim().parse::<u32>().ok()?;
            let end_col = end_parts.next()?.trim().parse::<u32>().ok()?;
            if end_parts.next().is_some() || end_line == 0 || end_col == 0 {
                return None;
            }
            return Some(Self {
                file: start.file,
                start_line: start.line,
                start_col: start.col,
                end_line,
                end_col,
            });
        }
        let pos = SourcePos::parse_rustc_pos(trimmed)?;
        Some(Self {
            file: pos.file,
            start_line: pos.line,
            start_col: pos.col,
            end_line: pos.line,
            end_col: pos.col,
        })
    }

    /// Return `true` iff `pos` lies inside `self` within the same source file.
    pub fn contains_pos(&self, pos: &SourcePos) -> bool {
        if !source_files_match(&self.file, &pos.file) {
            return false;
        }
        let start = (self.start_line, self.start_col);
        let end = (self.end_line, self.end_col);
        let point = (pos.line, pos.col);
        start <= point && point <= end
    }

    /// Format as `"<file>:<start_line>:<start_col>: <end_line>:<end_col>"`.
    pub fn display_short(&self) -> String {
        format!(
            "{}:{}:{}: {}:{}",
            self.file, self.start_line, self.start_col, self.end_line, self.end_col
        )
    }
}

fn normalize_file_for_match(raw: &str) -> String {
    let slash = raw.replace('\\', "/");
    let trimmed = slash.trim();
    trimmed.strip_prefix("./").unwrap_or(trimmed).to_string()
}

/// Compare a captured MIR relative file path (such as `"src/lib.rs"`) against
/// a `rustc` or Miri diagnostic file path (such as `"src/lib.rs"` or
/// `"/tmp/.../corpus/src/lib.rs"`).
pub fn source_files_match(a: &str, b: &str) -> bool {
    let na = normalize_file_for_match(a);
    let nb = normalize_file_for_match(b);
    if na.is_empty() || nb.is_empty() {
        return false;
    }
    if na == nb {
        return true;
    }
    na.ends_with(&format!("/{nb}")) || nb.ends_with(&format!("/{na}"))
}

/// Outcome observed from executing a single zero-argument item under Miri.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiriOutcome {
    /// Normal return of `()`.
    PassUnit,
    /// Normal return of a scalar value with unsigned bit representation `bits`
    /// and byte width `size_bytes`.
    PassScalar {
        /// Unsigned little-endian integer bit pattern
        /// (`0 ..< 2^(8*size_bytes)`).
        bits: u128,
        /// Scalar width in bytes (`1..=16`).
        size_bytes: u32,
    },
    /// Unwinding panic observed at `pos`.
    Panic {
        /// Panic site extracted from `panicked at <file>:<line>:<col>`.
        pos: Option<SourcePos>,
        /// Panic diagnostic line.
        message: String,
    },
    /// Undefined Behavior observed at `pos`.
    Ub {
        /// Fault position extracted from the first `--> <file>:<line>:<col>`
        /// after `error: Undefined Behavior:`.
        pos: Option<SourcePos>,
        /// Diagnostic message following `error: Undefined Behavior:`.
        message: String,
    },
    /// Miri failed to compile or run the driver, or exited without entering the
    /// target item.
    OracleError(String),
}

impl MiriOutcome {
    /// Concise human-readable tag summarizing this Miri outcome.
    pub fn summary_tag(&self) -> String {
        match self {
            Self::PassUnit => "pass:unit".to_string(),
            Self::PassScalar { bits, size_bytes } => {
                format!("pass:scalar:{bits}:{size_bytes}")
            }
            Self::Panic { pos, .. } => match pos {
                Some(p) => format!("panic@{}", p.display_short()),
                None => "panic".to_string(),
            },
            Self::Ub { pos, .. } => match pos {
                Some(p) => format!("ub@{}", p.display_short()),
                None => "ub".to_string(),
            },
            Self::OracleError(err) => format!("oracle_error:{err}"),
        }
    }
}

/// Outcome observed from evaluating a single zero-argument item in Anneal's
/// MIR-in-Lean semantics (`evalMirDiffTagBounded` + `probeMirDiffExecBounded`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnnealOutcome {
    /// Normal return of `.unit`.
    PassUnit,
    /// Normal return of `.scalar { bits, sizeBytes }`.
    PassScalar {
        /// Unsigned bit representation of the returned scalar.
        bits: u128,
        /// Width of the returned scalar in bytes.
        size_bytes: u32,
    },
    /// Normal return of a non-unit, non-scalar value
    /// (`MirDiffTag.normalOther`).
    PassOther,
    /// Unwinding panic (`MirOutcome.panic`) at terminator `span`.
    Panic {
        /// Span of the panicking statement or terminator.
        span: Option<SourceSpan>,
    },
    /// Process abort (`MirOutcome.abort`) at `span`.
    Abort {
        /// Span of the aborting statement or terminator.
        span: Option<SourceSpan>,
    },
    /// Strict Undefined Behavior (`FailureKind.ub`) at statement or terminator
    /// `span`.
    Ub {
        /// Span of the faulting statement or terminator.
        span: Option<SourceSpan>,
    },
    /// Unmodeled MIR construct (`FailureKind.unsupported`) at `span`.
    Unsupported {
        /// Span of the unsupported statement or terminator.
        span: Option<SourceSpan>,
    },
    /// Unresolved external call (`MirCallE`) to `def_path` at `span`.
    ExternalCall {
        /// Callee `DefPath`.
        def_path: String,
        /// Span of the call terminator.
        span: Option<SourceSpan>,
    },
    /// Step fuel exhausted at `span`.
    OutOfFuel {
        /// Last active statement or terminator span when fuel reached zero.
        span: Option<SourceSpan>,
    },
    /// MIR capture, scaffolding, or Lean probe execution failed.
    CaptureOrLeanError(String),
}

impl AnnealOutcome {
    /// Concise human-readable tag summarizing this Anneal outcome.
    pub fn summary_tag(&self) -> String {
        match self {
            Self::PassUnit => "pass:unit".to_string(),
            Self::PassScalar { bits, size_bytes } => {
                format!("pass:scalar:{bits}:{size_bytes}")
            }
            Self::PassOther => "pass:other".to_string(),
            Self::Panic { span } => match span {
                Some(s) => format!("panic@{}", s.display_short()),
                None => "panic".to_string(),
            },
            Self::Abort { span } => match span {
                Some(s) => format!("abort@{}", s.display_short()),
                None => "abort".to_string(),
            },
            Self::Ub { span } => match span {
                Some(s) => format!("ub@{}", s.display_short()),
                None => "ub".to_string(),
            },
            Self::Unsupported { span } => match span {
                Some(s) => format!("unsupported@{}", s.display_short()),
                None => "unsupported".to_string(),
            },
            Self::ExternalCall { def_path, .. } => format!("externalCall:{def_path}"),
            Self::OutOfFuel { .. } => "outOfFuel".to_string(),
            Self::CaptureOrLeanError(err) => format!("capture_error:{err}"),
        }
    }

    /// Render the Lean `MirDiffTag` constructor expression corresponding to
    /// this outcome, or `None` for `CaptureOrLeanError`.
    pub fn to_lean_mir_diff_tag(&self) -> Option<String> {
        match self {
            Self::PassUnit => Some("MirDiffTag.normalUnit".to_string()),
            Self::PassScalar { bits, size_bytes } => {
                Some(format!("(MirDiffTag.normalScalar {bits} {size_bytes})"))
            }
            Self::PassOther => Some("MirDiffTag.normalOther".to_string()),
            Self::Panic { .. } => Some("MirDiffTag.panic".to_string()),
            Self::Abort { .. } => Some("MirDiffTag.abort".to_string()),
            Self::Ub { .. } => Some("MirDiffTag.ub".to_string()),
            Self::Unsupported { .. } => Some("MirDiffTag.unsupported".to_string()),
            Self::ExternalCall { def_path, .. } => {
                let escaped = escape_lean_string(def_path);
                Some(format!("(MirDiffTag.externalCall \"{escaped}\")"))
            }
            Self::OutOfFuel { .. } => Some("MirDiffTag.outOfFuel".to_string()),
            Self::CaptureOrLeanError(_) => None,
        }
    }

    /// Return the captured `SourceSpan` associated with this outcome, if any.
    pub fn span(&self) -> Option<&SourceSpan> {
        match self {
            Self::PassUnit | Self::PassScalar { .. } | Self::PassOther => None,
            Self::Panic { span }
            | Self::Abort { span }
            | Self::Ub { span }
            | Self::Unsupported { span }
            | Self::ExternalCall { span, .. }
            | Self::OutOfFuel { span } => span.as_ref(),
            Self::CaptureOrLeanError(_) => None,
        }
    }
}

/// Specific class of semantic divergence between Miri and Anneal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DivergenceKind {
    /// Both oracles returned normally (or Anneal aborted), but with different
    /// values or widths.
    WrongValue {
        /// Miri return summary.
        miri: String,
        /// Anneal return summary.
        anneal: String,
    },
    /// Miri returned normally or panicked cleanly, whereas Anneal raised
    /// `FailureKind.ub`.
    FalsePositiveUb {
        /// Miri outcome summary.
        miri: String,
        /// Statement or terminator span where Anneal raised `FailureKind.ub`.
        anneal_span: Option<SourceSpan>,
    },
    /// Miri detected Undefined Behavior, whereas Anneal returned normally,
    /// panicked, or aborted without raising `FailureKind.ub`.
    MissedUb {
        /// Miri UB position.
        miri_pos: Option<SourcePos>,
        /// Miri UB diagnostic message.
        miri_msg: String,
        /// Anneal outcome summary.
        anneal: String,
    },
    /// Miri panicked, whereas Anneal returned normally (or aborted).
    PanicVsReturn {
        /// Miri panic position.
        miri_pos: Option<SourcePos>,
        /// Miri panic message.
        miri_msg: String,
        /// Anneal outcome summary.
        anneal: String,
    },
    /// Miri returned normally, whereas Anneal panicked.
    ReturnVsPanic {
        /// Miri return summary.
        miri: String,
        /// Anneal panic span.
        anneal_span: Option<SourceSpan>,
    },
    /// Both Miri and Anneal reported Undefined Behavior, but Miri's fault
    /// position does not lie within Anneal's faulting statement/terminator
    /// span (or either location is missing).
    UbLocationMismatch {
        /// Miri UB position.
        miri_pos: Option<SourcePos>,
        /// Miri UB diagnostic message.
        miri_msg: String,
        /// Anneal UB statement or terminator span.
        anneal_span: Option<SourceSpan>,
    },
    /// Both Miri and Anneal panicked, but Miri's panic position does not lie
    /// within Anneal's panicking terminator span (or either location is
    /// missing).
    PanicSiteMismatch {
        /// Miri panic position.
        miri_pos: Option<SourcePos>,
        /// Anneal panic terminator span.
        anneal_span: Option<SourceSpan>,
    },
}

/// Reason why an item could not be semantically compared between Miri and
/// Anneal (never counted as `Agree`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotComparedReason {
    /// Anneal stopped at an uninterpreted external call (`MirCallE`).
    ExternalCall(String),
    /// Anneal hit `FailureKind.unsupported` on an unmodeled construct.
    Unsupported(Option<SourceSpan>),
    /// Anneal exhausted its step fuel bound.
    OutOfFuel(Option<SourceSpan>),
    /// Miri failed with an oracle execution or driver error.
    MiriOracleError(String),
    /// MIR capture, scaffolding, or Lean probe execution failed.
    CaptureFailed(String),
}

/// Three-way comparison verdict for a single item evaluated by both Miri and
/// Anneal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComparisonVerdict {
    /// Miri and Anneal agree on the outcome and (for `Panic` / `Ub`) the
    /// source location.
    Agree,
    /// Miri and Anneal semantically diverge.
    Diverge(DivergenceKind),
    /// The item hit an unmodeled construct, external call, fuel bound, or tool
    /// error and was not compared.
    NotCompared(NotComparedReason),
}

impl ComparisonVerdict {
    /// Return `true` iff this verdict is `ComparisonVerdict::Agree`.
    pub fn is_agree(&self) -> bool {
        matches!(self, Self::Agree)
    }

    /// Return `true` iff this verdict is `ComparisonVerdict::Diverge(_)`.
    pub fn is_diverge(&self) -> bool {
        matches!(self, Self::Diverge(_))
    }

    /// Return `true` iff this verdict is `ComparisonVerdict::NotCompared(_)`.
    pub fn is_not_compared(&self) -> bool {
        matches!(self, Self::NotCompared(_))
    }
}

/// Compare a single item's `MiriOutcome` and `AnnealOutcome`, enforcing
/// source-span containment on both `Ub` and `Panic` outcomes and ensuring
/// `NotCompared` cases are never classified as `Agree`.
pub fn compare_miri_and_anneal(
    miri: &MiriOutcome,
    anneal: &AnnealOutcome,
) -> ComparisonVerdict {
    if let MiriOutcome::OracleError(msg) = miri {
        return ComparisonVerdict::NotCompared(NotComparedReason::MiriOracleError(
            msg.clone(),
        ));
    }
    match anneal {
        AnnealOutcome::CaptureOrLeanError(msg) => {
            return ComparisonVerdict::NotCompared(NotComparedReason::CaptureFailed(
                msg.clone(),
            ));
        }
        AnnealOutcome::ExternalCall { def_path, .. } => {
            return ComparisonVerdict::NotCompared(NotComparedReason::ExternalCall(
                def_path.clone(),
            ));
        }
        AnnealOutcome::Unsupported { span } => {
            return ComparisonVerdict::NotCompared(NotComparedReason::Unsupported(
                span.clone(),
            ));
        }
        AnnealOutcome::OutOfFuel { span } => {
            return ComparisonVerdict::NotCompared(NotComparedReason::OutOfFuel(
                span.clone(),
            ));
        }
        _ => {}
    }

    match (miri, anneal) {
        (MiriOutcome::PassUnit, AnnealOutcome::PassUnit) => ComparisonVerdict::Agree,
        (
            MiriOutcome::PassScalar {
                bits: b1,
                size_bytes: s1,
            },
            AnnealOutcome::PassScalar {
                bits: b2,
                size_bytes: s2,
            },
        ) => {
            if b1 == b2 && s1 == s2 {
                ComparisonVerdict::Agree
            } else {
                ComparisonVerdict::Diverge(DivergenceKind::WrongValue {
                    miri: miri.summary_tag(),
                    anneal: anneal.summary_tag(),
                })
            }
        }
        (
            MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. },
            AnnealOutcome::PassUnit
            | AnnealOutcome::PassScalar { .. }
            | AnnealOutcome::PassOther
            | AnnealOutcome::Abort { .. },
        ) => ComparisonVerdict::Diverge(DivergenceKind::WrongValue {
            miri: miri.summary_tag(),
            anneal: anneal.summary_tag(),
        }),
        (
            MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. },
            AnnealOutcome::Panic { span },
        ) => ComparisonVerdict::Diverge(DivergenceKind::ReturnVsPanic {
            miri: miri.summary_tag(),
            anneal_span: span.clone(),
        }),
        (
            MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. },
            AnnealOutcome::Ub { span },
        ) => ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb {
            miri: miri.summary_tag(),
            anneal_span: span.clone(),
        }),
        (
            MiriOutcome::Panic { pos, message },
            AnnealOutcome::PassUnit
            | AnnealOutcome::PassScalar { .. }
            | AnnealOutcome::PassOther
            | AnnealOutcome::Abort { .. },
        ) => ComparisonVerdict::Diverge(DivergenceKind::PanicVsReturn {
            miri_pos: pos.clone(),
            miri_msg: message.clone(),
            anneal: anneal.summary_tag(),
        }),
        (MiriOutcome::Panic { .. }, AnnealOutcome::Ub { span }) => {
            ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb {
                miri: miri.summary_tag(),
                anneal_span: span.clone(),
            })
        }
        (MiriOutcome::Panic { pos, .. }, AnnealOutcome::Panic { span }) => {
            if let (Some(p), Some(s)) = (pos, span)
                && s.contains_pos(p)
            {
                ComparisonVerdict::Agree
            } else {
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch {
                    miri_pos: pos.clone(),
                    anneal_span: span.clone(),
                })
            }
        }
        (MiriOutcome::Ub { pos, message }, AnnealOutcome::Ub { span }) => {
            if let (Some(p), Some(s)) = (pos, span)
                && s.contains_pos(p)
            {
                ComparisonVerdict::Agree
            } else {
                ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
                    miri_pos: pos.clone(),
                    miri_msg: message.clone(),
                    anneal_span: span.clone(),
                })
            }
        }
        (
            MiriOutcome::Ub { pos, message },
            AnnealOutcome::PassUnit
            | AnnealOutcome::PassScalar { .. }
            | AnnealOutcome::PassOther
            | AnnealOutcome::Panic { .. }
            | AnnealOutcome::Abort { .. },
        ) => ComparisonVerdict::Diverge(DivergenceKind::MissedUb {
            miri_pos: pos.clone(),
            miri_msg: message.clone(),
            anneal: anneal.summary_tag(),
        }),
        _ => unreachable!("all NotCompared variants handled above"),
    }
}

/// Resolved paths to the pinned `rustc` binary, `miri` driver binary, and
/// pre-built Miri sysroot directory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MiriToolchain {
    /// Path to `rustc` matching the `miri` binary.
    pub rustc_bin: PathBuf,
    /// Path to the `miri` driver binary.
    pub miri_bin: PathBuf,
    /// Path to the Miri sysroot containing `lib/rustlib`.
    pub miri_sysroot: PathBuf,
}

impl MiriToolchain {
    /// Resolve `rustc`, `miri`, and `miri_sysroot` from explicit overrides,
    /// `ANNEAL_MIRI_{RUSTC,BIN,SYSROOT}` environment variables, or the default
    /// `~/.rustup/toolchains/nightly-2026-06-01-*` and `~/.cache/miri`
    /// locations.
    ///
    /// Returns an `Err` if any component is missing. All three paths are
    /// absolute: they are validated against the current directory, but `rustc`,
    /// `miri`, and `--sysroot` are consumed by children spawned with
    /// `current_dir(corpus_root)`, which would re-resolve a relative path
    /// against a different directory.
    pub fn resolve(
        explicit_rustc: Option<&Path>,
        explicit_miri: Option<&Path>,
        explicit_sysroot: Option<&Path>,
    ) -> Result<Self, String> {
        Self::resolve_with(
            explicit_rustc,
            explicit_miri,
            explicit_sysroot,
            &process_env_var,
            ensure_miri_sysroot_initialized,
        )
    }

    fn resolve_with<P>(
        explicit_rustc: Option<&Path>,
        explicit_miri: Option<&Path>,
        explicit_sysroot: Option<&Path>,
        get_env: EnvLookup<'_>,
        provision_default: P,
    ) -> Result<Self, String>
    where
        P: FnOnce(&Path) -> Result<PathBuf, String>,
    {
        let rustc_bin =
            resolve_tool_path_with(explicit_rustc, get_env, "ANNEAL_MIRI_RUSTC", "rustc")?;
        let miri_bin = resolve_tool_path_with(explicit_miri, get_env, "ANNEAL_MIRI_BIN", "miri")?;
        let miri_sysroot = resolve_sysroot_path_with(explicit_sysroot, get_env, provision_default)?;
        Ok(Self {
            rustc_bin,
            miri_bin,
            miri_sysroot,
        })
    }
}

/// `path` anchored to the current directory (symlinks and `..` are kept).
///
/// Every path the toolchain resolver validates is returned in this form, so
/// the file that was checked is the file a child spawned with a different
/// `current_dir` (or handed `--sysroot <path>`) actually uses.
fn absolutize(path: &Path) -> Result<PathBuf, String> {
    std::path::absolute(path)
        .map_err(|err| format!("failed to make {} absolute: {err}", path.display()))
}

fn find_executable_in_path_with(get_env: EnvLookup<'_>, tool_name: &str) -> Option<PathBuf> {
    let path_var = get_env("ANNEAL_CALLER_PATH").or_else(|| get_env("PATH"))?;
    for dir in env::split_paths(&path_var) {
        let candidate = dir.join(tool_name);
        if candidate.is_file() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = fs::metadata(&candidate)
                    && (meta.permissions().mode() & 0o111) != 0
                {
                    return Some(candidate);
                }
            }
            #[cfg(not(unix))]
            {
                return Some(candidate);
            }
        }
    }
    None
}

fn resolve_tool_path_with(
    explicit: Option<&Path>,
    get_env: EnvLookup<'_>,
    env_var: &str,
    tool_name: &str,
) -> Result<PathBuf, String> {
    if let Some(path) = explicit {
        let path = absolutize(path)?;
        if path.is_file() {
            return Ok(path);
        }
        return Err(format!(
            "explicit {tool_name} binary does not exist: {}",
            path.display()
        ));
    }
    if let Some(val) = non_empty_env_str(get_env, env_var) {
        if val.chars().any(std::path::is_separator) {
            let p = absolutize(Path::new(&val))?;
            if p.is_file() {
                return Ok(p);
            }
            return Err(format!(
                "{env_var} points to non-existent {tool_name} binary: {}",
                p.display()
            ));
        }
        let found = find_executable_in_path_with(get_env, &val).ok_or_else(|| {
            format!(
                "{env_var} points to non-existent {tool_name} binary: {val} (not found on PATH)"
            )
        })?;
        return absolutize(&found);
    }
    let home = non_empty_env_str(get_env, "HOME").map(PathBuf::from);
    if tool_name == "miri" {
        if let Some(path_miri) = find_executable_in_path_with(get_env, "miri") {
            let path_miri = absolutize(&path_miri)?;
            let cargo_home = non_empty_env_str(get_env, "CARGO_HOME")
                .map(PathBuf::from)
                .or_else(|| home.as_ref().map(|h| h.join(".cargo")));
            let is_cargo_proxy = cargo_home
                .and_then(|c| absolutize(&c.join("bin/miri")).ok())
                .is_some_and(|p| p == path_miri);
            if !is_cargo_proxy {
                return Ok(path_miri);
            }
        } else if find_executable_in_path_with(get_env, "cargo-miri").is_none() {
            return Err(
                "could not locate 'miri' or 'cargo-miri' on PATH \
                 (set ANNEAL_MIRI_BIN or add Miri to PATH)"
                    .to_string(),
            );
        }
    }
    let rustup_home = non_empty_env_str(get_env, "RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| home.map(|h| h.join(".rustup")));
    if let Some(rustup_home) = rustup_home {
        let toolchains_dir = rustup_home.join("toolchains");
        if let Ok(entries) = fs::read_dir(&toolchains_dir) {
            let mut candidates: Vec<PathBuf> = entries
                .filter_map(|e| e.ok().map(|d| d.path()))
                .filter(|p| {
                    p.file_name()
                        .and_then(|n| n.to_str())
                        .is_some_and(|n| n.starts_with("nightly-2026-06-01"))
                })
                .map(|p| p.join("bin").join(tool_name))
                .filter(|p| p.is_file())
                .collect();
            candidates.sort();
            if let Some(first) = candidates.into_iter().next() {
                return absolutize(&first);
            }
        }
    }
    Err(format!(
        "could not locate pinned nightly-2026-06-01 '{tool_name}' binary \
         (set {env_var} or install the nightly-2026-06-01 toolchain)"
    ))
}

/// Environment lookup injected into the Miri sysroot resolver.
///
/// Production code passes [`process_env_var`]. Unit tests pass a fixed map
/// instead of calling `env::set_var`: mutating the process environment races
/// every concurrently running test in the same binary that reads `HOME` or
/// `PATH` or spawns an `elan`/`rustup` proxy (which locate their toolchains
/// through `HOME`).
type EnvLookup<'a> = &'a dyn Fn(&str) -> Option<OsString>;

fn process_env_var(key: &str) -> Option<OsString> {
    env::var_os(key)
}

/// `key` as a trimmed, non-empty UTF-8 string, matching the
/// `env::var(key)` + `trim()` handling of the other `ANNEAL_*` overrides
/// (non-UTF-8 or blank values count as unset).
fn non_empty_env_str(get_env: EnvLookup<'_>, key: &str) -> Option<String> {
    let raw = get_env(key)?.into_string().ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed.to_string())
    }
}

/// [`resolve_sysroot_path`] with an injected environment and default-path
/// provisioner.
///
/// A caller-supplied sysroot (`explicit`, then `ANNEAL_MIRI_SYSROOT`) must
/// already contain `lib/rustlib`: it is never created, locked, or provisioned.
/// Only the default `${HOME}/.cache/miri` is handed to `provision_default`.
fn resolve_sysroot_path_with<P>(
    explicit: Option<&Path>,
    get_env: EnvLookup<'_>,
    provision_default: P,
) -> Result<PathBuf, String>
where
    P: FnOnce(&Path) -> Result<PathBuf, String>,
{
    if let Some(path) = explicit {
        let path = absolutize(path)?;
        if path.join("lib/rustlib").is_dir() {
            return Ok(path);
        }
        return Err(format!(
            "explicit Miri sysroot is missing lib/rustlib: {}",
            path.display()
        ));
    }
    if let Some(val) = non_empty_env_str(get_env, "ANNEAL_MIRI_SYSROOT") {
        let p = absolutize(Path::new(&val))?;
        if p.join("lib/rustlib").is_dir() {
            return Ok(p);
        }
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT is missing lib/rustlib: {}",
            p.display()
        ));
    }
    if let Some(home) = non_empty_env_str(get_env, "HOME") {
        return provision_default(&absolutize(&PathBuf::from(home).join(".cache/miri"))?);
    }
    Err(
        "Miri sysroot not found at ~/.cache/miri (or ANNEAL_MIRI_SYSROOT); \
         missing Miri sysroot is a hard error"
            .to_string(),
    )
}

/// Toolchain argument passed to a `rustup` proxy `cargo` for `miri setup`.
const MIRI_SETUP_TOOLCHAIN_ARG: &str = "+nightly-2026-06-01";

/// Ensure the Miri sysroot directory at `candidate` contains `lib/rustlib`,
/// auto-provisioning it via `cargo +nightly-2026-06-01 miri setup` under an
/// exclusive advisory lock (`<candidate>/.setup.lock`) when absent.
///
/// Fails closed if `miri setup` cannot be started, exits non-zero, exceeds
/// [`MIRI_SETUP_TIMEOUT_ENV`] seconds (default
/// [`DEFAULT_MIRI_SETUP_TIMEOUT_SECS`]), or leaves `lib/rustlib` absent, and
/// if the lock cannot be acquired within [`MIRI_SETUP_LOCK_TIMEOUT_ENV`]
/// seconds (default: setup timeout + 60).
pub fn ensure_miri_sysroot_initialized(candidate: &Path) -> Result<PathBuf, String> {
    ensure_miri_sysroot_initialized_from_env(candidate, &process_env_var)
}

fn ensure_miri_sysroot_initialized_from_env(
    candidate: &Path,
    get_env: EnvLookup<'_>,
) -> Result<PathBuf, String> {
    let candidate = absolutize(candidate)?;
    // Fast path first, so a populated sysroot never depends on the setup knobs.
    if candidate.join("lib/rustlib").is_dir() {
        return Ok(candidate);
    }
    let setup_timeout = miri_setup_timeout(get_env)?;
    let lock_wait = miri_setup_lock_wait(get_env, setup_timeout)?;
    ensure_miri_sysroot_initialized_bounded(&candidate, lock_wait, |dir| {
        run_miri_setup(dir, get_env, setup_timeout)
    })
}

/// Test-friendly variant of [`ensure_miri_sysroot_initialized`] that invokes
/// `setup_fn(candidate)` under `<candidate>/.setup.lock` when
/// `<candidate>/lib/rustlib` is absent and verifies `<candidate>/lib/rustlib`
/// exists afterwards. Waits at most the default lock timeout
/// ([`DEFAULT_MIRI_SETUP_TIMEOUT_SECS`] + 60 seconds) for the lock.
pub fn ensure_miri_sysroot_initialized_with<F>(
    candidate: &Path,
    setup_fn: F,
) -> Result<PathBuf, String>
where
    F: FnOnce(&Path) -> Result<(), String>,
{
    ensure_miri_sysroot_initialized_bounded(
        candidate,
        default_lock_wait(Duration::from_secs(DEFAULT_MIRI_SETUP_TIMEOUT_SECS)),
        setup_fn,
    )
}

fn default_lock_wait(setup_timeout: Duration) -> Duration {
    setup_timeout.saturating_add(Duration::from_secs(60))
}

fn ensure_miri_sysroot_initialized_bounded<F>(
    candidate: &Path,
    lock_wait: Duration,
    setup_fn: F,
) -> Result<PathBuf, String>
where
    F: FnOnce(&Path) -> Result<(), String>,
{
    let candidate = absolutize(candidate)?;
    let candidate = candidate.as_path();
    if candidate.join("lib/rustlib").is_dir() {
        return Ok(candidate.to_path_buf());
    }

    fs::create_dir_all(candidate).map_err(|err| {
        format!(
            "failed to create Miri sysroot directory {}: {err}",
            candidate.display()
        )
    })?;

    let lock_path = candidate.join(".setup.lock");
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .map_err(|err| {
            format!(
                "failed to open Miri sysroot lock file {}: {err}",
                lock_path.display()
            )
        })?;
    // Bounded wait: a holder that never releases (a hung `miri setup` started
    // by an older launcher, or a stuck operator `flock`) must not wedge every
    // later difftest run. The lock is released when `lock_file` is dropped.
    // Compare `started.elapsed() >= lock_wait` rather than `Instant::now() + lock_wait`
    // so arbitrarily large `Duration`s never panic on `Instant` addition overflow.
    let started = Instant::now();
    loop {
        match lock_file.try_lock() {
            Ok(()) => break,
            Err(fs::TryLockError::WouldBlock) => {
                if started.elapsed() >= lock_wait {
                    return Err(format!(
                        "timed out after {}s waiting for the Miri sysroot setup lock {} \
                         (held by another `miri setup`); missing Miri sysroot is a hard error",
                        lock_wait.as_secs(),
                        lock_path.display()
                    ));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(fs::TryLockError::Error(err)) => {
                return Err(format!(
                    "failed to acquire advisory lock on {}: {err}",
                    lock_path.display()
                ));
            }
        }
    }

    // Re-check after acquiring the exclusive lock in case another process
    // finished provisioning while we waited.
    if candidate.join("lib/rustlib").is_dir() {
        return Ok(candidate.to_path_buf());
    }

    setup_fn(candidate)?;

    if !candidate.join("lib/rustlib").is_dir() {
        return Err(format!(
            "Miri sysroot setup completed for {}, but {}/lib/rustlib is still missing; \
             missing Miri sysroot is a hard error",
            candidate.display(),
            candidate.display()
        ));
    }

    Ok(candidate.to_path_buf())
}

/// Upper bound (`1 year` in seconds) for `ANNEAL_MIRI_SETUP_TIMEOUT_SECS` and
/// `ANNEAL_MIRI_SETUP_LOCK_TIMEOUT_SECS`, matching `run_capsule_diff_test.sh`
/// and preventing `Instant` / `flock -w` overflow on pathological inputs.
const MAX_MIRI_SETUP_TIMEOUT_SECS: u64 = 31_536_000;

/// Parse a positive whole number of seconds (`1..=MAX_MIRI_SETUP_TIMEOUT_SECS`)
/// from `key`, or `default` when unset.
fn positive_secs_env(
    get_env: EnvLookup<'_>,
    key: &str,
    default: Duration,
) -> Result<Duration, String> {
    let Some(raw) = get_env(key) else {
        return Ok(default);
    };
    let text = raw.to_string_lossy();
    if text.trim().is_empty() {
        // Blank counts as unset, like `${VAR:-default}` in the launcher.
        return Ok(default);
    }
    match text.trim().parse::<u64>() {
        Ok(secs) if (1..=MAX_MIRI_SETUP_TIMEOUT_SECS).contains(&secs) => {
            Ok(Duration::from_secs(secs))
        }
        _ => Err(format!(
            "{key} must be a positive whole number of seconds (at most {MAX_MIRI_SETUP_TIMEOUT_SECS}), got {text:?}"
        )),
    }
}

fn miri_setup_timeout(get_env: EnvLookup<'_>) -> Result<Duration, String> {
    positive_secs_env(
        get_env,
        MIRI_SETUP_TIMEOUT_ENV,
        Duration::from_secs(DEFAULT_MIRI_SETUP_TIMEOUT_SECS),
    )
}

fn miri_setup_lock_wait(
    get_env: EnvLookup<'_>,
    setup_timeout: Duration,
) -> Result<Duration, String> {
    positive_secs_env(
        get_env,
        MIRI_SETUP_LOCK_TIMEOUT_ENV,
        default_lock_wait(setup_timeout),
    )
}

/// How to invoke `cargo miri setup` for the pinned `nightly-2026-06-01` toolchain.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MiriSetupCommand {
    /// `cargo` binary to run.
    cargo_bin: PathBuf,
    /// Whether `cargo_bin` is a `rustup` proxy needing `+nightly-2026-06-01`.
    pass_toolchain_arg: bool,
    /// Directory prepended to `PATH` so `cargo miri` resolves the pinned
    /// toolchain's `cargo-miri`.
    prepend_path_dir: Option<PathBuf>,
    /// `RUSTUP_TOOLCHAIN` pin for a direct toolchain `cargo`, so `rustup` proxies
    /// that `cargo-miri` invokes (e.g. `~/.cargo/bin/cargo-miri`, which `cargo`
    /// searches before `PATH`, or `rustup component add rust-src`) cannot
    /// resolve a different toolchain from the working directory.
    rustup_toolchain: Option<String>,
}

fn run_miri_setup(
    candidate: &Path,
    get_env: EnvLookup<'_>,
    timeout: Duration,
) -> Result<(), String> {
    let setup = resolve_miri_setup_cargo(get_env)?;
    let cmd = build_miri_setup_command(&setup, candidate, get_env);

    let outcome = run_with_timeout(cmd, timeout).map_err(|err| {
        format!(
            "failed to execute '{}' to initialize Miri sysroot at {}: {err}; \
             missing Miri sysroot is a hard error",
            setup.cargo_bin.display(),
            candidate.display()
        )
    })?;
    match outcome {
        TimedOutput::Finished(output) if output.status.success() => Ok(()),
        TimedOutput::Finished(output) => Err(format!(
            "Miri sysroot auto-provisioning failed at {} (status {}):\nstdout:\n{}\nstderr:\n{}; \
             missing Miri sysroot is a hard error",
            candidate.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        )),
        TimedOutput::TimedOut { stdout, stderr } => Err(format!(
            "Miri sysroot auto-provisioning timed out after {}s at {} (killed `{} miri setup`; \
             raise {MIRI_SETUP_TIMEOUT_ENV} if the build is legitimately slow):\nstdout:\n{}\nstderr:\n{}; \
             missing Miri sysroot is a hard error",
            timeout.as_secs(),
            candidate.display(),
            setup.cargo_bin.display(),
            String::from_utf8_lossy(&stdout).trim(),
            String::from_utf8_lossy(&stderr).trim()
        )),
    }
}

/// Builds the `cargo miri setup` command that provisions the Miri sysroot at
/// `candidate`.
///
/// The sysroot belongs to the Miri reference toolchain, so the command drops an
/// ambient `anneal-rustc-capture` configuration: `ANNEAL_CAPTURE_DIR` and
/// `ANNEAL_CAPTURE_FILTER`, and the `RUSTC_WRAPPER` and
/// `RUSTC_WORKSPACE_WRAPPER` variables through which Cargo would run a wrapper
/// on the sysroot build's own crates (recording their units into an unrelated
/// capture directory).
fn build_miri_setup_command(
    setup: &MiriSetupCommand,
    candidate: &Path,
    get_env: EnvLookup<'_>,
) -> Command {
    let mut cmd = Command::new(&setup.cargo_bin);
    if setup.pass_toolchain_arg {
        cmd.arg(MIRI_SETUP_TOOLCHAIN_ARG);
    }
    cmd.args(["miri", "setup"]);
    cmd.env("MIRI_SYSROOT", candidate)
        .env_remove(ANNEAL_CAPTURE_DIR_ENV)
        .env_remove(ANNEAL_CAPTURE_FILTER_ENV)
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER");
    if let Some(toolchain) = &setup.rustup_toolchain {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    if let Some(bin_dir) = &setup.prepend_path_dir {
        let current_path = get_env("ANNEAL_CALLER_PATH")
            .or_else(|| get_env("PATH"))
            .unwrap_or_default();
        let mut paths = vec![bin_dir.clone()];
        paths.extend(env::split_paths(&current_path));
        if let Ok(joined) = env::join_paths(paths) {
            cmd.env("PATH", joined);
        }
    }
    cmd
}

/// Result of [`run_with_timeout`].
enum TimedOutput {
    Finished(std::process::Output),
    TimedOut { stdout: Vec<u8>, stderr: Vec<u8> },
}

/// Run `cmd` in its own process group with stdin closed and stdout/stderr
/// captured, killing the entire process group once `timeout` elapses so
/// grandchildren (`cargo-miri`, `cargo build`, `rustc`) cannot outlive the
/// `.setup.lock` guard or keep stdout/stderr pipes open.
///
/// Design trade-off: placing `cmd` into a dedicated process group (`pgid = child.id()`)
/// means a process-group signal sent to `cargo-anneal` itself (e.g., terminal
/// `SIGINT`) will not automatically reach the setup subtree if `cargo-anneal`
/// terminates before `kill_child_and_group` runs; in that rare event,
/// `rustc-build-sysroot` stages builds in a temporary directory and atomically
/// renames into `lib/rustlib`, while keeping `.setup.lock` `CLOEXEC` ensures a
/// hung grandchild can never wedge `.setup.lock` past `timeout`.
fn run_with_timeout(mut cmd: Command, timeout: Duration) -> std::io::Result<TimedOutput> {
    use std::io::Read;
    use std::process::Stdio;
    use std::sync::mpsc;

    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }
    let mut child = spawn_retrying_text_file_busy(&mut cmd)?;
    fn kill_child_and_group(child: &mut std::process::Child) {
        #[cfg(unix)]
        {
            let pgid_arg = format!("-{}", child.id());
            let killed = Command::new("kill")
                .args(["-s", "KILL", "--", &pgid_arg])
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()
                .is_ok();
            if !killed {
                let _ = Command::new("/bin/kill")
                    .args(["-s", "KILL", "--", &pgid_arg])
                    .stdin(Stdio::null())
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .status();
            }
        }
        let _ = child.kill();
        let _ = child.wait();
    }
    fn drain<R: Read + Send + 'static>(pipe: Option<R>) -> mpsc::Receiver<Vec<u8>> {
        let (tx, rx) = mpsc::channel();
        match pipe {
            Some(mut pipe) => {
                std::thread::spawn(move || {
                    let mut buf = Vec::new();
                    let _ = pipe.read_to_end(&mut buf);
                    let _ = tx.send(buf);
                });
            }
            None => {
                let _ = tx.send(Vec::new());
            }
        }
        rx
    }
    let stdout_rx = drain(child.stdout.take());
    let stderr_rx = drain(child.stderr.take());

    let started = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if started.elapsed() >= timeout => {
                kill_child_and_group(&mut child);
                break None;
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(25)),
            Err(err) => {
                kill_child_and_group(&mut child);
                return Err(err);
            }
        }
    };
    // One shared grace period for both pipes (not 5s each, in sequence): if the
    // group kill could not run (e.g. no `kill` binary), descendants that left
    // the process group may still hold the pipes open.
    let grace = Duration::from_secs(5);
    let drain_started = Instant::now();
    let stdout = stdout_rx.recv_timeout(grace).unwrap_or_default();
    let stderr = stderr_rx
        .recv_timeout(grace.saturating_sub(drain_started.elapsed()))
        .unwrap_or_default();
    Ok(match status {
        Some(status) => TimedOutput::Finished(std::process::Output {
            status,
            stdout,
            stderr,
        }),
        None => TimedOutput::TimedOut { stdout, stderr },
    })
}

/// `cmd.spawn()`, retrying `ETXTBSY`: `execve` of a just-written executable
/// fails transiently while a concurrently forked child still holds an
/// inherited write descriptor for it.
fn spawn_retrying_text_file_busy(cmd: &mut Command) -> std::io::Result<std::process::Child> {
    let mut attempt: u64 = 0;
    loop {
        match cmd.spawn() {
            Err(err) if err.kind() == std::io::ErrorKind::ExecutableFileBusy && attempt < 10 => {
                attempt += 1;
                std::thread::sleep(Duration::from_millis(10 * attempt));
            }
            other => return other,
        }
    }
}

fn resolve_miri_setup_cargo(get_env: EnvLookup<'_>) -> Result<MiriSetupCommand, String> {
    if let Some(val) = non_empty_env_str(get_env, MIRI_SETUP_BIN_ENV) {
        // A bare command name (no path separator) is looked up on PATH, exactly
        // like the staged launcher's `"${ANNEAL_MIRI_SETUP_BIN:-cargo}"`, and the
        // resolved path is what gets spawned (`Command::new("name")` would search
        // PATH even if `./name` exists, so checking `is_file()` on a bare name
        // validated a different file than the one executed). Anything with a
        // separator is a path that must exist. All returned paths are absolutized
        // so `cargo-miri` / `rustc-build-sysroot` changing directories cannot
        // shift a relative binary or `PATH` entry.
        let resolved = if val.chars().any(std::path::is_separator) {
            let p = absolutize(Path::new(&val))?;
            if !p.is_file() {
                return Err(format!(
                    "{MIRI_SETUP_BIN_ENV} points to non-existent binary: {}",
                    p.display()
                ));
            }
            p
        } else {
            let found = find_executable_in_path_with(get_env, &val).ok_or_else(|| {
                format!("{MIRI_SETUP_BIN_ENV} command `{val}` was not found on PATH")
            })?;
            absolutize(&found)?
        };
        return Ok(MiriSetupCommand {
            cargo_bin: resolved,
            pass_toolchain_arg: true,
            prepend_path_dir: None,
            rustup_toolchain: None,
        });
    }
    let home = non_empty_env_str(get_env, "HOME").map(PathBuf::from);
    let rustup_home = non_empty_env_str(get_env, "RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| home.as_ref().map(|h| h.join(".rustup")));
    if let Some(rustup_home) = rustup_home
        && let Ok(entries) = fs::read_dir(rustup_home.join("toolchains"))
    {
        let mut candidates: Vec<(String, PathBuf)> = entries
            .filter_map(|e| e.ok().map(|d| d.path()))
            .filter_map(|p| {
                let name = p.file_name()?.to_str()?.to_string();
                name.starts_with("nightly-2026-06-01")
                    .then(|| (name, p.join("bin")))
            })
            .filter(|(_, bin_dir)| {
                bin_dir.join("cargo").is_file() && bin_dir.join("cargo-miri").is_file()
            })
            .collect();
        candidates.sort();
        if let Some((toolchain, bin_dir)) = candidates.into_iter().next() {
            let bin_dir = absolutize(&bin_dir)?;
            return Ok(MiriSetupCommand {
                cargo_bin: bin_dir.join("cargo"),
                pass_toolchain_arg: false,
                prepend_path_dir: Some(bin_dir),
                rustup_toolchain: Some(toolchain),
            });
        }
    }
    let cargo_home = non_empty_env_str(get_env, "CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| home.as_ref().map(|h| h.join(".cargo")));
    if let Some(cargo_home) = cargo_home {
        let cargo_proxy = cargo_home.join("bin/cargo");
        if cargo_proxy.is_file() {
            let cargo_proxy = absolutize(&cargo_proxy)?;
            return Ok(MiriSetupCommand {
                cargo_bin: cargo_proxy,
                pass_toolchain_arg: true,
                prepend_path_dir: None,
                rustup_toolchain: None,
            });
        }
    }
    if let Some(path_cargo) = find_executable_in_path_with(get_env, "cargo") {
        let path_cargo = absolutize(&path_cargo)?;
        let direct_toolchain = path_cargo
            .parent()
            .and_then(Path::parent)
            .and_then(Path::file_name)
            .and_then(|n| n.to_str())
            .filter(|n| n.starts_with("nightly-2026-06-01"))
            .map(str::to_string);
        let bin_dir = path_cargo.parent().map(Path::to_path_buf);
        return Ok(MiriSetupCommand {
            cargo_bin: path_cargo,
            pass_toolchain_arg: direct_toolchain.is_none(),
            prepend_path_dir: bin_dir,
            rustup_toolchain: direct_toolchain,
        });
    }
    Err(
        "could not locate 'cargo' for `cargo +nightly-2026-06-01 miri setup` \
         (set ANNEAL_MIRI_SETUP_BIN or install the nightly-2026-06-01 toolchain)"
            .to_string(),
    )
}

/// Specification of a single zero-argument item to evaluate in the oracle
/// pipeline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OracleItemSpec {
    /// Rust function identifier in the corpus crate (`src/lib.rs`).
    pub name: String,
    /// Step fuel bound for Anneal's bounded evaluator.
    pub fuel: u32,
}

impl OracleItemSpec {
    /// Construct an `OracleItemSpec` with `DEFAULT_ORACLE_FUEL` (`128`).
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            fuel: DEFAULT_ORACLE_FUEL,
        }
    }

    /// Construct an `OracleItemSpec` with an explicit `fuel` bound.
    pub fn with_fuel(name: impl Into<String>, fuel: u32) -> Self {
        Self {
            name: name.into(),
            fuel,
        }
    }
}

/// Discover zero-argument `pub fn <name>()` and `pub unsafe fn <name>()` items
/// in `rust_source` in source order.
pub fn discover_zero_arg_pub_fns(rust_source: &str) -> Vec<String> {
    let mut names = Vec::new();
    for raw_line in rust_source.lines() {
        let line = raw_line.trim();
        let rest = if let Some(r) = line.strip_prefix("pub fn ") {
            r
        } else if let Some(r) = line.strip_prefix("pub unsafe fn ") {
            r
        } else {
            continue;
        };
        let rest = rest.trim_start();
        let Some((ident, after_ident)) = rest.split_once('(') else {
            continue;
        };
        let ident = ident.trim();
        if ident.is_empty()
            || !ident
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            continue;
        }
        let after_open = after_ident.trim_start();
        if !after_open.starts_with(')') {
            continue;
        }
        names.push(ident.to_string());
    }
    names
}

/// Render the standalone Rust dispatch driver source compiled and executed by
/// `miri` against the corpus `.rlib`.
pub fn render_miri_driver_source(crate_name: &str, item_names: &[String]) -> String {
    let mut out = String::new();
    out.push_str(
        "fn print_result<T>(val: T) {\n\
         \x20   let size = core::mem::size_of::<T>();\n\
         \x20   if size == 0 {\n\
         \x20       println!(\"MIRI_PASS:unit\");\n\
         \x20       return;\n\
         \x20   }\n\
         \x20   assert!(size <= 16, \"unsupported scalar return size {size}\");\n\
         \x20   let mut buf = [0u8; 16];\n\
         \x20   unsafe {\n\
         \x20       core::ptr::copy_nonoverlapping(\n\
         \x20           (&raw const val) as *const u8,\n\
         \x20           buf.as_mut_ptr(),\n\
         \x20           size,\n\
         \x20       );\n\
         \x20   }\n\
         \x20   let bits = u128::from_le_bytes(buf);\n\
         \x20   println!(\"MIRI_PASS:scalar:{bits}:{size}\");\n\
         }\n\n\
         fn main() {\n\
         \x20   let name = std::env::var(\"MIRI_ORACLE_ITEM\")\n\
         \x20       .expect(\"MIRI_ORACLE_ITEM must be set\");\n\
         \x20   match name.as_str() {\n",
    );
    for name in item_names {
        out.push_str(&format!(
            "        \"{name}\" => {{\n\
             \x20           println!(\"MIRI_START:{name}\");\n\
             \x20           print_result({crate_name}::{name}());\n\
             \x20       }}\n"
        ));
    }
    out.push_str(
        "        other => panic!(\"unknown Miri oracle item: {other}\"),\n\
         \x20   }\n\
         }\n",
    );
    out
}

/// Parse the `stdout`, `stderr`, and exit status of a single Miri invocation
/// for `item_name` into a `MiriOutcome`.
///
/// Requires `MIRI_START:<item_name>` on `stdout` before accepting any pass,
/// panic, or UB outcome, and extracts UB positions strictly after the
/// `error: Undefined Behavior:` diagnostic header so compiler warnings earlier
/// in `stderr` are never mistaken for UB locations.
pub fn parse_miri_process_output(
    item_name: &str,
    exit_success: bool,
    stdout: &str,
    stderr: &str,
) -> MiriOutcome {
    let expected_start = format!("MIRI_START:{item_name}");
    let saw_start = stdout.lines().any(|line| line.trim() == expected_start);
    if !saw_start {
        return MiriOutcome::OracleError(format!(
            "Miri did not emit '{expected_start}' for '{item_name}' \
             (exit_success={exit_success}):\nstdout:\n{stdout}\nstderr:\n{stderr}"
        ));
    }

    if exit_success {
        for raw_line in stdout.lines() {
            let line = raw_line.trim();
            if line == "MIRI_PASS:unit" {
                return MiriOutcome::PassUnit;
            }
            if let Some(rest) = line.strip_prefix("MIRI_PASS:scalar:") {
                let mut parts = rest.split(':');
                if let (Some(b_str), Some(s_str), None) =
                    (parts.next(), parts.next(), parts.next())
                    && let (Ok(bits), Ok(size_bytes)) =
                        (b_str.parse::<u128>(), s_str.parse::<u32>())
                {
                    return MiriOutcome::PassScalar { bits, size_bytes };
                }
                return MiriOutcome::OracleError(format!(
                    "malformed MIRI_PASS:scalar line '{line}' for '{item_name}'"
                ));
            }
        }
        return MiriOutcome::OracleError(format!(
            "Miri exited 0 on '{item_name}' without a MIRI_PASS line:\n{stdout}"
        ));
    }

    if let Some(ub_idx) = stderr.find("error: Undefined Behavior:") {
        let after_ub = &stderr[ub_idx..];
        let first_line = after_ub.lines().next().unwrap_or("");
        let message = first_line
            .strip_prefix("error: Undefined Behavior:")
            .unwrap_or(first_line)
            .trim()
            .to_string();
        let pos = extract_ub_pos_after_header(after_ub);
        return MiriOutcome::Ub { pos, message };
    }

    if let Some((pos, message)) = extract_panic_from_stderr(stderr) {
        return MiriOutcome::Panic { pos, message };
    }

    MiriOutcome::OracleError(format!(
        "unrecognized Miri failure on '{item_name}':\n{stderr}"
    ))
}

fn is_stdlib_or_driver_path(file: &str) -> bool {
    let norm = normalize_file_for_match(file);
    norm.contains("/.rustup/")
        || norm.contains("/library/core/")
        || norm.contains("/library/std/")
        || norm.contains("/library/alloc/")
        || norm.ends_with("miri_driver.rs")
}

fn extract_ub_pos_after_header(after_ub: &str) -> Option<SourcePos> {
    let mut arrow_positions: Vec<SourcePos> = Vec::new();
    let mut backtrace_positions: Vec<SourcePos> = Vec::new();

    for raw_line in after_ub.lines().skip(1) {
        let trimmed = raw_line.trim();
        if trimmed.starts_with("warning:") || trimmed.starts_with("error: aborting") {
            break;
        }
        if let Some(arrow_idx) = trimmed.find("-->") {
            let candidate = trimmed[arrow_idx + 3..].trim();
            if let Some(pos) = SourcePos::parse_rustc_pos(candidate) {
                arrow_positions.push(pos);
            }
        } else if trimmed.starts_with("= note:")
            && let Some(at_idx) = trimmed.rfind(" at ")
        {
            let candidate = trimmed[at_idx + 4..].trim();
            if let Some(pos) = SourcePos::parse_rustc_pos(candidate) {
                backtrace_positions.push(pos);
            }
        }
    }

    if let Some(local_arrow) = arrow_positions
        .iter()
        .find(|p| !is_stdlib_or_driver_path(&p.file))
    {
        return Some(local_arrow.clone());
    }
    if let Some(local_bt) = backtrace_positions
        .iter()
        .find(|p| !is_stdlib_or_driver_path(&p.file))
    {
        return Some(local_bt.clone());
    }
    arrow_positions
        .into_iter()
        .next()
        .or_else(|| backtrace_positions.into_iter().next())
}

fn extract_panic_from_stderr(stderr: &str) -> Option<(Option<SourcePos>, String)> {
    let mut lines = stderr.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(idx) = line.find("panicked at ") else {
            continue;
        };
        let after = line[idx + "panicked at ".len()..].trim();
        // Modern rustc format:
        //   thread 'main' (...) panicked at src/lib.rs:140:5:
        //   attempt to compute `u32::MAX + 1_u32`, which would overflow
        if let Some(pos) = SourcePos::parse_rustc_pos(after.trim_end_matches(':')) {
            let next_msg = lines
                .peek()
                .map(|l| l.trim().to_string())
                .unwrap_or_default();
            return Some((Some(pos), next_msg));
        }
        // Legacy / inline format:
        //   thread 'main' panicked at 'message', src/lib.rs:140:5
        if let Some(comma_idx) = after.rfind(", ") {
            let msg_part = after[..comma_idx].trim().trim_matches('\'').to_string();
            let pos_part = after[comma_idx + 2..].trim();
            let pos = SourcePos::parse_rustc_pos(pos_part);
            return Some((pos, msg_part));
        }
        return Some((None, after.to_string()));
    }
    None
}

/// Configuration for running the live Miri oracle on a corpus crate.
#[derive(Clone, Debug)]
pub struct MiriOracleConfig {
    /// Root directory of the corpus crate containing `Cargo.toml` and
    /// `src/lib.rs`.
    pub corpus_root: PathBuf,
    /// Compiler flags passed to `rustc` when compiling the corpus `.rlib`.
    pub capture_rustflags: Vec<String>,
    /// Flags passed to `miri` when executing the dispatch driver.
    pub miri_flags: Vec<String>,
    /// Resolved `rustc`, `miri`, and `miri_sysroot` paths.
    pub toolchain: MiriToolchain,
}

/// Compile `config.corpus_root` as an `.rlib` against the Miri sysroot and
/// execute `miri` once per item in `items`.
pub fn run_miri_oracle(
    config: &MiriOracleConfig,
    items: &[OracleItemSpec],
) -> Result<BTreeMap<String, MiriOutcome>, String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let corpus_root = normalize_path_against(&base_dir, &config.corpus_root);
    let lib_rs = corpus_root.join("src/lib.rs");
    if !lib_rs.is_file() {
        return Err(format!(
            "corpus crate is missing src/lib.rs at {}",
            lib_rs.display()
        ));
    }

    let crate_name = infer_corpus_crate_name(&corpus_root);
    let scratch_dir = unique_oracle_temp_dir("miri-oracle");
    let rlib_path = scratch_dir.join(format!("lib{crate_name}.rlib"));
    let driver_rs_path = scratch_dir.join("miri_driver.rs");

    let item_names: Vec<String> = items.iter().map(|i| i.name.clone()).collect();
    let driver_src = render_miri_driver_source(&crate_name, &item_names);
    fs::write(&driver_rs_path, &driver_src).map_err(|err| {
        let _ = fs::remove_dir_all(&scratch_dir);
        format!(
            "failed to write Miri dispatch driver {}: {}",
            driver_rs_path.display(),
            err
        )
    })?;

    let mut compile_cmd =
        build_miri_rlib_compile_command(config, &corpus_root, &crate_name, &rlib_path);

    let compile_out = compile_cmd.output().map_err(|err| {
        let _ = fs::remove_dir_all(&scratch_dir);
        format!(
            "failed to invoke '{}' to compile corpus rlib: {}",
            config.toolchain.rustc_bin.display(),
            err
        )
    })?;
    if !compile_out.status.success() {
        let stderr = String::from_utf8_lossy(&compile_out.stderr);
        let _ = fs::remove_dir_all(&scratch_dir);
        return Err(format!(
            "rustc failed to compile corpus rlib for Miri oracle ({}):\n{}",
            compile_out.status, stderr
        ));
    }

    let mut outcomes = BTreeMap::new();
    for item in items {
        let mut miri_cmd = build_miri_item_command(
            config,
            &corpus_root,
            &crate_name,
            &driver_rs_path,
            &rlib_path,
            &item.name,
        );

        let outcome = match miri_cmd.output() {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                parse_miri_process_output(
                    &item.name,
                    output.status.success(),
                    &stdout,
                    &stderr,
                )
            }
            Err(err) => MiriOutcome::OracleError(format!(
                "failed to execute '{}' for '{}': {}",
                config.toolchain.miri_bin.display(),
                item.name,
                err
            )),
        };
        outcomes.insert(item.name.clone(), outcome);
    }

    let _ = fs::remove_dir_all(&scratch_dir);
    Ok(outcomes)
}

fn build_miri_rlib_compile_command(
    config: &MiriOracleConfig,
    corpus_root: &Path,
    crate_name: &str,
    rlib_path: &Path,
) -> Command {
    let mut compile_cmd = Command::new(&config.toolchain.rustc_bin);
    compile_cmd
        .current_dir(corpus_root)
        .env_remove(ANNEAL_CAPTURE_DIR_ENV)
        .env_remove(ANNEAL_CAPTURE_FILTER_ENV)
        .arg("--sysroot")
        .arg(&config.toolchain.miri_sysroot)
        .arg("--edition=2024")
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={crate_name}"))
        .arg("-Zalways-encode-mir");
    for flag in expand_flag_tokens(&config.capture_rustflags) {
        compile_cmd.arg(flag);
    }
    compile_cmd.arg("src/lib.rs").arg("-o").arg(rlib_path);
    compile_cmd
}

fn build_miri_item_command(
    config: &MiriOracleConfig,
    corpus_root: &Path,
    crate_name: &str,
    driver_rs_path: &Path,
    rlib_path: &Path,
    item_name: &str,
) -> Command {
    let mut miri_cmd = Command::new(&config.toolchain.miri_bin);
    miri_cmd
        .current_dir(corpus_root)
        .env_remove(ANNEAL_CAPTURE_DIR_ENV)
        .env_remove(ANNEAL_CAPTURE_FILTER_ENV)
        .arg("--sysroot")
        .arg(&config.toolchain.miri_sysroot);
    for flag in &config.miri_flags {
        miri_cmd.arg(flag);
    }
    miri_cmd
        .arg("-Zmiri-disable-isolation")
        .arg("--edition=2024")
        .arg(driver_rs_path)
        .arg("--extern")
        .arg(format!("{crate_name}={}", rlib_path.display()))
        .env("MIRI_ORACLE_ITEM", item_name);
    miri_cmd
}

fn expand_flag_tokens(flags: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for raw in flags {
        for tok in raw.split_whitespace() {
            if !tok.is_empty() {
                out.push(tok.to_string());
            }
        }
    }
    out
}

fn infer_corpus_crate_name(corpus_root: &Path) -> String {
    let cargo_toml = corpus_root.join("Cargo.toml");
    if let Ok(raw) = fs::read_to_string(&cargo_toml) {
        let mut in_package = false;
        for line in raw.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with('[') {
                in_package = trimmed == "[package]";
                continue;
            }
            if in_package
                && let Some(rest) = trimmed.strip_prefix("name")
                && let Some(eq_rest) = rest.trim_start().strip_prefix('=')
            {
                let unquoted = eq_rest.trim().trim_matches('"');
                if !unquoted.is_empty() {
                    return unquoted.replace('-', "_");
                }
            }
        }
    }
    "miri_diff_corpus".to_string()
}

fn unique_oracle_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-{}-{}-{}",
        label,
        std::process::id(),
        nanos
    ));
    let _ = fs::create_dir_all(&dir);
    dir
}

fn escape_lean_string(raw: &str) -> String {
    raw.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Render the Lean probe module (`.anneal/oracle/MiriOracleProbe.lean`) that
/// evaluates each item's `Mir.<Crate>.<name>.body` and prints its
/// `MirDiffTag` and final statement/terminator span.
pub fn render_anneal_probe_module(
    crate_camel: &str,
    items: &[OracleItemSpec],
) -> String {
    let mut out = String::new();
    out.push_str("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    for item in items {
        out.push_str(&format!("import Mir.{crate_camel}.{}\n", item.name));
    }
    out.push_str(
        "\nnamespace MiriOracleProbe\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         def activeSpan (body : CapturedMir) (st : MirExecState) : String :=\n  \
           let raw :=\n    \
             match st with\n    \
             | .running s =>\n      \
               let cur := s.memory.activeCallee.getD body\n      \
               match get? cur.basicBlocks s.frame.blockIdx with\n      \
               | some bb =>\n        \
                 match get? bb.statements s.frame.stmtIdx with\n        \
                 | some stmt => stmt.span\n        \
                 | none => bb.terminator.span\n      \
               | none => \"none\"\n    \
             | _ => \"none\"\n  \
           if raw == \"\" || raw == \"<dummy>\" then \"none\" else raw\n\n\
         def probeMirDiffExecBounded\n    \
             (fuel : Nat) (body : CapturedMir) (st : MirExecState) :\n    \
             MirDiffTag × String :=\n  \
           match fuel with\n  \
           | 0 => (.outOfFuel, activeSpan body st)\n  \
           | fuel' + 1 =>\n    \
             match stepMirState body st with\n    \
             | .ret (.normal (.unit, _)) => (.normalUnit, \"none\")\n    \
             | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, \"none\")\n    \
             | .ret (.normal (val, mem)) => ((MirDiffVerdict.normal val mem).toTagWithBody body, \"none\")\n    \
             | .ret .panic => (.panic, activeSpan body st)\n    \
             | .ret .abort => (.abort, activeSpan body st)\n    \
             | .tau st' => probeMirDiffExecBounded fuel' body st'\n    \
             | .vis (.inl (.fail .ub)) _ => (.ub, activeSpan body st)\n    \
             | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeSpan body st)\n    \
             | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeSpan body st)\n    \
             | .vis (.inr (.inl _)) k => probeMirDiffExecBounded fuel' body (k PUnit.unit)\n    \
             | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)\n\n\
         def formatTag : MirDiffTag → String\n  \
           | .normalUnit => \"pass:unit\"\n  \
           | .normalScalar bits sz => s!\"pass:scalar:{bits}:{sz}\"\n  \
           | .normalOther => \"pass:other\"\n  \
           | .panic => \"panic\"\n  \
           | .abort => \"abort\"\n  \
           | .ub => \"ub\"\n  \
           | .unsupported => \"unsupported\"\n  \
           | .externalCall p => s!\"externalCall:{p}\"\n  \
           | .outOfFuel => \"outOfFuel\"\n\n\
         def formatProbeLine (name : String) (fuel : Nat) (body : CapturedMir) : String :=\n  \
           let s := initMachineStateWithMemory body [] emptyMemory\n  \
           let (tag, span) := probeMirDiffExecBounded fuel body (.running s)\n  \
           s!\"ANNEAL_PROBE\\t{name}\\t{formatTag tag}\\t{span}\"\n\n",
    );
    for item in items {
        let escaped_name = escape_lean_string(&item.name);
        out.push_str(&format!(
            "#eval IO.println (formatProbeLine \"{escaped_name}\" {} Mir.{crate_camel}.{}.body)\n",
            item.fuel, item.name
        ));
    }
    out.push_str("\nend MiriOracleProbe\n");
    out
}

/// Parse the `stdout` emitted by running `lake env lean` on
/// `MiriOracleProbe.lean` into a map from item name to `AnnealOutcome`.
pub fn parse_anneal_probe_output(
    stdout: &str,
) -> Result<BTreeMap<String, AnnealOutcome>, String> {
    let mut outcomes = BTreeMap::new();
    for raw_line in stdout.lines() {
        let Some(rest) = raw_line.trim().strip_prefix("ANNEAL_PROBE\t") else {
            continue;
        };
        let parts: Vec<&str> = rest.splitn(3, '\t').collect();
        if parts.len() != 3 {
            return Err(format!("malformed ANNEAL_PROBE line: '{raw_line}'"));
        }
        let name = parts[0].trim().to_string();
        let tag_str = parts[1].trim();
        let span_str = parts[2].trim();
        let span = SourceSpan::parse_anneal_span(span_str);

        let outcome = if tag_str == "pass:unit" {
            AnnealOutcome::PassUnit
        } else if let Some(scalar_rest) = tag_str.strip_prefix("pass:scalar:") {
            let mut sp = scalar_rest.split(':');
            let (Some(b_str), Some(s_str), None) = (sp.next(), sp.next(), sp.next()) else {
                return Err(format!(
                    "malformed scalar tag '{tag_str}' for item '{name}'"
                ));
            };
            let bits = b_str.parse::<u128>().map_err(|e| {
                format!("invalid scalar bits in '{tag_str}' for '{name}': {e}")
            })?;
            let size_bytes = s_str.parse::<u32>().map_err(|e| {
                format!("invalid scalar size in '{tag_str}' for '{name}': {e}")
            })?;
            AnnealOutcome::PassScalar { bits, size_bytes }
        } else if tag_str == "pass:other" {
            AnnealOutcome::PassOther
        } else if tag_str == "panic" {
            AnnealOutcome::Panic { span }
        } else if tag_str == "abort" {
            AnnealOutcome::Abort { span }
        } else if tag_str == "ub" {
            AnnealOutcome::Ub { span }
        } else if tag_str == "unsupported" {
            AnnealOutcome::Unsupported { span }
        } else if let Some(def_path) = tag_str.strip_prefix("externalCall:") {
            AnnealOutcome::ExternalCall {
                def_path: def_path.to_string(),
                span,
            }
        } else if tag_str == "outOfFuel" {
            AnnealOutcome::OutOfFuel { span }
        } else {
            return Err(format!(
                "unrecognized Anneal probe tag '{tag_str}' for item '{name}'"
            ));
        };
        outcomes.insert(name, outcome);
    }
    Ok(outcomes)
}

/// Render a kernel-checked confirmation module
/// (`.anneal/oracle/MiriOracleConfirm.lean`) proving `evalMirDiffTagBounded`
/// (and `probeMirDiffExecBounded` when a span is present) by `rfl` for the
/// selected items.
pub fn render_anneal_confirm_module(
    crate_camel: &str,
    items: &[(OracleItemSpec, AnnealOutcome)],
) -> Result<String, String> {
    let mut out = String::new();
    out.push_str("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    for (item, _) in items {
        out.push_str(&format!("import Mir.{crate_camel}.{}\n", item.name));
    }
    out.push_str(
        "\nset_option maxRecDepth 100000\n\
         set_option maxHeartbeats 2000000\n\n\
         namespace MiriOracleConfirm\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         def activeSpan (body : CapturedMir) (st : MirExecState) : String :=\n  \
           let raw :=\n    \
             match st with\n    \
             | .running s =>\n      \
               let cur := s.memory.activeCallee.getD body\n      \
               match get? cur.basicBlocks s.frame.blockIdx with\n      \
               | some bb =>\n        \
                 match get? bb.statements s.frame.stmtIdx with\n        \
                 | some stmt => stmt.span\n        \
                 | none => bb.terminator.span\n      \
               | none => \"none\"\n    \
             | _ => \"none\"\n  \
           if raw == \"\" || raw == \"<dummy>\" then \"none\" else raw\n\n\
         def probeMirDiffExecBounded\n    \
             (fuel : Nat) (body : CapturedMir) (st : MirExecState) :\n    \
             MirDiffTag × String :=\n  \
           match fuel with\n  \
           | 0 => (.outOfFuel, activeSpan body st)\n  \
           | fuel' + 1 =>\n    \
             match stepMirState body st with\n    \
             | .ret (.normal (.unit, _)) => (.normalUnit, \"none\")\n    \
             | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, \"none\")\n    \
             | .ret (.normal (val, mem)) => ((MirDiffVerdict.normal val mem).toTagWithBody body, \"none\")\n    \
             | .ret .panic => (.panic, activeSpan body st)\n    \
             | .ret .abort => (.abort, activeSpan body st)\n    \
             | .tau st' => probeMirDiffExecBounded fuel' body st'\n    \
             | .vis (.inl (.fail .ub)) _ => (.ub, activeSpan body st)\n    \
             | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeSpan body st)\n    \
             | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeSpan body st)\n    \
             | .vis (.inr (.inl _)) k => probeMirDiffExecBounded fuel' body (k PUnit.unit)\n    \
             | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)\n\n",
    );

    for (item, outcome) in items {
        let Some(tag_expr) = outcome.to_lean_mir_diff_tag() else {
            return Err(format!(
                "cannot render kernel confirmation theorem for '{}' with error outcome {:?}",
                item.name, outcome
            ));
        };
        let fuel = item.fuel;
        let name = &item.name;
        out.push_str(&format!(
            "theorem confirm_tag_{name} :\n    \
                 evalMirDiffTagBounded {fuel} Mir.{crate_camel}.{name}.body\n      \
                   (initMachineStateWithMemory Mir.{crate_camel}.{name}.body [] emptyMemory) =\n      \
                 {tag_expr} := by\n  \
               rfl\n\n"
        ));
        let escaped_span = outcome
            .span()
            .map(|span| escape_lean_string(&span.display_short()))
            .unwrap_or_else(|| "none".to_string());
        out.push_str(&format!(
            "theorem confirm_probe_{name} :\n    \
                 probeMirDiffExecBounded {fuel} Mir.{crate_camel}.{name}.body\n      \
                   (.running (initMachineStateWithMemory Mir.{crate_camel}.{name}.body [] emptyMemory)) =\n      \
                 ({tag_expr}, \"{escaped_span}\") := by\n  \
               rfl\n\n"
        ));
    }

    out.push_str("end MiriOracleConfirm\n");
    Ok(out)
}

/// Configuration for running the Anneal MIR-in-Lean oracle on a corpus crate.
#[derive(Clone, Debug)]
pub struct AnnealOracleConfig {
    /// Root directory of the corpus crate containing `Cargo.toml` and
    /// `src/lib.rs`.
    pub corpus_root: PathBuf,
    /// Compiler flags passed via `RUSTFLAGS` during `anneal-rustc-capture`.
    pub capture_rustflags: Vec<String>,
    /// Optional explicit path to the Anneal repository root containing
    /// `trusted/lean` and `theory`.
    pub anneal_repo_root: Option<PathBuf>,
    /// Optional explicit path to the `anneal-rustc-capture` binary.
    pub rustc_wrapper: Option<PathBuf>,
}

/// Capture MIR from `config.corpus_root`, scaffold `.anneal/`, build `Mir` and
/// `SymbolicEval` with Lake, and run the generated Lean probe module to obtain
/// an `AnnealOutcome` (with statement/terminator span) for every item in
/// `items`.
///
/// Returns `(crate_camel, outcomes_by_name)`.
pub fn run_anneal_oracle(
    config: &AnnealOracleConfig,
    items: &[OracleItemSpec],
) -> Result<(String, BTreeMap<String, AnnealOutcome>), String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let corpus_root = normalize_path_against(&base_dir, &config.corpus_root);
    let units_dir = corpus_root.join("target/anneal/units");
    if units_dir.exists() {
        let _ = fs::remove_dir_all(&units_dir);
    }
    fs::create_dir_all(&units_dir).map_err(|err| {
        format!(
            "failed to create capture units directory {}: {}",
            units_dir.display(),
            err
        )
    })?;

    let driver_cfg = CaptureDriverConfig {
        workspace_root: corpus_root.clone(),
        manifest_path: None,
        units_dir: units_dir.clone(),
        rustc_wrapper: config.rustc_wrapper.clone(),
        filter: None,
        extra_cargo_args: vec!["--lib".to_string()],
    };

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let mut cmd = Command::new(cargo_bin);
    cmd.current_dir(&corpus_root);
    cmd.arg("check").arg("--lib");
    let wrapper = resolve_rustc_wrapper(&driver_cfg);
    let rustflags = if config.capture_rustflags.is_empty() {
        DEFAULT_CAPTURE_RUSTFLAGS.join(" ")
    } else {
        config.capture_rustflags.join(" ")
    };
    cmd.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
    cmd.env(ANNEAL_CAPTURE_DIR_ENV, &units_dir);
    cmd.env("RUSTFLAGS", rustflags);
    cmd.env_remove(ANNEAL_CAPTURE_FILTER_ENV);

    let capture_out = cmd
        .output()
        .map_err(|err| format!("failed to execute cargo check on corpus: {err}"))?;
    if !capture_out.status.success() {
        let stderr = String::from_utf8_lossy(&capture_out.stderr);
        return Err(format!(
            "cargo check failed during Anneal oracle capture ({}):\n{}",
            capture_out.status, stderr
        ));
    }

    let (_capture_manifest, records) = aggregate_unit_manifests(&units_dir)?;
    let scaffold_cfg = ScaffoldConfig {
        workspace_root: corpus_root.clone(),
        units_dir: Some(units_dir),
        anneal_repo_root: config.anneal_repo_root.clone(),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    scaffold_workspace_with_config(&scaffold_cfg, &records)?;

    let subject_records: Vec<&UnitTargetRecord> = records
        .iter()
        .filter(|r| r.item_kind == CapturedItemKind::Subject)
        .collect();
    if subject_records.is_empty() {
        return Err("zero subject functions captured from corpus crate".to_string());
    }

    let sample_suffix = derive_item_module_suffix(subject_records[0]);
    let crate_camel = sample_suffix
        .split('.')
        .next()
        .ok_or_else(|| format!("invalid item suffix '{sample_suffix}'"))?
        .to_string();

    let mut captured_names = BTreeMap::new();
    for rec in &subject_records {
        let short = rec
            .target
            .def_id
            .rsplit("::")
            .next()
            .unwrap_or(&rec.target.def_id)
            .to_string();
        captured_names.insert(short, *rec);
    }

    let mut present_items = Vec::new();
    let mut outcomes = BTreeMap::new();
    for item in items {
        if captured_names.contains_key(&item.name) {
            present_items.push(item.clone());
        } else {
            outcomes.insert(
                item.name.clone(),
                AnnealOutcome::CaptureOrLeanError(format!(
                    "item '{}' was not found among captured MIR subjects",
                    item.name
                )),
            );
        }
    }

    if present_items.is_empty() {
        return Ok((crate_camel, outcomes));
    }

    let dot_anneal = corpus_root.join(".anneal");
    run_lake_verify_targets(
        &dot_anneal,
        &[
            "Mir".to_string(),
            "Anneal.Rustc.V2026_06_01.SymbolicEval".to_string(),
        ],
    )?;

    let oracle_dir = dot_anneal.join("oracle");
    fs::create_dir_all(&oracle_dir).map_err(|err| {
        format!(
            "failed to create {}: {}",
            oracle_dir.display(),
            err
        )
    })?;
    let probe_path = oracle_dir.join("MiriOracleProbe.lean");
    let probe_src = render_anneal_probe_module(&crate_camel, &present_items);
    fs::write(&probe_path, &probe_src).map_err(|err| {
        format!(
            "failed to write {}: {}",
            probe_path.display(),
            err
        )
    })?;

    let lake_bin = resolve_lake_binary();
    let probe_out = Command::new(&lake_bin)
        .current_dir(&dot_anneal)
        .arg("env")
        .arg("lean")
        .arg("oracle/MiriOracleProbe.lean")
        .output()
        .map_err(|err| {
            format!(
                "failed to execute '{} env lean oracle/MiriOracleProbe.lean': {}",
                lake_bin.display(),
                err
            )
        })?;
    if !probe_out.status.success() {
        let stdout = String::from_utf8_lossy(&probe_out.stdout);
        let stderr = String::from_utf8_lossy(&probe_out.stderr);
        return Err(format!(
            "Lean probe evaluation failed in {} ({}):\n{}\n{}",
            dot_anneal.display(),
            probe_out.status,
            stdout,
            stderr
        ));
    }

    let stdout = String::from_utf8_lossy(&probe_out.stdout);
    let mut parsed = parse_anneal_probe_output(&stdout)?;
    for item in &present_items {
        if let Some(outcome) = parsed.remove(&item.name) {
            outcomes.insert(item.name.clone(), outcome);
        } else {
            outcomes.insert(
                item.name.clone(),
                AnnealOutcome::CaptureOrLeanError(format!(
                    "Lean probe output omitted ANNEAL_PROBE line for '{}'",
                    item.name
                )),
            );
        }
    }

    Ok((crate_camel, outcomes))
}

/// Compile a Lean kernel confirmation module
/// (`.anneal/oracle/MiriOracleConfirm.lean`) verifying each `(item, outcome)`
/// pair by `rfl` in the Lean 4 kernel (`evalMirDiffTagBounded` and
/// `probeMirDiffExecBounded`).
pub fn confirm_anneal_outcomes_in_kernel(
    corpus_root: &Path,
    crate_camel: &str,
    items: &[(OracleItemSpec, AnnealOutcome)],
) -> Result<PathBuf, String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let abs_corpus = normalize_path_against(&base_dir, corpus_root);
    let dot_anneal = abs_corpus.join(".anneal");
    let oracle_dir = dot_anneal.join("oracle");
    fs::create_dir_all(&oracle_dir).map_err(|err| {
        format!(
            "failed to create {}: {}",
            oracle_dir.display(),
            err
        )
    })?;
    let confirm_path = oracle_dir.join("MiriOracleConfirm.lean");
    let confirm_src = render_anneal_confirm_module(crate_camel, items)?;
    fs::write(&confirm_path, &confirm_src).map_err(|err| {
        format!(
            "failed to write {}: {}",
            confirm_path.display(),
            err
        )
    })?;

    let lake_bin = resolve_lake_binary();
    let output = Command::new(&lake_bin)
        .current_dir(&dot_anneal)
        .arg("env")
        .arg("lean")
        .arg("oracle/MiriOracleConfirm.lean")
        .output()
        .map_err(|err| {
            format!(
                "failed to execute '{} env lean oracle/MiriOracleConfirm.lean': {}",
                lake_bin.display(),
                err
            )
        })?;
    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "Lean kernel confirmation failed in {} ({}):\n{}\n{}",
            confirm_path.display(),
            output.status,
            stdout,
            stderr
        ));
    }
    Ok(confirm_path)
}

/// Configuration for the combined Miri + Anneal differential oracle pipeline.
#[derive(Clone, Debug)]
pub struct DifftestOracleConfig {
    /// Root directory of the corpus crate (`Cargo.toml` + `src/lib.rs`).
    pub corpus_root: PathBuf,
    /// Compiler flags used for both Miri `.rlib` compilation and
    /// `anneal-rustc-capture`.
    pub capture_rustflags: Vec<String>,
    /// Flags passed to `miri` (`["-Zmiri-tree-borrows"]` by default).
    pub miri_flags: Vec<String>,
    /// Optional explicit path to the Anneal repository root.
    pub anneal_repo_root: Option<PathBuf>,
    /// Optional explicit path to `anneal-rustc-capture`.
    pub rustc_wrapper: Option<PathBuf>,
    /// Resolved Miri toolchain and sysroot.
    pub toolchain: MiriToolchain,
}

/// Combined per-item oracle report produced by `run_difftest_oracle_pipeline`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemOracleReport {
    /// Item name in the corpus crate.
    pub name: String,
    /// Step fuel bound used for Anneal evaluation.
    pub fuel: u32,
    /// Live Miri oracle outcome.
    pub miri: MiriOutcome,
    /// Live Anneal MIR-in-Lean oracle outcome.
    pub anneal: AnnealOutcome,
    /// Comparison classification (`Agree`, `Diverge`, or `NotCompared`).
    pub verdict: ComparisonVerdict,
    /// Whether this item's Anneal outcome and span were confirmed via a
    /// kernel-checked `by rfl` theorem in `MiriOracleConfirm.lean`.
    pub kernel_confirmed: bool,
}

/// Aggregate report returned by `run_difftest_oracle_pipeline`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DifftestOracleReport {
    /// CamelCase Lean module prefix for the corpus crate.
    pub crate_camel: String,
    /// Per-item oracle outcomes and verdicts in input order.
    pub items: Vec<ItemOracleReport>,
    /// Count of items classified as `ComparisonVerdict::Agree`.
    pub agree_count: usize,
    /// Count of items classified as `ComparisonVerdict::Diverge(_)`.
    pub diverge_count: usize,
    /// Count of items classified as `ComparisonVerdict::NotCompared(_)`.
    pub not_compared_count: usize,
    /// Path to `.anneal/oracle/MiriOracleConfirm.lean` if any divergent items
    /// were kernel-certified.
    pub confirm_module_path: Option<PathBuf>,
}

impl DifftestOracleReport {
    /// Look up the `ItemOracleReport` for `name`.
    pub fn item(&self, name: &str) -> Option<&ItemOracleReport> {
        self.items.iter().find(|i| i.name == name)
    }
}

/// Run both the Miri oracle and the Anneal oracle on `items`, classify every
/// item via `compare_miri_and_anneal`, and kernel-check (`by rfl`) every
/// divergent item's Anneal tag and source span in `MiriOracleConfirm.lean`.
pub fn run_difftest_oracle_pipeline(
    config: &DifftestOracleConfig,
    items: &[OracleItemSpec],
) -> Result<DifftestOracleReport, String> {
    let miri_cfg = MiriOracleConfig {
        corpus_root: config.corpus_root.clone(),
        capture_rustflags: config.capture_rustflags.clone(),
        miri_flags: config.miri_flags.clone(),
        toolchain: config.toolchain.clone(),
    };
    let miri_outcomes = run_miri_oracle(&miri_cfg, items)?;

    let anneal_cfg = AnnealOracleConfig {
        corpus_root: config.corpus_root.clone(),
        capture_rustflags: config.capture_rustflags.clone(),
        anneal_repo_root: config.anneal_repo_root.clone(),
        rustc_wrapper: config.rustc_wrapper.clone(),
    };
    let (crate_camel, anneal_outcomes) = run_anneal_oracle(&anneal_cfg, items)?;

    let mut reports = Vec::with_capacity(items.len());
    let mut to_confirm: Vec<(OracleItemSpec, AnnealOutcome)> = Vec::new();
    let mut agree_count = 0usize;
    let mut diverge_count = 0usize;
    let mut not_compared_count = 0usize;

    for spec in items {
        let miri = miri_outcomes.get(&spec.name).cloned().unwrap_or_else(|| {
            MiriOutcome::OracleError(format!("missing Miri outcome for '{}'", spec.name))
        });
        let anneal = anneal_outcomes
            .get(&spec.name)
            .cloned()
            .unwrap_or_else(|| {
                AnnealOutcome::CaptureOrLeanError(format!(
                    "missing Anneal outcome for '{}'",
                    spec.name
                ))
            });
        let verdict = compare_miri_and_anneal(&miri, &anneal);
        let should_confirm = verdict.is_diverge() && anneal.to_lean_mir_diff_tag().is_some();
        if should_confirm {
            to_confirm.push((spec.clone(), anneal.clone()));
        }
        match &verdict {
            ComparisonVerdict::Agree => agree_count += 1,
            ComparisonVerdict::Diverge(_) => diverge_count += 1,
            ComparisonVerdict::NotCompared(_) => not_compared_count += 1,
        }
        reports.push(ItemOracleReport {
            name: spec.name.clone(),
            fuel: spec.fuel,
            miri,
            anneal,
            verdict,
            kernel_confirmed: should_confirm,
        });
    }

    let confirm_module_path = if to_confirm.is_empty() {
        None
    } else {
        Some(confirm_anneal_outcomes_in_kernel(
            &config.corpus_root,
            &crate_camel,
            &to_confirm,
        )?)
    };

    Ok(DifftestOracleReport {
        crate_camel,
        items: reports,
        agree_count,
        diverge_count,
        not_compared_count,
        confirm_module_path,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_span_parsing_and_containment() {
        let span = SourceSpan::parse_anneal_span("src/lib.rs:597:23: 597:28")
            .expect("parse anneal span");
        assert_eq!(span.file, "src/lib.rs");
        assert_eq!(span.start_line, 597);
        assert_eq!(span.start_col, 23);
        assert_eq!(span.end_line, 597);
        assert_eq!(span.end_col, 28);

        let inside = SourcePos::parse_rustc_pos("/tmp/work/corpus/src/lib.rs:597:23")
            .expect("parse rustc pos");
        let inside_end = SourcePos::parse_rustc_pos("src/lib.rs:597:28").unwrap();
        let wrong_line = SourcePos::parse_rustc_pos("src/lib.rs:598:5").unwrap();
        let wrong_col = SourcePos::parse_rustc_pos("src/lib.rs:597:22").unwrap();
        let wrong_file = SourcePos::parse_rustc_pos("src/other.rs:597:23").unwrap();

        assert!(span.contains_pos(&inside));
        assert!(span.contains_pos(&inside_end));
        assert!(!span.contains_pos(&wrong_line));
        assert!(!span.contains_pos(&wrong_col));
        assert!(!span.contains_pos(&wrong_file));
    }

    #[test]
    fn miri_parser_skips_pre_ub_warnings_and_requires_start_marker() {
        let stderr_with_warning = "\
warning: integer-to-pointer cast
  --> src/lib.rs:435:25
   |
435|     let p: *const u32 = 0usize as *const u32;
   |                         ^^^^^^^^^^^^^^^^^^^^
error: Undefined Behavior: memory access failed: null pointer is a dangling pointer
  --> src/lib.rs:436:14
   |
436|     unsafe { *p }
   |              ^^
";
        let out = parse_miri_process_output(
            "ub_deref_null_ptr_read",
            false,
            "MIRI_START:ub_deref_null_ptr_read\n",
            stderr_with_warning,
        );
        assert_eq!(
            out,
            MiriOutcome::Ub {
                pos: Some(SourcePos {
                    file: "src/lib.rs".to_string(),
                    line: 436,
                    col: 14,
                }),
                message: "memory access failed: null pointer is a dangling pointer".to_string(),
            }
        );

        // Without MIRI_START, even exit 0 or panic must be classified as
        // OracleError.
        let missing_start = parse_miri_process_output(
            "ub_deref_null_ptr_read",
            true,
            "MIRI_PASS:unit\n",
            "",
        );
        assert!(matches!(missing_start, MiriOutcome::OracleError(_)));
    }

    use std::ffi::OsStr;

    // Miri sysroot provisioning tests. None of these tests call
    // `env::set_var`/`env::remove_var`: mutating the process environment races
    // every concurrently running test in this binary that reads `HOME`/`PATH`
    // or spawns an `elan`/`rustup` proxy. Environment inputs are injected
    // through `EnvLookup` maps instead.

    fn env_map(pairs: &[(&str, &OsStr)]) -> impl Fn(&str) -> Option<OsString> + use<> {
        let vars: BTreeMap<String, OsString> = pairs
            .iter()
            .map(|(k, v)| ((*k).to_string(), (*v).to_os_string()))
            .collect();
        move |key: &str| vars.get(key).cloned()
    }

    #[cfg(unix)]
    fn write_executable_script(path: &Path, body: &str) {
        use std::os::unix::fs::PermissionsExt;
        fs::write(path, body).expect("write script");
        let mut perms = fs::metadata(path).expect("script metadata").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).expect("chmod +x script");
    }

    /// Mock `cargo` that records its argv, `MIRI_SYSROOT`, and
    /// `RUSTUP_TOOLCHAIN`, then populates `${MIRI_SYSROOT}/lib/rustlib`.
    #[cfg(unix)]
    const RECORDING_MOCK_CARGO: &str = "#!/bin/sh\n\
        if [ -z \"${MIRI_SYSROOT:-}\" ]; then echo 'MIRI_SYSROOT missing' >&2; exit 1; fi\n\
        printf '%s\\n' \"$*\" > \"${MIRI_SYSROOT}.args\"\n\
        printf '%s\\n' \"${MIRI_SYSROOT}\" > \"${MIRI_SYSROOT}.sysroot\"\n\
        printf '%s\\n' \"${RUSTUP_TOOLCHAIN:-<unset>}\" > \"${MIRI_SYSROOT}.toolchain\"\n\
        if read -r _line; then echo 'stdin must be closed' >&2; exit 1; fi\n\
        mkdir -p \"${MIRI_SYSROOT}/lib/rustlib\"\n";

    #[test]
    fn sysroot_fast_path_skips_setup_when_lib_rustlib_already_exists() {
        let temp = unique_oracle_temp_dir("sysroot-fast-path");
        let sysroot = temp.join(".cache/miri");
        fs::create_dir_all(sysroot.join("lib/rustlib")).expect("create lib/rustlib");

        let mut called = false;
        let resolved = ensure_miri_sysroot_initialized_with(&sysroot, |_| {
            called = true;
            Err("setup_fn must not be invoked when lib/rustlib already exists".to_string())
        })
        .expect("fast path should succeed");
        assert_eq!(resolved, sysroot);
        assert!(!called, "setup_fn must not run when lib/rustlib exists");
        assert!(
            !sysroot.join(".setup.lock").exists(),
            "the fast path must not create or take .setup.lock"
        );

        // The production resolver reaches the same fast path through `HOME`,
        // even with a broken setup binary and invalid setup knobs (none of
        // which may be consulted for an already-populated sysroot).
        let get_env = env_map(&[
            ("HOME", temp.as_os_str()),
            (MIRI_SETUP_BIN_ENV, OsStr::new("/nonexistent/cargo")),
            (MIRI_SETUP_TIMEOUT_ENV, OsStr::new("not-a-number")),
        ]);
        let via_resolve = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect("resolve_sysroot_path fast path");
        assert_eq!(via_resolve, sysroot);

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn sysroot_resolution_order_and_caller_paths_are_never_provisioned() {
        let temp = unique_oracle_temp_dir("sysroot-resolution-order");
        let valid = temp.join("valid-sysroot");
        fs::create_dir_all(valid.join("lib/rustlib")).expect("create valid lib/rustlib");
        let bare = temp.join("bare-sysroot");
        fs::create_dir_all(&bare).expect("create bare sysroot");
        let home = temp.join("home");
        let default_candidate = home.join(".cache/miri");

        let never_provision = |candidate: &Path| -> Result<PathBuf, String> {
            panic!(
                "caller-supplied sysroot must not be provisioned: {}",
                candidate.display()
            )
        };

        // 1. `explicit` wins over `ANNEAL_MIRI_SYSROOT` and `HOME`.
        let env_all = env_map(&[
            ("ANNEAL_MIRI_SYSROOT", bare.as_os_str()),
            ("HOME", home.as_os_str()),
        ]);
        assert_eq!(
            resolve_sysroot_path_with(Some(&valid), &env_all, never_provision),
            Ok(valid.clone())
        );
        let err_explicit = resolve_sysroot_path_with(Some(&bare), &env_all, never_provision)
            .expect_err("explicit path without lib/rustlib must fail immediately");
        assert!(
            err_explicit.contains("explicit Miri sysroot is missing lib/rustlib"),
            "unexpected error: {err_explicit}"
        );

        // 2. `ANNEAL_MIRI_SYSROOT` wins over `HOME` and is never provisioned.
        let env_valid = env_map(&[
            ("ANNEAL_MIRI_SYSROOT", valid.as_os_str()),
            ("HOME", home.as_os_str()),
        ]);
        assert_eq!(
            resolve_sysroot_path_with(None, &env_valid, never_provision),
            Ok(valid.clone())
        );
        let err_env = resolve_sysroot_path_with(None, &env_all, never_provision)
            .expect_err("ANNEAL_MIRI_SYSROOT without lib/rustlib must fail");
        assert!(
            err_env.contains("ANNEAL_MIRI_SYSROOT is missing lib/rustlib"),
            "unexpected error: {err_env}"
        );
        assert!(
            !bare.join(".setup.lock").exists() && !bare.join("lib").exists(),
            "caller-supplied sysroot paths must not be mutated"
        );

        // 3. Blank `ANNEAL_MIRI_SYSROOT` counts as unset: fall back to `HOME`.
        let env_blank = env_map(&[
            ("ANNEAL_MIRI_SYSROOT", OsStr::new("  ")),
            ("HOME", home.as_os_str()),
        ]);
        let mut provisioned = Vec::new();
        let resolved = resolve_sysroot_path_with(None, &env_blank, |candidate| {
            provisioned.push(candidate.to_path_buf());
            Ok(candidate.to_path_buf())
        });
        assert_eq!(resolved, Ok(default_candidate.clone()));
        assert_eq!(provisioned, vec![default_candidate]);

        // 4. Neither `ANNEAL_MIRI_SYSROOT` nor a non-blank `HOME`: hard error.
        for get_env in [env_map(&[]), env_map(&[("HOME", OsStr::new(" "))])] {
            let err = resolve_sysroot_path_with(None, &get_env, never_provision)
                .expect_err("no sysroot location must fail closed");
            assert!(
                err.contains("Miri sysroot not found") && err.contains("hard error"),
                "unexpected error: {err}"
            );
        }

        // 5. The production wrapper reads the real process environment
        // (read-only: no test in this binary mutates it).
        let expected = resolve_sysroot_path_with(None, &process_env_var, |candidate| {
            Ok(candidate.to_path_buf())
        });
        let real_home = env::var("HOME").ok().filter(|h| !h.trim().is_empty());
        let real_override = env::var("ANNEAL_MIRI_SYSROOT")
            .ok()
            .filter(|s| !s.trim().is_empty());
        if real_override.is_none()
            && let Some(real_home) = real_home
        {
            assert_eq!(
                expected,
                Ok(PathBuf::from(real_home.trim()).join(".cache/miri"))
            );
        }

        let _ = fs::remove_dir_all(&temp);
    }

    #[cfg(unix)]
    #[test]
    fn missing_sysroot_auto_provisions_via_miri_setup_and_returns_path() {
        let temp = unique_oracle_temp_dir("sysroot-autoprovision");
        let mock_cargo = temp.join("mock-cargo");
        write_executable_script(&mock_cargo, RECORDING_MOCK_CARGO);

        let expected_sysroot = temp.join(".cache/miri");
        assert!(!expected_sysroot.join("lib/rustlib").exists());

        // Full production plumbing (`resolve_sysroot_path` ->
        // `ensure_miri_sysroot_initialized` -> `run_miri_setup`) with only the
        // environment injected.
        let get_env = env_map(&[
            ("HOME", temp.as_os_str()),
            (MIRI_SETUP_BIN_ENV, mock_cargo.as_os_str()),
        ]);
        let resolved = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect("auto-provision should succeed");
        assert_eq!(resolved, expected_sysroot);

        assert!(expected_sysroot.join("lib/rustlib").is_dir());
        assert!(expected_sysroot.join(".setup.lock").is_file());
        let read_record = |suffix: &str| {
            fs::read_to_string(temp.join(format!(".cache/miri.{suffix}")))
                .unwrap_or_else(|err| panic!("read mock record {suffix}: {err}"))
        };
        assert_eq!(read_record("args").trim(), "+nightly-2026-06-01 miri setup");
        assert_eq!(
            read_record("sysroot").trim(),
            expected_sysroot.to_str().expect("utf-8 temp path")
        );
        // An explicit `ANNEAL_MIRI_SETUP_BIN` is used as given: no toolchain pin
        // is added on top of whatever this process inherited.
        let inherited_toolchain =
            env::var("RUSTUP_TOOLCHAIN").unwrap_or_else(|_| "<unset>".to_string());
        assert_eq!(read_record("toolchain").trim(), inherited_toolchain);

        // Without an override, a pinned `nightly-2026-06-01*` toolchain `cargo`
        // runs directly: no `+toolchain` argument, its `bin/` first on `PATH`,
        // and `RUSTUP_TOOLCHAIN` pinned to the toolchain directory name.
        let home2 = temp.join("home2");
        let toolchain_name = "nightly-2026-06-01-anneal-test";
        let toolchain_bin = home2
            .join(".rustup/toolchains")
            .join(toolchain_name)
            .join("bin");
        fs::create_dir_all(&toolchain_bin).expect("create fake toolchain bin");
        write_executable_script(
            &toolchain_bin.join("cargo"),
            &format!(
                "{RECORDING_MOCK_CARGO}printf '%s\\n' \"${{PATH%%:*}}\" > \"${{MIRI_SYSROOT}}.path0\"\n"
            ),
        );
        write_executable_script(&toolchain_bin.join("cargo-miri"), "#!/bin/sh\nexit 0\n");
        let real_path = env::var_os("PATH").unwrap_or_default();
        let get_env2 = env_map(&[("HOME", home2.as_os_str()), ("PATH", real_path.as_os_str())]);
        let sysroot2 = home2.join(".cache/miri");
        let resolved2 = resolve_sysroot_path_with(None, &get_env2, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env2)
        })
        .expect("auto-provision through the pinned toolchain cargo should succeed");
        assert_eq!(resolved2, sysroot2);
        let read_record2 = |suffix: &str| {
            fs::read_to_string(home2.join(format!(".cache/miri.{suffix}")))
                .unwrap_or_else(|err| panic!("read mock record {suffix}: {err}"))
        };
        assert_eq!(read_record2("args").trim(), "miri setup");
        assert_eq!(read_record2("toolchain").trim(), toolchain_name);
        assert_eq!(
            read_record2("path0").trim(),
            toolchain_bin.to_str().expect("utf-8 temp path")
        );
        assert!(sysroot2.join("lib/rustlib").is_dir());

        let _ = fs::remove_dir_all(&temp);
    }

    #[cfg(unix)]
    #[test]
    fn missing_sysroot_fails_closed_when_miri_setup_fails_or_leaves_rustlib_absent() {
        let temp = unique_oracle_temp_dir("sysroot-fail-closed");

        // Case 1: `miri setup` exits non-zero.
        let failing_cargo = temp.join("mock-failing-cargo");
        write_executable_script(
            &failing_cargo,
            "#!/bin/sh\necho 'partial setup progress'\necho 'simulated rust-src missing error' >&2\nexit 17\n",
        );
        let home_fail = temp.join("home-fail");
        let get_env = env_map(&[
            ("HOME", home_fail.as_os_str()),
            (MIRI_SETUP_BIN_ENV, failing_cargo.as_os_str()),
        ]);
        let err = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect_err("non-zero miri setup must fail closed");
        assert!(
            err.contains("Miri sysroot auto-provisioning failed")
                && err.contains("exit status: 17")
                && err.contains("partial setup progress")
                && err.contains("simulated rust-src missing error")
                && err.contains("missing Miri sysroot is a hard error"),
            "unexpected error: {err}"
        );
        assert!(!home_fail.join(".cache/miri/lib/rustlib").exists());

        // Case 2: `miri setup` exits 0 without populating `lib/rustlib`.
        let lying_cargo = temp.join("mock-lying-cargo");
        write_executable_script(&lying_cargo, "#!/bin/sh\nexit 0\n");
        let home_lie = temp.join("home-lie");
        let get_env = env_map(&[
            ("HOME", home_lie.as_os_str()),
            (MIRI_SETUP_BIN_ENV, lying_cargo.as_os_str()),
        ]);
        let err = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect_err("setup leaving lib/rustlib absent must fail closed");
        assert!(
            err.contains("lib/rustlib is still missing")
                && err.contains("missing Miri sysroot is a hard error"),
            "unexpected error: {err}"
        );

        // Case 3: a configured setup binary that does not exist.
        let home_missing = temp.join("home-missing-bin");
        let get_env = env_map(&[
            ("HOME", home_missing.as_os_str()),
            (MIRI_SETUP_BIN_ENV, OsStr::new("/nonexistent/anneal/cargo")),
        ]);
        let err = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect_err("missing setup binary must fail closed");
        assert!(
            err.contains("ANNEAL_MIRI_SETUP_BIN points to non-existent binary"),
            "unexpected error: {err}"
        );

        // Case 4: generic `setup_fn` contract.
        let empty_sysroot = temp.join("empty-after-setup");
        let err = ensure_miri_sysroot_initialized_with(&empty_sysroot, |_dir| Ok(()))
            .expect_err("setup leaving lib/rustlib absent must fail closed");
        assert!(
            err.contains("lib/rustlib is still missing"),
            "unexpected error: {err}"
        );

        let _ = fs::remove_dir_all(&temp);
    }

    /// Whether `pid` still names a live (not yet killed) process whose command
    /// name is `comm`.
    ///
    /// A SIGKILLed orphan is reparented and reaped asynchronously by PID 1 or a
    /// subreaper, so until then it is a zombie that still answers `kill -0`
    /// (and where PID 1 never reaps, it answers forever). Zombies therefore
    /// count as dead, and a recycled PID running something else is not "alive".
    #[cfg(unix)]
    fn process_is_live(pid: &str, comm: &str) -> bool {
        #[cfg(target_os = "linux")]
        {
            let Ok(stat) = fs::read_to_string(format!("/proc/{pid}/stat")) else {
                return false;
            };
            // `<pid> (<comm>) <state> ...`; `comm` may itself contain spaces or `)`.
            let (Some(open), Some(close)) = (stat.find('('), stat.rfind(')')) else {
                return false;
            };
            let state = stat[close + 1..].split_whitespace().next().unwrap_or("");
            !matches!(state, "Z" | "X" | "x") && &stat[open + 1..close] == comm
        }
        #[cfg(not(target_os = "linux"))]
        {
            let _ = comm;
            Command::new("kill")
                .args(["-s", "0", pid])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .is_ok_and(|s| s.success())
        }
    }

    #[cfg(unix)]
    #[test]
    fn hung_miri_setup_is_killed_at_the_timeout_and_fails_closed() {
        let temp = unique_oracle_temp_dir("sysroot-setup-timeout");
        let hung_cargo = temp.join("mock-hung-cargo");
        let grandchild_pid_file = temp.join("grandchild.pid");
        // Spawn a non-`exec` child sleeper (modeling `cargo` -> `cargo-miri` ->
        // `rustc`) to verify that process-group termination kills descendants
        // and closes stdout/stderr pipes immediately without a grace stall.
        write_executable_script(
            &hung_cargo,
            &format!(
                "#!/bin/sh\necho 'compiling core...' >&2\nsleep 60 &\nprintf '%s\\n' \"$!\" > \"{}\"\nwait\n",
                grandchild_pid_file.display()
            ),
        );
        let home = temp.join("home");
        // 2s (not 1s) so the mock has recorded its grandchild before the kill
        // even on a heavily loaded machine; the slack below stays 4s.
        let get_env = env_map(&[
            ("HOME", home.as_os_str()),
            (MIRI_SETUP_BIN_ENV, hung_cargo.as_os_str()),
            (MIRI_SETUP_TIMEOUT_ENV, OsStr::new("2")),
        ]);
        let started = Instant::now();
        let err = resolve_sysroot_path_with(None, &get_env, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env)
        })
        .expect_err("a hung miri setup must fail closed");
        let elapsed = started.elapsed();
        assert!(
            elapsed < Duration::from_secs(6),
            "process-group kill must terminate hung setup and grandchildren without pipe-drain stall, took {elapsed:?}"
        );
        let grandchild_pid = fs::read_to_string(&grandchild_pid_file)
            .expect("grandchild pid recorded")
            .trim()
            .to_string();
        // Reaping the killed (reparented) grandchild is asynchronous: allow it
        // a moment to leave the run queue, but a survivor of the timeout would
        // keep sleeping for a minute and fail this.
        let deadline = Instant::now() + Duration::from_secs(5);
        while process_is_live(&grandchild_pid, "sleep") && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(20));
        }
        assert!(
            !process_is_live(&grandchild_pid, "sleep"),
            "grandchild process {grandchild_pid} must be killed when miri setup times out"
        );
        assert!(
            err.contains("timed out after 2s")
                && err.contains("compiling core...")
                && err.contains(MIRI_SETUP_TIMEOUT_ENV)
                && err.contains("missing Miri sysroot is a hard error"),
            "unexpected error: {err}"
        );
        assert!(!home.join(".cache/miri/lib/rustlib").exists());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn miri_setup_timeouts_are_validated_and_defaulted() {
        let default = Duration::from_secs(DEFAULT_MIRI_SETUP_TIMEOUT_SECS);
        assert_eq!(miri_setup_timeout(&env_map(&[])), Ok(default));
        assert_eq!(
            miri_setup_lock_wait(&env_map(&[]), default),
            Ok(default + Duration::from_secs(60))
        );
        assert_eq!(
            miri_setup_timeout(&env_map(&[(MIRI_SETUP_TIMEOUT_ENV, OsStr::new(" 42 "))])),
            Ok(Duration::from_secs(42))
        );
        assert_eq!(
            miri_setup_timeout(&env_map(&[(
                MIRI_SETUP_TIMEOUT_ENV,
                OsStr::new("0000000042")
            )])),
            Ok(Duration::from_secs(42))
        );
        assert_eq!(
            miri_setup_lock_wait(
                &env_map(&[(MIRI_SETUP_LOCK_TIMEOUT_ENV, OsStr::new("7"))]),
                default
            ),
            Ok(Duration::from_secs(7))
        );
        for blank in ["", "  "] {
            assert_eq!(
                miri_setup_timeout(&env_map(&[(MIRI_SETUP_TIMEOUT_ENV, OsStr::new(blank))])),
                Ok(default)
            );
        }
        // The documented maximum is accepted for both knobs, and only an explicit
        // lock timeout is capped: the derived default may exceed the cap by 60s
        // (the staged launcher derives and validates the same way).
        let max = Duration::from_secs(MAX_MIRI_SETUP_TIMEOUT_SECS);
        assert_eq!(MAX_MIRI_SETUP_TIMEOUT_SECS, 31_536_000);
        assert_eq!(
            miri_setup_timeout(&env_map(&[(
                MIRI_SETUP_TIMEOUT_ENV,
                OsStr::new("31536000")
            )])),
            Ok(max)
        );
        assert_eq!(
            miri_setup_lock_wait(&env_map(&[]), max),
            Ok(max + Duration::from_secs(60))
        );
        assert_eq!(
            miri_setup_lock_wait(
                &env_map(&[(MIRI_SETUP_LOCK_TIMEOUT_ENV, OsStr::new("31536000"))]),
                default
            ),
            Ok(max)
        );
        for bad in [
            "0",
            "-5",
            "abc",
            "1.5",
            "31536001",
            "9223372036854775807",
            "18446744073709551615",
            "18446744073709551616",
        ] {
            let err = miri_setup_timeout(&env_map(&[(MIRI_SETUP_TIMEOUT_ENV, OsStr::new(bad))]))
                .expect_err("invalid timeout must be rejected");
            assert!(
                err.contains(MIRI_SETUP_TIMEOUT_ENV) && err.contains("positive whole number"),
                "unexpected error for {bad:?}: {err}"
            );
            assert!(
                miri_setup_lock_wait(
                    &env_map(&[(MIRI_SETUP_LOCK_TIMEOUT_ENV, OsStr::new(bad))]),
                    default
                )
                .is_err()
            );
        }
    }

    #[test]
    fn miri_setup_cargo_prefers_pinned_toolchain_and_pins_rustup_toolchain() {
        let temp = unique_oracle_temp_dir("sysroot-setup-cargo-resolution");
        let home = temp.join("home");

        // Only a `rustup` proxy: pass `+nightly-2026-06-01`, no PATH/toolchain pin.
        let proxy = home.join(".cargo/bin/cargo");
        fs::create_dir_all(proxy.parent().expect("proxy dir")).expect("create proxy dir");
        fs::write(&proxy, b"").expect("write proxy");
        let no_bin = temp.join("no-bin");
        let get_env = env_map(&[("HOME", home.as_os_str()), ("PATH", no_bin.as_os_str())]);
        assert_eq!(
            resolve_miri_setup_cargo(&get_env),
            Ok(MiriSetupCommand {
                cargo_bin: proxy.clone(),
                pass_toolchain_arg: true,
                prepend_path_dir: None,
                rustup_toolchain: None,
            })
        );

        // A pinned toolchain with `cargo-miri` wins and pins `RUSTUP_TOOLCHAIN`
        // (toolchains without `cargo-miri` are skipped).
        let toolchains = home.join(".rustup/toolchains");
        let no_miri = toolchains.join("nightly-2026-06-01-aarch64-unknown-linux-gnu/bin");
        fs::create_dir_all(&no_miri).expect("create toolchain without miri");
        fs::write(no_miri.join("cargo"), b"").expect("write cargo");
        let pinned_name = "nightly-2026-06-01-x86_64-unknown-linux-gnu";
        let pinned = toolchains.join(pinned_name).join("bin");
        fs::create_dir_all(&pinned).expect("create pinned toolchain");
        fs::write(pinned.join("cargo"), b"").expect("write cargo");
        fs::write(pinned.join("cargo-miri"), b"").expect("write cargo-miri");
        let other = toolchains.join("nightly-2026-07-01-x86_64-unknown-linux-gnu/bin");
        fs::create_dir_all(&other).expect("create other toolchain");
        fs::write(other.join("cargo"), b"").expect("write cargo");
        fs::write(other.join("cargo-miri"), b"").expect("write cargo-miri");
        assert_eq!(
            resolve_miri_setup_cargo(&get_env),
            Ok(MiriSetupCommand {
                cargo_bin: pinned.join("cargo"),
                pass_toolchain_arg: false,
                prepend_path_dir: Some(pinned.clone()),
                rustup_toolchain: Some(pinned_name.to_string()),
            })
        );

        // `RUSTUP_HOME` takes precedence over `${HOME}/.rustup`.
        let empty_rustup_home = temp.join("empty-rustup-home");
        fs::create_dir_all(empty_rustup_home.join("toolchains")).expect("create rustup home");
        let get_env_rustup_home = env_map(&[
            ("HOME", home.as_os_str()),
            ("RUSTUP_HOME", empty_rustup_home.as_os_str()),
            ("PATH", no_bin.as_os_str()),
        ]);
        assert_eq!(
            resolve_miri_setup_cargo(&get_env_rustup_home).map(|c| c.cargo_bin),
            Ok(proxy)
        );

        // No cargo anywhere: fail closed.
        let get_env_none = env_map(&[
            ("HOME", temp.join("empty-home").as_os_str()),
            ("PATH", no_bin.as_os_str()),
        ]);
        let err = resolve_miri_setup_cargo(&get_env_none).expect_err("no cargo must fail");
        assert!(
            err.contains("could not locate 'cargo'"),
            "unexpected error: {err}"
        );

        let _ = fs::remove_dir_all(&temp);
    }

    #[cfg(unix)]
    #[test]
    fn miri_setup_bin_bare_names_resolve_on_path_like_the_launcher() {
        let temp = unique_oracle_temp_dir("sysroot-setup-bin-bare-name");
        let bin_dir = temp.join("bin");
        let empty_dir = temp.join("empty-bin");
        fs::create_dir_all(&bin_dir).expect("create bin dir");
        fs::create_dir_all(&empty_dir).expect("create empty bin dir");
        write_executable_script(&bin_dir.join("anneal-test-cargo"), RECORDING_MOCK_CARGO);

        // A bare name (padding trimmed) resolves to the executable on PATH, and
        // the resolved absolute path is what gets spawned.
        let get_env = env_map(&[
            ("PATH", bin_dir.as_os_str()),
            (MIRI_SETUP_BIN_ENV, OsStr::new(" anneal-test-cargo ")),
        ]);
        assert_eq!(
            resolve_miri_setup_cargo(&get_env),
            Ok(MiriSetupCommand {
                cargo_bin: bin_dir.join("anneal-test-cargo"),
                pass_toolchain_arg: true,
                prepend_path_dir: None,
                rustup_toolchain: None,
            })
        );

        // `ANNEAL_CALLER_PATH` wins over `PATH`, as for every lookup here.
        let get_env_caller = env_map(&[
            ("ANNEAL_CALLER_PATH", empty_dir.as_os_str()),
            ("PATH", bin_dir.as_os_str()),
            (MIRI_SETUP_BIN_ENV, OsStr::new("anneal-test-cargo")),
        ]);
        let err = resolve_miri_setup_cargo(&get_env_caller)
            .expect_err("ANNEAL_CALLER_PATH without the command must not fall back to PATH");
        assert!(
            err.contains("`anneal-test-cargo` was not found on PATH"),
            "unexpected error: {err}"
        );

        // A path (with a separator) must exist.
        let missing = bin_dir.join("missing-cargo");
        let get_env_path = env_map(&[(MIRI_SETUP_BIN_ENV, missing.as_os_str())]);
        let err = resolve_miri_setup_cargo(&get_env_path).expect_err("missing path must fail");
        assert!(
            err.contains("ANNEAL_MIRI_SETUP_BIN points to non-existent binary"),
            "unexpected error: {err}"
        );

        // End to end: the bare name provisions through the production path.
        let home = temp.join("home");
        let get_env_e2e = env_map(&[
            ("HOME", home.as_os_str()),
            ("PATH", bin_dir.as_os_str()),
            (MIRI_SETUP_BIN_ENV, OsStr::new("anneal-test-cargo")),
        ]);
        let resolved = resolve_sysroot_path_with(None, &get_env_e2e, |candidate| {
            ensure_miri_sysroot_initialized_from_env(candidate, &get_env_e2e)
        })
        .expect("bare-name setup binary provisions the sysroot");
        assert_eq!(resolved, home.join(".cache/miri"));
        assert!(resolved.join("lib/rustlib").is_dir());
        assert_eq!(
            fs::read_to_string(home.join(".cache/miri.args"))
                .expect("read mock args")
                .trim(),
            "+nightly-2026-06-01 miri setup"
        );

        let _ = fs::remove_dir_all(&temp);
    }

    #[cfg(unix)]
    #[test]
    fn resolve_tool_path_honors_bare_names_rustup_home_and_cargo_home() {
        let temp = unique_oracle_temp_dir("resolve-tool-path-parity");
        let bin_dir = temp.join("bin");
        fs::create_dir_all(&bin_dir).expect("create bin dir");
        write_executable_script(&bin_dir.join("custom-rustc"), "#!/bin/sh\nexit 0\n");

        // Bare `ANNEAL_RUSTC_BIN` resolves on `PATH` (rather than checking `./custom-rustc` in cwd).
        let get_env = env_map(&[
            ("PATH", bin_dir.as_os_str()),
            ("ANNEAL_RUSTC_BIN", OsStr::new(" custom-rustc ")),
        ]);
        assert_eq!(
            resolve_tool_path_with(None, &get_env, "ANNEAL_RUSTC_BIN", "rustc"),
            Ok(bin_dir.join("custom-rustc"))
        );

        // `CARGO_HOME/bin/miri` proxy is skipped in favor of `RUSTUP_HOME` toolchain `miri`.
        let cargo_home = temp.join("custom-cargo-home");
        let cargo_bin = cargo_home.join("bin");
        fs::create_dir_all(&cargo_bin).expect("create cargo_home/bin");
        write_executable_script(&cargo_bin.join("miri"), "#!/bin/sh\nexit 0\n");
        let rustup_home = temp.join("custom-rustup-home");
        let tc_bin = rustup_home
            .join("toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin");
        fs::create_dir_all(&tc_bin).expect("create rustup_home toolchain bin");
        write_executable_script(&tc_bin.join("miri"), "#!/bin/sh\nexit 0\n");
        write_executable_script(&tc_bin.join("rustc"), "#!/bin/sh\nexit 0\n");
        let get_env_homes = env_map(&[
            ("PATH", cargo_bin.as_os_str()),
            ("CARGO_HOME", cargo_home.as_os_str()),
            ("RUSTUP_HOME", rustup_home.as_os_str()),
        ]);
        assert_eq!(
            resolve_tool_path_with(None, &get_env_homes, "ANNEAL_MIRI_BIN", "miri"),
            Ok(tc_bin.join("miri"))
        );
        assert_eq!(
            resolve_tool_path_with(None, &get_env_homes, "ANNEAL_RUSTC_BIN", "rustc"),
            Ok(tc_bin.join("rustc"))
        );

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn resolved_toolchain_paths_are_absolute_so_corpus_root_children_use_the_validated_files() {
        // Unit tests run with the package root as the working directory.
        let cwd = env::current_dir().expect("current dir");
        assert!(
            cwd.join("Cargo.toml").is_file(),
            "expected to run from the cargo-anneal package root, got {}",
            cwd.display()
        );
        let temp = unique_oracle_temp_dir("toolchain-absolute-paths");
        let sysroot = temp.join("sysroot");
        fs::create_dir_all(sysroot.join("lib/rustlib")).expect("create lib/rustlib");
        let never_provision = |candidate: &Path| -> Result<PathBuf, String> {
            panic!(
                "an explicit sysroot must not be provisioned: {}",
                candidate.display()
            )
        };

        // Relative explicit tool paths (validated against the cwd) come back
        // anchored to the cwd, never as a bare/relative program name that a
        // `current_dir(corpus_root)` spawn would resolve elsewhere.
        let toolchain = MiriToolchain::resolve_with(
            Some(Path::new("Cargo.toml")),
            Some(Path::new("./Cargo.toml")),
            Some(&sysroot),
            &env_map(&[]),
            never_provision,
        )
        .expect("resolve toolchain from explicit paths");
        assert_eq!(toolchain.rustc_bin, cwd.join("Cargo.toml"));
        assert!(
            toolchain.miri_bin.is_absolute(),
            "{}",
            toolchain.miri_bin.display()
        );
        assert_eq!(
            fs::canonicalize(&toolchain.miri_bin).expect("canonicalize miri_bin"),
            fs::canonicalize(cwd.join("Cargo.toml")).expect("canonicalize Cargo.toml")
        );
        assert_eq!(toolchain.miri_sysroot, sysroot);

        // A relative env override with a separator is anchored the same way.
        let get_env = env_map(&[("ANNEAL_MIRI_RUSTC", OsStr::new("src/../Cargo.toml"))]);
        let rustc = resolve_tool_path_with(None, &get_env, "ANNEAL_MIRI_RUSTC", "rustc")
            .expect("relative ANNEAL_MIRI_RUSTC resolves");
        assert_eq!(rustc, cwd.join("src/../Cargo.toml"));

        // `resolve_miri_setup_cargo` also absolutizes relative `ANNEAL_MIRI_SETUP_BIN`
        // overrides and names the absolute path on failure.
        let get_setup_env = env_map(&[(MIRI_SETUP_BIN_ENV, OsStr::new("src/../Cargo.toml"))]);
        let setup_cmd =
            resolve_miri_setup_cargo(&get_setup_env).expect("relative ANNEAL_MIRI_SETUP_BIN");
        assert_eq!(setup_cmd.cargo_bin, cwd.join("src/../Cargo.toml"));
        let err = resolve_miri_setup_cargo(&env_map(&[(
            MIRI_SETUP_BIN_ENV,
            OsStr::new("src/../no-such-setup-cargo"),
        )]))
        .expect_err("missing relative ANNEAL_MIRI_SETUP_BIN must fail closed");
        assert!(
            err.contains(&cwd.join("src/../no-such-setup-cargo").display().to_string()),
            "unexpected error: {err}"
        );

        // Diagnostics name the absolute location that was actually checked.
        let err = resolve_sysroot_path_with(
            None,
            &env_map(&[(
                "ANNEAL_MIRI_SYSROOT",
                OsStr::new("no-such-relative-sysroot"),
            )]),
            never_provision,
        )
        .expect_err("missing relative sysroot must fail closed");
        let expected = cwd.join("no-such-relative-sysroot");
        assert!(
            err.contains(&expected.display().to_string()),
            "error must name {}: {err}",
            expected.display()
        );
        let err = resolve_sysroot_path_with(
            Some(Path::new("no-such-explicit-sysroot")),
            &env_map(&[]),
            never_provision,
        )
        .expect_err("missing explicit sysroot must fail closed");
        assert!(
            err.contains(&cwd.join("no-such-explicit-sysroot").display().to_string()),
            "unexpected error: {err}"
        );
        assert!(!cwd.join("no-such-relative-sysroot").exists());
        assert!(!cwd.join("no-such-explicit-sysroot").exists());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn unopenable_setup_lock_fails_closed_without_running_setup() {
        // Parity with the staged launcher's exit-74 path: a `.setup.lock` that
        // cannot be opened (here: a directory) is a hard error, never an
        // unlocked setup.
        let temp = unique_oracle_temp_dir("sysroot-lock-unopenable");
        let sysroot = temp.join(".cache/miri");
        fs::create_dir_all(sysroot.join(".setup.lock")).expect("create .setup.lock as a dir");
        let mut called = false;
        let err = ensure_miri_sysroot_initialized_with(&sysroot, |_| {
            called = true;
            Ok(())
        })
        .expect_err("an unopenable .setup.lock must fail closed");
        assert!(!called, "setup must never run without the lock");
        assert!(
            err.contains("failed to open Miri sysroot lock file")
                && err.contains(".setup.lock"),
            "unexpected error: {err}"
        );
        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn lock_wait_is_bounded_when_another_holder_never_releases() {
        let temp = unique_oracle_temp_dir("sysroot-lock-wait");
        let sysroot = temp.join(".cache/miri");
        fs::create_dir_all(&sysroot).expect("create sysroot dir");
        let holder = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(sysroot.join(".setup.lock"))
            .expect("open lock as foreign holder");
        holder.lock().expect("foreign holder takes the lock");

        let mut called = false;
        let err =
            ensure_miri_sysroot_initialized_bounded(&sysroot, Duration::from_millis(300), |_| {
                called = true;
                Ok(())
            })
            .expect_err("a never-released lock must fail closed after the bounded wait");
        assert!(!called, "setup must never run without the lock");
        assert!(
            err.contains("waiting for the Miri sysroot setup lock")
                && err.contains("missing Miri sysroot is a hard error"),
            "unexpected error: {err}"
        );

        holder.unlock().expect("release foreign lock");
        let resolved =
            ensure_miri_sysroot_initialized_bounded(&sysroot, Duration::from_secs(5), |dir| {
                fs::create_dir_all(dir.join("lib/rustlib")).map_err(|e| e.to_string())
            })
            .expect("provisioning proceeds once the lock is released");
        assert_eq!(resolved, sysroot);

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn concurrent_callers_serialize_on_setup_lock_and_provision_once() {
        use std::sync::{
            Arc, Barrier,
            atomic::{AtomicUsize, Ordering},
        };
        use std::thread;

        let temp = unique_oracle_temp_dir("sysroot-concurrent-lock");
        let sysroot = Arc::new(temp.join(".cache/miri"));
        let barrier = Arc::new(Barrier::new(4));
        let setup_runs = Arc::new(AtomicUsize::new(0));
        let active_in_setup = Arc::new(AtomicUsize::new(0));
        let max_concurrent_in_setup = Arc::new(AtomicUsize::new(0));

        let mut handles = Vec::new();
        for _ in 0..4 {
            let sysroot = Arc::clone(&sysroot);
            let barrier = Arc::clone(&barrier);
            let setup_runs = Arc::clone(&setup_runs);
            let active_in_setup = Arc::clone(&active_in_setup);
            let max_concurrent_in_setup = Arc::clone(&max_concurrent_in_setup);
            handles.push(thread::spawn(move || {
                barrier.wait();
                ensure_miri_sysroot_initialized_with(&sysroot, |dir| {
                    let cur = active_in_setup.fetch_add(1, Ordering::SeqCst) + 1;
                    max_concurrent_in_setup.fetch_max(cur, Ordering::SeqCst);
                    setup_runs.fetch_add(1, Ordering::SeqCst);
                    thread::sleep(Duration::from_millis(40));
                    fs::create_dir_all(dir.join("lib/rustlib"))
                        .map_err(|e| format!("create lib/rustlib: {e}"))?;
                    active_in_setup.fetch_sub(1, Ordering::SeqCst);
                    Ok(())
                })
            }));
        }

        for h in handles {
            let path = h
                .join()
                .expect("join thread")
                .expect("concurrent sysroot init");
            assert_eq!(path, *sysroot);
        }

        assert_eq!(
            setup_runs.load(Ordering::SeqCst),
            1,
            "second and subsequent callers must see lib/rustlib after acquiring .setup.lock"
        );
        assert_eq!(
            max_concurrent_in_setup.load(Ordering::SeqCst),
            1,
            "advisory lock must serialize setup_fn execution"
        );
        assert!(sysroot.join(".setup.lock").is_file());
        assert!(sysroot.join("lib/rustlib").is_dir());

        let _ = fs::remove_dir_all(&temp);
    }

    /// Live end-to-end check of the production provisioning path against the
    /// real pinned toolchain: resolves `cargo` exactly as the oracle does and
    /// runs `cargo miri setup` into a fresh directory (never `~/.cache/miri`).
    /// Run it with
    /// `cargo test -p cargo-anneal --lib -- --ignored live_miri_setup`.
    #[test]
    #[ignore = "builds a real Miri sysroot with the pinned nightly-2026-06-01 toolchain (minutes)"]
    fn live_miri_setup_provisions_a_fresh_sysroot_through_the_production_path() {
        let temp = unique_oracle_temp_dir("sysroot-live-setup");
        let candidate = temp.join("miri-sysroot");
        let resolved = ensure_miri_sysroot_initialized_from_env(&candidate, &process_env_var)
            .unwrap_or_else(|err| panic!("live miri setup failed: {err}"));
        assert_eq!(resolved, candidate);
        assert!(candidate.join(".setup.lock").is_file());
        let mut rlibs = Vec::new();
        for target in fs::read_dir(candidate.join("lib/rustlib")).expect("read lib/rustlib") {
            let lib_dir = target.expect("target dir entry").path().join("lib");
            if let Ok(entries) = fs::read_dir(&lib_dir) {
                rlibs.extend(
                    entries
                        .filter_map(|e| e.ok())
                        .filter_map(|e| e.file_name().into_string().ok())
                        .filter(|name| name.ends_with(".rlib")),
                );
            }
        }
        for krate in ["core", "alloc", "std"] {
            assert!(
                rlibs
                    .iter()
                    .any(|name| name.starts_with(&format!("lib{krate}-"))),
                "live sysroot is missing lib{krate}-*.rlib: {rlibs:?}"
            );
        }
        let _ = fs::remove_dir_all(&temp);
    }

    /// R4 regression guard: `cargo-anneal` unit tests share one process, so a
    /// test that mutates the process environment or working directory races
    /// every test that reads it (relative-path validation and `absolutize`
    /// both depend on a stable cwd). Inject configuration instead (see
    /// `EnvLookup`) and pass `Command::current_dir` to children.
    #[test]
    fn cargo_anneal_sources_never_mutate_the_process_environment() {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let forbidden = [
            concat!("set", "_var("),
            concat!("remove", "_var("),
            concat!("set_current", "_dir("),
        ];
        let mut stack = vec![manifest_dir.join("src"), manifest_dir.join("tests")];
        let mut offenders = Vec::new();
        while let Some(dir) = stack.pop() {
            for entry in fs::read_dir(&dir).expect("read src dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "rs") {
                    let text = fs::read_to_string(&path).expect("read source");
                    for (lineno, line) in text.lines().enumerate() {
                        if forbidden.iter().any(|needle| line.contains(needle)) {
                            offenders.push(format!(
                                "{}:{}: {}",
                                path.display(),
                                lineno + 1,
                                line.trim()
                            ));
                        }
                    }
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "process-environment mutation in cargo-anneal sources:\n{}",
            offenders.join("\n")
        );
    }

    #[test]
    fn miri_oracle_commands_strip_anneal_capture_env_vars() {
        let cfg = MiriOracleConfig {
            corpus_root: PathBuf::from("/tmp/corpus"),
            capture_rustflags: vec!["-Zmir-opt-level=0".to_string()],
            miri_flags: vec!["-Zmiri-tree-borrows".to_string()],
            toolchain: MiriToolchain {
                rustc_bin: PathBuf::from("/usr/bin/rustc"),
                miri_bin: PathBuf::from("/usr/bin/miri"),
                miri_sysroot: PathBuf::from("/tmp/miri-sysroot"),
            },
        };
        let compile_cmd = build_miri_rlib_compile_command(
            &cfg,
            Path::new("/tmp/corpus"),
            "miri_diff_corpus",
            Path::new("/tmp/scratch/libmiri_diff_corpus.rlib"),
        );
        let miri_cmd = build_miri_item_command(
            &cfg,
            Path::new("/tmp/corpus"),
            "miri_diff_corpus",
            Path::new("/tmp/scratch/miri_driver.rs"),
            Path::new("/tmp/scratch/libmiri_diff_corpus.rlib"),
            "cand_item",
        );
        for (label, cmd) in [("compile_cmd", &compile_cmd), ("miri_cmd", &miri_cmd)] {
            let envs: BTreeMap<&OsStr, Option<&OsStr>> = cmd.get_envs().collect();
            for removed in [ANNEAL_CAPTURE_DIR_ENV, ANNEAL_CAPTURE_FILTER_ENV] {
                assert_eq!(
                    envs.get(OsStr::new(removed)),
                    Some(&None),
                    "{label} must explicitly remove {removed}"
                );
            }
        }

        // `cargo miri setup` builds the Miri sysroot through Cargo, so it also
        // drops the rustc wrappers; the setup-specific variables stay set.
        let setup = MiriSetupCommand {
            cargo_bin: PathBuf::from("/usr/bin/cargo"),
            pass_toolchain_arg: false,
            prepend_path_dir: Some(PathBuf::from("/opt/toolchain/bin")),
            rustup_toolchain: Some("nightly-2026-06-01".to_string()),
        };
        let get_env = env_map(&[("PATH", OsStr::new("/usr/bin"))]);
        let setup_cmd = build_miri_setup_command(&setup, Path::new("/tmp/miri-sysroot"), &get_env);
        let envs: BTreeMap<&OsStr, Option<&OsStr>> = setup_cmd.get_envs().collect();
        for removed in [
            ANNEAL_CAPTURE_DIR_ENV,
            ANNEAL_CAPTURE_FILTER_ENV,
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
        ] {
            assert_eq!(
                envs.get(OsStr::new(removed)),
                Some(&None),
                "setup_cmd must explicitly remove {removed}"
            );
        }
        for (key, value) in [
            ("MIRI_SYSROOT", "/tmp/miri-sysroot"),
            ("RUSTUP_TOOLCHAIN", "nightly-2026-06-01"),
            ("PATH", "/opt/toolchain/bin:/usr/bin"),
        ] {
            assert_eq!(
                envs.get(OsStr::new(key)),
                Some(&Some(OsStr::new(value))),
                "setup_cmd must set {key}"
            );
        }
    }
}
