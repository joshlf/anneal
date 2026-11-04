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
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

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
    /// Returns an `Err` if any component is missing.
    pub fn resolve(
        explicit_rustc: Option<&Path>,
        explicit_miri: Option<&Path>,
        explicit_sysroot: Option<&Path>,
    ) -> Result<Self, String> {
        let rustc_bin = resolve_tool_path(
            explicit_rustc,
            "ANNEAL_MIRI_RUSTC",
            "rustc",
        )?;
        let miri_bin = resolve_tool_path(
            explicit_miri,
            "ANNEAL_MIRI_BIN",
            "miri",
        )?;
        let miri_sysroot = resolve_sysroot_path(explicit_sysroot)?;
        Ok(Self {
            rustc_bin,
            miri_bin,
            miri_sysroot,
        })
    }
}

fn find_executable_in_path(tool_name: &str) -> Option<PathBuf> {
    let path_var = env::var_os("ANNEAL_CALLER_PATH").or_else(|| env::var_os("PATH"))?;
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

fn resolve_tool_path(
    explicit: Option<&Path>,
    env_var: &str,
    tool_name: &str,
) -> Result<PathBuf, String> {
    if let Some(path) = explicit {
        if path.is_file() {
            return Ok(path.to_path_buf());
        }
        return Err(format!(
            "explicit {tool_name} binary does not exist: {}",
            path.display()
        ));
    }
    if let Ok(val) = env::var(env_var)
        && !val.trim().is_empty()
    {
        let p = PathBuf::from(val.trim());
        if p.is_file() {
            return Ok(p);
        }
        return Err(format!(
            "{env_var} points to non-existent {tool_name} binary: {}",
            p.display()
        ));
    }
    if tool_name == "miri" {
        if let Some(path_miri) = find_executable_in_path("miri") {
            let is_cargo_proxy = env::var("HOME")
                .ok()
                .map(|h| PathBuf::from(h).join(".cargo/bin/miri"))
                .is_some_and(|p| p == path_miri);
            if !is_cargo_proxy {
                return Ok(path_miri);
            }
        } else if find_executable_in_path("cargo-miri").is_none() {
            return Err(
                "could not locate 'miri' or 'cargo-miri' on PATH \
                 (set ANNEAL_MIRI_BIN or add Miri to PATH)"
                    .to_string(),
            );
        }
    }
    if let Ok(home) = env::var("HOME") {
        let toolchains_dir = PathBuf::from(home).join(".rustup/toolchains");
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
                return Ok(first);
            }
        }
    }
    Err(format!(
        "could not locate pinned nightly-2026-06-01 '{tool_name}' binary \
         (set {env_var} or install the nightly-2026-06-01 toolchain)"
    ))
}

fn resolve_sysroot_path(explicit: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(path) = explicit {
        if path.join("lib/rustlib").is_dir() {
            return Ok(path.to_path_buf());
        }
        return Err(format!(
            "explicit Miri sysroot is missing lib/rustlib: {}",
            path.display()
        ));
    }
    if let Ok(val) = env::var("ANNEAL_MIRI_SYSROOT")
        && !val.trim().is_empty()
    {
        let p = PathBuf::from(val.trim());
        if p.join("lib/rustlib").is_dir() {
            return Ok(p);
        }
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT is missing lib/rustlib: {}",
            p.display()
        ));
    }
    if let Ok(home) = env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cache/miri");
        if candidate.join("lib/rustlib").is_dir() {
            return Ok(candidate);
        }
    }
    Err(
        "Miri sysroot not found at ~/.cache/miri (or ANNEAL_MIRI_SYSROOT); \
         missing Miri sysroot is a hard error"
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

    let mut compile_cmd = Command::new(&config.toolchain.rustc_bin);
    compile_cmd
        .current_dir(&corpus_root)
        .arg("--sysroot")
        .arg(&config.toolchain.miri_sysroot)
        .arg("--edition=2024")
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={crate_name}"))
        .arg("-Zalways-encode-mir");
    for flag in expand_flag_tokens(&config.capture_rustflags) {
        compile_cmd.arg(flag);
    }
    compile_cmd.arg("src/lib.rs").arg("-o").arg(&rlib_path);

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
        let mut miri_cmd = Command::new(&config.toolchain.miri_bin);
        miri_cmd
            .current_dir(&corpus_root)
            .arg("--sysroot")
            .arg(&config.toolchain.miri_sysroot);
        for flag in &config.miri_flags {
            miri_cmd.arg(flag);
        }
        miri_cmd
            .arg("-Zmiri-disable-isolation")
            .arg("--edition=2024")
            .arg(&driver_rs_path)
            .arg("--extern")
            .arg(format!("{crate_name}={}", rlib_path.display()))
            .env("MIRI_ORACLE_ITEM", &item.name);

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
             | .ret (.normal (_, _)) => (.normalOther, \"none\")\n    \
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
        "\nnamespace MiriOracleConfirm\n\n\
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
             | .ret (.normal (_, _)) => (.normalOther, \"none\")\n    \
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
}
