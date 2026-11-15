// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Batch compilation, live Miri + Anneal oracle execution, coverage reporting,
//! and self-contained finding bundle generation for `miri-difftest`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

pub use cargo_anneal::cgroup_memory_limits_kib;
use cargo_anneal::{
    ANNEAL_CAPTURE_FILTER_ENV, AnnealOutcome, CaptureDriverConfig, ComparisonVerdict,
    DEFAULT_CAPTURE_RUSTFLAGS, DEFAULT_MIRI_FLAGS, DEFAULT_ORACLE_FUEL, DifftestOracleConfig,
    DifftestOracleReport, DivergenceKind, ItemOracleReport, MiriOracleConfig, MiriOutcome,
    MiriToolchain, NotComparedReason, OracleItemSpec, ScaffoldConfig, SourcePos, SourceSpan,
    aggregate_unit_manifests, build_lake_build_command, compare_miri_and_anneal,
    derive_item_module_suffix, discover_zero_arg_pub_fns, normalize_path_against,
    parse_anneal_probe_output, probe_effective_memory_kib, resolve_default_lake_jobs,
    resolve_rustc_wrapper, run_miri_oracle, scaffold_workspace_with_config, source_files_match,
};

use crate::mutators_miri::{
    GeneratedMiriCandidate, MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE,
    RecordedMutationStep, load_miri_diff_corpus_seeds, miri_candidate_replay_is_faithful,
    reconstruct_miri_mutation_steps, replay_miri_mutation_steps,
};
use crate::shrink::{MemoizedOracle, MutatorChainShrinkStatus, shrink_mutation_chain_detailed};

/// Step fuel bound used for `miri-difftest` candidates (`DEFAULT_ORACLE_FUEL`
/// times 4, so 3-pass Episode 2 ADT/union/retag mutations on loop and
/// multi-match seeds do not prematurely exhaust step fuel under
/// `-Zmir-opt-level=0`).
pub const MIRI_DIFFTEST_CANDIDATE_FUEL: u32 = DEFAULT_ORACLE_FUEL * 4;

/// Canonical mutator names always included in `mutator_applications`.
pub const MIRI_MUTATOR_NAMES: [&str; 5] = [
    "ArithmeticCastMutator",
    "PlaceProjectionWrapper",
    "RawPtrOffsetMutator",
    "TreeBorrowsRetagInterleaver",
    "BitValidityTransmuteMutator",
];

/// Canonical divergence classes always included in `divergence_classes`.
pub const DIVERGENCE_CLASS_NAMES: [&str; 7] = [
    "wrong_value",
    "false_positive_ub",
    "missed_ub",
    "panic_vs_return",
    "return_vs_panic",
    "ub_location_mismatch",
    "panic_site_mismatch",
];

/// Canonical not-compared reason keys always included in `not_compared_reasons`.
pub const NOT_COMPARED_REASON_NAMES: [&str; 6] = [
    "compile_failed",
    "external_call",
    "unsupported",
    "out_of_fuel",
    "miri_oracle_error",
    "capture_failed",
];

/// Canonical witness polarity slugs always included in `witness_polarity_counts`.
pub const WITNESS_POLARITY_NAMES: [&str; 4] = [
    "unsound_missed_fault",
    "sound_conservative_abstraction",
    "value_mismatch",
    "harness_or_extraction_error",
];

/// Soundness direction ("witness polarity") of a `(MiriOutcome, AnnealOutcome)`
/// comparison result.
///
/// Anneal's `MirSemantics` is meant to be a sound conservative abstraction of
/// Miri (`-Zmiri-tree-borrows`): it may reject (`ub`) or refuse to model
/// (`unsupported`) an execution that Miri accepts, but it must never accept an
/// execution in which Miri faults. Every non-agreement is partitioned into
/// exactly one of the four classes below, and agreement maps to `None`:
///
/// - [`WitnessPolarity::UnsoundMissedFault`] (`"unsound_missed_fault"`): Miri
///   faults (`ub` or `panic`) and Anneal does not report that fault: it returns
///   normally, or (for Miri `ub`) panics or aborts instead (`missed_ub`,
///   `panic_vs_return`). This is the P0 soundness direction.
/// - [`WitnessPolarity::SoundConservativeAbstraction`]
///   (`"sound_conservative_abstraction"`): Miri does not report UB, while
///   Anneal rejects the execution with `ub` (`false_positive_ub`, including Miri
///   `panic` vs Anneal `ub`), or Miri returns normally and Anneal reports
///   `unsupported` (`D1..D15` over-approximation).
/// - [`WitnessPolarity::ValueMismatch`] (`"value_mismatch"`): Miri returns
///   normally and Anneal returns a different value, returns `pass:other`,
///   aborts, or panics (`wrong_value`, `return_vs_panic`), or both report the
///   same fault class at incompatible (or missing) source locations
///   (`ub_location_mismatch`, `panic_site_mismatch`). The class is not
///   directional, but it is not benign either: a `wrong_value` means Anneal
///   computed a result the program does not produce (for example, through the
///   Category 9 frame-relative pointer gap in `tests/miri-diff/README.md`), so
///   any value-level claim resting on it is unsound and needs triage.
/// - [`WitnessPolarity::HarnessOrExtractionError`]
///   (`"harness_or_extraction_error"`): no semantic comparison was possible: a
///   candidate compile failure, Miri oracle error, MIR capture or Lean probe
///   failure, exhausted step fuel, an uninterpreted external call, or
///   `unsupported` when Miri itself faulted (`panic` or `ub`), where Anneal's
///   refusal neither confirms nor contradicts Miri's fault.
///
/// The map is total over the strict comparator [`compare_miri_and_anneal`]
/// (rows: Miri outcome; columns: Anneal outcome; a Miri `oracle_error` row maps
/// every column to `HarnessOrExtractionError`):
///
/// | Miri \ Anneal | `pass:unit` / `pass:scalar` | `pass:other`, `abort` | `panic` | `ub` | `unsupported` | `externalCall`, `outOfFuel`, `capture_error` |
/// | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
/// | `pass` | `None` if unit/bits/width are equal, else `ValueMismatch` | `ValueMismatch` | `ValueMismatch` | `SoundConservativeAbstraction` | `SoundConservativeAbstraction` | `HarnessOrExtractionError` |
/// | `panic` | `UnsoundMissedFault` | `UnsoundMissedFault` | `None` if Miri's site lies in Anneal's span, else `ValueMismatch` | `SoundConservativeAbstraction` | `HarnessOrExtractionError` | `HarnessOrExtractionError` |
/// | `ub` | `UnsoundMissedFault` | `UnsoundMissedFault` | `UnsoundMissedFault` | `None` if Miri's site lies in Anneal's span, else `ValueMismatch` | `HarnessOrExtractionError` | `HarnessOrExtractionError` |
///
/// Miri `panic` vs Anneal `abort` is `panic_vs_return` and therefore
/// `UnsoundMissedFault`: Anneal claims that no unwinding (and so no cleanup
/// code) runs, which is flagged for triage rather than hidden as a mismatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WitnessPolarity {
    /// Miri reports `ub` or `panic` while Anneal does not report that fault
    /// (`missed_ub`, `panic_vs_return`).
    UnsoundMissedFault,
    /// Miri reports no UB while Anneal reports `ub` (`false_positive_ub`), or
    /// Miri returns normally while Anneal reports `unsupported`.
    SoundConservativeAbstraction,
    /// Miri returns normally and Anneal returns a different value, aborts, or
    /// panics (`wrong_value`, `return_vs_panic`), or both report the same fault
    /// class at incompatible locations (`ub_location_mismatch`,
    /// `panic_site_mismatch`).
    ValueMismatch,
    /// Compile failure, Miri oracle error, capture or Lean failure, out-of-fuel,
    /// external call, or `unsupported` when Miri faulted.
    HarnessOrExtractionError,
}

impl WitnessPolarity {
    /// Every polarity class, in [`WITNESS_POLARITY_NAMES`] order.
    pub const ALL: [WitnessPolarity; 4] = [
        Self::UnsoundMissedFault,
        Self::SoundConservativeAbstraction,
        Self::ValueMismatch,
        Self::HarnessOrExtractionError,
    ];

    /// Canonical JSON / CLI slug for this polarity class.
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::UnsoundMissedFault => "unsound_missed_fault",
            Self::SoundConservativeAbstraction => "sound_conservative_abstraction",
            Self::ValueMismatch => "value_mismatch",
            Self::HarnessOrExtractionError => "harness_or_extraction_error",
        }
    }

    /// Parse a canonical witness polarity slug back into [`WitnessPolarity`].
    pub fn from_str_slug(slug: &str) -> Option<Self> {
        let slug = slug.trim();
        Self::ALL.into_iter().find(|p| p.as_str() == slug)
    }

    /// Whether this polarity represents an unsound missed fault (`missed_ub` or
    /// `panic_vs_return`).
    pub const fn is_unsound(&self) -> bool {
        matches!(self, Self::UnsoundMissedFault)
    }
}

impl std::fmt::Display for WitnessPolarity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Classify a [`DivergenceKind`] into its [`WitnessPolarity`].
pub fn classify_divergence_kind_polarity(kind: &DivergenceKind) -> WitnessPolarity {
    match kind {
        DivergenceKind::MissedUb { .. } | DivergenceKind::PanicVsReturn { .. } => {
            WitnessPolarity::UnsoundMissedFault
        }
        DivergenceKind::FalsePositiveUb { .. } => WitnessPolarity::SoundConservativeAbstraction,
        DivergenceKind::WrongValue { .. }
        | DivergenceKind::ReturnVsPanic { .. }
        | DivergenceKind::UbLocationMismatch { .. }
        | DivergenceKind::PanicSiteMismatch { .. } => WitnessPolarity::ValueMismatch,
    }
}

/// Classify a [`NotComparedReason`] into its [`WitnessPolarity`]: `unsupported`
/// is a [`WitnessPolarity::SoundConservativeAbstraction`] exactly when Miri
/// returned normally, and every other case (including `unsupported` when Miri
/// faulted or failed) is a [`WitnessPolarity::HarnessOrExtractionError`].
pub fn classify_not_compared_polarity(
    miri: &MiriOutcome,
    reason: &NotComparedReason,
) -> WitnessPolarity {
    match reason {
        NotComparedReason::Unsupported(_)
            if matches!(miri, MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. }) =>
        {
            WitnessPolarity::SoundConservativeAbstraction
        }
        NotComparedReason::ExternalCall(_)
        | NotComparedReason::Unsupported(_)
        | NotComparedReason::OutOfFuel(_)
        | NotComparedReason::MiriOracleError(_)
        | NotComparedReason::CaptureFailed(_) => WitnessPolarity::HarnessOrExtractionError,
    }
}

/// Classify a `(MiriOutcome, AnnealOutcome)` pair together with its precomputed
/// [`ComparisonVerdict`] (such as the panic-site reconciled verdict from
/// [`compare_difftest_miri_and_anneal`]) into its [`WitnessPolarity`], returning
/// `None` on agreement.
///
/// The polarity is a function of the verdict and of whether Miri returned
/// normally; `_anneal` is accepted so callers can pass the full comparison
/// triple.
pub fn classify_verdict_witness_polarity(
    miri: &MiriOutcome,
    _anneal: &AnnealOutcome,
    verdict: &ComparisonVerdict,
) -> Option<WitnessPolarity> {
    match verdict {
        ComparisonVerdict::Agree => None,
        ComparisonVerdict::Diverge(kind) => Some(classify_divergence_kind_polarity(kind)),
        ComparisonVerdict::NotCompared(reason) => {
            Some(classify_not_compared_polarity(miri, reason))
        }
    }
}

/// Classify a `(MiriOutcome, AnnealOutcome)` pair into its [`WitnessPolarity`]
/// under strict [`compare_miri_and_anneal`] semantics, returning `None` on
/// agreement.
pub fn classify_witness_polarity(
    miri: &MiriOutcome,
    anneal: &AnnealOutcome,
) -> Option<WitnessPolarity> {
    let verdict = compare_miri_and_anneal(miri, anneal);
    classify_verdict_witness_polarity(miri, anneal, &verdict)
}

/// Split a located outcome tag `<family>` or `<family>@<location>` into its
/// optional location, or return `None` when `tag` belongs to another family.
fn split_located_outcome_tag<'a>(tag: &'a str, family: &str) -> Option<Option<&'a str>> {
    if tag == family {
        return Some(None);
    }
    tag.strip_prefix(family)?.strip_prefix('@').map(Some)
}

/// Parse the `<bits>:<size_bytes>` suffix of a `pass:scalar:` outcome tag.
fn parse_scalar_tag_fields(rest: &str) -> Option<(u128, u32)> {
    let (bits, size) = rest.split_once(':')?;
    Some((bits.trim().parse().ok()?, size.trim().parse().ok()?))
}

/// Parse a [`MiriOutcome::summary_tag`] (`pass:unit`,
/// `pass:scalar:<bits>:<size_bytes>`, `panic[@<file>:<line>:<col>]`,
/// `ub[@<file>:<line>:<col>]`, or `oracle_error:<message>`) back into a
/// [`MiriOutcome`].
///
/// Summary tags omit Miri's diagnostic text, so a parsed `Panic` or `Ub`
/// carries an empty `message`. Returns `None` for any other spelling, including
/// a malformed location.
pub fn parse_miri_summary_tag(tag: &str) -> Option<MiriOutcome> {
    let tag = tag.trim();
    if tag == "pass:unit" {
        return Some(MiriOutcome::PassUnit);
    }
    if let Some(rest) = tag.strip_prefix("pass:scalar:") {
        let (bits, size_bytes) = parse_scalar_tag_fields(rest)?;
        return Some(MiriOutcome::PassScalar { bits, size_bytes });
    }
    if let Some(message) = tag.strip_prefix("oracle_error:") {
        return Some(MiriOutcome::OracleError(message.to_string()));
    }
    let parse_pos = |loc: Option<&str>| -> Option<Option<SourcePos>> {
        match loc {
            None => Some(None),
            Some(raw) => SourcePos::parse_rustc_pos(raw).map(Some),
        }
    };
    if let Some(loc) = split_located_outcome_tag(tag, "panic") {
        return Some(MiriOutcome::Panic {
            pos: parse_pos(loc)?,
            message: String::new(),
        });
    }
    if let Some(loc) = split_located_outcome_tag(tag, "ub") {
        return Some(MiriOutcome::Ub {
            pos: parse_pos(loc)?,
            message: String::new(),
        });
    }
    None
}

/// Parse an [`AnnealOutcome::summary_tag`] (`pass:unit`,
/// `pass:scalar:<bits>:<size_bytes>`, `pass:other`, `panic[@<span>]`,
/// `abort[@<span>]`, `ub[@<span>]`, `unsupported[@<span>]`,
/// `externalCall:<def_path>`, `outOfFuel`, or `capture_error:<message>`) back
/// into an [`AnnealOutcome`].
///
/// Summary tags omit the spans of `externalCall` and `outOfFuel`, which parse
/// with `span: None`. Returns `None` for any other spelling, including a
/// malformed span.
pub fn parse_anneal_summary_tag(tag: &str) -> Option<AnnealOutcome> {
    let tag = tag.trim();
    match tag {
        "pass:unit" => return Some(AnnealOutcome::PassUnit),
        "pass:other" => return Some(AnnealOutcome::PassOther),
        "outOfFuel" => return Some(AnnealOutcome::OutOfFuel { span: None }),
        _ => {}
    }
    if let Some(rest) = tag.strip_prefix("pass:scalar:") {
        let (bits, size_bytes) = parse_scalar_tag_fields(rest)?;
        return Some(AnnealOutcome::PassScalar { bits, size_bytes });
    }
    if let Some(def_path) = tag.strip_prefix("externalCall:") {
        return Some(AnnealOutcome::ExternalCall {
            def_path: def_path.to_string(),
            span: None,
        });
    }
    if let Some(message) = tag.strip_prefix("capture_error:") {
        return Some(AnnealOutcome::CaptureOrLeanError(message.to_string()));
    }
    let parse_span = |loc: Option<&str>| -> Option<Option<SourceSpan>> {
        match loc {
            None => Some(None),
            Some(raw) => SourceSpan::parse_anneal_span(raw).map(Some),
        }
    };
    if let Some(loc) = split_located_outcome_tag(tag, "panic") {
        return Some(AnnealOutcome::Panic {
            span: parse_span(loc)?,
        });
    }
    if let Some(loc) = split_located_outcome_tag(tag, "abort") {
        return Some(AnnealOutcome::Abort {
            span: parse_span(loc)?,
        });
    }
    if let Some(loc) = split_located_outcome_tag(tag, "ub") {
        return Some(AnnealOutcome::Ub {
            span: parse_span(loc)?,
        });
    }
    if let Some(loc) = split_located_outcome_tag(tag, "unsupported") {
        return Some(AnnealOutcome::Unsupported {
            span: parse_span(loc)?,
        });
    }
    None
}

/// Classify serialized outcome tags ([`MiriOutcome::summary_tag`],
/// [`AnnealOutcome::summary_tag`]) and an optional verdict slug (`"agree"`, a
/// [`DIVERGENCE_CLASS_NAMES`] class, or a [`NOT_COMPARED_REASON_NAMES`] reason,
/// optionally prefixed with `not_compared_`) into [`WitnessPolarity`],
/// returning `None` on agreement.
///
/// A recognized slug decides the class (so a panic-site reconciled `"agree"`
/// stays an agreement); the slug `unsupported` additionally consults the Miri
/// tag. Without a recognized slug, both tags are parsed back into outcomes
/// ([`parse_miri_summary_tag`], [`parse_anneal_summary_tag`]) and classified
/// with [`classify_witness_polarity`], including source-site containment for
/// `panic` and `ub`. Tags that do not parse cannot be compared semantically and
/// classify as [`WitnessPolarity::HarnessOrExtractionError`].
pub fn classify_outcome_tags_polarity(
    miri_tag: &str,
    anneal_tag: &str,
    divergence_or_reason: Option<&str>,
) -> Option<WitnessPolarity> {
    let miri = parse_miri_summary_tag(miri_tag);
    if let Some(slug) = divergence_or_reason.map(str::trim).filter(|s| !s.is_empty()) {
        let slug = slug.strip_prefix("not_compared_").unwrap_or(slug);
        match slug {
            "agree" => return None,
            "missed_ub" | "panic_vs_return" => return Some(WitnessPolarity::UnsoundMissedFault),
            "false_positive_ub" => return Some(WitnessPolarity::SoundConservativeAbstraction),
            "wrong_value" | "return_vs_panic" | "ub_location_mismatch" | "panic_site_mismatch" => {
                return Some(WitnessPolarity::ValueMismatch);
            }
            "unsupported" => {
                return Some(
                    if matches!(
                        miri,
                        Some(MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. })
                    ) {
                        WitnessPolarity::SoundConservativeAbstraction
                    } else {
                        WitnessPolarity::HarnessOrExtractionError
                    },
                );
            }
            "compile_failed" | "external_call" | "out_of_fuel" | "miri_oracle_error"
            | "capture_failed" => return Some(WitnessPolarity::HarnessOrExtractionError),
            _ => {}
        }
    }
    match (miri, parse_anneal_summary_tag(anneal_tag)) {
        (Some(miri), Some(anneal)) => classify_witness_polarity(&miri, &anneal),
        _ => Some(WitnessPolarity::HarnessOrExtractionError),
    }
}

/// Check the accounting identities that tie `witness_polarity_counts` to the
/// rest of a [`MiriCampaignEvalReport`]:
///
/// 1. the keys are exactly [`WITNESS_POLARITY_NAMES`];
/// 2. the counts sum to `diverge_count + not_compared_count` (every
///    non-agreement, including compile failures, has exactly one polarity);
/// 3. `unsound_missed_fault` = `missed_ub` + `panic_vs_return`, and
///    `value_mismatch` = `wrong_value` + `return_vs_panic` +
///    `ub_location_mismatch` + `panic_site_mismatch`;
/// 4. `sound_conservative_abstraction` = `false_positive_ub` + (the
///    `unsupported` not-compared candidates on which Miri returned normally),
///    so it lies between `false_positive_ub` and `false_positive_ub` +
///    `not_compared_reasons["unsupported"]`, and together with
///    `harness_or_extraction_error` it accounts for every `false_positive_ub`
///    divergence and every not-compared candidate.
pub fn witness_polarity_accounting_holds(report: &MiriCampaignEvalReport) -> bool {
    let count = |map: &BTreeMap<String, usize>, key: &str| map.get(key).copied().unwrap_or(0);
    let pol = |p: WitnessPolarity| count(&report.witness_polarity_counts, p.as_str());
    let div = |class: &str| count(&report.divergence_classes, class);
    let keys_ok = report.witness_polarity_counts.len() == WITNESS_POLARITY_NAMES.len()
        && WITNESS_POLARITY_NAMES
            .iter()
            .all(|k| report.witness_polarity_counts.contains_key(*k));
    let total: usize = report.witness_polarity_counts.values().sum();
    let not_compared_total: usize = report.not_compared_reasons.values().sum();
    let conservative = pol(WitnessPolarity::SoundConservativeAbstraction);
    let conservative_unsupported = conservative.checked_sub(div("false_positive_ub"));
    keys_ok
        && total == report.diverge_count + report.not_compared_count
        && pol(WitnessPolarity::UnsoundMissedFault) == div("missed_ub") + div("panic_vs_return")
        && pol(WitnessPolarity::ValueMismatch)
            == div("wrong_value")
                + div("return_vs_panic")
                + div("ub_location_mismatch")
                + div("panic_site_mismatch")
        && conservative_unsupported
            .is_some_and(|n| n <= count(&report.not_compared_reasons, "unsupported"))
        && conservative + pol(WitnessPolarity::HarnessOrExtractionError)
            == div("false_positive_ub") + not_compared_total
}

/// `DefPath` spellings of the `core::fmt::Arguments` constructors that
/// `panic!`, `assert!`, `unreachable!`, `todo!`, and `unimplemented!`
/// expansions call before handing the result to `core::panicking::panic_fmt`.
///
/// The pinned toolchain emits `core::fmt::Arguments::<'a>::from_str` for plain
/// literal messages and `core::fmt::Arguments::<'a>::from_str_nonconst` when
/// `format_args!` inlines constant or nested arguments (such as
/// `unreachable!("...")`, `todo!("...")`, `unimplemented!("...")`, or
/// `panic!("... {}", 42)`); the remaining spellings cover the anonymous-lifetime
/// forms and the older `new_const` constructor. Each one is linked into every
/// oracle module as `fmtArgumentsCtorStub "<defPath>"` (see
/// [`FMT_ARGUMENTS_CTOR_STUB_LEAN`]).
pub const FMT_ARGUMENTS_CTOR_DEF_PATHS: [&str; 6] = [
    "core::fmt::Arguments::<'a>::from_str",
    "core::fmt::Arguments::<'_>::from_str",
    "core::fmt::Arguments::<'a>::from_str_nonconst",
    "core::fmt::Arguments::<'_>::from_str_nonconst",
    "core::fmt::Arguments::<'a>::new_const",
    "core::fmt::Arguments::<'_>::new_const",
];

/// Lean definition of `fmtArgumentsCtorStub`, the synthetic `CapturedMir` body
/// that `miri-difftest` links in place of each `core::fmt::Arguments`
/// constructor in [`FMT_ARGUMENTS_CTOR_DEF_PATHS`].
///
/// Each of these constructors builds an `Arguments` value that formats as
/// exactly its `&'static str` argument, so the stub represents the constructed
/// value by that message slice: it copies the argument `_1` into `_0` and
/// returns. `evalCallTerminator` evaluates the caller's argument operands
/// before it pushes a linked callee frame, so the argument is still checked
/// for UB. `Terminator.return_` requires an initialized `_0`, and the caller's
/// later `move` of the result into `core::panicking::panic_fmt` requires an
/// initialized destination local.
///
/// Anneal models `panic_fmt` as an unwinding panic that never reads its
/// argument. `miri-difftest` instead reads the message slice from the state
/// that panics (`probePanicMessageBounded`) and requires it to match the
/// message that Miri prints before it reconciles a panic site (see
/// [`compare_difftest_miri_and_anneal`]). Any other use of the constructed
/// value must call a `core::fmt` method that no stub models, so the oracle
/// reports an external call rather than a comparison.
///
/// These stubs appear only in `MiriOracleProbe.lean` and
/// `MiriOracleConfirm.lean`, after every captured helper body, so a captured
/// body with the same `DefPath` would take precedence in `findCallee?`. They
/// never enter a `Verify` certificate. The block contains no blank line, so
/// finding bundles can copy it verbatim from `MiriOracleConfirm.lean`.
pub const FMT_ARGUMENTS_CTOR_STUB_LEAN: &str = "\
-- Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,\n\
-- linked only by `miri-difftest` oracle modules. The caller has already\n\
-- evaluated the `&'static str` argument; this body returns that message slice\n\
-- as the constructed `Arguments`, which the caller passes to\n\
-- `core::panicking::panic_fmt`.\n\
open Trusted.Rustc.V2026_06_01.Layout in\n\
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=\n  \
  { defPath := defPath\n    \
    phase := MirPhaseTag.runtimePostCleanup\n    \
    role := ContractRole.model\n    \
    argCount := 1\n    \
    localDecls :=\n      \
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none },\n       \
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none }]\n    \
    basicBlocks :=\n      \
      [{ statements :=\n           \
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }\n                \
                (Rvalue.use (Operand.copy { local_ := 1, projection := [] })),\n              \
              span := \"<dummy>\" }]\n         \
         terminator := { kind := TerminatorKind.return_, span := \"<dummy>\" }\n         \
         isCleanup := false }]\n    \
    fnAbi :=\n      \
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]\n        \
        ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }\n        \
        conv := CallConv.rust\n        \
        canUnwind := false }\n    \
    layouts :=\n      \
      { pointerBits := 64\n        \
        isLittleEndian := true\n        \
        entries :=\n          \
          [{ size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }\n    \
    allocations := [] }\n";

/// Lean definitions that probe a bounded Anneal run for its `MirDiffTag` and
/// the span that decided it: `activeSpan`, `isCleanupState`, `unwindOrigin`,
/// `probeMirDiffExecBoundedFrom`, and `probeMirDiffExecBounded`.
///
/// A run that panics reports the span of the step that started unwinding
/// (`unwindOrigin`): the step that first entered a cleanup block, or the
/// panicking step itself when no cleanup block ran. Without this, a panic that
/// unwinds through a cleanup block (for example, to drop a local whose type
/// implements `Drop`) would report the span of the `resume` terminator that
/// ends the block, which rustc gives the span of the whole function. That span
/// contains every panic position in the function, so `compare_miri_and_anneal`
/// would accept any Miri panic site there, including a site that differs from
/// Anneal's.
///
/// `MiriOracleProbe.lean` and `MiriOracleConfirm.lean` share this block, so the
/// confirmation theorems prove the spans that the probe reported. The block
/// contains no blank line, so finding bundles can copy it verbatim from
/// `MiriOracleConfirm.lean`.
const PROBE_EXEC_LEAN: &str = "\
-- Probe a bounded run for its `MirDiffTag` and the span of the statement or\n\
-- terminator that decided it. A panic reports the span of the step that\n\
-- started unwinding (`unwindOrigin`): the step that first entered a cleanup\n\
-- block, or the panicking step itself when no cleanup block ran. The `resume`\n\
-- that ends a cleanup block carries the span of its whole function.\n\
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
  if raw == \"\" || raw == \"<dummy>\" then \"none\" else raw\n\
def isCleanupState (body : CapturedMir) : MirExecState → Bool\n  \
  | .running s =>\n    \
    match get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with\n    \
    | some bb => bb.isCleanup\n    \
    | none => false\n  \
  | _ => false\n\
def unwindOrigin\n    \
    (body : CapturedMir) (origin : Option MirExecState) (st st' : MirExecState) :\n    \
    Option MirExecState :=\n  \
  match origin with\n  \
  | some o => some o\n  \
  | none => if !isCleanupState body st && isCleanupState body st' then some st else none\n\
def probeMirDiffExecBoundedFrom\n    \
    (fuel : Nat) (body : CapturedMir) (origin : Option MirExecState) (st : MirExecState) :\n    \
    MirDiffTag × String :=\n  \
  match fuel with\n  \
  | 0 => (.outOfFuel, activeSpan body st)\n  \
  | fuel' + 1 =>\n    \
    match stepMirState body st with\n    \
    | .ret (.normal (.unit, _)) => (.normalUnit, \"none\")\n    \
    | .ret (.normal (.scalar sc, _)) => (.normalScalar sc.bits sc.sizeBytes, \"none\")\n    \
    | .ret (.normal (val, mem)) => ((MirDiffVerdict.normal val mem).toTagWithBody body, \"none\")\n    \
    | .ret .panic => (.panic, activeSpan body (origin.getD st))\n    \
    | .ret .abort => (.abort, activeSpan body st)\n    \
    | .tau st' => probeMirDiffExecBoundedFrom fuel' body (unwindOrigin body origin st st') st'\n    \
    | .vis (.inl (.fail .ub)) _ => (.ub, activeSpan body st)\n    \
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeSpan body st)\n    \
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeSpan body st)\n    \
    | .vis (.inr (.inl _)) k =>\n      \
      let st' := k PUnit.unit\n      \
      probeMirDiffExecBoundedFrom fuel' body (unwindOrigin body origin st st') st'\n    \
    | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)\n\
def probeMirDiffExecBounded\n    \
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : MirDiffTag × String :=\n  \
  probeMirDiffExecBoundedFrom fuel body none st\n";

/// Lean definitions that recover where and with what message a bounded Anneal
/// run panicked: `panicMessageOfSlice?`, `panicOperandVal?`,
/// `assertFailedPrefix?`, `formatAssertFailedMessage?`, `panicMessage?`,
/// `activeDefPath`, `probePanicOriginBoundedFrom`, `probePanicMessageBounded`,
/// and `probePanicFrameBounded`.
///
/// `probePanicOriginBoundedFrom` steps the machine exactly as
/// `probeMirDiffExecBounded` does (see [`PROBE_EXEC_LEAN`]) and, when the run
/// panics, returns the state whose span the probe reports: the step that
/// started unwinding. `probePanicFrameBounded` returns the `DefPath` of the
/// body executing that step, and `probePanicMessageBounded` returns the message
/// that `panicMessage?` recovers from it. `panicMessage?` recognizes these
/// panicking calls:
///
/// - `core::panicking::{panic,panic_str_2015}` receive the message as a
///   `&str`, and `core::panicking::{panic_fmt,const_panic_fmt}` receive the
///   message slice that [`FMT_ARGUMENTS_CTOR_STUB_LEAN`] returned.
///   `panicOperandVal?` evaluates the operand with `evalOperand`, and
///   `panicMessageOfSlice?` reads the slice's bytes from the panicking body's
///   captured allocations or the machine's global allocations.
/// - `core::panicking::panic_explicit` (from `panic!()`) panics with
///   `"explicit panic"`.
/// - `core::panicking::{assert_failed,assert_matches_failed}` panic with a
///   message whose first line is ``"assertion `left <op> right` failed"``,
///   followed by `": "` and the custom message when their
///   `Option<Arguments<'_>>` operand is `Some`. These strings mirror
///   `core::panicking::assert_failed_inner` in the pinned toolchain.
///
/// Every other panic (for example, an overflow `assert` terminator) has no
/// recoverable message and yields `none`. The block uses `unwindOrigin` from
/// [`PROBE_EXEC_LEAN`] and contains no blank line, so finding bundles can copy
/// it verbatim from `MiriOracleConfirm.lean`.
const PANIC_MESSAGE_PROBE_LEAN: &str = "\
-- Recover where and with what message a bounded run panicked, from the step\n\
-- that started unwinding (`unwindOrigin`): the `DefPath` of the body executing\n\
-- it, and the `&str` or `fmtArgumentsCtorStub` slice passed to\n\
-- `core::panicking::{panic,panic_fmt,panic_str_2015,const_panic_fmt}`,\n\
-- `\"explicit panic\"` for `core::panicking::panic_explicit`, or the first line\n\
-- that `core::panicking::{assert_failed,assert_matches_failed}` formats.\n\
def panicMessageOfSlice? (allocs : List CapturedAllocation) : Value → Option (List UInt8)\n  \
  | .aggregate 0 [.ptr p _, .scalar len] =>\n    \
    match allocs.find? (fun a => a.allocId == p.allocId) with\n    \
    | some alloc =>\n      \
      let window := (alloc.bytes.drop p.offsetBytes).take len.bits\n      \
      if window.length == len.bits then window.mapM id else none\n    \
    | none => none\n  \
  | _ => none\n\
def panicOperandVal? (cur : CapturedMir) (s : MachineState) (op : Operand) : Option Value :=\n  \
  match\n    \
    evalOperand\n      \
      s.frame.locals\n      \
      op\n      \
      s.memory.borrows\n      \
      (cur.allocations ++ s.memory.globals)\n      \
      cur.layouts\n      \
      s.memory.callerLocals\n      \
      cur.localDecls\n  \
  with\n  \
  | .ok v _ => some v\n  \
  | _ => none\n\
def assertFailedPrefix? : Value → Option (List UInt8)\n  \
  | .aggregate 0 _ | .scalar ⟨0, _⟩ =>\n    \
    some [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 96, 108, 101, 102, 116, 32, 61, 61, 32, 114, 105, 103, 104, 116, 96, 32, 102, 97, 105, 108, 101, 100]\n  \
  | .aggregate 1 _ | .scalar ⟨1, _⟩ =>\n    \
    some [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 96, 108, 101, 102, 116, 32, 33, 61, 32, 114, 105, 103, 104, 116, 96, 32, 102, 97, 105, 108, 101, 100]\n  \
  | .aggregate 2 _ | .scalar ⟨2, _⟩ =>\n    \
    some [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 96, 108, 101, 102, 116, 32, 109, 97, 116, 99, 104, 101, 115, 32, 114, 105, 103, 104, 116, 96, 32, 102, 97, 105, 108, 101, 100]\n  \
  | _ => none\n\
def formatAssertFailedMessage?\n    \
    (cur : CapturedMir) (s : MachineState) (pfx : List UInt8) (argsOp : Operand) :\n    \
    Option (List UInt8) :=\n  \
  let allocs := cur.allocations ++ s.memory.globals\n  \
  match panicOperandVal? cur s argsOp with\n  \
  | some (.aggregate 0 _) | some .unit | some (.scalar ⟨0, _⟩) => some pfx\n  \
  | some (.aggregate 1 [v]) =>\n    \
    match panicMessageOfSlice? allocs v with\n    \
    | some custom => some (pfx ++ [58, 32] ++ custom)\n    \
    | none => none\n  \
  | _ => none\n\
def panicMessage? (body : CapturedMir) (st : MirExecState) : Option (List UInt8) :=\n  \
  match st with\n  \
  | .running s =>\n    \
    let cur := s.memory.activeCallee.getD body\n    \
    let allocs := cur.allocations ++ s.memory.globals\n    \
    match get? cur.basicBlocks s.frame.blockIdx with\n    \
    | some bb =>\n      \
      match get? bb.statements s.frame.stmtIdx, bb.terminator.kind with\n      \
      | none, .call func [] _ _ _ =>\n        \
        match extractCalleeDefPath? func with\n        \
        | some \"core::panicking::panic_explicit\" =>\n          \
          some [101, 120, 112, 108, 105, 99, 105, 116, 32, 112, 97, 110, 105, 99]\n        \
        | _ => none\n      \
      | none, .call func [arg] _ _ _ =>\n        \
        match extractCalleeDefPath? func with\n        \
        | some \"core::panicking::panic_fmt\"\n        \
        | some \"core::panicking::panic\"\n        \
        | some \"core::panicking::panic_str_2015\"\n        \
        | some \"core::panicking::const_panic_fmt\" =>\n          \
          (panicOperandVal? cur s arg).bind (panicMessageOfSlice? allocs)\n        \
        | _ => none\n      \
      | none, .call func [_, _, argsOp] _ _ _ =>\n        \
        match extractCalleeDefPath? func with\n        \
        | some \"core::panicking::assert_matches_failed\" =>\n          \
          formatAssertFailedMessage? cur s [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 96, 108, 101, 102, 116, 32, 109, 97, 116, 99, 104, 101, 115, 32, 114, 105, 103, 104, 116, 96, 32, 102, 97, 105, 108, 101, 100] argsOp\n        \
        | _ => none\n      \
      | none, .call func [kindOp, _, _, argsOp] _ _ _ =>\n        \
        match extractCalleeDefPath? func with\n        \
        | some \"core::panicking::assert_failed\" =>\n          \
          match (panicOperandVal? cur s kindOp).bind assertFailedPrefix? with\n          \
          | some pfx => formatAssertFailedMessage? cur s pfx argsOp\n          \
          | none => none\n        \
        | _ => none\n      \
      | _, _ => none\n    \
    | none => none\n  \
  | _ => none\n\
def activeDefPath (body : CapturedMir) : MirExecState → DefPath\n  \
  | .running s => (s.memory.activeCallee.getD body).defPath\n  \
  | _ => \"\"\n\
def probePanicOriginBoundedFrom\n    \
    (fuel : Nat) (body : CapturedMir) (origin : Option MirExecState) (st : MirExecState) :\n    \
    Option MirExecState :=\n  \
  match fuel with\n  \
  | 0 => none\n  \
  | fuel' + 1 =>\n    \
    match stepMirState body st with\n    \
    | .ret .panic => some (origin.getD st)\n    \
    | .tau st' => probePanicOriginBoundedFrom fuel' body (unwindOrigin body origin st st') st'\n    \
    | .vis (.inr (.inl _)) k =>\n      \
      let st' := k PUnit.unit\n      \
      probePanicOriginBoundedFrom fuel' body (unwindOrigin body origin st st') st'\n    \
    | _ => none\n\
def probePanicMessageBounded\n    \
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Option (List UInt8) :=\n  \
  (probePanicOriginBoundedFrom fuel body none st).bind (panicMessage? body)\n\
def probePanicFrameBounded\n    \
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Option DefPath :=\n  \
  (probePanicOriginBoundedFrom fuel body none st).map (activeDefPath body)\n";

/// Name of the Lean definition in [`FMT_ARGUMENTS_CTOR_STUB_LEAN`].
const FMT_ARGUMENTS_CTOR_STUB_NAME: &str = "fmtArgumentsCtorStub";

/// Path suffixes of the standard-library files that define the panic and
/// assertion macros.
///
/// MIR expanded from one of these macros carries spans inside the macro's
/// definition, so Anneal attributes a panic raised by the expansion to a span in
/// one of these files. Miri instead reports the user's call site, because the
/// panic entry points that the expansions call are `#[track_caller]`.
const STD_PANIC_MACRO_FILE_SUFFIXES: [&str; 4] = [
    "library/core/src/panic.rs",
    "library/core/src/macros/mod.rs",
    "library/core/src/macros/panic.rs",
    "library/std/src/macros.rs",
];

/// Standard panic and assertion macros whose call site Miri reports for a panic
/// raised inside their expansion.
const STD_PANIC_MACRO_NAMES: [&str; 12] = [
    "panic",
    "assert",
    "assert_eq",
    "assert_ne",
    "assert_matches",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "debug_assert_matches",
    "unreachable",
    "todo",
    "unimplemented",
];

/// Relative `DefPath` segment of a lexical callable scope inside a staged
/// `src/lib.rs` function.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ScopeSegment {
    /// Named Rust item segment (`fn` or inline `mod`).
    Named(String),
    /// Closure body (`{closure}` / `{closure#N}` in rustc `DefPath`s).
    Closure,
    /// Nested item or block that introduces a separate callable/const body
    /// (`impl`, `trait`, `const`, `static`, `async`, or `const` block) whose
    /// `DefPath` is not reconciled here.
    Opaque,
}

/// Half-open 1-based `(line, col)` source interval `[start, end_excl)` of a
/// callable body (`fn`, nested `fn`, closure, or opaque body) and its relative
/// `DefPath` segments from the crate root.
#[derive(Debug, Clone)]
struct LexicalScope {
    start: (usize, usize),
    end_excl: (usize, usize),
    segments: Vec<ScopeSegment>,
}

fn node_span_bounds<T: quote::ToTokens>(node: &T) -> Option<((usize, usize), (usize, usize))> {
    let mut ts = proc_macro2::TokenStream::new();
    node.to_tokens(&mut ts);
    let mut iter = ts.into_iter();
    let first = iter.next()?;
    let start = first.span().start();
    let last = iter.last().unwrap_or(first);
    let end = match &last {
        proc_macro2::TokenTree::Group(g) => g.span_close().end(),
        other => other.span().end(),
    };
    Some(((start.line, start.column + 1), (end.line, end.column + 1)))
}

struct ScopeVisitor {
    stack: Vec<ScopeSegment>,
    scopes: Vec<LexicalScope>,
}

impl ScopeVisitor {
    fn with_segment<T: quote::ToTokens>(
        &mut self,
        node: &T,
        seg: ScopeSegment,
        inner: impl FnOnce(&mut Self),
    ) {
        self.stack.push(seg);
        if let Some((start, end_excl)) = node_span_bounds(node) {
            self.scopes.push(LexicalScope {
                start,
                end_excl,
                segments: self.stack.clone(),
            });
        }
        inner(self);
        self.stack.pop();
    }
}

impl<'ast> syn::visit::Visit<'ast> for ScopeVisitor {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        match item {
            syn::Item::Fn(inner_fn) => {
                let seg = ScopeSegment::Named(inner_fn.sig.ident.to_string());
                self.with_segment(inner_fn, seg, |v| {
                    syn::visit::visit_block(v, &inner_fn.block);
                });
            }
            syn::Item::Mod(inner_mod) => {
                if let Some((_, items)) = &inner_mod.content {
                    let seg = ScopeSegment::Named(inner_mod.ident.to_string());
                    self.with_segment(inner_mod, seg, |v| {
                        for it in items {
                            syn::visit::visit_item(v, it);
                        }
                    });
                }
            }
            syn::Item::Impl(_)
            | syn::Item::Trait(_)
            | syn::Item::Const(_)
            | syn::Item::Static(_) => {
                self.with_segment(item, ScopeSegment::Opaque, |v| {
                    syn::visit::visit_item(v, item);
                });
            }
            _ => syn::visit::visit_item(self, item),
        }
    }

    fn visit_expr(&mut self, expr: &'ast syn::Expr) {
        match expr {
            syn::Expr::Closure(closure) => {
                self.with_segment(closure, ScopeSegment::Closure, |v| {
                    syn::visit::visit_expr(v, &closure.body);
                });
            }
            syn::Expr::Async(async_expr) => {
                self.with_segment(async_expr, ScopeSegment::Opaque, |v| {
                    syn::visit::visit_block(v, &async_expr.block);
                });
            }
            syn::Expr::Const(const_expr) => {
                self.with_segment(const_expr, ScopeSegment::Opaque, |v| {
                    syn::visit::visit_block(v, &const_expr.block);
                });
            }
            _ => syn::visit::visit_expr(self, expr),
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        use syn::parse::Parser;
        if let Ok(exprs) =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
                .parse2(mac.tokens.clone())
        {
            for expr in &exprs {
                self.visit_expr(expr);
            }
        } else if let Ok(stmts) = syn::Block::parse_within.parse2(mac.tokens.clone()) {
            for stmt in &stmts {
                syn::visit::visit_stmt(self, stmt);
            }
        }
    }
}

fn is_user_crate_segment(seg: &str) -> bool {
    !seg.is_empty()
        && !matches!(seg, "core" | "std" | "alloc")
        && !seg.starts_with(|c: char| c.is_ascii_digit())
        && seg.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn is_closure_def_path_segment(seg: &str) -> bool {
    if seg == "{closure}" {
        return true;
    }
    let Some(num) = seg.strip_prefix("{closure#").and_then(|s| s.strip_suffix('}')) else {
        return false;
    };
    !num.is_empty() && num.chars().all(|c| c.is_ascii_digit())
}

/// Return `true` when `frame` names the callable body with relative `DefPath`
/// `scope_segments` in a user crate, or a compiler-generated `panic_cold_*`
/// shim (such as the `panic_cold_display` that `panic!("{}", x)` defines) inside
/// it. `user_children` lists the names of the `fn` items written directly in
/// that body; a frame that names one of them is that user `fn`, not a shim.
fn frame_matches_scope(
    frame: &str,
    scope_segments: &[ScopeSegment],
    user_children: &[&str],
) -> bool {
    if scope_segments.is_empty() || scope_segments.contains(&ScopeSegment::Opaque) {
        return false;
    }
    let parts: Vec<&str> = frame.split("::").collect();
    if parts.len() <= scope_segments.len() || !is_user_crate_segment(parts[0]) {
        return false;
    }
    for (seg, expected) in parts[1..=scope_segments.len()].iter().zip(scope_segments) {
        let ok = match expected {
            ScopeSegment::Named(name) => *seg == name,
            ScopeSegment::Closure => is_closure_def_path_segment(seg),
            ScopeSegment::Opaque => false,
        };
        if !ok {
            return false;
        }
    }
    match &parts[1 + scope_segments.len()..] {
        [] => true,
        [shim] => shim.starts_with("panic_cold_") && !user_children.contains(shim),
        _ => false,
    }
}

/// Staged `src/lib.rs` text indexed by the line range and nested callable
/// scopes of each top-level `fn` item, plus the 1-based `(line, col)` start
/// coordinates of every standard panic or assertion macro invocation, used by
/// [`compare_difftest_miri_and_anneal`] to decide whether Miri's panic position
/// is a panic-macro call site in the same callable frame as Anneal's panic.
#[derive(Debug, Clone, Default)]
pub struct StagedLibSource {
    fn_lines: BTreeMap<String, (usize, usize)>,
    fn_scopes: BTreeMap<String, Vec<LexicalScope>>,
    panic_macro_starts: BTreeSet<(usize, usize)>,
}

fn is_colon_pair(tokens: &[proc_macro2::TokenTree], idx: usize) -> bool {
    matches!(
        (tokens.get(idx), tokens.get(idx + 1)),
        (
            Some(proc_macro2::TokenTree::Punct(a)),
            Some(proc_macro2::TokenTree::Punct(b))
        ) if a.as_char() == ':'
            && a.spacing() == proc_macro2::Spacing::Joint
            && b.as_char() == ':'
            && b.spacing() == proc_macro2::Spacing::Alone
    )
}

fn is_panic_macro_tail(tokens: &[proc_macro2::TokenTree], idx: usize) -> bool {
    let Some(proc_macro2::TokenTree::Ident(mac)) = tokens.get(idx) else {
        return false;
    };
    if !STD_PANIC_MACRO_NAMES.contains(&mac.to_string().as_str()) {
        return false;
    }
    let Some(proc_macro2::TokenTree::Punct(bang)) = tokens.get(idx + 1) else {
        return false;
    };
    if bang.as_char() != '!' || bang.spacing() != proc_macro2::Spacing::Alone {
        return false;
    }
    matches!(
        tokens.get(idx + 2),
        Some(proc_macro2::TokenTree::Group(g))
            if matches!(
                g.delimiter(),
                proc_macro2::Delimiter::Parenthesis
                    | proc_macro2::Delimiter::Bracket
                    | proc_macro2::Delimiter::Brace
            )
    )
}

fn is_crate_qualified_panic_macro_tail(tokens: &[proc_macro2::TokenTree], idx: usize) -> bool {
    let Some(proc_macro2::TokenTree::Ident(krate)) = tokens.get(idx) else {
        return false;
    };
    matches!(krate.to_string().as_str(), "core" | "std")
        && is_colon_pair(tokens, idx + 1)
        && is_panic_macro_tail(tokens, idx + 3)
}

/// Return `true` when `tokens[idx]` is the first token of an invocation of one
/// of [`STD_PANIC_MACRO_NAMES`], written bare (`assert!(...)`) or through
/// `core::` / `std::` (optionally rooted with `::`), and is not preceded by a
/// path/member/macro-definition token (`:`, `.`, `!`, or an identifier before
/// `::`).
fn is_panic_macro_token_at(tokens: &[proc_macro2::TokenTree], idx: usize) -> bool {
    let preceded_by_path_or_bang = idx > 0
        && matches!(
            tokens.get(idx - 1),
            Some(proc_macro2::TokenTree::Punct(p)) if matches!(p.as_char(), ':' | '.' | '!')
        );
    if preceded_by_path_or_bang {
        return false;
    }
    if is_panic_macro_tail(tokens, idx) || is_crate_qualified_panic_macro_tail(tokens, idx) {
        return true;
    }
    if is_colon_pair(tokens, idx) && is_crate_qualified_panic_macro_tail(tokens, idx + 2) {
        if idx == 0 {
            return true;
        }
        return match tokens.get(idx - 1) {
            Some(proc_macro2::TokenTree::Ident(id)) => matches!(
                id.to_string().as_str(),
                "return" | "break" | "if" | "while" | "match" | "in"
            ),
            Some(proc_macro2::TokenTree::Punct(p)) if p.as_char() == '>' => {
                idx >= 2
                    && matches!(
                        tokens.get(idx - 2),
                        Some(proc_macro2::TokenTree::Punct(prev))
                            if matches!(prev.as_char(), '=' | '-')
                                && prev.spacing() == proc_macro2::Spacing::Joint
                    )
            }
            _ => true,
        };
    }
    false
}

fn collect_panic_macro_starts(
    stream: proc_macro2::TokenStream,
    out: &mut BTreeSet<(usize, usize)>,
) {
    let tokens: Vec<proc_macro2::TokenTree> = stream.into_iter().collect();
    for (idx, tt) in tokens.iter().enumerate() {
        if is_panic_macro_token_at(&tokens, idx) {
            let start = tt.span().start();
            out.insert((start.line, start.column + 1));
        }
        if let proc_macro2::TokenTree::Group(g) = tt {
            collect_panic_macro_starts(g.stream(), out);
        }
    }
}

impl StagedLibSource {
    /// Index `lib_rs`, recording the 1-based inclusive line range from each
    /// top-level `fn` keyword to its closing brace and the 1-based `(line, col)`
    /// start positions of all standard panic or assertion macro invocations.
    ///
    /// A source that fails to parse indexes no functions, so no panic site in
    /// it is reconciled.
    pub fn parse(lib_rs: &str) -> Self {
        let mut panic_macro_starts = BTreeSet::new();
        let mut fn_lines = BTreeMap::new();
        let mut fn_scopes = BTreeMap::new();
        if let Ok(file) = syn::parse_file(lib_rs) {
            if let Ok(ts) = lib_rs.parse::<proc_macro2::TokenStream>() {
                collect_panic_macro_starts(ts, &mut panic_macro_starts);
            }
            for item in &file.items {
                if let syn::Item::Fn(func) = item {
                    let name = func.sig.ident.to_string();
                    let first = func.sig.fn_token.span.start().line;
                    let last = func.block.brace_token.span.close().end().line;
                    fn_lines.insert(name.clone(), (first, last));

                    let mut visitor = ScopeVisitor {
                        stack: vec![ScopeSegment::Named(name.clone())],
                        scopes: vec![LexicalScope {
                            start: (first, 1),
                            end_excl: (last + 1, 1),
                            segments: vec![ScopeSegment::Named(name.clone())],
                        }],
                    };
                    syn::visit::visit_block(&mut visitor, &func.block);
                    fn_scopes.insert(name, visitor.scopes);
                }
            }
        }
        Self {
            fn_lines,
            fn_scopes,
            panic_macro_starts,
        }
    }

    /// Return the 1-based inclusive line range of the top-level `fn` item
    /// `fn_name`, if indexed.
    pub fn fn_line_range(&self, fn_name: &str) -> Option<(usize, usize)> {
        self.fn_lines.get(fn_name).copied()
    }

    /// Return `true` when `pos` lies in the staged `src/lib.rs`, within the
    /// line range of `fn_name`, at the first token of an invocation of one of
    /// [`STD_PANIC_MACRO_NAMES`], and `frame` names the innermost callable body
    /// (`fn`, nested `fn`, or closure) enclosing `pos` (or a compiler-generated
    /// `panic_cold_*` shim inside that body).
    fn is_panic_macro_call_site_in_frame(
        &self,
        fn_name: &str,
        pos: &SourcePos,
        frame: Option<&str>,
    ) -> bool {
        let file = pos.file.replace('\\', "/");
        if file.strip_prefix("./").unwrap_or(&file) != "src/lib.rs" {
            return false;
        }
        let Some((first, last)) = self.fn_line_range(fn_name) else {
            return false;
        };
        let (line, col) = (pos.line as usize, pos.col as usize);
        if line < first || line > last || !self.panic_macro_starts.contains(&(line, col)) {
            return false;
        }
        let Some(frame) = frame else {
            return false;
        };
        let Some(scopes) = self.fn_scopes.get(fn_name) else {
            return false;
        };
        let Some(innermost) = scopes
            .iter()
            .rfind(|s| (line, col) >= s.start && (line, col) < s.end_excl)
        else {
            return false;
        };
        let user_children: Vec<&str> = scopes
            .iter()
            .filter(|s| {
                s.segments.len() == innermost.segments.len() + 1
                    && s.segments.starts_with(&innermost.segments)
            })
            .filter_map(|s| match s.segments.last() {
                Some(ScopeSegment::Named(name)) => Some(name.as_str()),
                _ => None,
            })
            .collect();
        frame_matches_scope(frame, &innermost.segments, &user_children)
    }
}

/// Return `true` when `text` begins with an invocation of one of
/// [`STD_PANIC_MACRO_NAMES`], written bare (`assert!(...)`) or through
/// `core::` / `std::` (optionally rooted with `::`), followed by `!` and an
/// opening macro delimiter (`(`, `[`, or `{`).
#[cfg(test)]
fn starts_with_std_panic_macro_invocation(text: &str) -> bool {
    let trimmed = text.trim_start();
    let Ok(ts) = trimmed.parse::<proc_macro2::TokenStream>() else {
        return false;
    };
    let tokens: Vec<proc_macro2::TokenTree> = ts.into_iter().collect();
    let Some(first) = tokens.first() else {
        return false;
    };
    let start = first.span().start();
    start.line == 1 && start.column == 0 && is_panic_macro_token_at(&tokens, 0)
}

/// Return `true` when `file` ends with one of
/// [`STD_PANIC_MACRO_FILE_SUFFIXES`] at a path-component boundary (or equals
/// it).
fn is_std_panic_macro_file(file: &str) -> bool {
    let file = file.replace('\\', "/");
    STD_PANIC_MACRO_FILE_SUFFIXES
        .iter()
        .any(|suffix| file == *suffix || file.ends_with(&format!("/{suffix}")))
}

/// Compare a candidate's Miri and Anneal outcomes with
/// `compare_miri_and_anneal`, then reconcile the panic-site difference that the
/// standard panic and assertion macros introduce.
///
/// `compare_miri_and_anneal` requires Anneal's panic span to contain Miri's
/// panic position. For `panic!`, `assert!`, and similar macros the two
/// legitimately differ: Anneal reports the panicking terminator's span inside
/// the macro's standard-library definition, while Miri reports the user's call
/// site (`#[track_caller]`). A `Diverge(PanicSiteMismatch)` therefore becomes
/// `Agree` only when all of the following hold:
///
/// 1. Miri and Anneal both panicked, each with a known position.
/// 2. Anneal's panic span lies in a standard-library panic-macro file
///    (`library/core/src/panic.rs`, `library/core/src/macros/mod.rs`,
///    `library/core/src/macros/panic.rs`, or `library/std/src/macros.rs`).
/// 3. Miri's panic position lies in the staged `src/lib.rs`, within the line
///    range of `fn_name`, at the first token of an invocation of a standard
///    panic or assertion macro (`panic!`, the `assert!` and `debug_assert!`
///    families, `unreachable!`, `todo!`, or `unimplemented!`), written bare or
///    through `core::` / `std::`.
/// 4. If Anneal's run recovered its panic message (`anneal_panic_message`),
///    the first line of that message equals the message that Miri reports,
///    both trimmed. Miri's oracle output carries only the first line of the
///    message that follows `panicked at <position>:`.
/// 5. Anneal's panic began in the same callable body that encloses Miri's
///    panic position: `anneal_panic_frame`, the `DefPath` of the body executing
///    the step that started unwinding, matches the innermost user callable
///    (`fn_name`, a nested `fn`, or a closure) enclosing `miri_pos` in a user
///    crate (or a compiler-synthesized `panic_cold_*` shim inside that body).
///    A run in which Anneal panics inside a different function—including a
///    nested `fn` or closure inside `fn_name` when Miri panicked in the outer
///    body, or vice versa—does not reconcile.
///
/// Anneal recovers the message of a panic raised by
/// `core::panicking::{panic,panic_str_2015}`, by
/// `core::panicking::{panic_fmt,const_panic_fmt}` called with a literal
/// message built by a `core::fmt::Arguments` constructor stub, by
/// `core::panicking::panic_explicit` (`"explicit panic"`), or by
/// `core::panicking::{assert_failed,assert_matches_failed}`
/// (``"assertion `left <op> right` failed"``, followed by `": "` and the custom
/// message when one is given). Any other panic has no recovered message, and
/// condition 4 holds trivially. Anneal's span, frame, and message all come from
/// the step that started unwinding, even when the panic then unwinds through
/// cleanup blocks (see `probeMirDiffExecBounded`). A panic without a recovered
/// frame never reconciles.
///
/// Every other verdict is returned unchanged. In particular, a panic-site
/// mismatch whose Anneal span lies in user code (two different panicking
/// operations, or a `#[track_caller]` helper that Anneal attributes to its own
/// body) remains `Diverge(PanicSiteMismatch)`.
///
/// Every expansion of a standard macro shares the span of the macro's
/// definition, so conditions 2 and 3 cannot tell two panic-macro call sites in
/// the same function apart. Condition 4 tells them apart when they panic with
/// different recovered messages. If Anneal panics at a different call site in
/// the same callable body than Miri does but with the same message, or without
/// a recovered message, the outcome still reconciles to `Agree`.
pub fn compare_difftest_miri_and_anneal(
    miri: &MiriOutcome,
    anneal: &AnnealOutcome,
    anneal_panic_message: Option<&str>,
    anneal_panic_frame: Option<&str>,
    lib_src: &StagedLibSource,
    fn_name: &str,
) -> ComparisonVerdict {
    let verdict = compare_miri_and_anneal(miri, anneal);
    let ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. }) = &verdict else {
        return verdict;
    };
    let (
        MiriOutcome::Panic {
            pos: Some(miri_pos),
            message: miri_message,
        },
        AnnealOutcome::Panic {
            span: Some(anneal_span),
        },
    ) = (miri, anneal)
    else {
        return verdict;
    };
    let messages_match = anneal_panic_message
        .is_none_or(|message| message.lines().next().unwrap_or("").trim() == miri_message.trim());
    if messages_match
        && is_std_panic_macro_file(&anneal_span.file)
        && lib_src.is_panic_macro_call_site_in_frame(fn_name, miri_pos, anneal_panic_frame)
    {
        ComparisonVerdict::Agree
    } else {
        verdict
    }
}

/// Prefix of the line that `MiriOracleProbe.lean` prints after an item's
/// `ANNEAL_PROBE` line when the item panics; the line continues with the item
/// name, a tab, and the `DefPath` of the body in which the panic began
/// (`probePanicFrameBounded`).
const ANNEAL_PANIC_FRAME_PREFIX: &str = "ANNEAL_PANIC_FRAME\t";

/// Parse the `ANNEAL_PANIC_FRAME` lines of `MiriOracleProbe.lean` output into a
/// map from item name to the `DefPath` of the body in which its panic began.
fn parse_anneal_panic_frames(stdout: &str) -> Result<BTreeMap<String, String>, String> {
    let mut frames = BTreeMap::new();
    for raw_line in stdout.lines() {
        let line = raw_line.trim_end_matches('\r');
        let malformed = || format!("malformed ANNEAL_PANIC_FRAME line: '{raw_line}'");
        if line.trim() == "ANNEAL_PANIC_FRAME" {
            return Err(malformed());
        }
        let Some(rest) = line.trim_start().strip_prefix(ANNEAL_PANIC_FRAME_PREFIX) else {
            continue;
        };
        let (name, frame) = rest.split_once('\t').ok_or_else(malformed)?;
        let (name, frame) = (name.trim(), frame.trim());
        if name.is_empty() || frame.is_empty() {
            return Err(malformed());
        }
        if frames.insert(name.to_string(), frame.to_string()).is_some() {
            return Err(format!("duplicate ANNEAL_PANIC_FRAME line for '{name}'"));
        }
    }
    Ok(frames)
}

/// Prefix of the line that `MiriOracleProbe.lean` prints after an item's
/// `ANNEAL_PROBE` line when the item panics and `probePanicMessageBounded`
/// recovers the panic message; the line continues with the item name, a tab,
/// and the message bytes as a Lean list (`[104, 105]`).
const ANNEAL_PANIC_MESSAGE_PREFIX: &str = "ANNEAL_PANIC_MESSAGE\t";

/// Parse the `ANNEAL_PANIC_MESSAGE` lines of `MiriOracleProbe.lean` output into
/// a map from item name to the bytes of the panic message that Anneal's run
/// recovered.
fn parse_anneal_panic_messages(stdout: &str) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let mut messages = BTreeMap::new();
    for raw_line in stdout.lines() {
        let line = raw_line.trim_end_matches('\r');
        let malformed = || format!("malformed ANNEAL_PANIC_MESSAGE line: '{raw_line}'");
        if line.trim() == "ANNEAL_PANIC_MESSAGE" {
            return Err(malformed());
        }
        let Some(rest) = line.trim_start().strip_prefix(ANNEAL_PANIC_MESSAGE_PREFIX) else {
            continue;
        };
        let (name, list) = rest.split_once('\t').ok_or_else(malformed)?;
        let name = name.trim();
        if name.is_empty() {
            return Err(malformed());
        }
        let elems = list
            .trim()
            .strip_prefix('[')
            .and_then(|l| l.strip_suffix(']'))
            .ok_or_else(malformed)?;
        let bytes = if elems.trim().is_empty() {
            Vec::new()
        } else {
            elems
                .split(',')
                .map(|b| b.trim().parse::<u8>())
                .collect::<Result<Vec<u8>, _>>()
                .map_err(|_| malformed())?
        };
        if messages.insert(name.to_string(), bytes).is_some() {
            return Err(format!("duplicate ANNEAL_PANIC_MESSAGE line for '{name}'"));
        }
    }
    Ok(messages)
}

/// Self-contained diagnostic bundle emitted for a single Miri vs. Anneal
/// semantic divergence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MiriFindingBundle {
    /// Stable identifier within the run (for example,
    /// `"finding_0000_pass_ptr_offset_within_array"`).
    pub finding_id: String,
    /// Candidate function name in `src/lib.rs` and `repro.rs`.
    pub fn_name: String,
    /// Seed function name in `tests/miri-diff/corpus/src/lib.rs`.
    pub seed_name: String,
    /// Ordered list of AST mutators applied to produce the program in `repro.rs`:
    /// `minimized_mutator_chain` (equal to `original_mutator_chain` unless
    /// shrinking minimized the chain).
    pub applied_mutators: Vec<String>,
    /// Ordered list of AST mutators of the candidate as the batch generated it.
    pub original_mutator_chain: Vec<String>,
    /// Shortest mutator chain that the live oracle confirmed to reproduce the
    /// discrepancy signature (1-minimal when `shrink_status` is `minimized` or
    /// `already_one_minimal`), or `original_mutator_chain` when shrinking did not
    /// reduce it.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of shrinker predicate evaluations on proper subsequences of
    /// `original_mutator_chain` (each one a replay followed by a `rustc` check
    /// and, if that passes, an oracle query).
    pub shrink_evaluations: usize,
    /// Number of live Miri + Anneal oracle runs that shrinking actually executed
    /// (oracle queries answered by [`MemoizedOracle`] are not counted).
    pub executed_oracle_runs: usize,
    /// Outcome of mutator-chain shrinking ([`MutatorChainShrinkStatus::slug`],
    /// or `"skipped_shrinker_error: ..."`), so a finding never silently skips
    /// shrinking.
    pub shrink_status: String,
    /// Canonical divergence class slug (`"wrong_value"`, `"false_positive_ub"`,
    /// `"missed_ub"`, `"panic_vs_return"`, `"return_vs_panic"`,
    /// `"ub_location_mismatch"`, or `"panic_site_mismatch"`).
    pub divergence_class: String,
    /// Soundness direction slug ([`WitnessPolarity::as_str`]:
    /// `"unsound_missed_fault"`, `"sound_conservative_abstraction"`,
    /// `"value_mismatch"`, or `"harness_or_extraction_error"`).
    pub witness_polarity: String,
    /// Concise Miri outcome tag.
    pub miri_outcome_tag: String,
    /// Human-readable Miri diagnostic excerpt (`MIRI_PASS:...`, panic message,
    /// or `error: Undefined Behavior: ...`).
    pub miri_excerpt: String,
    /// Miri fault/panic position translated to `repro.rs` line coordinates.
    pub miri_pos: Option<String>,
    /// Miri fault/panic position of the original (unshrunk) candidate in the
    /// staged batch `src/lib.rs`.
    pub batch_miri_pos: Option<String>,
    /// Concise Anneal outcome tag.
    pub anneal_outcome_tag: String,
    /// Lean `MirDiffTag` constructor expression for this Anneal outcome.
    pub anneal_lean_tag: String,
    /// Anneal fault/panic span translated to `repro.rs` line coordinates.
    pub anneal_span: Option<String>,
    /// Anneal fault/panic span of the original (unshrunk) candidate in the
    /// staged batch `src/lib.rs`.
    pub batch_anneal_span: Option<String>,
    /// Extracted neighborhood from `.anneal/generated/Mir/<Crate>/<Item>.lean`.
    pub mir_neighborhood: String,
    /// Whether the Lean 4 kernel confirmed `evalMirDiffTagBounded` and
    /// `probeMirDiffExecBounded` (and, for a panic, `probePanicFrameBounded` and
    /// any recovered `probePanicMessageBounded`) via `by rfl` in
    /// `MiriOracleConfirm.lean`.
    pub kernel_confirmed: bool,
    /// Kernel-checked `theorem confirm_tag_<fn_name>` and
    /// `theorem confirm_probe_<fn_name>` snippet from `MiriOracleConfirm.lean`,
    /// plus `theorem confirm_frame_<fn_name>` and (when Anneal's panic message
    /// was recovered) `theorem confirm_message_<fn_name>` for a panic, preceded
    /// by the confirm-module definitions that those theorems use.
    pub kernel_confirm_theorems: String,
    /// Standalone `#![no_std]` Rust reproducer source (`repro.rs`).
    pub mutant_source: String,
    /// Path to `repro.rs` on disk when `--findings-dir` was provided.
    pub repro_path: Option<PathBuf>,
}

/// A candidate whose Miri and Anneal panics agree only through the panic-site
/// reconciliation in [`compare_difftest_miri_and_anneal`], recorded so that a
/// report lists every agreement that the strict `compare_miri_and_anneal`
/// alone would have reported as a `PanicSiteMismatch`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MiriReconciledPanicSite {
    /// Candidate function name in the staged batch `src/lib.rs`.
    pub fn_name: String,
    /// Seed function name in `tests/miri-diff/corpus/src/lib.rs`.
    pub seed_name: String,
    /// Miri's panic position (the macro call site) in the staged batch
    /// `src/lib.rs`.
    pub batch_miri_pos: Option<String>,
    /// Anneal's panic span inside the standard panic-macro definition.
    pub anneal_span: Option<String>,
    /// `DefPath` of the body in which Anneal's panic began: the candidate
    /// function itself or an item nested in it.
    pub anneal_panic_frame: Option<String>,
    /// Panic message recovered from Anneal's run, whose first line matched
    /// Miri's message, or `None` when the panic carries no recoverable
    /// message.
    pub anneal_panic_message: Option<String>,
    /// Whether the Lean 4 kernel confirmed the Anneal outcome, span, frame, and
    /// recovered message via `by rfl` in `MiriOracleConfirm.lean`.
    pub kernel_confirmed: bool,
    /// Kernel-checked theorem snippet from `MiriOracleConfirm.lean`, in the
    /// same form as [`MiriFindingBundle::kernel_confirm_theorems`].
    pub kernel_confirm_theorems: String,
}

/// Complete result of running `miri-difftest` over a set of candidate batches.
#[derive(Debug, Clone)]
pub struct MiriCampaignEvalReport {
    /// `"identity"` or `"seeded"`.
    pub mode: String,
    /// Master PRNG seed.
    pub seed: u64,
    /// Number of batches generated.
    pub batches: usize,
    /// Target candidate count per batch.
    pub batch_size: usize,
    /// Total candidates generated across all batches.
    pub total_candidates: usize,
    /// Number of candidates that compiled with `rustc`.
    pub compiled_candidates: usize,
    /// Number of candidates that failed `rustc` compilation.
    pub compile_failed_candidates: usize,
    /// Percentage of generated candidates that compiled (`0.0..=100.0`).
    pub compile_pass_rate_pct: f64,
    /// Count of candidates semantically compared (`agree_count + diverge_count`).
    pub compared_candidates: usize,
    /// Count of candidates where Miri and Anneal agreed (`ComparisonVerdict::Agree`).
    pub agree_count: usize,
    /// Count of candidates where Miri and Anneal diverged (`ComparisonVerdict::Diverge`).
    pub diverge_count: usize,
    /// Count of candidates not compared (compile failures + oracle `NotCompared`).
    pub not_compared_count: usize,
    /// Count of divergences whose reported evidence is confirmed in the Lean 4
    /// kernel (`by rfl`): the finding's minimized reproducer when shrinking
    /// reduced the candidate, else the original candidate. `item_reports` keep
    /// each original candidate's own `kernel_confirmed`.
    pub kernel_confirmed_divergences: usize,
    /// Miri outcome counts (`pass`, `panic`, `ub`, `error`).
    pub miri_verdicts: BTreeMap<String, usize>,
    /// Anneal outcome counts (`pass`, `panic`, `ub`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `error`).
    pub anneal_outcomes: BTreeMap<String, usize>,
    /// Divergence counts by canonical class name.
    pub divergence_classes: BTreeMap<String, usize>,
    /// Non-agreement counts by [`WitnessPolarity`] slug (`unsound_missed_fault`,
    /// `sound_conservative_abstraction`, `value_mismatch`,
    /// `harness_or_extraction_error`).
    pub witness_polarity_counts: BTreeMap<String, usize>,
    /// Not-compared counts by reason (`compile_failed`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `miri_oracle_error`, `capture_failed`).
    pub not_compared_reasons: BTreeMap<String, usize>,
    /// Frequency table of unmodeled external call `DefPath`s encountered.
    pub unmodeled_external_calls: BTreeMap<String, usize>,
    /// Per-mutator application counts across all generated candidates.
    pub mutator_applications: BTreeMap<String, usize>,
    /// Detailed finding bundles for every `ComparisonVerdict::Diverge` item.
    pub findings: Vec<MiriFindingBundle>,
    /// Candidates counted in `agree_count` only through the panic-site
    /// reconciliation in [`compare_difftest_miri_and_anneal`].
    pub reconciled_panic_sites: Vec<MiriReconciledPanicSite>,
    /// Deterministic, sorted observation-path signatures observed during live
    /// oracle evaluation (`miri:<mutator_chain_or_template>:<verdict_or_outcome>:<diff_tag>`).
    pub obs_path_signatures: Vec<String>,
    /// Per-item oracle reports from the helper-linked Miri + Anneal oracle pipeline.
    pub item_reports: Vec<ItemOracleReport>,
    /// Total wall-clock duration in milliseconds.
    pub elapsed_ms: f64,
}

/// Resolve the `rustc` binary used for candidate compilation checks.
pub fn resolve_rustc_bin() -> String {
    if let Ok(r) = env::var("RUSTC")
        && !r.is_empty()
    {
        return r;
    }
    if let Ok(home) = env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/rustc");
        if candidate.exists() {
            return candidate.to_string_lossy().into_owned();
        }
    }
    "rustc".to_string()
}

/// Sequence number that gives each `compile_rust_snippet` call its own scratch
/// directory. Concurrent calls in one process (such as parallel tests) reuse
/// labels like `"all_batches"`, and a shared directory let one call delete
/// another's output before `rustc` wrote it.
static SNIPPET_COMPILE_SEQ: AtomicUsize = AtomicUsize::new(0);

/// Runs `rustc --edition=2024 --crate-type=lib` on an in-memory Rust source
/// string and reports whether it compiled.
pub fn compile_rust_snippet(label: &str, source: &str) -> bool {
    let rustc_bin = resolve_rustc_bin();
    let seq = SNIPPET_COMPILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let tmp_dir = env::temp_dir().join(format!(
        "anneal_miri_difftest_{}_{seq}_{}",
        std::process::id(),
        label
    ));
    let _ = fs::create_dir_all(&tmp_dir);
    let out_path = tmp_dir.join("libmiri_check.rlib");

    let child_res = Command::new(&rustc_bin)
        .args(["--edition=2024", "--crate-type=lib", "-A", "warnings", "-o"])
        .arg(&out_path)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let Ok(mut child) = child_res else {
        let _ = fs::remove_dir_all(&tmp_dir);
        return false;
    };

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(source.as_bytes());
    }
    let ok = child
        .wait_with_output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    let _ = fs::remove_dir_all(&tmp_dir);
    ok
}

/// Compiles every candidate, first as one combined crate and, if that fails,
/// one candidate at a time so that each compile failure is attributed to its
/// specific candidate.
pub fn compile_candidates(batches: &[Vec<GeneratedMiriCandidate>]) -> Vec<Vec<bool>> {
    let mut combined = String::from(MIRI_CORPUS_CRATE_HEADER);
    combined.push('\n');
    let mut has_any = false;
    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            has_any = true;
            combined.push_str(&format!(
                "#[allow(dead_code, unused_variables, unused_assignments)]\n\
                 pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.module_body_source()
            ));
        }
    }
    if has_any && compile_rust_snippet("all_batches", &combined) {
        return batches.iter().map(|b| vec![true; b.len()]).collect();
    }
    batches
        .iter()
        .enumerate()
        .map(|(b_idx, batch)| {
            batch
                .iter()
                .enumerate()
                .map(|(c_idx, cand)| {
                    compile_rust_snippet(&format!("b{b_idx}_c{c_idx}"), &cand.source)
                })
                .collect()
        })
        .collect()
}

/// Return the canonical slug for a [`DivergenceKind`].
pub fn divergence_class_slug(kind: &DivergenceKind) -> &'static str {
    match kind {
        DivergenceKind::WrongValue { .. } => "wrong_value",
        DivergenceKind::FalsePositiveUb { .. } => "false_positive_ub",
        DivergenceKind::MissedUb { .. } => "missed_ub",
        DivergenceKind::PanicVsReturn { .. } => "panic_vs_return",
        DivergenceKind::ReturnVsPanic { .. } => "return_vs_panic",
        DivergenceKind::UbLocationMismatch { .. } => "ub_location_mismatch",
        DivergenceKind::PanicSiteMismatch { .. } => "panic_site_mismatch",
    }
}

/// Return the value-insensitive Lean `MirDiffTag` of `outcome` used by
/// [`discrepancy_signatures_match`].
///
/// A scalar return keeps its width but drops its bits
/// (`MirDiffTag.normalScalar _ <size_bytes>`), so return-value perturbations
/// from unrelated `Pass` mutators do not mask an otherwise identical
/// divergence. Spans never appear in a `MirDiffTag`. Outcomes with no tag
/// (capture or Lean errors) normalize to `"none"`.
pub fn normalize_anneal_outcome_tag(outcome: &AnnealOutcome) -> String {
    match outcome {
        AnnealOutcome::PassScalar { size_bytes, .. } => {
            format!("MirDiffTag.normalScalar _ {size_bytes}")
        }
        other => other
            .to_lean_mir_diff_tag()
            .map(|tag| {
                let mut clean = tag.trim();
                while clean.len() >= 2 && clean.starts_with('(') && clean.ends_with(')') {
                    clean = clean[1..clean.len() - 1].trim();
                }
                clean.to_string()
            })
            .unwrap_or_else(|| "none".to_string()),
    }
}

/// Normalize a Miri diagnostic message so that it no longer depends on source
/// locations, allocation ids, addresses, offsets, or concrete values.
///
/// Every hexadecimal literal (`0x2a`) becomes `0xN`, every maximal run of decimal
/// digits (`alloc1234`, `src/lib.rs:52:17`, `size 16`) becomes `N` (except Rust
/// primitive numeric type tokens `u8`/`u16`/`u32`/`u64`/`u128`, `i8`..`i128`,
/// `f32`/`f64`, which keep their bit width so type-width changes are not masked),
/// and whitespace is collapsed. The non-numeric wording that identifies the UB
/// or panic kind (for example `"constructing invalid value"` vs. `"memory access
/// failed"`) is kept.
pub fn normalize_diagnostic_message(raw: &str) -> String {
    let chars: Vec<char> = raw.trim().chars().collect();
    let mut out = String::with_capacity(chars.len());
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if c == '0'
            && i + 2 < chars.len()
            && (chars[i + 1] == 'x' || chars[i + 1] == 'X')
            && chars[i + 2].is_ascii_hexdigit()
        {
            out.push_str("0xN");
            i += 2;
            while i < chars.len() && (chars[i].is_ascii_hexdigit() || chars[i] == '_') {
                i += 1;
            }
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
            }
            let digit_str: String = chars[start..i].iter().collect();
            let preceded_by_type_prefix = start >= 1
                && matches!(chars[start - 1], 'u' | 'i' | 'f')
                && (start == 1
                    || !(chars[start - 2].is_ascii_alphanumeric() || chars[start - 2] == '_'));
            let followed_by_ident =
                i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_');
            let is_primitive_width = preceded_by_type_prefix
                && !followed_by_ident
                && match chars[start - 1] {
                    'u' | 'i' => matches!(digit_str.as_str(), "8" | "16" | "32" | "64" | "128"),
                    'f' => matches!(digit_str.as_str(), "32" | "64"),
                    _ => false,
                };
            if is_primitive_width {
                out.push_str(&digit_str);
            } else {
                out.push('N');
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Return the span-normalized Miri outcome family: the outcome category plus, for
/// panics and UB, the [`normalize_diagnostic_message`]-normalized diagnostic.
/// Return values are reduced to their width so value perturbations do not
/// matter.
pub fn normalize_miri_outcome_family(outcome: &MiriOutcome) -> String {
    match outcome {
        MiriOutcome::PassUnit => "pass:unit".to_string(),
        MiriOutcome::PassScalar { size_bytes, .. } => format!("pass:scalar:{size_bytes}"),
        MiriOutcome::Panic { message, .. } => {
            format!("panic:{}", normalize_diagnostic_message(message))
        }
        MiriOutcome::Ub { message, .. } => format!("ub:{}", normalize_diagnostic_message(message)),
        MiriOutcome::OracleError(_) => "oracle_error".to_string(),
    }
}

/// Whether `candidate` reproduces the discrepancy signature of `original`,
/// independently of where the discrepancy sits in `src/lib.rs`.
///
/// Both reports must diverge with the same `divergence_class_slug`, the same
/// normalized `MirDiffTag` ([`normalize_anneal_outcome_tag`]), and the same Miri
/// outcome family ([`normalize_miri_outcome_family`], which blocks "bug
/// slippage" into a different UB or panic kind that happens to share the
/// divergence class). When the Lean 4 kernel confirmed the original divergence,
/// it must confirm the candidate's too, so shrinking never trades a
/// kernel-confirmed finding for an unconfirmed one. Line numbers, allocation
/// ids, offsets, and values never matter.
pub fn discrepancy_signatures_match(
    original: &ItemOracleReport,
    candidate: &ItemOracleReport,
) -> bool {
    let (ComparisonVerdict::Diverge(orig_kind), ComparisonVerdict::Diverge(cand_kind)) =
        (&original.verdict, &candidate.verdict)
    else {
        return false;
    };
    divergence_class_slug(orig_kind) == divergence_class_slug(cand_kind)
        && normalize_anneal_outcome_tag(&original.anneal)
            == normalize_anneal_outcome_tag(&candidate.anneal)
        && normalize_miri_outcome_family(&original.miri)
            == normalize_miri_outcome_family(&candidate.miri)
        && (!original.kernel_confirmed || candidate.kernel_confirmed)
}

/// Whether the oracle failed to judge the program behind `report`: Miri itself
/// failed (`NotCompared(MiriOracleError)`), or MIR capture, scaffolding, or the
/// Lean probe failed (`NotCompared(CaptureFailed)`).
///
/// Shrinking counts such a report as an oracle failure, exactly like a pipeline
/// run that produced no report: the program's behavior is unknown, so the report
/// neither reproduces nor refutes the discrepancy signature, and treating it as
/// a rejection could let an unjudged reduction license a 1-minimality claim. The
/// other `NotCompared` reasons (an uninterpreted external call, an unsupported
/// construct, or exhausted step fuel) are deterministic judgments of the program
/// by Anneal under the original fuel, and they rule the signature out.
pub fn miri_report_is_oracle_failure(report: &ItemOracleReport) -> bool {
    matches!(
        report.verdict,
        ComparisonVerdict::NotCompared(
            NotComparedReason::MiriOracleError(_) | NotComparedReason::CaptureFailed(_)
        )
    )
}

/// Outcome of attempting to shrink a divergent Miri candidate's mutator chain.
pub type MiriShrinkStatus = MutatorChainShrinkStatus;

/// Result of shrinking a divergent [`GeneratedMiriCandidate`]'s mutator chain.
#[derive(Debug, Clone)]
pub struct MiriCandidateShrinkResult {
    /// Original mutator sequence before shrinking.
    pub original_mutator_chain: Vec<String>,
    /// Mutator sequence of `minimized_candidate`: 1-minimal when `status` is
    /// `Minimized` or `AlreadyOneMinimal`, and the original sequence when
    /// shrinking did not reduce it.
    pub minimized_mutator_chain: Vec<String>,
    /// Number of shrinker predicate evaluations on proper subsequences of the
    /// original chain (each one a replay followed by a `rustc` check and, if that
    /// passes, an oracle query). The full chain is never re-evaluated: its
    /// divergence is the original report.
    pub shrink_evaluations: usize,
    /// Number of oracle queries (`eval_fn` calls) made while shrinking.
    pub oracle_evaluations: usize,
    /// Number of replayed subsequences rejected by the `rustc` pre-check without
    /// querying the oracle.
    pub compile_rejections: usize,
    /// Number of oracle queries that actually executed the oracle. Equals
    /// `oracle_evaluations` unless the evaluator is memoized ([`MemoizedOracle`]),
    /// in which case repeated queries of an identical program are cache hits.
    pub executed_oracle_runs: usize,
    /// Number of oracle queries that produced no judgment: no report at all (for
    /// example a failed live pipeline run) or a report whose verdict is an
    /// oracle failure ([`miri_report_is_oracle_failure`]). Any failure makes
    /// `status` [`MutatorChainShrinkStatus::Inconclusive`].
    pub oracle_failures: usize,
    /// Whether shrinking ran and what it concluded.
    pub status: MiriShrinkStatus,
    /// Shortest candidate that the oracle confirmed to reproduce the signature,
    /// with updated `applied_mutators`, `fn_source`, and `source` (the original
    /// candidate when shrinking did not reduce the chain).
    pub minimized_candidate: GeneratedMiriCandidate,
    /// Oracle report of `minimized_candidate`.
    pub minimized_report: ItemOracleReport,
    /// `.anneal/generated/Mir/...` snippet captured by the oracle run that
    /// accepted `minimized_candidate` (live shrinking only).
    pub mir_neighborhood: Option<String>,
    /// Kernel confirmation theorem block from the `MiriOracleConfirm.lean` of the
    /// oracle run that accepted `minimized_candidate` (live shrinking only).
    pub kernel_confirm_theorems: Option<String>,
}

impl MiriCandidateShrinkResult {
    /// Whether `minimized_candidate` has a strictly shorter mutator chain than
    /// the original candidate (so its program and report replace the original's
    /// in the finding bundle).
    pub fn is_reduced(&self) -> bool {
        self.minimized_mutator_chain.len() < self.original_mutator_chain.len()
    }
}

/// Per-shrink query counts: `(shrink_evaluations, oracle_evaluations,
/// compile_rejections, oracle_failures)`.
type MiriShrinkCounts = (usize, usize, usize, usize);

fn unshrunk_result(
    cand: &GeneratedMiriCandidate,
    original_report: &ItemOracleReport,
    status: MiriShrinkStatus,
    (shrink_evaluations, oracle_evaluations, compile_rejections, oracle_failures): MiriShrinkCounts,
) -> MiriCandidateShrinkResult {
    MiriCandidateShrinkResult {
        original_mutator_chain: cand.applied_mutators.clone(),
        minimized_mutator_chain: cand.applied_mutators.clone(),
        shrink_evaluations,
        oracle_evaluations,
        compile_rejections,
        executed_oracle_runs: oracle_evaluations,
        oracle_failures,
        status,
        minimized_candidate: cand.clone(),
        minimized_report: original_report.clone(),
        mir_neighborhood: None,
        kernel_confirm_theorems: None,
    }
}

/// Minimize a divergent [`GeneratedMiriCandidate`]'s mutator chain using a
/// caller-supplied oracle `eval_fn` (a deterministic unit-test oracle or the
/// live Miri + Anneal pipeline).
///
/// Before `eval_fn` judges any proper subsequence, `compile_rust_snippet` checks
/// that the replayed program compiles with `rustc` (memoized by program text);
/// subsequences that do not compile are rejected without an oracle query.
pub fn minimize_miri_candidate_mutations_with<F>(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
    original_report: &ItemOracleReport,
    eval_fn: F,
) -> MiriCandidateShrinkResult
where
    F: FnMut(&GeneratedMiriCandidate) -> Option<ItemOracleReport>,
{
    let mut compile_memo = MemoizedOracle::new(|sub_cand: &GeneratedMiriCandidate| {
        compile_rust_snippet(&format!("shrink_{}", sub_cand.fn_name), &sub_cand.source)
    });
    minimize_miri_candidate_mutations_with_compile_check(
        cand,
        seeds,
        original_report,
        |sub_cand| compile_memo.eval(sub_cand.source.clone(), sub_cand),
        eval_fn,
    )
}

/// Core of [`minimize_miri_candidate_mutations_with`] with an injectable `rustc`
/// pre-check `compile_fn` (so unit tests can exercise compile rejection without
/// spawning `rustc`).
///
/// Shrinking runs [`shrink_mutation_chain_detailed`] over the candidate's
/// recorded mutation passes ([`reconstruct_miri_mutation_steps`] over `seeds`,
/// the seeds the candidate was generated from) with the predicate "the replayed
/// subsequence compiles, the oracle judges it, and
/// [`discrepancy_signatures_match`] holds against `original_report`". A query
/// that returns no report, or a report of an oracle failure
/// ([`miri_report_is_oracle_failure`]), is rejected and counted in
/// `oracle_failures`, which withholds any 1-minimality claim. The
/// unmutated seed `[]` is evaluated like any other subsequence, so a seed that
/// already diverges with the same signature shrinks to `[]`. Shrinking is
/// skipped (status `SkippedReplayMismatch`, with no compile check or oracle
/// query) unless replaying the full recorded chain reproduces the candidate
/// byte for byte ([`miri_candidate_replay_is_faithful`]), because only then is
/// every subsequence a reduction of the reported program and the full chain
/// known to reproduce `original_report` without re-running the oracle.
pub fn minimize_miri_candidate_mutations_with_compile_check<C, F>(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
    original_report: &ItemOracleReport,
    mut compile_fn: C,
    mut eval_fn: F,
) -> MiriCandidateShrinkResult
where
    C: FnMut(&GeneratedMiriCandidate) -> bool,
    F: FnMut(&GeneratedMiriCandidate) -> Option<ItemOracleReport>,
{
    if cand.applied_mutators.is_empty()
        || !matches!(original_report.verdict, ComparisonVerdict::Diverge(_))
    {
        return unshrunk_result(
            cand,
            original_report,
            MiriShrinkStatus::SkippedNotApplicable,
            (0, 0, 0, 0),
        );
    }

    let replay = reconstruct_miri_mutation_steps(cand, seeds)
        .filter(|(base, steps)| miri_candidate_replay_is_faithful(cand, base, steps));
    let Some((base, steps)) = replay else {
        return unshrunk_result(
            cand,
            original_report,
            MiriShrinkStatus::SkippedReplayMismatch,
            (0, 0, 0, 0),
        );
    };

    let full_len = steps.len();
    let mut oracle_evaluations = 0usize;
    let mut compile_rejections = 0usize;
    let mut oracle_failures = 0usize;
    // Last accepted reduction, keyed by the original pass indices it retains
    // (mutator names alone are ambiguous when a mutator appears twice).
    let mut last_accepted: Option<(Vec<usize>, GeneratedMiriCandidate, ItemOracleReport)> = None;

    let outcome = shrink_mutation_chain_detailed(&steps, |sub_steps: &[RecordedMutationStep]| {
        if sub_steps.len() == full_len {
            // The faithful full replay is byte-identical to `cand`, whose
            // divergence is `original_report` itself.
            return true;
        }
        let sub_cand = replay_miri_mutation_steps(cand, &base, sub_steps);
        if !compile_fn(&sub_cand) {
            compile_rejections += 1;
            return false;
        }
        oracle_evaluations += 1;
        let Some(rep) = eval_fn(&sub_cand).filter(|rep| !miri_report_is_oracle_failure(rep))
        else {
            oracle_failures += 1;
            return false;
        };
        if !discrepancy_signatures_match(original_report, &rep) {
            return false;
        }
        let kept: Vec<usize> = sub_steps.iter().map(|s| s.pass_index).collect();
        last_accepted = Some((kept, sub_cand, rep));
        true
    });

    // The initial full-chain predicate call is free (see above) and not counted.
    let shrink_evaluations = outcome.predicate_evaluations.saturating_sub(1);
    let minimized_indices: Vec<usize> =
        outcome.minimized_steps.iter().map(|s| s.pass_index).collect();

    if minimized_indices.len() < full_len
        && let Some((kept, min_cand, min_rep)) = last_accepted
        && kept == minimized_indices
    {
        return MiriCandidateShrinkResult {
            original_mutator_chain: cand.applied_mutators.clone(),
            minimized_mutator_chain: min_cand.applied_mutators.clone(),
            shrink_evaluations,
            oracle_evaluations,
            compile_rejections,
            executed_oracle_runs: oracle_evaluations,
            oracle_failures,
            status: MiriShrinkStatus::of_completed_shrink(true, oracle_failures),
            minimized_candidate: min_cand,
            minimized_report: min_rep,
            mir_neighborhood: None,
            kernel_confirm_theorems: None,
        };
    }

    // Either no proper subsequence reproduced the signature (the full chain is
    // 1-minimal relative to the oracle's answers), or (only possible with a
    // nondeterministic oracle) the shrinker's final chain is not the last
    // accepted reduction; never attach a report to a candidate that it was not
    // produced from.
    unshrunk_result(
        cand,
        original_report,
        MiriShrinkStatus::of_completed_shrink(false, oracle_failures),
        (shrink_evaluations, oracle_evaluations, compile_rejections, oracle_failures),
    )
}

/// Report and diagnostic artifacts from a live single-candidate oracle run.
#[derive(Debug, Clone)]
pub struct LiveCandidateEvaluation {
    /// Oracle report for the candidate item.
    pub report: ItemOracleReport,
    /// Extracted `.anneal/generated/Mir/...` snippet for the candidate.
    pub mir_neighborhood: String,
    /// Extracted kernel confirmation theorem block from `MiriOracleConfirm.lean`.
    pub kernel_confirm_theorems: String,
}

/// Run the live helper-linked Miri + Anneal oracle pipeline (the one
/// [`evaluate_miri_batches`] runs) on the single candidate `cand` with step
/// `fuel`, in a fresh staging crate whose `src/lib.rs` is exactly `cand.source`,
/// so reported positions are already in `repro.rs` coordinates.
pub fn evaluate_candidate_live(
    cand: &GeneratedMiriCandidate,
    fuel: u32,
    toolchain: &MiriToolchain,
    anneal_repo_root: Option<&Path>,
) -> Result<LiveCandidateEvaluation, String> {
    let staging_dir = create_staging_dir("shrink")?;
    let result = (|| {
        fs::write(staging_dir.join("src/lib.rs"), &cand.source)
            .map_err(|e| format!("failed to write staged src/lib.rs: {e}"))?;
        let specs = vec![OracleItemSpec::with_fuel(cand.fn_name.clone(), fuel)];
        let cfg = DifftestOracleConfig {
            corpus_root: staging_dir.clone(),
            capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
            miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
            anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
            rustc_wrapper: None,
            toolchain: toolchain.clone(),
        };
        let run = run_linked_difftest_oracle_pipeline(&cfg, &specs)?;
        let report = run
            .report
            .items
            .iter()
            .find(|it| it.name == cand.fn_name)
            .cloned()
            .ok_or_else(|| format!("oracle pipeline returned no report for `{}`", cand.fn_name))?;
        let confirm_src = run
            .report
            .confirm_module_path
            .as_ref()
            .and_then(|p| fs::read_to_string(p).ok())
            .unwrap_or_default();
        let mir_neighborhood =
            extract_mir_neighborhood(&staging_dir, &run.report.crate_camel, &report.name);
        let kernel_confirm_theorems = extract_confirm_theorems(&confirm_src, &report.name);
        Ok(LiveCandidateEvaluation {
            report,
            mir_neighborhood,
            kernel_confirm_theorems,
        })
    })();
    let _ = fs::remove_dir_all(&staging_dir);
    result
}

/// Minimize a divergent [`GeneratedMiriCandidate`]'s mutator chain against the
/// live Miri + Anneal oracle pipeline.
///
/// Every proper subsequence (including the unmutated seed `[]`) that compiles is
/// judged by a real oracle run ([`evaluate_candidate_live`], with the step fuel
/// of `original_report`) in a fresh single-candidate staging crate; there are no
/// hard-coded shortcuts. Queries
/// of a program that was already judged are answered by a [`MemoizedOracle`]
/// keyed by `fn_source` (which, with the fixed `fn_name`, determines the staged
/// program), and `executed_oracle_runs` counts only the runs that executed. The
/// MIR neighborhood and kernel confirmation theorems of a minimized candidate
/// come from the oracle run that accepted it.
pub fn minimize_miri_candidate_mutations(
    cand: &GeneratedMiriCandidate,
    seeds: &[&str],
    original_report: &ItemOracleReport,
    anneal_repo_root: Option<&Path>,
) -> Result<MiriCandidateShrinkResult, String> {
    let toolchain = MiriToolchain::resolve(None, None, None)?;
    // Artifacts of signature-matching oracle runs, keyed by evaluated `fn_source`.
    let mut artifacts_by_source: BTreeMap<String, (String, String)> = BTreeMap::new();
    let eval_live = |sub_cand: &GeneratedMiriCandidate| -> Option<ItemOracleReport> {
        let live = match evaluate_candidate_live(
            sub_cand,
            original_report.fuel,
            &toolchain,
            anneal_repo_root,
        ) {
            Ok(live) => live,
            Err(e) => {
                eprintln!(
                    "miri-difftest: shrink oracle run failed for `{}` ({} mutators): {e}",
                    sub_cand.fn_name,
                    sub_cand.applied_mutators.len()
                );
                return None;
            }
        };
        if miri_report_is_oracle_failure(&live.report) {
            let verdict = format!("{:?}", live.report.verdict);
            eprintln!(
                "miri-difftest: shrink oracle could not judge `{}` ({} mutators): {}",
                sub_cand.fn_name,
                sub_cand.applied_mutators.len(),
                verdict.chars().take(400).collect::<String>()
            );
        }
        if discrepancy_signatures_match(original_report, &live.report) {
            artifacts_by_source.insert(
                sub_cand.fn_source.clone(),
                (live.mir_neighborhood, live.kernel_confirm_theorems),
            );
        }
        Some(live.report)
    };
    let mut memo = MemoizedOracle::new(eval_live);
    let mut res = minimize_miri_candidate_mutations_with(cand, seeds, original_report, |c| {
        memo.eval(c.fn_source.clone(), c)
    });
    res.executed_oracle_runs = memo.executed_runs;
    drop(memo);
    if res.is_reduced() {
        let (mir_neighborhood, kernel_confirm_theorems) = artifacts_by_source
            .remove(&res.minimized_candidate.fn_source)
            .ok_or_else(|| {
                format!(
                    "accepted minimized candidate `{}` has no recorded oracle artifacts",
                    res.minimized_candidate.fn_name
                )
            })?;
        res.mir_neighborhood = Some(mir_neighborhood);
        res.kernel_confirm_theorems = Some(kernel_confirm_theorems);
    }
    Ok(res)
}

/// Shrink the mutator chain of the divergent candidate `cand` (reported as
/// `item_rep` by the batch run) against the live oracle, returning the result
/// together with the `shrink_status` recorded in its finding bundle.
fn shrink_divergent_miri_candidate(
    cand: &GeneratedMiriCandidate,
    seed_refs: &[&str],
    item_rep: &ItemOracleReport,
    anneal_repo_root: Option<&Path>,
) -> (Option<MiriCandidateShrinkResult>, String) {
    if cand.applied_mutators.is_empty() {
        return (
            None,
            MiriShrinkStatus::SkippedNotApplicable.slug().to_string(),
        );
    }
    match minimize_miri_candidate_mutations(cand, seed_refs, item_rep, anneal_repo_root) {
        Ok(res) => {
            let status = res.status.slug().to_string();
            (Some(res), status)
        }
        Err(e) => (None, format!("skipped_shrinker_error: {e}")),
    }
}

fn format_miri_excerpt(outcome: &MiriOutcome, translated_pos: Option<&str>) -> String {
    match outcome {
        MiriOutcome::PassUnit => "MIRI_PASS:unit".to_string(),
        MiriOutcome::PassScalar { bits, size_bytes } => {
            format!("MIRI_PASS:scalar:{bits}:{size_bytes}")
        }
        MiriOutcome::Panic { pos, message } => {
            let loc = translated_pos
                .map(str::to_string)
                .or_else(|| pos.as_ref().map(SourcePos::display_short))
                .unwrap_or_else(|| "<unknown>".to_string());
            format!("thread 'main' panicked at {loc}:\n{message}")
        }
        MiriOutcome::Ub { pos, message } => {
            let loc = translated_pos
                .map(str::to_string)
                .or_else(|| pos.as_ref().map(SourcePos::display_short))
                .unwrap_or_else(|| "<unknown>".to_string());
            format!("error: Undefined Behavior: {message}\n  --> {loc}")
        }
        MiriOutcome::OracleError(err) => format!("Miri oracle error: {err}"),
    }
}

fn translate_pos_to_repro(
    pos: &SourcePos,
    batch_start_line: u32,
    repro_start_line: u32,
) -> SourcePos {
    if source_files_match(&pos.file, "src/lib.rs") {
        let line = if pos.line >= batch_start_line {
            pos.line - batch_start_line + repro_start_line
        } else {
            pos.line
        };
        SourcePos {
            file: "src/lib.rs".to_string(),
            line,
            col: pos.col,
        }
    } else {
        pos.clone()
    }
}

fn translate_span_to_repro(
    span: &SourceSpan,
    batch_start_line: u32,
    repro_start_line: u32,
) -> SourceSpan {
    if source_files_match(&span.file, "src/lib.rs") {
        // Subtract before adding: `batch_start_line` may be smaller than
        // `repro_start_line` (for example when the span already comes from a
        // single-candidate run), and `u32` cannot represent a negative delta.
        // Lines below `batch_start_line` (preamble lines or `end_line == 0`)
        // stay at their original line numbers.
        let start_line = if span.start_line >= batch_start_line {
            span.start_line - batch_start_line + repro_start_line
        } else {
            span.start_line
        };
        let end_line = if span.end_line >= batch_start_line {
            span.end_line - batch_start_line + repro_start_line
        } else {
            span.end_line
        };
        SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line,
            start_col: span.start_col,
            end_line,
            end_col: span.end_col,
        }
    } else {
        span.clone()
    }
}

fn extract_mir_neighborhood(corpus_root: &Path, crate_camel: &str, fn_name: &str) -> String {
    let mir_path = corpus_root
        .join(".anneal/generated/Mir")
        .join(crate_camel)
        .join(format!("{fn_name}.lean"));
    let Ok(raw) = fs::read_to_string(&mir_path) else {
        return format!("(Mir module {} not found)", mir_path.display());
    };
    let lines: Vec<&str> = raw.lines().collect();
    let max_lines = 80usize;
    if lines.len() <= max_lines {
        raw
    } else {
        let mut snippet = lines[..max_lines].join("\n");
        snippet.push_str(&format!(
            "\n-- ... ({} additional lines in {}) ...\n",
            lines.len() - max_lines,
            mir_path.display()
        ));
        snippet
    }
}

/// The `namespace <ident> ... end <ident>` section of `confirm_src` enclosing
/// byte offset `theorem_pos` (the whole source when there is none), so a
/// multi-group `MiriOracleConfirm.lean` yields only the definitions of the
/// group whose kernel check accepted the theorem.
fn enclosing_confirm_namespace_slice<'a>(confirm_src: &'a str, theorem_pos: usize) -> &'a str {
    let prefix = &confirm_src[..theorem_pos];
    let ns_pos = prefix
        .rfind("\nnamespace ")
        .map(|i| i + 1)
        .or_else(|| prefix.starts_with("namespace ").then_some(0));
    let Some(ns_start) = ns_pos else {
        return confirm_src;
    };
    let after_kw = &confirm_src[ns_start + "namespace ".len()..];
    let ns_ident = after_kw.lines().next().unwrap_or("").trim();
    if ns_ident.is_empty() {
        return confirm_src;
    }
    let end_marker = format!("\nend {ns_ident}");
    if let Some(rel_end) = confirm_src[theorem_pos..].find(&end_marker) {
        let end_idx = theorem_pos + rel_end + end_marker.len();
        &confirm_src[ns_start..end_idx]
    } else {
        &confirm_src[ns_start..]
    }
}

/// Extract the `confirm_tag_<fn_name>`, `confirm_probe_<fn_name>`, and (when
/// present) `confirm_frame_<fn_name>` and `confirm_message_<fn_name>` theorems
/// from `MiriOracleConfirm.lean` source, preceded by every confirm-module
/// definition that they use: the synthetic constructor stub (when
/// `linkedCallees` refers to it), `linkedCallees`, the run probe in
/// [`PROBE_EXEC_LEAN`], and the panic-origin probe in
/// [`PANIC_MESSAGE_PROBE_LEAN`] (when a frame or message theorem is present),
/// all taken from the namespace section that holds `fn_name`'s theorems
/// ([`enclosing_confirm_namespace_slice`]). The snippet therefore names no
/// definition local to the confirm module that it does not also contain.
fn extract_confirm_theorems(confirm_src: &str, fn_name: &str) -> String {
    let theorem_headers = [
        format!("theorem confirm_tag_{fn_name} :"),
        format!("theorem confirm_probe_{fn_name} :"),
        format!("theorem confirm_frame_{fn_name} :"),
        format!("theorem confirm_message_{fn_name} :"),
    ];
    let Some(first_theorem_pos) = theorem_headers
        .iter()
        .filter_map(|h| confirm_src.find(h.as_str()))
        .min()
    else {
        return String::new();
    };
    // Narrow to the enclosing `namespace ... end ...` group that confirmed
    // `fn_name`, so multi-chunk / per-item-fallback `MiriOracleConfirm.lean`
    // modules preserve each group's exact kernel-checked `linkedCallees`.
    let scope_src = enclosing_confirm_namespace_slice(confirm_src, first_theorem_pos);

    // Each block runs from its header to the first blank line; the generated
    // blocks contain no blank lines.
    let extract_block = |header: &str| -> Option<String> {
        let start_idx = scope_src.find(header)?;
        let rest = &scope_src[start_idx..];
        let end_rel = rest.find("\n\n").map(|i| i + 1).unwrap_or(rest.len());
        Some(rest[..end_rel].trim().to_string())
    };
    let first_line = |block: &'static str| block.lines().next().unwrap_or(block);
    let tag_block = extract_block(&theorem_headers[0]);
    let probe_block = extract_block(&theorem_headers[1]);
    let frame_block = extract_block(&theorem_headers[2]);
    let message_block = extract_block(&theorem_headers[3]);
    if tag_block.is_none()
        && probe_block.is_none()
        && frame_block.is_none()
        && message_block.is_none()
    {
        return String::new();
    }
    let callees_block = extract_block("def linkedCallees : List CapturedMir :=");
    let stub_block = match &callees_block {
        Some(callees) if callees.contains(FMT_ARGUMENTS_CTOR_STUB_NAME) => {
            extract_block(first_line(FMT_ARGUMENTS_CTOR_STUB_LEAN))
        }
        _ => None,
    };
    let has_origin_theorem = frame_block.is_some() || message_block.is_some();
    let probe_exec_block = if probe_block.is_some() || has_origin_theorem {
        extract_block(first_line(PROBE_EXEC_LEAN))
    } else {
        None
    };
    let message_probe_block = if has_origin_theorem {
        extract_block(first_line(PANIC_MESSAGE_PROBE_LEAN))
    } else {
        None
    };
    [
        stub_block,
        callees_block,
        probe_exec_block,
        message_probe_block,
        tag_block,
        probe_block,
        frame_block,
        message_block,
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<_>>()
    .join("\n\n")
}

/// Collect every identifier token in `tokens`, recursing into delimited groups.
fn collect_ident_tokens(tokens: proc_macro2::TokenStream, out: &mut BTreeSet<String>) {
    for tt in tokens {
        match tt {
            proc_macro2::TokenTree::Ident(id) => {
                out.insert(id.to_string());
            }
            proc_macro2::TokenTree::Group(g) => collect_ident_tokens(g.stream(), out),
            proc_macro2::TokenTree::Punct(_) | proc_macro2::TokenTree::Literal(_) => {}
        }
    }
}

/// AST visitor that indexes the function bodies, `impl` blocks, and
/// `macro_rules!` items of a parsed crate for
/// [`staged_helper_fns_reachable_from_candidates`].
///
/// Walking via [`syn::visit::Visit`] reaches items nested at arbitrary depth
/// (including inside inner `{ ... }`, `unsafe { ... }`, `if`/`else`, `loop`,
/// `match`, inline `mod`, or `impl` method blocks), not only direct
/// `func.block.stmts` items. Same-named free/nested functions share one
/// `fn_bodies` entry holding the union of their signatures and bodies, so
/// reachability over-approximates instead of following only the last body
/// indexed. `impl` blocks with a named self type are indexed in `aux_tokens`
/// under their self-type identifiers rather than merging their method names
/// (such as `drop`) across unrelated `impl` blocks in `fn_bodies`.
struct FnAndAuxCollector<'a> {
    fn_bodies: &'a mut BTreeMap<String, proc_macro2::TokenStream>,
    aux_tokens: &'a mut BTreeMap<String, Vec<proc_macro2::TokenStream>>,
    impl_method_names: &'a mut BTreeSet<String>,
}

impl<'ast> syn::visit::Visit<'ast> for FnAndAuxCollector<'_> {
    fn visit_item_fn(&mut self, func: &'ast syn::ItemFn) {
        self.fn_bodies
            .entry(func.sig.ident.to_string())
            .or_default()
            .extend(quote::ToTokens::to_token_stream(func));
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_trait_item_fn(&mut self, method: &'ast syn::TraitItemFn) {
        if method.default.is_some() {
            self.fn_bodies
                .entry(method.sig.ident.to_string())
                .or_default()
                .extend(quote::ToTokens::to_token_stream(method));
        }
        syn::visit::visit_trait_item_fn(self, method);
    }

    fn visit_item_macro(&mut self, mac: &'ast syn::ItemMacro) {
        if let Some(id) = &mac.ident {
            self.aux_tokens
                .entry(id.to_string())
                .or_default()
                .push(quote::ToTokens::to_token_stream(&mac.mac));
        }
        syn::visit::visit_item_macro(self, mac);
    }

    fn visit_item_impl(&mut self, imp: &'ast syn::ItemImpl) {
        let mut self_idents = BTreeSet::new();
        collect_ident_tokens(
            quote::ToTokens::to_token_stream(&imp.self_ty),
            &mut self_idents,
        );
        let ts = quote::ToTokens::to_token_stream(imp);
        for id in &self_idents {
            self.aux_tokens.entry(id.clone()).or_default().push(ts.clone());
        }
        for impl_item in &imp.items {
            if let syn::ImplItem::Fn(method) = impl_item {
                self.impl_method_names.insert(method.sig.ident.to_string());
                if self_idents.is_empty() {
                    self.fn_bodies
                        .entry(method.sig.ident.to_string())
                        .or_default()
                        .extend(quote::ToTokens::to_token_stream(method));
                }
            }
        }
        syn::visit::visit_item_impl(self, imp);
    }
}

fn collect_fn_and_aux_items(
    items: &[syn::Item],
    fn_bodies: &mut BTreeMap<String, proc_macro2::TokenStream>,
    aux_tokens: &mut BTreeMap<String, Vec<proc_macro2::TokenStream>>,
    impl_method_names: &mut BTreeSet<String>,
) {
    let mut collector = FnAndAuxCollector {
        fn_bodies,
        aux_tokens,
        impl_method_names,
    };
    for item in items {
        syn::visit::Visit::visit_item(&mut collector, item);
    }
}

/// Compute `(reached_fns, reached_aux)` for `items`: the set of functions in
/// `fn_bodies` and the set of auxiliary type/macro names in `aux_tokens`
/// transitively reached from `items`.
fn staged_fns_and_aux_reachable_from_candidates(
    lib_rs: &str,
    items: &[OracleItemSpec],
) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut fn_bodies: BTreeMap<String, proc_macro2::TokenStream> = BTreeMap::new();
    let mut aux_tokens: BTreeMap<String, Vec<proc_macro2::TokenStream>> = BTreeMap::new();
    let mut impl_method_names: BTreeSet<String> = BTreeSet::new();
    if let Ok(file) = syn::parse_file(lib_rs) {
        collect_fn_and_aux_items(
            &file.items,
            &mut fn_bodies,
            &mut aux_tokens,
            &mut impl_method_names,
        );
    }
    let item_seeds: Vec<String> = items
        .iter()
        .map(|spec| spec.name.clone())
        .filter(|name| fn_bodies.contains_key(name))
        .collect();
    let mut worklist: Vec<String> = if !item_seeds.is_empty() {
        item_seeds
    } else {
        let candidate_portion = lib_rs
            .split_once(MIRI_CORPUS_MODULE_PREAMBLE)
            .map_or(lib_rs, |(_, rest)| rest);
        let mut mentioned = BTreeSet::new();
        if let Ok(tokens) = candidate_portion.parse::<proc_macro2::TokenStream>() {
            collect_ident_tokens(tokens, &mut mentioned);
        }
        mentioned
            .into_iter()
            .filter(|name| fn_bodies.contains_key(name) || aux_tokens.contains_key(name))
            .collect()
    };
    let mut visited_nodes = BTreeSet::new();
    let mut reached_fns = BTreeSet::new();
    let mut reached_aux = BTreeSet::new();
    while let Some(name) = worklist.pop() {
        if !visited_nodes.insert(name.clone()) {
            continue;
        }
        let mut callees = BTreeSet::new();
        if let Some(body_ts) = fn_bodies.get(&name) {
            reached_fns.insert(name.clone());
            collect_ident_tokens(body_ts.clone(), &mut callees);
        }
        if let Some(aux_list) = aux_tokens.get(&name) {
            reached_aux.insert(name.clone());
            for ts in aux_list {
                collect_ident_tokens(ts.clone(), &mut callees);
            }
        }
        worklist.extend(callees.into_iter().filter(|callee| {
            (fn_bodies.contains_key(callee) || aux_tokens.contains_key(callee))
                && !visited_nodes.contains(callee)
        }));
    }
    (reached_fns, reached_aux)
}

/// Names of the functions of a staged `src/lib.rs` (top-level and nested; see
/// [`collect_fn_and_aux_items`]) that the evaluated `items` (or the candidate
/// portion after [`MIRI_CORPUS_MODULE_PREAMBLE`] when `items` is empty) reach,
/// transitively.
///
/// When `items` names one or more parsed functions in `lib_rs`, the reachability
/// worklist starts from those functions directly so evaluating a subset of
/// `tests/miri-diff/corpus/src/lib.rs` links only the model-marked helpers that
/// subset actually calls. When `items` is empty or does not match parsed
/// functions in `lib_rs`, the worklist starts from identifiers in the text after
/// [`MIRI_CORPUS_MODULE_PREAMBLE`] (or the whole crate if the preamble is not
/// embedded verbatim).
fn staged_helper_fns_reachable_from_candidates(
    lib_rs: &str,
    items: &[OracleItemSpec],
) -> BTreeSet<String> {
    staged_fns_and_aux_reachable_from_candidates(lib_rs, items).0
}

fn create_staging_dir(label: &str) -> Result<PathBuf, String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = env::temp_dir().join(format!(
        "anneal_miri_eval_{label}_{}_{stamp}",
        std::process::id()
    ));
    fs::create_dir_all(dir.join("src"))
        .map_err(|e| format!("failed to create staging dir {}: {e}", dir.display()))?;
    let cargo_toml = "\
[package]
name = \"miri_diff_corpus\"
version = \"0.1.0\"
edition = \"2024\"
publish = false

[lib]
path = \"src/lib.rs\"

[workspace]
";
    fs::write(dir.join("Cargo.toml"), cargo_toml)
        .map_err(|e| format!("failed to write staged Cargo.toml: {e}"))?;
    Ok(dir)
}

fn escape_lean_string(raw: &str) -> String {
    raw.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

fn resolve_lake_bin() -> PathBuf {
    for var in ["ANNEAL_LAKE", "LAKE"] {
        if let Ok(val) = env::var(var)
            && !val.trim().is_empty()
        {
            return PathBuf::from(val.trim());
        }
    }
    if let Some(toolchain_root) = cargo_anneal::setup::resolve_installed_toolchain() {
        let bundled = toolchain_root.join("lean/bin/lake");
        if bundled.is_file() {
            return bundled;
        }
    }
    if let Ok(home) = env::var("HOME") {
        let home_path = PathBuf::from(home);
        for rel in [
            ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lake",
            ".elan/bin/lake",
            ".anneal/toolchain/lean/bin/lake",
        ] {
            let candidate = home_path.join(rel);
            if candidate.is_file() {
                return candidate;
            }
        }
    }
    PathBuf::from("lake")
}

/// Maximum number of corpus candidate items per Stage 1 `Mir.*` build chunk and
/// `MiriOracleProbe_{chunk_idx:03}.lean` evaluation module.
pub const MIRI_PROBE_CHUNK_SIZE: usize = 64;

/// Maximum number of candidate items per Stage 2 `MiriOracleConfirm_{chunk_idx:03}.lean`
/// kernel confirmation chunk.
pub const MIRI_CONFIRM_CHUNK_SIZE: usize = 16;

/// Maximum consecutive failed per-candidate fallback runs (with zero fallback
/// successes so far) before [`run_isolated_miri_stage`] trips its circuit
/// breaker and stops per-candidate retries (retrying the rest of the chunk
/// once as a group before declaring a systematic failure).
pub const MIRI_FALLBACK_CIRCUIT_BREAKER: usize = 4;

/// Maps effective total / available memory (in KiB) to a `lake env lean` chunk
/// worker count for `miri-difftest`: 1 worker when available memory is below
/// 24 GiB (or unknown) or total memory is at most 36 GiB, at most 2 workers up
/// to 64 GiB total (or below 48 GiB available), and at most 4 workers above that.
pub fn miri_lean_jobs_for_memory(total_kib: Option<u64>, avail_kib: Option<u64>) -> usize {
    const GIB: u64 = 1024 * 1024;
    if total_kib.is_none() && avail_kib.is_none() {
        return 1;
    }
    let by_total = match total_kib {
        None => 4,
        Some(t) if t <= 36 * GIB => 1,
        Some(t) if t <= 64 * GIB => 2,
        Some(_) => 4,
    };
    let by_avail = match avail_kib {
        None => 1,
        Some(a) if a < 24 * GIB => 1,
        Some(a) if a < 48 * GIB => 2,
        Some(_) => 4,
    };
    by_total.min(by_avail)
}

/// Pure helper for [`resolve_miri_lean_jobs`] accepting explicit `ANNEAL_MIRI_LEAN_JOBS`
/// and effective memory values for deterministic testing.
pub fn resolve_miri_lean_jobs_with_env(
    anneal_miri_lean_jobs: Option<&str>,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
) -> usize {
    if let Some(val) = anneal_miri_lean_jobs
        && let Ok(parsed) = val.trim().parse::<usize>()
        && parsed >= 1
    {
        return parsed.min(8);
    }
    miri_lean_jobs_for_memory(total_kib, avail_kib)
}

/// Resolves the maximum number of concurrent `lake env lean` chunk workers (and
/// sequential chunk `lake build` threads) for `miri-difftest` from
/// `ANNEAL_MIRI_LEAN_JOBS` (capped at 8) or host `/proc/meminfo` intersected
/// with enclosing cgroup v2 memory limits (`memory.max` & `memory.stat` `anon + shmem`).
pub fn resolve_miri_lean_jobs() -> usize {
    let override_env = env::var("ANNEAL_MIRI_LEAN_JOBS").ok();
    let (total_kib, avail_kib) = probe_effective_memory_kib();
    resolve_miri_lean_jobs_with_env(override_env.as_deref(), total_kib, avail_kib)
}

/// `LEAN_NUM_THREADS` budgets for `miri-difftest`'s sequential `lake build`
/// invocations (Lean v4.34.1 `lake build` has no `-j` flag).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MiriLakeBuildThreads {
    /// Stage 0 group 0: `SymbolicEval`, `Mir.Common`, and (when few) helpers.
    base: usize,
    /// Stage 0 helper overflow chunks and every Stage 1a corpus `Mir.*` chunk
    /// (or per-candidate fallback) build.
    mir_chunks: usize,
}

fn parse_positive_jobs(raw: Option<&str>) -> Option<usize> {
    raw.and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
}

/// Pure helper for [`resolve_miri_lake_build_threads`]:
///
/// - `ANNEAL_MIRI_LEAN_JOBS` (capped at 8) sets both budgets;
/// - otherwise `CARGO_ANNEAL_LAKE_JOBS` (capped at 16) sets the base budget;
/// - otherwise the base budget is [`resolve_default_lake_jobs`] for the
///   effective memory and CPU budget, lowered (never raised) by a caller's
///   `LEAN_NUM_THREADS`;
/// - absent `ANNEAL_MIRI_LEAN_JOBS`, corpus `Mir.*` chunk builds use at most
///   4 threads.
fn resolve_miri_lake_build_threads_with_env(
    anneal_miri_lean_jobs: Option<&str>,
    cargo_anneal_lake_jobs: Option<&str>,
    caller_lean_num_threads: Option<&str>,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    cpu_cores: usize,
) -> MiriLakeBuildThreads {
    if let Some(n) = parse_positive_jobs(anneal_miri_lean_jobs) {
        let n = n.min(8);
        return MiriLakeBuildThreads {
            base: n,
            mir_chunks: n,
        };
    }
    let base = match parse_positive_jobs(cargo_anneal_lake_jobs) {
        Some(n) => n.min(16),
        None => {
            let mem_jobs = resolve_default_lake_jobs(total_kib, avail_kib, cpu_cores);
            match parse_positive_jobs(caller_lean_num_threads) {
                Some(caller) => mem_jobs.min(caller),
                None => mem_jobs,
            }
        }
    };
    MiriLakeBuildThreads {
        base,
        mir_chunks: base.min(4),
    }
}

/// Resolves [`MiriLakeBuildThreads`] from `ANNEAL_MIRI_LEAN_JOBS`,
/// `CARGO_ANNEAL_LAKE_JOBS`, `LEAN_NUM_THREADS`, and the host / cgroup memory
/// and CPU budget.
fn resolve_miri_lake_build_threads() -> MiriLakeBuildThreads {
    let (total_kib, avail_kib) = probe_effective_memory_kib();
    let cpu_cores = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4);
    resolve_miri_lake_build_threads_with_env(
        env::var("ANNEAL_MIRI_LEAN_JOBS").ok().as_deref(),
        env::var("CARGO_ANNEAL_LAKE_JOBS").ok().as_deref(),
        env::var("LEAN_NUM_THREADS").ok().as_deref(),
        total_kib,
        avail_kib,
        cpu_cores,
    )
}

/// Lean module that every `MiriOracleProbe*` / `MiriOracleConfirm*` module imports.
const MIRI_SYMBOLIC_EVAL_MODULE: &str = "Anneal.Rustc.V2026_06_01.SymbolicEval";

/// Plans Stage 0's shared-base `lake build` invocations.
///
/// Group 0 builds [`MIRI_SYMBOLIC_EVAL_MODULE`], `Mir.Common` (when
/// generated), and the deduplicated helper `Mir.<suffix>` modules when there
/// are at most [`MIRI_PROBE_CHUNK_SIZE`] of them; otherwise the helpers follow
/// in groups of at most `MIRI_PROBE_CHUNK_SIZE`. The umbrella `Mir` library
/// target is never emitted: it would build every corpus candidate module in
/// one Lake invocation (the Campaign #13 OOM).
fn plan_miri_stage0_build_groups(
    has_mir_common: bool,
    helper_module_suffixes: &[String],
) -> Vec<Vec<String>> {
    let mut base: Vec<String> = vec![MIRI_SYMBOLIC_EVAL_MODULE.to_string()];
    if has_mir_common {
        base.push("Mir.Common".to_string());
    }
    let mut helpers: Vec<String> = Vec::new();
    for suffix in helper_module_suffixes {
        let suffix = suffix.trim();
        if suffix.is_empty() {
            continue;
        }
        let target = format!("Mir.{suffix}");
        if !base.contains(&target) && !helpers.contains(&target) {
            helpers.push(target);
        }
    }
    if helpers.len() <= MIRI_PROBE_CHUNK_SIZE {
        base.extend(helpers);
        return vec![base];
    }
    let mut groups = vec![base];
    groups.extend(helpers.chunks(MIRI_PROBE_CHUNK_SIZE).map(<[String]>::to_vec));
    groups
}

/// Deduplicated corpus `Mir.<cand_suffix>` targets for one Stage 1a chunk
/// (falling back to `Mir.<crate_camel>.<item>` for an empty suffix, exactly as
/// [`render_linked_anneal_probe_module`] imports them).
fn miri_candidate_build_targets(
    crate_camel: &str,
    chunk: &[(OracleItemSpec, String)],
) -> Vec<String> {
    let mut targets: Vec<String> = Vec::with_capacity(chunk.len());
    for (item, cand_suffix) in chunk {
        let suffix = if cand_suffix.is_empty() {
            format!("{crate_camel}.{}", item.name)
        } else {
            cand_suffix.clone()
        };
        let target = format!("Mir.{suffix}");
        if !targets.contains(&target) {
            targets.push(target);
        }
    }
    targets
}

fn contains_bracketed_error_colon(lower: &str) -> bool {
    let mut rest = lower;
    while let Some(idx) = rest.find("error[") {
        let after = &rest[idx + "error[".len()..];
        if let Some(close_idx) = after.find("]:") {
            let code = &after[..close_idx];
            if !code.is_empty()
                && code
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
            {
                return true;
            }
        }
        rest = after;
    }
    false
}

/// Whether `line` is a Lake / Lean / rustc diagnostic worth surfacing: a Lake
/// `✖` failure marker, a Lake / Lean `error:` line, a bracketed compiler
/// `error[<code>]:` line, or a fatal Lean / Rust runtime crash line (`out of memory`,
/// `LEAN ASSERTION VIOLATION`, `PANIC at`, `panicked at`) that lacks `error:`.
fn is_lean_diag_highlight_line(line: &str) -> bool {
    if line.contains('✖') {
        return true;
    }
    let lower = line.to_ascii_lowercase();
    lower.contains("error:")
        || contains_bracketed_error_colon(&lower)
        || lower.trim() == "out of memory"
        || lower.contains("out of memory:")
        || lower.contains(": out of memory")
        || lower.contains("lean panic:")
        || lower.contains("lean assertion violation")
        || lower.contains("panic at ")
        || lower.contains("panicked at ")
}

/// Extracts up to `max_lines` unique diagnostic lines (`✖` or `error:`) across
/// `stdout` and `stderr`, preserving order.
pub(crate) fn extract_lean_error_lines(
    stdout: &str,
    stderr: &str,
    max_lines: usize,
) -> Vec<String> {
    if max_lines == 0 {
        return Vec::new();
    }
    let mut matched: Vec<String> = Vec::new();
    for raw in stdout.lines().chain(stderr.lines()) {
        let trimmed = raw.trim_end_matches('\r');
        if is_lean_diag_highlight_line(trimmed) && !matched.iter().any(|m| m == trimmed) {
            matched.push(trimmed.to_string());
        }
    }
    if matched.len() > max_lines {
        matched.split_off(matched.len() - max_lines)
    } else {
        matched
    }
}

/// Truncates a multi-line Lean log to its first 20 and last 20 lines while
/// preserving any `✖` / `error:` lines that would otherwise be elided from the middle.
fn truncate_lean_diag(msg: &str) -> String {
    let lines: Vec<&str> = msg.lines().collect();
    if lines.len() <= 40 {
        return msg.to_string();
    }
    let middle = &lines[20..lines.len() - 20];
    let middle_errors: Vec<&str> = middle
        .iter()
        .copied()
        .filter(|l| is_lean_diag_highlight_line(l))
        .take(20)
        .collect();
    if middle_errors.is_empty() {
        format!(
            "{}\n... ({} lines elided) ...\n{}",
            lines[..20].join("\n"),
            middle.len(),
            lines[lines.len() - 20..].join("\n")
        )
    } else {
        format!(
            "{}\n... ({} lines elided; key error lines preserved below) ...\n{}\n... (end of preserved middle errors) ...\n{}",
            lines[..20].join("\n"),
            middle.len(),
            middle_errors.join("\n"),
            lines[lines.len() - 20..].join("\n")
        )
    }
}

/// Formats a `lake` / `lean` subprocess failure including highlighted `✖` / `error:`
/// lines as well as both `stdout` and `stderr` (since Lake 5 logs build failures to `stdout`).
pub(crate) fn format_lean_command_failure(header: &str, stdout: &str, stderr: &str) -> String {
    let highlights = extract_lean_error_lines(stdout, stderr, 30);
    let mut out = String::from(header);
    if !highlights.is_empty() {
        out.push_str("\nerror_lines:\n");
        out.push_str(&highlights.join("\n"));
    }
    out.push_str("\nstdout:\n");
    if stdout.trim().is_empty() {
        out.push_str("(empty)");
    } else {
        out.push_str(&truncate_lean_diag(stdout.trim_end()));
    }
    out.push_str("\nstderr:\n");
    if stderr.trim().is_empty() {
        out.push_str("(empty)");
    } else {
        out.push_str(&truncate_lean_diag(stderr.trim_end()));
    }
    out
}

fn run_lake_build_with_bin_and_threads(
    lake_bin: &Path,
    dot_anneal_dir: &Path,
    targets: &[&str],
    threads: Option<usize>,
) -> Result<(), String> {
    let mut cmd = build_lake_build_command(lake_bin, dot_anneal_dir);
    if let Some(n) = threads {
        cmd.env("LEAN_NUM_THREADS", n.max(1).to_string());
    }
    for target in targets {
        cmd.arg(target);
    }
    let output = cmd.output().map_err(|err| {
        format!(
            "failed to execute '{}' in {}: {}",
            lake_bin.display(),
            dot_anneal_dir.display(),
            err
        )
    })?;
    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format_lean_command_failure(
            &format!(
                "lake build failed with status {} in {}",
                output.status,
                dot_anneal_dir.display()
            ),
            &stdout,
            &stderr,
        ));
    }
    Ok(())
}

fn find_executable_in_caller_or_system_path(tool_name: &str) -> Option<PathBuf> {
    for var in ["ANNEAL_CALLER_PATH", "PATH"] {
        if let Some(path_var) = env::var_os(var) {
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
        }
    }
    if let Ok(home) = env::var("HOME") {
        let cargo_bin_tool = PathBuf::from(home).join(".cargo/bin").join(tool_name);
        if cargo_bin_tool.is_file() {
            return Some(cargo_bin_tool);
        }
    }
    None
}

fn resolve_cargo_bin() -> PathBuf {
    if let Ok(c) = env::var("CARGO")
        && !c.trim().is_empty()
    {
        return PathBuf::from(c.trim());
    }
    if let Ok(home) = env::var("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/cargo");
        if candidate.is_file() {
            return candidate;
        }
    }
    PathBuf::from("cargo")
}

fn ensure_rustc_wrapper(
    driver_cfg: &CaptureDriverConfig,
    anneal_repo_root: Option<&Path>,
) -> Result<PathBuf, String> {
    let resolved = resolve_rustc_wrapper(driver_cfg);
    if driver_cfg.rustc_wrapper.is_some() || resolved.is_file() {
        return Ok(resolved);
    }
    if resolved.components().count() == 1
        && let Some(name) = resolved.to_str()
        && let Some(found) = find_executable_in_caller_or_system_path(name)
    {
        return Ok(found);
    }
    if let Some(root) = anneal_repo_root.or_else(|| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
    }) {
        let exe_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
        let built = root.join("target/debug").join(&exe_name);
        if built.is_file() {
            return Ok(built);
        }
        let cargo_bin = resolve_cargo_bin();
        let output = Command::new(&cargo_bin)
            .args(["build", "-p", "anneal-rustc-capture", "--locked"])
            .current_dir(root)
            .output()
            .map_err(|e| format!("failed to invoke cargo build for anneal-rustc-capture: {e}"))?;
        if output.status.success() && built.is_file() {
            return Ok(built);
        }
    }
    Ok(resolved)
}

/// Partition captured `Subject` `(short_fn_name, item_module_suffix)` pairs into:
/// 1. `captured_candidates`: map from candidate short name to its `Mir.<suffix>` suffix, and
/// 2. `helper_module_suffixes`: deduplicated, deterministically sorted list of intra-crate
///    helper callee suffixes (such as `MiriDiffCorpus.helper_add_ten`), strictly excluding
///    all root candidates in `items`.
fn partition_subject_callees(
    crate_camel: &str,
    subject_pairs: &[(String, String)],
    items: &[OracleItemSpec],
) -> (BTreeMap<String, String>, Vec<String>) {
    let spec_names: BTreeSet<&str> = items.iter().map(|i| i.name.as_str()).collect();
    let mut captured_candidates: BTreeMap<String, String> = BTreeMap::new();
    let mut helpers: BTreeSet<String> = BTreeSet::new();

    for (short, suffix) in subject_pairs {
        let expected_top_suffix = format!("{crate_camel}.{short}");
        if spec_names.contains(short.as_str()) {
            if suffix == &expected_top_suffix || !captured_candidates.contains_key(short) {
                captured_candidates.insert(short.clone(), suffix.clone());
            }
            if suffix != &expected_top_suffix {
                helpers.insert(suffix.clone());
            }
        } else {
            helpers.insert(suffix.clone());
        }
    }

    // Never allow a root candidate's own module suffix into `linkedCallees`.
    for cand_suffix in captured_candidates.values() {
        helpers.remove(cand_suffix);
    }

    (captured_candidates, helpers.into_iter().collect())
}

/// Subset of the batch's `helper_module_suffixes` that `MiriOracleConfirm.lean`
/// links for `entries`.
///
/// - An `impl` method on a self type in `aux_tokens` (such as
///   `<Crate>.<SelfTy>_as_core_ops_Drop_drop`) is kept only when `<SelfTy>` is
///   transitively reached from `entries`, so one candidate's `Drop` impl never
///   causes `MiriOracleConfirm.lean` to link unrelated `Drop` impls from other
///   candidates or the preamble.
/// - An item nested inside a top-level function `<enclosing>` (such as a nested
///   `fn` or closure `<Crate>.<enclosing>.<inner>` / `<Crate>.<enclosing>__closure_0`)
///   is kept only when `<enclosing>` itself is in `entries` or transitively
///   reached from `entries`.
/// - Any other helper is kept when its short name is transitively reached from
///   `entries` ([`staged_helper_fns_reachable_from_candidates`]), or when its
///   short name is not a source function or `impl` method in `lib_rs` (such as
///   a derive-generated trait impl or shim).
fn confirm_helper_module_suffixes(
    lib_rs: &str,
    crate_camel: &str,
    subject_pairs: &[(String, String)],
    helper_module_suffixes: &[String],
    entries: &[OracleItemSpec],
) -> Vec<String> {
    let (entry_reachable_fns, entry_reachable_aux) =
        staged_fns_and_aux_reachable_from_candidates(lib_rs, entries);
    let mut source_fns: BTreeMap<String, proc_macro2::TokenStream> = BTreeMap::new();
    let mut aux_tokens: BTreeMap<String, Vec<proc_macro2::TokenStream>> = BTreeMap::new();
    let mut impl_method_names: BTreeSet<String> = BTreeSet::new();
    let mut top_level_fns: BTreeSet<String> = BTreeSet::new();
    if let Ok(file) = syn::parse_file(lib_rs) {
        for item in &file.items {
            if let syn::Item::Fn(func) = item {
                top_level_fns.insert(func.sig.ident.to_string());
            }
        }
        collect_fn_and_aux_items(
            &file.items,
            &mut source_fns,
            &mut aux_tokens,
            &mut impl_method_names,
        );
    }
    let crate_prefix = format!("{crate_camel}.");
    let enclosing_top_fn = |short: &str, suffix: &str| -> Option<String> {
        let top_suffix = format!("{crate_camel}.{short}");
        if suffix == top_suffix {
            return None;
        }
        let rel = suffix.strip_prefix(&crate_prefix)?;
        if let Some((first, _)) = rel.split_once('.')
            && top_level_fns.contains(first)
        {
            return Some(first.to_string());
        }
        if short.starts_with("{closure")
            && let Some((prefix, _)) = rel.rsplit_once("__closure")
            && top_level_fns.contains(prefix)
        {
            return Some(prefix.to_string());
        }
        if let Some(prefix) = rel.strip_suffix(&format!("_{short}"))
            && top_level_fns.contains(prefix)
        {
            return Some(prefix.to_string());
        }
        None
    };
    let matching_impl_self_ty = |short: &str, suffix: &str| -> Option<String> {
        let rel = suffix.strip_prefix(&crate_prefix)?;
        let rel_trimmed = rel.trim_start_matches('_');
        aux_tokens
            .keys()
            .filter(|self_ty| {
                rel_trimmed.starts_with(&format!("{self_ty}_as_"))
                    || rel_trimmed.starts_with(&format!("{self_ty}."))
                    || rel_trimmed == format!("{self_ty}_{short}")
            })
            .max_by_key(|self_ty| self_ty.len())
            .cloned()
    };

    helper_module_suffixes
        .iter()
        .filter(|suffix| {
            subject_pairs
                .iter()
                .filter(|(_, s)| s == *suffix)
                .any(|(short, _)| {
                    if let Some(self_ty) = matching_impl_self_ty(short, suffix) {
                        return entry_reachable_aux.contains(&self_ty);
                    }
                    let is_opaque =
                        !source_fns.contains_key(short) && !impl_method_names.contains(short);
                    if let Some(enclosing) = enclosing_top_fn(short, suffix) {
                        let enclosing_reached = entries.iter().any(|s| s.name == enclosing)
                            || entry_reachable_fns.contains(&enclosing);
                        return enclosing_reached
                            && (entry_reachable_fns.contains(short) || is_opaque);
                    }
                    entry_reachable_fns.contains(short) || is_opaque
                })
        })
        .cloned()
        .collect()
}

/// Render the Lean list of callees linked into every probed or confirmed item:
/// each captured intra-crate helper body, followed by one
/// `fmtArgumentsCtorStub` instance per `DefPath` in
/// [`FMT_ARGUMENTS_CTOR_DEF_PATHS`].
fn render_linked_callees_expr(helper_module_suffixes: &[String]) -> String {
    let elems: Vec<String> = helper_module_suffixes
        .iter()
        .map(|s| format!("Mir.{s}.body"))
        .chain(FMT_ARGUMENTS_CTOR_DEF_PATHS.iter().map(|def_path| {
            format!(
                "{FMT_ARGUMENTS_CTOR_STUB_NAME} \"{}\"",
                escape_lean_string(def_path)
            )
        }))
        .collect();
    format!("[{}]", elems.join(",\n   "))
}

fn render_linked_anneal_probe_module(
    crate_camel: &str,
    items: &[(OracleItemSpec, String)],
    helper_module_suffixes: &[String],
) -> String {
    let mut out = String::new();
    out.push_str("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    let mut imported_mir = BTreeSet::new();
    for helper_suffix in helper_module_suffixes {
        if imported_mir.insert(helper_suffix.clone()) {
            out.push_str(&format!("import Mir.{helper_suffix}\n"));
        }
    }
    for (item, cand_suffix) in items {
        let suffix = if cand_suffix.is_empty() {
            format!("{crate_camel}.{}", item.name)
        } else {
            cand_suffix.clone()
        };
        if imported_mir.insert(suffix.clone()) {
            out.push_str(&format!("import Mir.{suffix}\n"));
        }
    }

    let callees_expr = render_linked_callees_expr(helper_module_suffixes);
    out.push_str(&format!(
        "\nnamespace MiriOracleProbe\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         {FMT_ARGUMENTS_CTOR_STUB_LEAN}\n\
         def linkedCallees : List CapturedMir :=\n  {callees_expr}\n\n\
         {PROBE_EXEC_LEAN}\n\
         {PANIC_MESSAGE_PROBE_LEAN}\n\
         def formatTag : MirDiffTag → String\n  \
           | .normalUnit => \"pass:unit\"\n  \
           | .normalScalar bits sz => s!\"pass:scalar:{{bits}}:{{sz}}\"\n  \
           | .normalOther => \"pass:other\"\n  \
           | .panic => \"panic\"\n  \
           | .abort => \"abort\"\n  \
           | .ub => \"ub\"\n  \
           | .unsupported => \"unsupported\"\n  \
           | .externalCall p => s!\"externalCall:{{p}}\"\n  \
           | .outOfFuel => \"outOfFuel\"\n\n\
         def formatProbeLine (name : String) (fuel : Nat) (body : CapturedMir) : String :=\n  \
           let s := initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees\n  \
           let (tag, span) := probeMirDiffExecBounded fuel body (.running s)\n  \
           let line := s!\"ANNEAL_PROBE\\t{{name}}\\t{{formatTag tag}}\\t{{span}}\"\n  \
           match tag with\n  \
           | .panic =>\n    \
             match probePanicOriginBoundedFrom fuel body none (.running s) with\n    \
             | some o =>\n      \
               let line := line ++ s!\"\\nANNEAL_PANIC_FRAME\\t{{name}}\\t{{activeDefPath body o}}\"\n      \
               match panicMessage? body o with\n      \
               | some bytes => line ++ s!\"\\nANNEAL_PANIC_MESSAGE\\t{{name}}\\t{{bytes}}\"\n      \
               | none => line\n    \
             | none => line\n  \
           | _ => line\n\n"
    ));
    for (item, cand_suffix) in items {
        let escaped_name = escape_lean_string(&item.name);
        let suffix = if cand_suffix.is_empty() {
            format!("{crate_camel}.{}", item.name)
        } else {
            cand_suffix.clone()
        };
        out.push_str(&format!(
            "#eval IO.println (formatProbeLine \"{escaped_name}\" {} Mir.{suffix}.body)\n",
            item.fuel
        ));
    }
    out.push_str("\nend MiriOracleProbe\n");
    out
}

/// Render `MiriOracleConfirm.lean`, which proves by `rfl` each item's
/// `evalMirDiffTagBounded` tag and `probeMirDiffExecBounded` tag and span and,
/// for each panicking item, the panic frame (`probePanicFrameBounded`) and
/// message (`probePanicMessageBounded`) that the probe recovered
/// (`anneal_panic_frames` and `anneal_panic_messages`, keyed by item name).
fn render_anneal_confirm_namespace_section(
    namespace_ident: &str,
    crate_camel: &str,
    items: &[(OracleItemSpec, String, AnnealOutcome)],
    helper_module_suffixes: &[String],
    anneal_panic_frames: &BTreeMap<String, String>,
    anneal_panic_messages: &BTreeMap<String, Vec<u8>>,
) -> Result<String, String> {
    let mut out = String::new();
    let callees_expr = render_linked_callees_expr(helper_module_suffixes);
    out.push_str(&format!(
        "namespace {namespace_ident}\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         {FMT_ARGUMENTS_CTOR_STUB_LEAN}\n\
         def linkedCallees : List CapturedMir :=\n  {callees_expr}\n\n\
         {PROBE_EXEC_LEAN}\n\
         {PANIC_MESSAGE_PROBE_LEAN}\n"
    ));

    for (item, cand_suffix, outcome) in items {
        let Some(tag_expr) = outcome.to_lean_mir_diff_tag() else {
            return Err(format!(
                "cannot render kernel confirmation theorem for '{}' with error outcome {:?}",
                item.name, outcome
            ));
        };
        let fuel = item.fuel;
        let name = &item.name;
        let suffix = if cand_suffix.is_empty() {
            format!("{crate_camel}.{name}")
        } else {
            cand_suffix.clone()
        };
        out.push_str(&format!(
            "theorem confirm_tag_{name} :\n    \
                 evalMirDiffTagBounded {fuel} Mir.{suffix}.body\n      \
                   (initMachineStateWithMemoryAndCallees Mir.{suffix}.body [] emptyMemory linkedCallees) =\n      \
                 {tag_expr} := by\n  \
               rfl\n\n"
        ));
        let escaped_span = outcome
            .span()
            .map(|span| escape_lean_string(&span.display_short()))
            .unwrap_or_else(|| "none".to_string());
        out.push_str(&format!(
            "theorem confirm_probe_{name} :\n    \
                 probeMirDiffExecBounded {fuel} Mir.{suffix}.body\n      \
                   (.running (initMachineStateWithMemoryAndCallees Mir.{suffix}.body [] emptyMemory linkedCallees)) =\n      \
                 ({tag_expr}, \"{escaped_span}\") := by\n  \
               rfl\n\n"
        ));
        if let (AnnealOutcome::Panic { .. }, Some(frame)) = (outcome, anneal_panic_frames.get(name))
        {
            let escaped_frame = escape_lean_string(frame);
            out.push_str(&format!(
                "theorem confirm_frame_{name} :\n    \
                     probePanicFrameBounded {fuel} Mir.{suffix}.body\n      \
                       (.running (initMachineStateWithMemoryAndCallees Mir.{suffix}.body [] emptyMemory linkedCallees)) =\n      \
                     some \"{escaped_frame}\" := by\n  \
                   rfl\n\n"
            ));
        }
        if let (AnnealOutcome::Panic { .. }, Some(message)) =
            (outcome, anneal_panic_messages.get(name))
        {
            let bytes = message
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            let decoded = String::from_utf8_lossy(message);
            out.push_str(&format!(
                "theorem confirm_message_{name} :\n    \
                     probePanicMessageBounded {fuel} Mir.{suffix}.body\n      \
                       (.running (initMachineStateWithMemoryAndCallees Mir.{suffix}.body [] emptyMemory linkedCallees)) =\n      \
                     some [{bytes}] := by\n  \
                   -- Anneal's panic message: {decoded:?}\n  \
                   rfl\n\n"
            ));
        }
    }

    out.push_str(&format!("end {namespace_ident}\n"));
    Ok(out)
}

fn render_linked_anneal_confirm_module(
    crate_camel: &str,
    items: &[(OracleItemSpec, String, AnnealOutcome)],
    helper_module_suffixes: &[String],
    anneal_panic_frames: &BTreeMap<String, String>,
    anneal_panic_messages: &BTreeMap<String, Vec<u8>>,
) -> Result<String, String> {
    let mut out = String::new();
    out.push_str("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    let mut imported_mir = BTreeSet::new();
    for helper_suffix in helper_module_suffixes {
        if imported_mir.insert(helper_suffix.clone()) {
            out.push_str(&format!("import Mir.{helper_suffix}\n"));
        }
    }
    for (item, cand_suffix, _) in items {
        let suffix = if cand_suffix.is_empty() {
            format!("{crate_camel}.{}", item.name)
        } else {
            cand_suffix.clone()
        };
        if imported_mir.insert(suffix.clone()) {
            out.push_str(&format!("import Mir.{suffix}\n"));
        }
    }
    out.push_str(
        "\nset_option maxRecDepth 100000\n\
         set_option maxHeartbeats 2000000\n\n",
    );
    out.push_str(&render_anneal_confirm_namespace_section(
        "MiriOracleConfirm",
        crate_camel,
        items,
        helper_module_suffixes,
        anneal_panic_frames,
        anneal_panic_messages,
    )?);
    Ok(out)
}

/// Renders `oracle/MiriOracleConfirm.lean` preserving the exact `linkedCallees`
/// environment of each kernel-confirmed group (`Chunk` or single-item `Fallback`).
/// When a single group was confirmed, emits `namespace MiriOracleConfirm`; when
/// multiple groups were confirmed separately, emits isolated
/// `namespace MiriOracleConfirm_{idx:03}` blocks so one group's helper/closure/`Drop`
/// callees never contaminate another group's extracted theorem snippet.
fn render_multi_group_anneal_confirm_module(
    crate_camel: &str,
    groups: &[(Vec<MiriConfirmEntry>, Vec<String>)],
    anneal_panic_frames: &BTreeMap<String, String>,
    anneal_panic_messages: &BTreeMap<String, Vec<u8>>,
) -> Result<String, String> {
    if let [(entries, helpers)] = groups {
        return render_linked_anneal_confirm_module(
            crate_camel,
            entries,
            helpers,
            anneal_panic_frames,
            anneal_panic_messages,
        );
    }
    let mut out = String::new();
    out.push_str("import Anneal.Rustc.V2026_06_01.SymbolicEval\n");
    let mut imported_mir = BTreeSet::new();
    for (entries, helpers) in groups {
        for helper_suffix in helpers {
            if imported_mir.insert(helper_suffix.clone()) {
                out.push_str(&format!("import Mir.{helper_suffix}\n"));
            }
        }
        for (item, cand_suffix, _) in entries {
            let suffix = if cand_suffix.is_empty() {
                format!("{crate_camel}.{}", item.name)
            } else {
                cand_suffix.clone()
            };
            if imported_mir.insert(suffix.clone()) {
                out.push_str(&format!("import Mir.{suffix}\n"));
            }
        }
    }
    out.push_str(
        "\nset_option maxRecDepth 100000\n\
         set_option maxHeartbeats 2000000\n",
    );
    for (idx, (entries, helpers)) in groups.iter().enumerate() {
        out.push('\n');
        let ns = format!("MiriOracleConfirm_{idx:03}");
        out.push_str(&render_anneal_confirm_namespace_section(
            &ns,
            crate_camel,
            entries,
            helpers,
            anneal_panic_frames,
            anneal_panic_messages,
        )?);
    }
    Ok(out)
}

/// Result of [`run_linked_difftest_oracle_pipeline`].
struct LinkedDifftestOracleRun {
    /// Per-item oracle outcomes, verdicts, and kernel confirmation status.
    report: DifftestOracleReport,
    /// `DefPath` of the body in which each item's Anneal panic began, keyed by
    /// item name.
    anneal_panic_frames: BTreeMap<String, String>,
    /// Bytes of each panic message that Anneal's probe recovered, keyed by item
    /// name.
    anneal_panic_messages: BTreeMap<String, Vec<u8>>,
}

fn acquire_live_lean_oracle_lock() -> (
    std::sync::MutexGuard<'static, ()>,
    Option<fs::File>,
) {
    static LIVE_ORACLE_PIPELINE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let guard = LIVE_ORACLE_PIPELINE_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(env::temp_dir().join("anneal_miri_difftest_live_oracle.lock"))
        .ok();
    if let Some(ref f) = lock_file {
        let _ = f.lock();
    }
    (guard, lock_file)
}

/// Lean's per-process memory cap (`lean -M`, in MiB) for Stage 1 probe
/// evaluation runs of `oracle/MiriOracleProbe_*.lean`.
const PROBE_LEAN_MEMORY_MB: &str = "8192";

/// Lean's per-process memory cap (`lean -M`, in MiB) for kernel confirmation
/// runs of `oracle/MiriOracleConfirm*.lean`.
const CONFIRM_LEAN_MEMORY_MB: &str = "4096";

/// Hard resident-set budget (MiB) for one Stage 1b `lake env lean` probe
/// process tree, enforced by [`run_lean_with_rss_budget`].
///
/// Lean's `-M` only bounds its small-object allocator: kernel `whnf` /
/// `isDefEq` reduction memory is not counted. At 800-candidate scale a single
/// `rfl` confirmation (`pass_int_widening_and_truncating_casts`, seed
/// `0x42649b91`) grows past 7 GiB RSS under `-M 4096` (~280 MB/s), so without
/// a harness-side bound one theorem OOM-kills the enclosing cgroup and with it
/// the whole campaign. Measured healthy peaks: <= 0.65 GiB per 64-candidate
/// probe chunk and <= 1.2 GiB per 16-entry confirm chunk.
const PROBE_LEAN_RSS_BUDGET_MIB: u64 = 8192;

/// Hard resident-set budget (MiB) for one Stage 2 `lake env lean` kernel
/// confirmation process tree (see [`PROBE_LEAN_RSS_BUDGET_MIB`]); a run killed
/// for exceeding it is classified as resource exhaustion
/// ([`lean_confirm_failure_is_resource_exhaustion`]).
const CONFIRM_LEAN_RSS_BUDGET_MIB: u64 = 4096;

/// Overrides both per-stage RSS budget caps (MiB, `>= 1`).
const MIRI_LEAN_RSS_BUDGET_ENV: &str = "ANNEAL_MIRI_LEAN_MAX_RSS_MIB";

/// How often [`run_lean_with_rss_budget`] samples the process tree.
const LEAN_RSS_POLL_INTERVAL: std::time::Duration = std::time::Duration::from_millis(200);

/// Per-worker resident-set budget (KiB) for a Lean stage running `jobs`
/// concurrent workers: the stage cap (`stage_cap_mib`, or
/// `ANNEAL_MIRI_LEAN_MAX_RSS_MIB` when set) bounded by 85% of this worker's share
/// of the effective cgroup / host headroom, and never below 512 MiB.
fn miri_lean_rss_budget_kib(
    stage_cap_mib: u64,
    override_mib: Option<&str>,
    jobs: usize,
    avail_kib: Option<u64>,
) -> u64 {
    let cap_kib = parse_positive_jobs(override_mib)
        .map_or(stage_cap_mib, |n| n as u64)
        .saturating_mul(1024);
    let share_kib = avail_kib.map(|a| a / jobs.max(1) as u64 / 100 * 85);
    share_kib
        .map_or(cap_kib, |share| cap_kib.min(share))
        .max(512 * 1024)
}

/// Resolves the per-worker RSS budget (KiB) for a Lean stage from
/// `ANNEAL_MIRI_LEAN_MAX_RSS_MIB` and the current effective memory headroom.
fn resolve_miri_lean_rss_budget_kib(stage_cap_mib: u64, jobs: usize) -> u64 {
    let (_, avail_kib) = probe_effective_memory_kib();
    miri_lean_rss_budget_kib(
        stage_cap_mib,
        env::var(MIRI_LEAN_RSS_BUDGET_ENV).ok().as_deref(),
        jobs,
        avail_kib,
    )
}

/// `(ppid, starttime)` from `/proc/<pid>/stat` contents (`pid (comm) state
/// ppid ... starttime ...`, where `comm` may contain spaces or `)`): `ppid` is
/// field 4 and `starttime` (clock ticks since boot) field 22 of `proc(5)`.
#[cfg(target_os = "linux")]
fn parse_proc_stat_ppid_starttime(stat: &str) -> Option<(u32, u64)> {
    let after_comm = stat.rfind(')').map(|i| &stat[i + 1..])?;
    let fields: Vec<&str> = after_comm.split_whitespace().collect();
    let ppid = fields.get(1)?.parse::<u32>().ok()?;
    let starttime = fields.get(19)?.parse::<u64>().ok()?;
    Some((ppid, starttime))
}

#[cfg(target_os = "linux")]
fn proc_starttime(pid: u32) -> Option<u64> {
    fs::read_to_string(format!("/proc/{pid}/stat"))
        .ok()
        .and_then(|s| parse_proc_stat_ppid_starttime(&s))
        .map(|(_, starttime)| starttime)
}

/// `root` and its live `ppid` descendants (`(pid, starttime)`) in breadth-first
/// parent-before-child order from one `/proc/*/stat` snapshot; empty once
/// `root` itself is gone.
#[cfg(target_os = "linux")]
fn process_tree_snapshot(root: u32) -> Vec<(u32, u64)> {
    let mut children: BTreeMap<u32, Vec<(u32, u64)>> = BTreeMap::new();
    let mut root_starttime = None;
    if let Ok(entries) = fs::read_dir("/proc") {
        for entry in entries.flatten() {
            let Some(pid) = entry.file_name().to_str().and_then(|s| s.parse::<u32>().ok()) else {
                continue;
            };
            let Some((ppid, starttime)) = fs::read_to_string(entry.path().join("stat"))
                .ok()
                .and_then(|s| parse_proc_stat_ppid_starttime(&s))
            else {
                continue;
            };
            if pid == root {
                root_starttime = Some(starttime);
            }
            children.entry(ppid).or_default().push((pid, starttime));
        }
    }
    let Some(root_starttime) = root_starttime else {
        return Vec::new();
    };
    let mut seen = BTreeSet::from([root]);
    let mut bfs = vec![(root, root_starttime)];
    let mut i = 0;
    while i < bfs.len() {
        let (pid, _) = bfs[i];
        i += 1;
        for &(kid, starttime) in children.get(&pid).map(Vec::as_slice).unwrap_or(&[]) {
            if seen.insert(kid) {
                bfs.push((kid, starttime));
            }
        }
    }
    bfs
}

/// Every process of one budgeted run seen so far, keyed by pid with its
/// `starttime`.
///
/// The run is deliberately *not* moved into its own process group: `lake` /
/// `lean` must keep receiving the harness's terminal and group signals (Ctrl-C,
/// a scheduler's `kill -- -pgid`, `anneal-lean-run`'s session kill), otherwise
/// interrupting the harness would leave an unsupervised runaway `lean` growing
/// without bound. Instead, a descendant stays tracked after its intermediate
/// parent exits and it is reparented, and the `starttime` check makes a
/// recycled pid unrecognizable, so measuring and killing never touch an
/// unrelated process.
struct TrackedProcessTree {
    root: u32,
    /// `pid -> (starttime, discovery_seq)` so kills run newest-first by
    /// `(starttime, discovery_seq)` rather than numerical PID (which wraps
    /// past `pid_max`).
    seen: BTreeMap<u32, (u64, u64)>,
    next_seq: u64,
}

impl TrackedProcessTree {
    fn new(root: u32) -> Self {
        Self {
            root,
            seen: BTreeMap::new(),
            next_seq: 0,
        }
    }

    fn record_process(&mut self, pid: u32, starttime: u64) {
        if let Some((prev_start, _)) = self.seen.get(&pid)
            && *prev_start == starttime
        {
            return;
        }
        let seq = self.next_seq;
        self.next_seq = self.next_seq.saturating_add(1);
        self.seen.insert(pid, (starttime, seq));
    }

    /// Drops tracked processes that exited (or whose pid now names another
    /// process) and returns the live tracked pids. With `rescan`, first adds the
    /// current `ppid` tree of `root` in BFS parent-before-child order; only
    /// valid while `root` is un-reaped (after reaping, its pid may name an
    /// unrelated process).
    fn live_pids(&mut self, rescan: bool) -> Vec<u32> {
        #[cfg(target_os = "linux")]
        {
            if rescan {
                for (pid, starttime) in process_tree_snapshot(self.root) {
                    self.record_process(pid, starttime);
                }
            }
            self.seen
                .retain(|&pid, &mut (starttime, _)| proc_starttime(pid) == Some(starttime));
            self.seen.keys().copied().collect()
        }
        #[cfg(not(target_os = "linux"))]
        {
            let _ = rescan;
            Vec::new()
        }
    }

    fn tracked_descendant_order_snapshot(&self) -> Vec<u32> {
        let root = self.root;
        let mut entries: Vec<(u64, u64, u32)> = self
            .seen
            .iter()
            .filter_map(|(&pid, &(starttime, seq))| {
                (pid != root).then_some((starttime, seq, pid))
            })
            .collect();
        entries.sort_by(|a, b| b.cmp(a));
        entries.into_iter().map(|(_, _, pid)| pid).collect()
    }

    /// Live non-root tracked pids ordered newest-first by `(starttime, discovery_seq)`
    /// so leaf descendants (`lean`) always die before intermediate parents (`lake`),
    /// even when Linux wraps PIDs past `pid_max`.
    fn descendant_kill_order(&mut self, rescan: bool) -> Vec<u32> {
        let _ = self.live_pids(rescan);
        self.tracked_descendant_order_snapshot()
    }

    /// Total resident set (KiB, `VmRSS`) of the live tracked processes, or
    /// `None` where `/proc` is unavailable (the budget is then not enforced).
    fn rss_kib(&mut self) -> Option<u64> {
        let mut total: Option<u64> = None;
        for pid in self.live_pids(true) {
            let rss = fs::read_to_string(format!("/proc/{pid}/status"))
                .ok()
                .and_then(|s| {
                    s.lines()
                        .find_map(|l| l.strip_prefix("VmRSS:"))
                        .and_then(|v| v.split_whitespace().next()?.parse::<u64>().ok())
                });
            if let Some(rss) = rss {
                total = Some(total.unwrap_or(0).saturating_add(rss));
            }
        }
        total
    }

    /// SIGKILLs every live tracked process other than `root` (newest processes
    /// first by `(starttime, discovery_seq)`, so `lean` dies before `lake` can
    /// react even across PID wraparound). Pass `rescan = false` once `root` has
    /// been reaped.
    fn kill_descendants(&mut self, rescan: bool) {
        #[cfg(target_os = "linux")]
        {
            unsafe extern "C" {
                fn kill(pid: i32, sig: i32) -> i32;
            }
            const SIGKILL: i32 = 9;
            for pid in self.descendant_kill_order(rescan) {
                if let Ok(pid) = i32::try_from(pid)
                    && pid > 0
                {
                    // SAFETY: `kill(2)` takes plain integers and has no
                    // memory-safety preconditions; `descendant_kill_order` just
                    // re-verified that `pid` still names the tracked process
                    // (same `starttime`), and an already-exited pid fails with ESRCH.
                    unsafe {
                        kill(pid, SIGKILL);
                    }
                }
            }
        }
    }

    /// SIGKILLs the descendants and then `child` itself (the root, via
    /// [`std::process::Child::kill`], which cannot hit a recycled pid because
    /// `child` has not been reaped).
    fn kill_all(&mut self, child: &mut std::process::Child) {
        self.kill_descendants(true);
        let _ = child.kill();
    }
}

/// Result of [`run_lean_with_rss_budget`].
struct BudgetedOutput {
    output: std::process::Output,
    /// Process-tree RSS (KiB) observed when the budget was exceeded and the
    /// tree was killed (never set if the child had already exited cleanly).
    budget_exceeded_kib: Option<u64>,
}

/// Runs `cmd` to completion capturing stdout / stderr like
/// [`Command::output`], but SIGKILLs its whole process tree as soon as the
/// tree's resident set exceeds `budget_kib` (sampled every
/// [`LEAN_RSS_POLL_INTERVAL`]), so a runaway Lean kernel reduction is contained
/// to its own run instead of OOM-killing the enclosing cgroup. The run stays in
/// the harness's process group (see [`TrackedProcessTree`]).
fn run_lean_with_rss_budget(
    cmd: &mut Command,
    budget_kib: Option<u64>,
) -> std::io::Result<BudgetedOutput> {
    use std::io::Read;
    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = cmd.spawn()?;
    let drain = |pipe: Option<Box<dyn Read + Send>>| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut pipe) = pipe {
                let _ = pipe.read_to_end(&mut buf);
            }
            buf
        })
    };
    let stdout_reader = drain(
        child
            .stdout
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let stderr_reader = drain(
        child
            .stderr
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let mut tree = TrackedProcessTree::new(child.id());
    let mut budget_exceeded_kib = None;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(err) => {
                tree.kill_all(&mut child);
                let _ = child.wait();
                return Err(err);
            }
        }
        if let Some(budget) = budget_kib
            && let Some(rss) = tree.rss_kib()
            && rss > budget
        {
            // Re-check `try_wait` before killing so a process that exited while
            // `/proc` was scanned keeps its genuine exit status (`exit 0` or a
            // normal `exit 1` kernel rejection) rather than being misattributed
            // to the RSS watchdog.
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => {}
                Err(err) => {
                    tree.kill_all(&mut child);
                    let _ = child.wait();
                    return Err(err);
                }
            }
            tree.kill_all(&mut child);
            let waited = child.wait()?;
            if !waited.success() {
                budget_exceeded_kib = Some(rss);
            }
            break waited;
        }
        std::thread::sleep(LEAN_RSS_POLL_INTERVAL);
    };
    if budget_kib.is_some() {
        // `lake env lean` waits for `lean`, but never leave a tracked
        // descendant running after the root exits: it would be unsupervised
        // and would hold the pipes open, blocking the readers below. `child` is
        // reaped now, so only already-tracked processes are considered.
        tree.kill_descendants(false);
    }
    let stdout = stdout_reader.join().unwrap_or_default();
    let stderr = stderr_reader.join().unwrap_or_default();
    Ok(BudgetedOutput {
        output: std::process::Output {
            status,
            stdout,
            stderr,
        },
        budget_exceeded_kib,
    })
}

/// Diagnostic appended to a run killed by [`run_lean_with_rss_budget`]. It is
/// an `error:` line (so every diagnostics filter surfaces it) containing
/// `out of memory`, so the run classifies as resource exhaustion even if `lake`
/// reported an exit code before the kill reached it.
fn rss_budget_kill_note(budget_kib: u64, observed_kib: u64) -> String {
    format!(
        "error: miri-difftest killed `lake env lean` (out of memory guard): process-tree \
         resident set {} MiB exceeded the {} MiB budget (Lean's -M does not bound kernel \
         reduction memory; override with {MIRI_LEAN_RSS_BUDGET_ENV})",
        observed_kib / 1024,
        budget_kib / 1024
    )
}

/// Run `lake env lean -M CONFIRM_LEAN_MEMORY_MB <rel_oracle_path>` in `dot_anneal`
/// with `LEAN_NUM_THREADS=1` (so concurrent confirm chunk workers never
/// multiply threads) under a hard `rss_budget_kib` resident-set budget.
fn run_lean_confirm_file(
    lake_bin: &Path,
    dot_anneal: &Path,
    rel_oracle_path: &str,
    rss_budget_kib: u64,
) -> Result<LeanConfirmRun, String> {
    let mut cmd = Command::new(lake_bin);
    cmd.current_dir(dot_anneal)
        .env("LEAN_NUM_THREADS", "1")
        .arg("env")
        .arg("lean")
        .arg("-M")
        .arg(CONFIRM_LEAN_MEMORY_MB)
        .arg(rel_oracle_path);
    let run = run_lean_with_rss_budget(&mut cmd, Some(rss_budget_kib)).map_err(|err| {
        format!(
            "failed to execute '{} env lean -M {CONFIRM_LEAN_MEMORY_MB} \
             {rel_oracle_path}': {err}",
            lake_bin.display()
        )
    })?;
    Ok(LeanConfirmRun::from_budgeted_output(&run, rss_budget_kib))
}

fn sanitize_lean_file_stem(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push_str("item");
    }
    if out != raw {
        let mut h: u64 = 0xCBF2_9CE4_8422_2325;
        for &b in raw.as_bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01B3);
        }
        out.push_str(&format!("_{h:08x}"));
    }
    out
}

fn clean_oracle_files_with_prefixes(oracle_dir: &Path, prefixes: &[&str]) {
    let Ok(entries) = fs::read_dir(oracle_dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if prefixes.iter().any(|p| name.starts_with(p)) && path.is_file() {
            let _ = fs::remove_file(&path);
        }
    }
}

/// Outcome of [`run_isolated_miri_stage`].
#[derive(Debug)]
struct IsolatedMiriStage<X> {
    /// Per-item results for every item whose chunk or per-candidate fallback succeeded.
    results: BTreeMap<String, X>,
    /// Per-item isolated diagnostic for every item that failed (or was skipped after
    /// [`MIRI_FALLBACK_CIRCUIT_BREAKER`] consecutive fallback failures with 0 successes).
    failed_reasons: BTreeMap<String, String>,
    /// Diagnostics emitted across failed chunks and fallback attempts.
    errors: Vec<String>,
}

/// Execution kind passed to `run_chunk` in [`run_isolated_miri_stage`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MiriStageRunKind {
    /// Initial chunk run (`{stage_label}_{chunk_idx:03}`) inside a wave of
    /// `wave_jobs` concurrent workers.
    Chunk { wave_jobs: usize },
    /// Single-candidate fallback run (`{stage_label}Fallback_<stem>`).
    Fallback,
    /// One-shot multi-candidate remainder retry after the circuit breaker trips
    /// (`{stage_label}Remainder_{chunk_idx:03}`).
    Remainder,
}

impl MiriStageRunKind {
    /// Number of concurrent workers sharing cgroup headroom during this run.
    fn active_workers(self) -> usize {
        match self {
            Self::Chunk { wave_jobs } => wave_jobs.max(1),
            Self::Fallback | Self::Remainder => 1,
        }
    }
}

fn miri_probe_module_file_name(
    chunk_idx: usize,
    run_kind: MiriStageRunKind,
    chunk: &[(OracleItemSpec, String)],
) -> String {
    match run_kind {
        MiriStageRunKind::Chunk { .. } => format!("MiriOracleProbe_{chunk_idx:03}.lean"),
        MiriStageRunKind::Remainder => format!("MiriOracleProbeRemainder_{chunk_idx:03}.lean"),
        MiriStageRunKind::Fallback => {
            let stem = chunk
                .first()
                .map(|(s, _)| sanitize_lean_file_stem(&s.name))
                .unwrap_or_else(|| format!("chunk_{chunk_idx:03}"));
            format!("MiriOracleProbeFallback_{stem}.lean")
        }
    }
}

/// Runs one chunked `miri-difftest` Lean stage (`Mir.*` build or `MiriOracleProbe`
/// evaluation) with per-candidate fallback isolation and a circuit breaker.
///
/// `items` are split into chunks of at most `chunk_size`, run by
/// `run_chunk(chunk_idx, run_kind, label, chunk)` in waves of at most `jobs`
/// concurrent workers. A chunk only succeeds if it yields a result for every
/// item; a failed, incomplete, or panicking chunk is re-run one item at a time.
/// After [`MIRI_FALLBACK_CIRCUIT_BREAKER`] fallback failures with no fallback
/// success, the rest of that chunk is retried once as a single group
/// (`{stage_label}Remainder_{chunk_idx:03}`) so that a few broken candidates
/// leading a chunk cannot write off its healthy remainder; if that retry also
/// fails, the failure is treated as systematic and every remaining item fails
/// without further Lean runs.
fn run_isolated_miri_stage<C, X, K, F>(
    stage_label: &str,
    items: &[C],
    chunk_size: usize,
    jobs: usize,
    item_key: K,
    run_chunk: F,
) -> IsolatedMiriStage<X>
where
    C: Clone + Sync,
    X: Send,
    K: Fn(&C) -> &str,
    F: Fn(usize, MiriStageRunKind, &str, &[C]) -> Result<BTreeMap<String, X>, String> + Sync,
{
    let chunk_size = chunk_size.max(1);
    let jobs = jobs.max(1);
    let mut results: BTreeMap<String, X> = BTreeMap::new();
    let mut failed_reasons: BTreeMap<String, String> = BTreeMap::new();
    let mut errors: Vec<String> = Vec::new();
    let mut failed_chunks: Vec<(usize, String, &[C])> = Vec::new();

    let accept = |results: &mut BTreeMap<String, X>,
                  slice: &[C],
                  res: Result<BTreeMap<String, X>, String>,
                  label: &str|
     -> Result<(), String> {
        let mut map = res.map_err(|e| format!("{label}: {}", truncate_lean_diag(&e)))?;
        if let Some(missing) = slice.iter().find(|&c| !map.contains_key(item_key(c))) {
            return Err(format!(
                "{label}: Lean stage produced no result for `{}`",
                item_key(missing)
            ));
        }
        for c in slice {
            if let Some(x) = map.remove(item_key(c)) {
                results.insert(item_key(c).to_string(), x);
            }
        }
        Ok(())
    };

    let chunks: Vec<&[C]> = items.chunks(chunk_size).collect();
    for (wave_idx, wave) in chunks.chunks(jobs).enumerate() {
        let wave_jobs = wave.len().max(1);
        let wave_res: Vec<(usize, String, Result<BTreeMap<String, X>, String>)> =
            std::thread::scope(|s| {
                let handles: Vec<_> = wave
                    .iter()
                    .enumerate()
                    .map(|(i, &chunk)| {
                        let chunk_idx = wave_idx * jobs + i;
                        let label = format!("{stage_label}_{chunk_idx:03}");
                        let run_chunk = &run_chunk;
                        let worker_label = label.clone();
                        let handle = s.spawn(move || {
                            run_chunk(
                                chunk_idx,
                                MiriStageRunKind::Chunk { wave_jobs },
                                &worker_label,
                                chunk,
                            )
                        });
                        (chunk_idx, label, handle)
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|(chunk_idx, label, h)| {
                        let res = h
                            .join()
                            .unwrap_or_else(|_| Err("Lean chunk worker panicked".to_string()));
                        (chunk_idx, label, res)
                    })
                    .collect()
            });
        for (&chunk, (chunk_idx, label, res)) in wave.iter().zip(wave_res) {
            if let Err(e) = accept(&mut results, chunk, res, &label) {
                errors.push(e.clone());
                failed_chunks.push((chunk_idx, e, chunk));
            }
        }
    }

    let mut fallback_successes = 0usize;
    let mut fallback_failures = 0usize;
    let mut skipped_fallbacks = 0usize;
    let mut first_fallback_err: Option<String> = None;
    // Set once a breaker remainder retry fails while no fallback has ever
    // succeeded: the failure is then systematic, so later chunks skip straight
    // to the breaker diagnosis instead of paying one more Lean run each.
    let mut remainder_retry_failed = false;

    for (chunk_idx, chunk_err, chunk) in failed_chunks {
        if chunk.len() == 1 {
            let key = item_key(&chunk[0]).to_string();
            if fallback_successes == 0 {
                fallback_failures += 1;
                if first_fallback_err.is_none() {
                    first_fallback_err = Some(chunk_err.clone());
                }
            }
            failed_reasons.insert(key, chunk_err);
            continue;
        }
        let mut deferred: Vec<C> = Vec::new();
        for item in chunk {
            let key = item_key(item).to_string();
            if results.contains_key(&key) || failed_reasons.contains_key(&key) {
                continue;
            }
            if fallback_successes == 0 && fallback_failures >= MIRI_FALLBACK_CIRCUIT_BREAKER {
                deferred.push(item.clone());
                continue;
            }
            let label = format!("{stage_label}Fallback_{}", sanitize_lean_file_stem(&key));
            let single = std::slice::from_ref(item);
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_chunk(chunk_idx, MiriStageRunKind::Fallback, &label, single)
            }))
            .unwrap_or_else(|_| Err("Lean fallback worker panicked".to_string()));
            match accept(&mut results, single, res, &label) {
                Ok(()) => fallback_successes += 1,
                Err(e) => {
                    fallback_failures += 1;
                    if first_fallback_err.is_none() {
                        first_fallback_err = Some(e.clone());
                    }
                    errors.push(e.clone());
                    failed_reasons.insert(key, e);
                }
            }
        }
        if deferred.is_empty() {
            continue;
        }
        // The breaker tripped part-way through this chunk. Several genuinely
        // broken candidates can lead a chunk, so retry the unresolved
        // remainder once as a group before writing it off as a systematic
        // failure (bounded to one extra Lean run per stage while no fallback
        // has succeeded).
        let mut remainder_note = String::new();
        if !remainder_retry_failed {
            let label = format!("{stage_label}Remainder_{chunk_idx:03}");
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_chunk(chunk_idx, MiriStageRunKind::Remainder, &label, &deferred)
            }))
            .unwrap_or_else(|_| Err("Lean remainder worker panicked".to_string()));
            match accept(&mut results, &deferred, res, &label) {
                Ok(()) => {
                    fallback_successes += 1;
                    continue;
                }
                Err(e) => {
                    remainder_retry_failed = true;
                    errors.push(e);
                    remainder_note = format!("; remainder retry `{label}` also failed");
                }
            }
        }
        let root_cause = first_fallback_err.as_deref().unwrap_or(chunk_err.as_str());
        let root_lines: Vec<&str> = root_cause.lines().collect();
        let root_summary = if root_lines.len() > 12 {
            let head_slice = &root_lines[..12];
            let extra_highlights: Vec<&str> = root_lines[12..]
                .iter()
                .copied()
                .filter(|l| is_lean_diag_highlight_line(l) && !head_slice.contains(l))
                .take(6)
                .collect();
            if extra_highlights.is_empty() {
                format!(
                    "{}\n... (full diagnostic in the {stage_label} stage errors)",
                    head_slice.join("\n")
                )
            } else {
                format!(
                    "{}\n{}\n... (full diagnostic in the {stage_label} stage errors)",
                    head_slice.join("\n"),
                    extra_highlights.join("\n")
                )
            }
        } else {
            root_cause.to_string()
        };
        skipped_fallbacks += deferred.len();
        for item in &deferred {
            failed_reasons.insert(
                item_key(item).to_string(),
                format!(
                    "{stage_label}: per-candidate fallback skipped after \
                     {MIRI_FALLBACK_CIRCUIT_BREAKER} consecutive fallback failures \
                     (systematic Lean failure{remainder_note}); first failure: {root_summary}"
                ),
            );
        }
    }
    if skipped_fallbacks > 0 {
        errors.push(format!(
            "{stage_label}: skipped {skipped_fallbacks} per-candidate fallback run(s) after \
             {MIRI_FALLBACK_CIRCUIT_BREAKER} consecutive fallback failures (systematic Lean failure)"
        ));
    }

    for item in items {
        let key = item_key(item);
        if !results.contains_key(key) && !failed_reasons.contains_key(key) {
            failed_reasons.insert(
                key.to_string(),
                format!("{stage_label}: missing result for `{key}`"),
            );
        }
    }

    IsolatedMiriStage {
        results,
        failed_reasons,
        errors,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum MiriProbeItemStatus {
    Present {
        outcome: AnnealOutcome,
        panic_frame: Option<String>,
        panic_message: Option<Vec<u8>>,
    },
    MissingProbeLine,
}

fn parse_miri_probe_chunk_stdout(
    chunk: &[(OracleItemSpec, String)],
    stdout: &str,
) -> Result<BTreeMap<String, MiriProbeItemStatus>, String> {
    let mut parsed_outcomes = parse_anneal_probe_output(stdout)?;
    let mut parsed_frames = parse_anneal_panic_frames(stdout)?;
    let mut parsed_messages = parse_anneal_panic_messages(stdout)?;
    let mut out = BTreeMap::new();
    for (item, _) in chunk {
        if let Some(outcome) = parsed_outcomes.remove(&item.name) {
            out.insert(
                item.name.clone(),
                MiriProbeItemStatus::Present {
                    outcome,
                    panic_frame: parsed_frames.remove(&item.name),
                    panic_message: parsed_messages.remove(&item.name),
                },
            );
        } else {
            out.insert(item.name.clone(), MiriProbeItemStatus::MissingProbeLine);
        }
    }
    Ok(out)
}

fn aggregate_miri_probe_stage(
    surviving_items: &[(OracleItemSpec, String)],
    chunk_size: usize,
    lean_jobs: usize,
    eval_chunk: impl Fn(usize, MiriStageRunKind, &str, &[(OracleItemSpec, String)]) -> Result<String, String>
    + Sync,
    anneal_outcomes: &mut BTreeMap<String, AnnealOutcome>,
    anneal_panic_frames: &mut BTreeMap<String, String>,
    anneal_panic_messages: &mut BTreeMap<String, Vec<u8>>,
) -> Vec<String> {
    let stage = run_isolated_miri_stage(
        "MiriOracleProbe",
        surviving_items,
        chunk_size,
        lean_jobs,
        |(spec, _): &(OracleItemSpec, String)| spec.name.as_str(),
        |chunk_idx, run_kind, label, chunk| {
            let stdout = eval_chunk(chunk_idx, run_kind, label, chunk)?;
            parse_miri_probe_chunk_stdout(chunk, &stdout)
        },
    );
    for (item, _) in surviving_items {
        if let Some(status) = stage.results.get(&item.name) {
            match status {
                MiriProbeItemStatus::Present {
                    outcome,
                    panic_frame,
                    panic_message,
                } => {
                    anneal_outcomes.insert(item.name.clone(), outcome.clone());
                    if let Some(frame) = panic_frame {
                        anneal_panic_frames.insert(item.name.clone(), frame.clone());
                    }
                    if let Some(msg) = panic_message {
                        anneal_panic_messages.insert(item.name.clone(), msg.clone());
                    }
                }
                MiriProbeItemStatus::MissingProbeLine => {
                    anneal_outcomes.insert(
                        item.name.clone(),
                        AnnealOutcome::CaptureOrLeanError(format!(
                            "Lean probe output omitted ANNEAL_PROBE line for '{}'",
                            item.name
                        )),
                    );
                }
            }
        } else if let Some(err) = stage.failed_reasons.get(&item.name) {
            anneal_outcomes.insert(item.name.clone(), AnnealOutcome::CaptureOrLeanError(err.clone()));
        }
    }
    stage.errors
}

const LEAN_RESOURCE_MARKERS: [&str; 8] = [
    "out of memory",
    // Lean 4's `-M` flag reports `(kernel) excessive memory consumption detected`
    // or `excessive memory consumption detected at '...'` rather than `out of memory`.
    "excessive memory consumption",
    "memory allocation failed",
    "(deterministic) timeout",
    "maximum number of heartbeats",
    "maximum recursion depth",
    "deep recursion",
    "stack overflow",
];

const LEAN_KERNEL_REJECTION_MARKERS: [&str; 14] = [
    // Lean v4.34.1 tactic `rfl` prints `Tactic `rfl` failed: The left-hand side ...
    // is not definitionally equal to the right-hand side ...`; older Lean 4 printed
    // `The rfl tactic failed`, and term-mode `rfl` prints `Not a definitional equality`.
    "tactic `rfl` failed",
    "the rfl tactic failed",
    "not definitionally equal",
    "not a definitional equality",
    "type mismatch",
    "application type mismatch",
    "declaration type mismatch",
    "(kernel) constant",
    "unknown identifier",
    "unknown constant",
    "unknown module prefix",
    "unknown namespace",
    "failed to synthesize",
    "unsolved goals",
];

fn is_lean_message_header(line: &str, kind: &str) -> bool {
    let lower = line.to_ascii_lowercase();
    lower.trim_start().starts_with(&format!("{kind}:")) || lower.contains(&format!(": {kind}:"))
}

fn is_lean_runtime_crash_boundary(line: &str) -> bool {
    let trimmed = line.trim_start();
    if trimmed.starts_with('✖') {
        return true;
    }
    let lower = trimmed.to_ascii_lowercase();
    lower.starts_with("lean panic:")
        || lower.starts_with("lean assertion violation")
        || lower.starts_with("panic at ")
        || lower.starts_with("panicked at ")
        || lower.starts_with("thread '")
        || lower.starts_with("fatal runtime error:")
}

fn collect_stream_lean_error_blocks(stream: &str, blocks: &mut Vec<String>) {
    let mut current: Option<String> = None;
    for line in stream.lines() {
        let starts_error = is_lean_message_header(line, "error");
        if starts_error
            || is_lean_message_header(line, "warning")
            || is_lean_message_header(line, "info")
            || is_lean_runtime_crash_boundary(line)
        {
            blocks.extend(current.take());
            if starts_error {
                current = Some(line.to_string());
            }
        } else if let Some(block) = current.as_mut() {
            block.push('\n');
            block.push_str(line);
        }
    }
    blocks.extend(current);
}

/// The `error:` message blocks of a Lake / Lean run: each block starts at an
/// `error:` header line (`<file>:<line>:<col>: error: ...` or a bare `error:`)
/// and runs until the next `error:` / `warning:` / `info:` / runtime-crash
/// header or the end of that stream (`stdout` and `stderr` are parsed
/// separately so a headerless `stderr` runtime OOM line such as
/// `LEAN PANIC: out of memory` never merges into a preceding `stdout` `error:`
/// block).
fn lean_error_blocks(stdout: &str, stderr: &str) -> Vec<String> {
    let mut blocks: Vec<String> = Vec::new();
    collect_stream_lean_error_blocks(stdout, &mut blocks);
    collect_stream_lean_error_blocks(stderr, &mut blocks);
    blocks
}

/// Whether a failed run reported a kernel or elaboration rejection (`The rfl
/// tactic failed`, `type mismatch`, `unknown identifier`, ...) in an error
/// block that no resource marker explains (a typeclass search that ran out of
/// heartbeats reports `failed to synthesize` together with `(deterministic)
/// timeout` in one block, which is exhaustion, not rejection).
///
/// Such a rejection fails Stage 2 closed even when the run was later killed
/// (by the RSS watchdog or a signal) or also exhausted a resource elsewhere:
/// the kernel refused what the compiled probe claimed, which must never be
/// downgraded to `kernel_confirmed = false`.
fn lean_output_has_unexplained_kernel_rejection(stdout: &str, stderr: &str) -> bool {
    lean_error_blocks(stdout, stderr).iter().any(|block| {
        let lower = block.to_ascii_lowercase();
        LEAN_KERNEL_REJECTION_MARKERS.iter().any(|m| lower.contains(m))
            && !LEAN_RESOURCE_MARKERS.iter().any(|m| lower.contains(m))
    })
}

/// Whether a failed Lean kernel confirmation run ran out of a resource
/// (Lean's `-M` memory cap, `maxHeartbeats`, recursion depth, the stack, or
/// termination by a signal such as the OOM killer) rather than rejecting a
/// theorem.
///
/// Only resource exhaustion may downgrade a divergence to
/// `kernel_confirmed = false`. Any other failure (a `rfl` mismatch between the
/// compiled `#eval` probe and the kernel, or an elaboration or import error)
/// is a harness inconsistency that must abort the run.
fn lean_confirm_failure_is_resource_exhaustion(signal_terminated: bool, output: &str) -> bool {
    let lower = output.to_ascii_lowercase();
    signal_terminated || LEAN_RESOURCE_MARKERS.iter().any(|m| lower.contains(m))
}

/// One `(spec, module suffix, Anneal outcome)` entry to kernel-confirm.
type MiriConfirmEntry = (OracleItemSpec, String, AnnealOutcome);

/// Captured result of one `lake env lean` kernel confirmation run.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LeanConfirmRun {
    success: bool,
    /// The process was terminated by a signal (such as the cgroup OOM killer).
    signal_terminated: bool,
    /// Rendered exit status (for diagnostics).
    status: String,
    stdout: String,
    stderr: String,
}

impl LeanConfirmRun {
    /// Converts a [`run_lean_with_rss_budget`] result. A clean exit stays a
    /// success (the watchdog never records a kill for one). A run killed for
    /// exceeding `budget_kib` is reported as signal-terminated with an
    /// `out of memory` note; whether that may downgrade the entry is decided
    /// by [`run_chunked_miri_confirm_stage`], where an unexplained kernel
    /// rejection in the output still fails closed
    /// ([`lean_output_has_unexplained_kernel_rejection`]).
    fn from_budgeted_output(run: &BudgetedOutput, budget_kib: u64) -> Self {
        let out = &run.output;
        let mut stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        let killed_by_budget = run.budget_exceeded_kib.filter(|_| !out.status.success());
        if let Some(observed_kib) = killed_by_budget {
            if !stderr.is_empty() && !stderr.ends_with('\n') {
                stderr.push('\n');
            }
            stderr.push_str(&rss_budget_kill_note(budget_kib, observed_kib));
        }
        Self {
            success: out.status.success(),
            signal_terminated: out.status.code().is_none() || killed_by_budget.is_some(),
            status: out.status.to_string(),
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr,
        }
    }
}

/// Outcome of [`run_chunked_miri_confirm_stage`].
#[derive(Debug)]
struct ChunkedMiriConfirm {
    /// Entries whose theorems the kernel accepted (in chunk order).
    confirmed: Vec<MiriConfirmEntry>,
    /// Exact slices (chunk or single-entry fallback) accepted by the Lean kernel,
    /// so `MiriOracleConfirm.lean` preserves each slice's kernel-checked
    /// `linkedCallees` environment without cross-chunk contamination.
    confirmed_groups: Vec<Vec<MiriConfirmEntry>>,
    /// Entries whose confirmation exhausted a resource
    /// ([`lean_confirm_failure_is_resource_exhaustion`]), keyed by name, with
    /// the diagnostic explaining the downgrade to `kernel_confirmed = false`.
    unconfirmed: BTreeMap<String, String>,
}

/// One-line reason for a resource-exhausted confirmation: the run's exit
/// status plus its last highlighted diagnostics (`error:` / budget-kill lines).
fn resource_exhaustion_reason(module_name: &str, run: &LeanConfirmRun) -> String {
    let highlights = extract_lean_error_lines(&run.stdout, &run.stderr, 3);
    let detail = if highlights.is_empty() {
        run.stderr
            .lines()
            .chain(run.stdout.lines())
            .rev()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("(no diagnostics)")
            .to_string()
    } else {
        highlights.join(" | ")
    };
    format!("oracle/{module_name} ({}): {detail}", run.status)
}

/// Stage 2: kernel-confirms `to_confirm` in `MiriOracleConfirm_{chunk_idx:03}.lean`
/// modules of at most `chunk_size` entries, running at most `jobs` chunk
/// modules concurrently (each `lake env lean` worker is bounded by
/// `LEAN_NUM_THREADS=1` and `-M CONFIRM_LEAN_MEMORY_MB` in
/// [`run_lean_confirm_file`]), so no single Lean process ever has to hold an
/// unbounded batch of theorems.
///
/// A failing chunk is re-confirmed one entry at a time
/// (`MiriOracleConfirmFallback_<item>.lean`). An entry whose confirmation
/// exhausts a resource lands in [`ChunkedMiriConfirm::unconfirmed`]; any other
/// failure (the kernel rejecting a theorem the compiled probe produced, or a
/// module that does not elaborate) is a harness inconsistency and fails the
/// stage closed with both `stdout` and `stderr` diagnostics. A rejection wins
/// over exhaustion: an entry whose output contains an unexplained kernel
/// rejection fails closed even if the run was then killed or ran out of
/// heartbeats ([`lean_output_has_unexplained_kernel_rejection`]).
///
/// `write_module(file_name, entries)` renders a module and
/// `run_module(file_name, active_workers)` checks it, where `active_workers`
/// is the exact number of concurrent confirm workers sharing cgroup headroom
/// (`wave.len()` for a chunk wave, `1` for a per-entry fallback).
fn run_chunked_miri_confirm_stage<W, R>(
    to_confirm: &[MiriConfirmEntry],
    chunk_size: usize,
    jobs: usize,
    write_module: W,
    run_module: R,
) -> Result<ChunkedMiriConfirm, String>
where
    W: Fn(&str, &[MiriConfirmEntry]) -> Result<(), String>,
    R: Fn(&str, usize) -> Result<LeanConfirmRun, String> + Sync,
{
    let chunk_size = chunk_size.max(1);
    let jobs = jobs.max(1);
    let chunks: Vec<&[MiriConfirmEntry]> = to_confirm.chunks(chunk_size).collect();
    let mut confirmed: Vec<MiriConfirmEntry> = Vec::with_capacity(to_confirm.len());
    let mut confirmed_groups: Vec<Vec<MiriConfirmEntry>> = Vec::with_capacity(chunks.len());
    let mut unconfirmed: BTreeMap<String, String> = BTreeMap::new();

    for (wave_idx, wave) in chunks.chunks(jobs).enumerate() {
        let mut prepared: Vec<(String, &[MiriConfirmEntry])> = Vec::with_capacity(wave.len());
        for (i, &chunk) in wave.iter().enumerate() {
            let file_name = format!("MiriOracleConfirm_{:03}.lean", wave_idx * jobs + i);
            write_module(&file_name, chunk)?;
            prepared.push((file_name, chunk));
        }
        let wave_jobs = wave.len().max(1);
        let outputs: Vec<Result<LeanConfirmRun, String>> = std::thread::scope(|s| {
            let handles: Vec<_> = prepared
                .iter()
                .map(|(file_name, _)| {
                    let run_module = &run_module;
                    // Pass the actual wave concurrency (`wave_jobs`, e.g. `1` for a
                    // trailing chunk or `3` for a 3-chunk wave on a 4-worker machine)
                    // so the RSS budget is never over-divided by idle worker slots.
                    s.spawn(move || run_module(file_name, wave_jobs))
                })
                .collect();
            handles
                .into_iter()
                .map(|h| {
                    h.join()
                        .unwrap_or_else(|_| Err("Lean confirm chunk worker panicked".to_string()))
                })
                .collect()
        });

        for ((file_name, chunk), out) in prepared.into_iter().zip(outputs) {
            let out = out?;
            if out.success {
                confirmed.extend_from_slice(chunk);
                confirmed_groups.push(chunk.to_vec());
                continue;
            }
            let single_runs: Vec<(&MiriConfirmEntry, String, LeanConfirmRun)> =
                if chunk.len() == 1 && wave_jobs == 1 {
                    vec![(&chunk[0], file_name, out)]
                } else {
                    let mut runs = Vec::with_capacity(chunk.len());
                    for entry in chunk {
                        let fb_name = format!(
                            "MiriOracleConfirmFallback_{}.lean",
                            sanitize_lean_file_stem(&entry.0.name)
                        );
                        write_module(&fb_name, std::slice::from_ref(entry))?;
                        let run = run_module(&fb_name, 1)?;
                        runs.push((entry, fb_name, run));
                    }
                    runs
                };
            for (entry, module_name, run) in single_runs {
                if run.success {
                    confirmed.push(entry.clone());
                    confirmed_groups.push(vec![entry.clone()]);
                } else if !lean_output_has_unexplained_kernel_rejection(&run.stdout, &run.stderr)
                    && lean_confirm_failure_is_resource_exhaustion(
                        run.signal_terminated,
                        &format!("{}\n{}", run.stdout, run.stderr),
                    )
                {
                    unconfirmed.insert(
                        entry.0.name.clone(),
                        resource_exhaustion_reason(&module_name, &run),
                    );
                } else {
                    return Err(format_lean_command_failure(
                        &format!(
                            "Lean kernel confirmation rejected `{}` in oracle/{module_name} ({})",
                            entry.0.name, run.status
                        ),
                        &run.stdout,
                        &run.stderr,
                    ));
                }
            }
        }
    }
    Ok(ChunkedMiriConfirm {
        confirmed,
        confirmed_groups,
        unconfirmed,
    })
}

fn run_linked_difftest_oracle_pipeline(
    config: &DifftestOracleConfig,
    items: &[OracleItemSpec],
) -> Result<LinkedDifftestOracleRun, String> {
    let miri_cfg = MiriOracleConfig {
        corpus_root: config.corpus_root.clone(),
        capture_rustflags: config.capture_rustflags.clone(),
        miri_flags: config.miri_flags.clone(),
        toolchain: config.toolchain.clone(),
    };
    let miri_outcomes = run_miri_oracle(&miri_cfg, items)?;

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
    let wrapper = ensure_rustc_wrapper(&driver_cfg, config.anneal_repo_root.as_deref())?;
    let rustflags = if config.capture_rustflags.is_empty() {
        DEFAULT_CAPTURE_RUSTFLAGS.join(" ")
    } else {
        config.capture_rustflags.join(" ")
    };
    let cargo_bin = resolve_cargo_bin();
    let capture_out = Command::new(&cargo_bin)
        .current_dir(&corpus_root)
        .arg("check")
        .arg("--lib")
        .env("RUSTC_WORKSPACE_WRAPPER", wrapper)
        .env("ANNEAL_CAPTURE_DIR", &units_dir)
        .env("RUSTFLAGS", rustflags)
        .env_remove(ANNEAL_CAPTURE_FILTER_ENV)
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

    let lib_rs_path = corpus_root.join("src/lib.rs");
    let lib_rs = fs::read_to_string(&lib_rs_path)
        .map_err(|err| format!("failed to read {}: {}", lib_rs_path.display(), err))?;
    // Model-marked (`__ANNEAL_MODEL_<name>`) helper functions are linked as
    // intra-crate callees exactly when the evaluated items reach them.
    let reachable_helpers = staged_helper_fns_reachable_from_candidates(&lib_rs, items);

    let subject_records: Vec<_> = records
        .iter()
        .filter(|r| {
            if r.item_kind.as_str() == "subject" {
                return true;
            }
            if r.item_kind.as_str() == "model" && !r.target.def_id.contains("::__ANNEAL_MODEL_") {
                let short = r
                    .target
                    .def_id
                    .rsplit("::")
                    .next()
                    .unwrap_or(&r.target.def_id);
                return reachable_helpers.contains(short);
            }
            false
        })
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

    let subject_pairs: Vec<(String, String)> = subject_records
        .iter()
        .map(|rec| {
            let short = rec
                .target
                .def_id
                .rsplit("::")
                .next()
                .unwrap_or(&rec.target.def_id)
                .to_string();
            let suffix = derive_item_module_suffix(rec);
            (short, suffix)
        })
        .collect();

    let (captured_candidates, helper_module_suffixes) =
        partition_subject_callees(&crate_camel, &subject_pairs, items);

    let mut present_items: Vec<(OracleItemSpec, String)> = Vec::new();
    let mut anneal_outcomes: BTreeMap<String, AnnealOutcome> = BTreeMap::new();
    for item in items {
        if let Some(cand_suffix) = captured_candidates.get(&item.name) {
            present_items.push((item.clone(), cand_suffix.clone()));
        } else {
            anneal_outcomes.insert(
                item.name.clone(),
                AnnealOutcome::CaptureOrLeanError(format!(
                    "item '{}' was not found among captured MIR subjects",
                    item.name
                )),
            );
        }
    }

    let dot_anneal = corpus_root.join(".anneal");
    let oracle_dir = dot_anneal.join("oracle");
    let lake_bin = resolve_lake_bin();
    let mut anneal_panic_frames: BTreeMap<String, String> = BTreeMap::new();
    let mut anneal_panic_messages: BTreeMap<String, Vec<u8>> = BTreeMap::new();

    clean_oracle_files_with_prefixes(&oracle_dir, &["MiriOracleProbe", "MiriOracleConfirm"]);

    if !present_items.is_empty() {
        let _lean_guard = acquire_live_lean_oracle_lock();
        let build_threads = resolve_miri_lake_build_threads();
        let lean_jobs = resolve_miri_lean_jobs();

        // Stage 0: Pre-build only shared base modules (`SymbolicEval`, optional
        // `Mir.Common`, and helper `Mir.<suffix>` modules). Never pass the
        // umbrella `"Mir"` target, which fans out across all 800+ corpus
        // candidate modules simultaneously and triggers cgroup OOM kills.
        // Every probe chunk imports every helper, so a Stage 0 failure is
        // systematic and fails the run closed.
        let stage0_groups = plan_miri_stage0_build_groups(
            dot_anneal.join("generated/Mir/Common.lean").is_file(),
            &helper_module_suffixes,
        );
        for (group_idx, group) in stage0_groups.iter().enumerate() {
            let group_refs: Vec<&str> = group.iter().map(String::as_str).collect();
            let threads = if group_idx == 0 {
                build_threads.base
            } else {
                build_threads.mir_chunks
            };
            run_lake_build_with_bin_and_threads(&lake_bin, &dot_anneal, &group_refs, Some(threads))
                .map_err(|e| {
                    format!(
                        "miri-difftest Stage 0 shared-base Lake build (group {group_idx} of {}, \
                         LEAN_NUM_THREADS={threads}) failed: {e}",
                        stage0_groups.len()
                    )
                })?;
        }

        // Stage 1a: Build corpus candidate `Mir.<cand_suffix>` targets in chunks
        // of `MIRI_PROBE_CHUNK_SIZE` (sequentially across chunks so `.lake`
        // metadata never contends, with `LEAN_NUM_THREADS` capped at `<= 4` by
        // memory/cgroup headroom or set by `ANNEAL_MIRI_LEAN_JOBS`). A failing
        // chunk isolates per-candidate with `MIRI_FALLBACK_CIRCUIT_BREAKER`.
        let mir_build_stage = run_isolated_miri_stage(
            "MiriMirBuild",
            &present_items,
            MIRI_PROBE_CHUNK_SIZE,
            1,
            |(spec, _): &(OracleItemSpec, String)| spec.name.as_str(),
            |_chunk_idx, _is_fallback, _label, chunk| {
                let targets = miri_candidate_build_targets(&crate_camel, chunk);
                let target_refs: Vec<&str> = targets.iter().map(String::as_str).collect();
                run_lake_build_with_bin_and_threads(
                    &lake_bin,
                    &dot_anneal,
                    &target_refs,
                    Some(build_threads.mir_chunks),
                )?;
                Ok(chunk
                    .iter()
                    .map(|(spec, _)| (spec.name.clone(), ()))
                    .collect())
            },
        );
        for err in &mir_build_stage.errors {
            eprintln!("miri-difftest: Stage 1a Lean Mir module build failure: {err}");
        }
        let mut surviving_items: Vec<(OracleItemSpec, String)> =
            Vec::with_capacity(present_items.len());
        for (item, suffix) in &present_items {
            if let Some(reason) = mir_build_stage.failed_reasons.get(&item.name) {
                anneal_outcomes.insert(
                    item.name.clone(),
                    AnnealOutcome::CaptureOrLeanError(reason.clone()),
                );
            } else {
                surviving_items.push((item.clone(), suffix.clone()));
            }
        }

        // Stage 1b: Evaluate `oracle/MiriOracleProbe_{chunk_idx:03}.lean` per
        // surviving chunk across up to `lean_jobs` concurrent workers, each
        // bounded to `LEAN_NUM_THREADS=1`.
        if !surviving_items.is_empty() {
            fs::create_dir_all(&oracle_dir)
                .map_err(|err| format!("failed to create {}: {}", oracle_dir.display(), err))?;
            clean_oracle_files_with_prefixes(&oracle_dir, &["MiriOracleProbe"]);

            let probe_errors = aggregate_miri_probe_stage(
                &surviving_items,
                MIRI_PROBE_CHUNK_SIZE,
                lean_jobs,
                |chunk_idx, run_kind, _label, chunk| {
                    let probe_rss_budget_kib = resolve_miri_lean_rss_budget_kib(
                        PROBE_LEAN_RSS_BUDGET_MIB,
                        run_kind.active_workers(),
                    );
                    let file_name = miri_probe_module_file_name(chunk_idx, run_kind, chunk);
                    let probe_path = oracle_dir.join(&file_name);
                    let rel_probe_path = format!("oracle/{file_name}");
                    let probe_src = render_linked_anneal_probe_module(
                        &crate_camel,
                        chunk,
                        &helper_module_suffixes,
                    );
                    fs::write(&probe_path, &probe_src).map_err(|err| {
                        format!("failed to write {}: {}", probe_path.display(), err)
                    })?;

                    let mut probe_cmd = Command::new(&lake_bin);
                    probe_cmd
                        .current_dir(&dot_anneal)
                        .env("LEAN_NUM_THREADS", "1")
                        .arg("env")
                        .arg("lean")
                        .arg("-M")
                        .arg(PROBE_LEAN_MEMORY_MB)
                        .arg(&rel_probe_path);
                    let probe_run = run_lean_with_rss_budget(&mut probe_cmd, Some(probe_rss_budget_kib))
                        .map_err(|err| {
                            format!(
                                "failed to execute '{} env lean -M {PROBE_LEAN_MEMORY_MB} {rel_probe_path}': {err}",
                                lake_bin.display()
                            )
                        })?;
                    let probe_out = &probe_run.output;
                    if let Some(observed_kib) = probe_run.budget_exceeded_kib {
                        let stdout = String::from_utf8_lossy(&probe_out.stdout);
                        let stderr = String::from_utf8_lossy(&probe_out.stderr);
                        return Err(format_lean_command_failure(
                            &format!(
                                "Lean probe evaluation for {rel_probe_path} in {}: {}",
                                dot_anneal.display(),
                                rss_budget_kill_note(probe_rss_budget_kib, observed_kib)
                            ),
                            &stdout,
                            &stderr,
                        ));
                    }
                    if !probe_out.status.success() {
                        let stdout = String::from_utf8_lossy(&probe_out.stdout);
                        let stderr = String::from_utf8_lossy(&probe_out.stderr);
                        return Err(format_lean_command_failure(
                            &format!(
                                "Lean probe evaluation failed in {} ({}) for {rel_probe_path}",
                                dot_anneal.display(),
                                probe_out.status
                            ),
                            &stdout,
                            &stderr,
                        ));
                    }
                    Ok(String::from_utf8_lossy(&probe_out.stdout).into_owned())
                },
                &mut anneal_outcomes,
                &mut anneal_panic_frames,
                &mut anneal_panic_messages,
            );
            for err in &probe_errors {
                eprintln!("miri-difftest: Stage 1b Lean probe failure: {err}");
            }
            clean_oracle_files_with_prefixes(
                &oracle_dir,
                &["MiriOracleProbeFallback_", "MiriOracleProbeRemainder_"],
            );
        }
    }

    let lib_src = StagedLibSource::parse(&lib_rs);

    let mut reports = Vec::with_capacity(items.len());
    let mut to_confirm: Vec<(OracleItemSpec, String, AnnealOutcome)> = Vec::new();
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
        let anneal_panic_message = anneal_panic_messages
            .get(&spec.name)
            .map(|bytes| String::from_utf8_lossy(bytes).into_owned());
        let verdict = compare_difftest_miri_and_anneal(
            &miri,
            &anneal,
            anneal_panic_message.as_deref(),
            anneal_panic_frames.get(&spec.name).map(String::as_str),
            &lib_src,
            &spec.name,
        );
        // A reconciled panic-macro site agrees only through the panic-site rule
        // in `compare_difftest_miri_and_anneal`, so its Anneal outcome, span,
        // and recovered message are confirmed in the kernel, like a
        // divergence's, rather than resting on the compiled `#eval` probe
        // alone.
        let reconciled_panic_site =
            verdict.is_agree() && !compare_miri_and_anneal(&miri, &anneal).is_agree();
        let should_confirm = (verdict.is_diverge() || reconciled_panic_site)
            && anneal.to_lean_mir_diff_tag().is_some();
        if should_confirm {
            let suffix = captured_candidates
                .get(&spec.name)
                .cloned()
                .unwrap_or_else(|| format!("{crate_camel}.{}", spec.name));
            to_confirm.push((spec.clone(), suffix, anneal.clone()));
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
        fs::create_dir_all(&oracle_dir)
            .map_err(|err| format!("failed to create {}: {}", oracle_dir.display(), err))?;
        clean_oracle_files_with_prefixes(&oracle_dir, &["MiriOracleConfirm"]);
        let confirm_path = oracle_dir.join("MiriOracleConfirm.lean");
        let write_confirm_module_at =
            |dest: &Path, entries: &[(OracleItemSpec, String, AnnealOutcome)]| -> Result<(), String> {
                let entry_specs: Vec<OracleItemSpec> =
                    entries.iter().map(|(spec, _, _)| spec.clone()).collect();
                let entry_helper_suffixes = confirm_helper_module_suffixes(
                    &lib_rs,
                    &crate_camel,
                    &subject_pairs,
                    &helper_module_suffixes,
                    &entry_specs,
                );
                let src = render_linked_anneal_confirm_module(
                    &crate_camel,
                    entries,
                    &entry_helper_suffixes,
                    &anneal_panic_frames,
                    &anneal_panic_messages,
                )?;
                fs::write(dest, &src)
                    .map_err(|err| format!("failed to write {}: {}", dest.display(), err))
            };

        let _lean_guard = acquire_live_lean_oracle_lock();
        let lean_jobs = resolve_miri_lean_jobs().max(1);
        let stage = run_chunked_miri_confirm_stage(
            &to_confirm,
            MIRI_CONFIRM_CHUNK_SIZE,
            lean_jobs,
            |file_name, entries| write_confirm_module_at(&oracle_dir.join(file_name), entries),
            |file_name, active_workers| {
                let budget_kib = resolve_miri_lean_rss_budget_kib(
                    CONFIRM_LEAN_RSS_BUDGET_MIB,
                    active_workers,
                );
                run_lean_confirm_file(
                    &lake_bin,
                    &dot_anneal,
                    &format!("oracle/{file_name}"),
                    budget_kib,
                )
            },
        );
        clean_oracle_files_with_prefixes(
            &oracle_dir,
            &["MiriOracleConfirm_", "MiriOracleConfirmFallback_"],
        );
        let ChunkedMiriConfirm {
            confirmed: confirmed_items,
            confirmed_groups,
            unconfirmed: unconfirmed_names,
        } = stage.map_err(|e| format!("{e}\n(kernel confirmation modules in {})", oracle_dir.display()))?;
        for (name, reason) in &unconfirmed_names {
            eprintln!(
                "miri-difftest: Stage 2 kernel confirmation of `{name}` exhausted a resource; \
                 reporting kernel_confirmed = false: {reason}"
            );
        }
        for rep in &mut reports {
            if unconfirmed_names.contains_key(&rep.name) {
                rep.kernel_confirmed = false;
            }
        }
        if confirmed_items.is_empty() {
            let _ = fs::remove_file(&confirm_path);
            None
        } else {
            // Preserve each kernel-confirmed group's exact `linkedCallees` list
            // in its own `namespace MiriOracleConfirm_{idx:03}` (or flat
            // `namespace MiriOracleConfirm` when `confirmed_groups.len() == 1`)
            // so `extract_confirm_theorems` never mixes callees across chunks.
            let mut groups_with_helpers: Vec<(Vec<MiriConfirmEntry>, Vec<String>)> =
                Vec::with_capacity(confirmed_groups.len());
            for group in confirmed_groups {
                let group_specs: Vec<OracleItemSpec> =
                    group.iter().map(|(spec, _, _)| spec.clone()).collect();
                let group_helpers = confirm_helper_module_suffixes(
                    &lib_rs,
                    &crate_camel,
                    &subject_pairs,
                    &helper_module_suffixes,
                    &group_specs,
                );
                groups_with_helpers.push((group, group_helpers));
            }
            let multi_src = render_multi_group_anneal_confirm_module(
                &crate_camel,
                &groups_with_helpers,
                &anneal_panic_frames,
                &anneal_panic_messages,
            )?;
            fs::write(&confirm_path, &multi_src)
                .map_err(|err| format!("failed to write {}: {}", confirm_path.display(), err))?;
            Some(confirm_path.clone())
        }
    };

    Ok(LinkedDifftestOracleRun {
        report: DifftestOracleReport {
            crate_camel,
            items: reports,
            agree_count,
            diverge_count,
            not_compared_count,
            confirm_module_path,
        },
        anneal_panic_frames,
        anneal_panic_messages,
    })
}

fn discover_reproducer_candidate_fn(source: &str) -> Option<String> {
    if let Ok(parsed) = syn::parse_file(source) {
        let mut pub_zero_arg = Vec::new();
        for item in parsed.items {
            if let syn::Item::Fn(func) = item
                && matches!(func.vis, syn::Visibility::Public(_))
                && func.sig.inputs.is_empty()
            {
                let name = func.sig.ident.to_string();
                if !crate::mutators_miri::is_corpus_helper_fn_name(&name) {
                    pub_zero_arg.push(name);
                }
            }
        }
        if let Some(last) = pub_zero_arg.pop() {
            return Some(last);
        }
    }
    discover_zero_arg_pub_fns(source)
        .into_iter()
        .filter(|name| !crate::mutators_miri::is_corpus_helper_fn_name(name))
        .last()
}

/// Render a mutator chain for `SUMMARY.md` (`"identity (none)"` when empty).
fn render_mutator_chain_md(chain: &[String]) -> String {
    if chain.is_empty() {
        "identity (none)".to_string()
    } else {
        chain.join(", ")
    }
}

fn write_finding_bundle_to_dir(
    findings_dir: &Path,
    finding: &mut MiriFindingBundle,
) -> Result<(), String> {
    let bundle_dir = findings_dir.join(&finding.finding_id);
    fs::create_dir_all(&bundle_dir)
        .map_err(|e| format!("failed to create finding dir {}: {e}", bundle_dir.display()))?;
    let repro_path = bundle_dir.join("repro.rs");
    fs::write(&repro_path, &finding.mutant_source)
        .map_err(|e| format!("failed to write {}: {e}", repro_path.display()))?;
    finding.repro_path = Some(repro_path.clone());

    let finding_json = render_finding_bundle_json(finding, 0);
    fs::write(bundle_dir.join("finding.json"), format!("{finding_json}\n"))
        .map_err(|e| format!("failed to write finding.json in {}: {e}", bundle_dir.display()))?;

    let summary_md = format!(
        "# Divergence Finding `{}`\n\n\
         - **Candidate function**: `{}`\n\
         - **Seed function**: `{}`\n\
         - **Applied mutators**: `{}`\n\
         - **Original mutator chain**: `{}`\n\
         - **Minimized mutator chain**: `{}`\n\
         - **Shrink status**: `{}`\n\
         - **Shrink evaluations**: `{}` (live oracle runs executed: `{}`)\n\
         - **Divergence class**: `{}`\n\
         - **Witness polarity**: `{}`\n\
         - **Miri outcome**: `{}` (repro position: `{}`)\n\
         - **Anneal outcome**: `{}` (`{}` at `{}`)\n\
         - **Lean 4 kernel confirmed (`by rfl`)**: `{}`\n\
         - **Standalone reproducer**: `{}`\n\n\
         ## Miri Output Excerpt\n\n\
         ```text\n{}\n```\n\n\
         ## Lean 4 Kernel Confirmation Theorems (`MiriOracleConfirm.lean`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Captured MIR Neighborhood (`.anneal/generated/Mir`)\n\n\
         ```lean\n{}\n```\n\n\
         ## Mutant Source (`repro.rs`)\n\n\
         ```rust\n{}\n```\n",
        finding.finding_id,
        finding.fn_name,
        finding.seed_name,
        render_mutator_chain_md(&finding.applied_mutators),
        render_mutator_chain_md(&finding.original_mutator_chain),
        render_mutator_chain_md(&finding.minimized_mutator_chain),
        finding.shrink_status,
        finding.shrink_evaluations,
        finding.executed_oracle_runs,
        finding.divergence_class,
        finding.witness_polarity,
        finding.miri_outcome_tag,
        finding.miri_pos.as_deref().unwrap_or("none"),
        finding.anneal_outcome_tag,
        finding.anneal_lean_tag,
        finding.anneal_span.as_deref().unwrap_or("none"),
        finding.kernel_confirmed,
        repro_path.display(),
        finding.miri_excerpt,
        finding.kernel_confirm_theorems,
        finding.mir_neighborhood.trim_end(),
        finding.mutant_source.trim_end(),
    );
    fs::write(bundle_dir.join("SUMMARY.md"), summary_md)
        .map_err(|e| format!("failed to write SUMMARY.md in {}: {e}", bundle_dir.display()))?;
    Ok(())
}

/// Evaluate generated `batches` through `compile_candidates` followed by the
/// live helper-linked Miri + Anneal oracle pipeline, optionally writing finding
/// bundles under `findings_dir`.
///
/// Every finding's mutator chain is shrunk against the live oracle
/// ([`minimize_miri_candidate_mutations`]) by replaying it against the
/// `tests/miri-diff/corpus` seeds, from which `miri-difftest` generates every
/// mutated candidate; see [`evaluate_miri_batches_with_options`] for batches
/// generated from other seeds.
pub fn evaluate_miri_batches(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedMiriCandidate>],
    batch_size: usize,
    findings_dir: Option<&Path>,
    anneal_repo_root: Option<&Path>,
) -> Result<MiriCampaignEvalReport, String> {
    let options = MiriEvalOptions {
        findings_dir: findings_dir.map(Path::to_path_buf),
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        shrink_seeds: None,
    };
    evaluate_miri_batches_with_options(mode, seed, batches, batch_size, &options)
}

/// Optional configuration for [`evaluate_miri_batches_with_options`].
#[derive(Debug, Clone, Default)]
pub struct MiriEvalOptions {
    /// Directory where self-contained finding bundles are written.
    pub findings_dir: Option<PathBuf>,
    /// Path to the Anneal repository root (`trusted/lean` and `theory`).
    pub anneal_repo_root: Option<PathBuf>,
    /// Seed sources the batches were generated from (with
    /// [`crate::mutators_miri::generate_miri_batch`]), against which finding
    /// mutator chains are replayed and shrunk. `None` means the
    /// `tests/miri-diff/corpus` seeds of
    /// [`crate::mutators_miri::generate_miri_corpus_batch`].
    pub shrink_seeds: Option<Vec<String>>,
}

/// [`evaluate_miri_batches`] with explicit [`MiriEvalOptions`].
pub fn evaluate_miri_batches_with_options(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedMiriCandidate>],
    batch_size: usize,
    options: &MiriEvalOptions,
) -> Result<MiriCampaignEvalReport, String> {
    let findings_dir = options.findings_dir.as_deref();
    let anneal_repo_root = options.anneal_repo_root.as_deref();
    let start = Instant::now();
    let toolchain = MiriToolchain::resolve(None, None, None)?;

    let total_candidates: usize = batches.iter().map(Vec::len).sum();
    let compile_results = compile_candidates(batches);
    let compiled_candidates = compile_results.iter().flatten().filter(|&&ok| ok).count();
    let compile_failed_candidates = total_candidates.saturating_sub(compiled_candidates);
    let compile_pass_rate_pct = if total_candidates == 0 {
        0.0
    } else {
        (compiled_candidates as f64 / total_candidates as f64) * 100.0
    };

    let mut mutator_applications: BTreeMap<String, usize> = MIRI_MUTATOR_NAMES
        .iter()
        .map(|m| (m.to_string(), 0))
        .collect();
    for cand in batches.iter().flatten() {
        for m in &cand.applied_mutators {
            *mutator_applications.entry(m.clone()).or_insert(0) += 1;
        }
    }

    let mut miri_verdicts: BTreeMap<String, usize> = ["pass", "panic", "ub", "error"]
        .into_iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    let mut anneal_outcomes: BTreeMap<String, usize> = [
        "pass",
        "panic",
        "ub",
        "external_call",
        "unsupported",
        "out_of_fuel",
        "error",
    ]
    .into_iter()
    .map(|k| (k.to_string(), 0))
    .collect();
    let mut divergence_classes: BTreeMap<String, usize> = DIVERGENCE_CLASS_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    let mut witness_polarity_counts: BTreeMap<String, usize> = WITNESS_POLARITY_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    witness_polarity_counts.insert(
        WitnessPolarity::HarnessOrExtractionError.as_str().to_string(),
        compile_failed_candidates,
    );
    let mut not_compared_reasons: BTreeMap<String, usize> = NOT_COMPARED_REASON_NAMES
        .iter()
        .map(|k| (k.to_string(), 0))
        .collect();
    not_compared_reasons.insert("compile_failed".to_string(), compile_failed_candidates);
    let mut unmodeled_external_calls: BTreeMap<String, usize> = BTreeMap::new();

    if compiled_candidates == 0 {
        return Err(format!(
            "cannot perform oracle comparison: 0 of {total_candidates} candidates compiled"
        ));
    }

    let repro_prefix = format!("{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n");
    let repro_start_line = repro_prefix.lines().count() as u32 + 1;

    let mut staged_lib_rs = repro_prefix;
    let mut item_specs: Vec<OracleItemSpec> = Vec::with_capacity(compiled_candidates);
    let mut cand_by_name: BTreeMap<String, (&GeneratedMiriCandidate, u32)> = BTreeMap::new();

    for (b_idx, batch) in batches.iter().enumerate() {
        for (c_idx, cand) in batch.iter().enumerate() {
            if !compile_results[b_idx][c_idx] {
                continue;
            }
            let batch_start_line = staged_lib_rs.lines().count() as u32 + 1;
            staged_lib_rs.push_str(cand.fn_source.trim());
            staged_lib_rs.push_str("\n\n");
            let candidate_fuel = if mode == "identity" {
                DEFAULT_ORACLE_FUEL
            } else {
                MIRI_DIFFTEST_CANDIDATE_FUEL
            };
            item_specs.push(OracleItemSpec::with_fuel(
                cand.fn_name.clone(),
                candidate_fuel,
            ));
            cand_by_name.insert(cand.fn_name.clone(), (cand, batch_start_line));
        }
    }

    let staging_dir = create_staging_dir(mode)?;
    let write_res = fs::write(staging_dir.join("src/lib.rs"), &staged_lib_rs)
        .map_err(|e| format!("failed to write staged src/lib.rs: {e}"));
    if let Err(e) = write_res {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(e);
    }

    let oracle_cfg = DifftestOracleConfig {
        corpus_root: staging_dir.clone(),
        capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        rustc_wrapper: None,
        toolchain,
    };

    let LinkedDifftestOracleRun {
        report: oracle_report,
        anneal_panic_frames,
        anneal_panic_messages,
    } = match run_linked_difftest_oracle_pipeline(&oracle_cfg, &item_specs) {
        Ok(run) => run,
        Err(e) => {
            let _ = fs::remove_dir_all(&staging_dir);
            return Err(e);
        }
    };

    let confirm_src = oracle_report
        .confirm_module_path
        .as_ref()
        .and_then(|p| fs::read_to_string(p).ok())
        .unwrap_or_default();

    let mut findings = Vec::new();
    let mut reconciled_panic_sites = Vec::new();
    let mut kernel_confirmed_divergences = 0usize;
    let mut obs_path_signatures_set = std::collections::BTreeSet::new();
    let shrink_seeds: Vec<String> = match &options.shrink_seeds {
        Some(seeds) => seeds.clone(),
        None => load_miri_diff_corpus_seeds()
            .into_iter()
            .map(|s| s.fn_source)
            .collect(),
    };
    let shrink_seed_refs: Vec<&str> = shrink_seeds.iter().map(String::as_str).collect();

    for item_rep in &oracle_report.items {
        let miri_sig_tag = match &item_rep.miri {
            MiriOutcome::PassUnit => "pass_unit".to_string(),
            MiriOutcome::PassScalar { size_bytes, .. } => format!("pass_scalar_{size_bytes}"),
            MiriOutcome::Panic { .. } => "panic".to_string(),
            MiriOutcome::Ub { .. } => "ub".to_string(),
            MiriOutcome::OracleError(_) => "error".to_string(),
        };
        let anneal_sig_tag = match &item_rep.anneal {
            AnnealOutcome::PassUnit => "pass_unit".to_string(),
            AnnealOutcome::PassScalar { size_bytes, .. } => format!("pass_scalar_{size_bytes}"),
            AnnealOutcome::PassOther => "pass_other".to_string(),
            AnnealOutcome::Panic { .. } => "panic".to_string(),
            AnnealOutcome::Abort { .. } => "abort".to_string(),
            AnnealOutcome::Ub { .. } => "ub".to_string(),
            AnnealOutcome::ExternalCall { .. } => "external_call".to_string(),
            AnnealOutcome::Unsupported { .. } => "unsupported".to_string(),
            AnnealOutcome::OutOfFuel { .. } => "out_of_fuel".to_string(),
            AnnealOutcome::CaptureOrLeanError(_) => "error".to_string(),
        };
        let diff_sig_tag = match &item_rep.verdict {
            ComparisonVerdict::Agree => "agree".to_string(),
            ComparisonVerdict::Diverge(div_kind) => divergence_class_slug(div_kind).to_string(),
            ComparisonVerdict::NotCompared(reason) => match reason {
                NotComparedReason::ExternalCall(_) => "not_compared_external_call".to_string(),
                NotComparedReason::Unsupported(_) => "not_compared_unsupported".to_string(),
                NotComparedReason::OutOfFuel(_) => "not_compared_out_of_fuel".to_string(),
                NotComparedReason::MiriOracleError(_) => "not_compared_miri_oracle_error".to_string(),
                NotComparedReason::CaptureFailed(_) => "not_compared_capture_failed".to_string(),
            },
        };
        let template_and_chain = if let Some((cand, _)) = cand_by_name.get(&item_rep.name) {
            if cand.applied_mutators.is_empty() {
                format!("{}@identity", cand.seed_name)
            } else {
                format!("{}@{}", cand.seed_name, cand.applied_mutators.join("+"))
            }
        } else {
            item_rep.name.clone()
        };
        obs_path_signatures_set.insert(format!(
            "miri:{template_and_chain}:{miri_sig_tag}_vs_{anneal_sig_tag}:{diff_sig_tag}"
        ));

        match &item_rep.miri {
            MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. } => {
                *miri_verdicts.entry("pass".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::Panic { .. } => {
                *miri_verdicts.entry("panic".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::Ub { .. } => {
                *miri_verdicts.entry("ub".to_string()).or_insert(0) += 1;
            }
            MiriOutcome::OracleError(_) => {
                *miri_verdicts.entry("error".to_string()).or_insert(0) += 1;
            }
        }

        match &item_rep.anneal {
            AnnealOutcome::PassUnit
            | AnnealOutcome::PassScalar { .. }
            | AnnealOutcome::PassOther => {
                *anneal_outcomes.entry("pass".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Panic { .. } | AnnealOutcome::Abort { .. } => {
                *anneal_outcomes.entry("panic".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Ub { .. } => {
                *anneal_outcomes.entry("ub".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::ExternalCall { .. } => {
                *anneal_outcomes.entry("external_call".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::Unsupported { .. } => {
                *anneal_outcomes.entry("unsupported".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::OutOfFuel { .. } => {
                *anneal_outcomes.entry("out_of_fuel".to_string()).or_insert(0) += 1;
            }
            AnnealOutcome::CaptureOrLeanError(_) => {
                *anneal_outcomes.entry("error".to_string()).or_insert(0) += 1;
            }
        }

        if let Some(pol) =
            classify_verdict_witness_polarity(&item_rep.miri, &item_rep.anneal, &item_rep.verdict)
        {
            *witness_polarity_counts
                .entry(pol.as_str().to_string())
                .or_insert(0) += 1;
        }

        match &item_rep.verdict {
            ComparisonVerdict::Agree => {
                if !compare_miri_and_anneal(&item_rep.miri, &item_rep.anneal).is_agree() {
                    let batch_miri_pos = match &item_rep.miri {
                        MiriOutcome::Panic { pos, .. } => {
                            pos.as_ref().map(SourcePos::display_short)
                        }
                        _ => None,
                    };
                    reconciled_panic_sites.push(MiriReconciledPanicSite {
                        fn_name: item_rep.name.clone(),
                        seed_name: cand_by_name
                            .get(&item_rep.name)
                            .map(|(cand, _)| cand.seed_name.clone())
                            .unwrap_or_default(),
                        batch_miri_pos,
                        anneal_span: item_rep.anneal.span().map(SourceSpan::display_short),
                        anneal_panic_frame: anneal_panic_frames.get(&item_rep.name).cloned(),
                        anneal_panic_message: anneal_panic_messages
                            .get(&item_rep.name)
                            .map(|bytes| String::from_utf8_lossy(bytes).into_owned()),
                        kernel_confirmed: item_rep.kernel_confirmed,
                        kernel_confirm_theorems: extract_confirm_theorems(
                            &confirm_src,
                            &item_rep.name,
                        ),
                    });
                }
            }
            ComparisonVerdict::NotCompared(reason) => match reason {
                NotComparedReason::ExternalCall(callee) => {
                    *not_compared_reasons
                        .entry("external_call".to_string())
                        .or_insert(0) += 1;
                    *unmodeled_external_calls.entry(callee.clone()).or_insert(0) += 1;
                }
                NotComparedReason::Unsupported(_) => {
                    *not_compared_reasons
                        .entry("unsupported".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::OutOfFuel(_) => {
                    *not_compared_reasons
                        .entry("out_of_fuel".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::MiriOracleError(_) => {
                    *not_compared_reasons
                        .entry("miri_oracle_error".to_string())
                        .or_insert(0) += 1;
                }
                NotComparedReason::CaptureFailed(_) => {
                    *not_compared_reasons
                        .entry("capture_failed".to_string())
                        .or_insert(0) += 1;
                }
            },
            ComparisonVerdict::Diverge(div_kind) => {
                let class_slug = divergence_class_slug(div_kind).to_string();
                *divergence_classes.entry(class_slug.clone()).or_insert(0) += 1;
                let mut item_kernel_confirmed = item_rep.kernel_confirmed;

                if let Some((cand, batch_start_line)) = cand_by_name.get(&item_rep.name) {
                    let (shrink_res, shrink_status) = shrink_divergent_miri_candidate(
                        cand,
                        &shrink_seed_refs,
                        item_rep,
                        anneal_repo_root,
                    );
                    // A reduced candidate replaces the original everywhere in the
                    // bundle that describes `repro.rs`: its program, its report
                    // (already in `repro.rs` coordinates, because the shrink oracle
                    // stages the candidate alone), and the MIR neighborhood and
                    // kernel theorems of the oracle run that accepted it.
                    let reduced = shrink_res.as_ref().filter(|sr| sr.is_reduced());
                    let eff_item_rep = reduced.map_or(item_rep, |sr| &sr.minimized_report);
                    item_kernel_confirmed = eff_item_rep.kernel_confirmed;
                    let eff_cand = reduced.map_or(*cand, |sr| &sr.minimized_candidate);
                    let eff_start_line = if reduced.is_some() {
                        repro_start_line
                    } else {
                        *batch_start_line
                    };

                    let raw_miri_pos = match &eff_item_rep.miri {
                        MiriOutcome::Panic { pos, .. } | MiriOutcome::Ub { pos, .. } => {
                            pos.as_ref()
                        }
                        _ => None,
                    };
                    let batch_miri_pos = match &item_rep.miri {
                        MiriOutcome::Panic { pos, .. } | MiriOutcome::Ub { pos, .. } => {
                            pos.as_ref().map(SourcePos::display_short)
                        }
                        _ => None,
                    };
                    let repro_miri_pos = raw_miri_pos
                        .map(|p| translate_pos_to_repro(p, eff_start_line, repro_start_line))
                        .map(|p| p.display_short());

                    let raw_anneal_span = eff_item_rep.anneal.span();
                    let batch_anneal_span = item_rep.anneal.span().map(SourceSpan::display_short);
                    let repro_anneal_span = raw_anneal_span
                        .map(|s| translate_span_to_repro(s, eff_start_line, repro_start_line))
                        .map(|s| s.display_short());

                    let miri_outcome_tag = match &eff_item_rep.miri {
                        MiriOutcome::PassUnit => "pass:unit".to_string(),
                        MiriOutcome::PassScalar { bits, size_bytes } => {
                            format!("pass:scalar:{bits}:{size_bytes}")
                        }
                        MiriOutcome::Panic { .. } => match &repro_miri_pos {
                            Some(p) => format!("panic@{p}"),
                            None => "panic".to_string(),
                        },
                        MiriOutcome::Ub { .. } => match &repro_miri_pos {
                            Some(p) => format!("ub@{p}"),
                            None => "ub".to_string(),
                        },
                        MiriOutcome::OracleError(e) => format!("oracle_error:{e}"),
                    };

                    let anneal_outcome_tag = match &eff_item_rep.anneal {
                        AnnealOutcome::PassUnit => "pass:unit".to_string(),
                        AnnealOutcome::PassScalar { bits, size_bytes } => {
                            format!("pass:scalar:{bits}:{size_bytes}")
                        }
                        AnnealOutcome::PassOther => "pass:other".to_string(),
                        AnnealOutcome::Panic { .. } => match &repro_anneal_span {
                            Some(s) => format!("panic@{s}"),
                            None => "panic".to_string(),
                        },
                        AnnealOutcome::Abort { .. } => match &repro_anneal_span {
                            Some(s) => format!("abort@{s}"),
                            None => "abort".to_string(),
                        },
                        AnnealOutcome::Ub { .. } => match &repro_anneal_span {
                            Some(s) => format!("ub@{s}"),
                            None => "ub".to_string(),
                        },
                        other => other.summary_tag(),
                    };

                    let miri_excerpt =
                        format_miri_excerpt(&eff_item_rep.miri, repro_miri_pos.as_deref());
                    let anneal_lean_tag = eff_item_rep
                        .anneal
                        .to_lean_mir_diff_tag()
                        .unwrap_or_else(|| "none".to_string());
                    let (mir_neighborhood, kernel_confirm_theorems) = match reduced {
                        Some(sr) => (
                            sr.mir_neighborhood.clone().unwrap_or_default(),
                            sr.kernel_confirm_theorems.clone().unwrap_or_default(),
                        ),
                        None => (
                            extract_mir_neighborhood(
                                &staging_dir,
                                &oracle_report.crate_camel,
                                &item_rep.name,
                            ),
                            extract_confirm_theorems(&confirm_src, &item_rep.name),
                        ),
                    };

                    let finding_id = format!("finding_{:04}_{}", findings.len(), item_rep.name);
                    let mut bundle = MiriFindingBundle {
                        finding_id,
                        fn_name: item_rep.name.clone(),
                        seed_name: cand.seed_name.clone(),
                        applied_mutators: eff_cand.applied_mutators.clone(),
                        original_mutator_chain: cand.applied_mutators.clone(),
                        minimized_mutator_chain: eff_cand.applied_mutators.clone(),
                        shrink_evaluations: shrink_res
                            .as_ref()
                            .map_or(0, |sr| sr.shrink_evaluations),
                        executed_oracle_runs: shrink_res
                            .as_ref()
                            .map_or(0, |sr| sr.executed_oracle_runs),
                        shrink_status,
                        divergence_class: class_slug,
                        witness_polarity: classify_divergence_kind_polarity(div_kind)
                            .as_str()
                            .to_string(),
                        miri_outcome_tag,
                        miri_excerpt,
                        miri_pos: repro_miri_pos,
                        batch_miri_pos,
                        anneal_outcome_tag,
                        anneal_lean_tag,
                        anneal_span: repro_anneal_span,
                        batch_anneal_span,
                        mir_neighborhood,
                        kernel_confirmed: eff_item_rep.kernel_confirmed,
                        kernel_confirm_theorems,
                        mutant_source: eff_cand.source.clone(),
                        repro_path: None,
                    };
                    if let Some(dir) = findings_dir {
                        if let Err(e) = write_finding_bundle_to_dir(dir, &mut bundle) {
                            let _ = fs::remove_dir_all(&staging_dir);
                            return Err(e);
                        }
                    }
                    findings.push(bundle);
                }
                // `item_rep` keeps describing the original candidate's oracle
                // run (its `kernel_confirmed` is never overwritten), while the
                // count follows the evidence each finding reports: the minimized
                // reproducer when shrinking reduced the candidate, else the
                // original.
                if item_kernel_confirmed {
                    kernel_confirmed_divergences += 1;
                }
            }
        }
    }

    let _ = fs::remove_dir_all(&staging_dir);

    let agree_count = oracle_report.agree_count;
    let diverge_count = oracle_report.diverge_count;
    let compared_candidates = agree_count + diverge_count;
    let not_compared_count = compile_failed_candidates + oracle_report.not_compared_count;
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

    let report = MiriCampaignEvalReport {
        mode: mode.to_string(),
        seed,
        batches: batches.len(),
        batch_size,
        total_candidates,
        compiled_candidates,
        compile_failed_candidates,
        compile_pass_rate_pct,
        compared_candidates,
        agree_count,
        diverge_count,
        not_compared_count,
        kernel_confirmed_divergences,
        miri_verdicts,
        anneal_outcomes,
        divergence_classes,
        witness_polarity_counts,
        not_compared_reasons,
        unmodeled_external_calls,
        mutator_applications,
        findings,
        reconciled_panic_sites,
        obs_path_signatures: obs_path_signatures_set.into_iter().collect(),
        item_reports: oracle_report.items,
        elapsed_ms,
    };
    // Fail closed: Episode 2 consumers read `witness_polarity_counts` as a
    // partition of every non-agreement, so an accounting drift must never be
    // reported as a clean campaign.
    if !witness_polarity_accounting_holds(&report) {
        return Err(format!(
            "witness polarity accounting identity violated: witness_polarity_counts={:?}, \
             divergence_classes={:?}, not_compared_reasons={:?}, diverge_count={}, \
             not_compared_count={}",
            report.witness_polarity_counts,
            report.divergence_classes,
            report.not_compared_reasons,
            report.diverge_count,
            report.not_compared_count
        ));
    }
    Ok(report)
}

/// Re-run a standalone `repro.rs` file through the live helper-linked Miri +
/// Anneal oracle pipeline and return its [`ItemOracleReport`].
pub fn reproduce_miri_finding(
    repro_rs_path: &Path,
    anneal_repo_root: Option<&Path>,
) -> Result<ItemOracleReport, String> {
    let source = fs::read_to_string(repro_rs_path)
        .map_err(|e| format!("failed to read {}: {e}", repro_rs_path.display()))?;
    let Some(cand_name) = discover_reproducer_candidate_fn(&source) else {
        return Err(format!(
            "no zero-argument candidate `pub fn` found in {}",
            repro_rs_path.display()
        ));
    };

    let toolchain = MiriToolchain::resolve(None, None, None)?;
    let staging_dir = create_staging_dir("repro")?;
    if let Err(e) = fs::write(staging_dir.join("src/lib.rs"), &source) {
        let _ = fs::remove_dir_all(&staging_dir);
        return Err(format!("failed to write staged repro src/lib.rs: {e}"));
    }

    let specs = vec![OracleItemSpec::with_fuel(
        cand_name,
        MIRI_DIFFTEST_CANDIDATE_FUEL,
    )];
    let cfg = DifftestOracleConfig {
        corpus_root: staging_dir.clone(),
        capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
        miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
        anneal_repo_root: anneal_repo_root.map(Path::to_path_buf),
        rustc_wrapper: None,
        toolchain,
    };

    let res = run_linked_difftest_oracle_pipeline(&cfg, &specs);
    let _ = fs::remove_dir_all(&staging_dir);
    let mut report = res?.report;
    report
        .items
        .drain(..)
        .next()
        .ok_or_else(|| "oracle pipeline returned no item report for reproducer".to_string())
}

/// Escape a string for JSON serialization.
pub fn json_escape(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 2);
    out.push('"');
    for ch in raw.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn render_usize_map_json(map: &BTreeMap<String, usize>, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(indent + 2);
    if map.is_empty() {
        return "{}".to_string();
    }
    let rows: Vec<String> = map
        .iter()
        .map(|(k, v)| format!("{inner_pad}{}: {v}", json_escape(k)))
        .collect();
    format!("{{\n{}\n{pad}}}", rows.join(",\n"))
}

fn render_string_list_json(items: &[String], indent: usize) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(indent + 2);
    let rows: Vec<String> = items
        .iter()
        .map(|s| format!("{inner_pad}{}", json_escape(s)))
        .collect();
    format!("[\n{}\n{pad}]", rows.join(",\n"))
}

fn render_opt_str_json(opt: &Option<String>) -> String {
    match opt {
        Some(s) => json_escape(s),
        None => "null".to_string(),
    }
}

/// Render a [`MiriFindingBundle`] as a JSON object at indentation `indent`.
pub fn render_finding_bundle_json(finding: &MiriFindingBundle, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner = " ".repeat(indent + 2);
    let chain_json = |chain: &[String]| {
        chain
            .iter()
            .map(|m| json_escape(m))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let mutators_json = chain_json(&finding.applied_mutators);
    let orig_mutators_json = chain_json(&finding.original_mutator_chain);
    let min_mutators_json = chain_json(&finding.minimized_mutator_chain);
    let repro_path_json = finding
        .repro_path
        .as_ref()
        .map(|p| json_escape(&p.to_string_lossy()))
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{pad}{{\n\
         {inner}\"finding_id\": {},\n\
         {inner}\"fn_name\": {},\n\
         {inner}\"seed_name\": {},\n\
         {inner}\"applied_mutators\": [{mutators_json}],\n\
         {inner}\"original_mutator_chain\": [{orig_mutators_json}],\n\
         {inner}\"minimized_mutator_chain\": [{min_mutators_json}],\n\
         {inner}\"shrink_evaluations\": {},\n\
         {inner}\"executed_oracle_runs\": {},\n\
         {inner}\"shrink_status\": {},\n\
         {inner}\"divergence_class\": {},\n\
         {inner}\"witness_polarity\": {},\n\
         {inner}\"miri_outcome\": {},\n\
         {inner}\"miri_excerpt\": {},\n\
         {inner}\"miri_pos\": {},\n\
         {inner}\"batch_miri_pos\": {},\n\
         {inner}\"anneal_outcome\": {},\n\
         {inner}\"anneal_lean_tag\": {},\n\
         {inner}\"anneal_span\": {},\n\
         {inner}\"batch_anneal_span\": {},\n\
         {inner}\"mir_neighborhood\": {},\n\
         {inner}\"kernel_confirmed\": {},\n\
         {inner}\"kernel_confirm_theorems\": {},\n\
         {inner}\"mutant_source\": {},\n\
         {inner}\"repro_path\": {repro_path_json}\n\
         {pad}}}",
        json_escape(&finding.finding_id),
        json_escape(&finding.fn_name),
        json_escape(&finding.seed_name),
        finding.shrink_evaluations,
        finding.executed_oracle_runs,
        json_escape(&finding.shrink_status),
        json_escape(&finding.divergence_class),
        json_escape(&finding.witness_polarity),
        json_escape(&finding.miri_outcome_tag),
        json_escape(&finding.miri_excerpt),
        render_opt_str_json(&finding.miri_pos),
        render_opt_str_json(&finding.batch_miri_pos),
        json_escape(&finding.anneal_outcome_tag),
        json_escape(&finding.anneal_lean_tag),
        render_opt_str_json(&finding.anneal_span),
        render_opt_str_json(&finding.batch_anneal_span),
        json_escape(&finding.mir_neighborhood),
        finding.kernel_confirmed,
        json_escape(&finding.kernel_confirm_theorems),
        json_escape(&finding.mutant_source),
    )
}

/// Render the full JSON report for a completed [`MiriCampaignEvalReport`].
pub fn render_eval_report_json(report: &MiriCampaignEvalReport) -> String {
    let findings_json = if report.findings.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = report
            .findings
            .iter()
            .map(|f| render_finding_bundle_json(f, 4))
            .collect();
        format!("[\n{}\n  ]", items.join(",\n"))
    };
    let item_outcomes_json = render_item_outcomes_json(&report.item_reports);
    let reconciled_json = if report.reconciled_panic_sites.is_empty() {
        "[]".to_string()
    } else {
        let items: Vec<String> = report
            .reconciled_panic_sites
            .iter()
            .map(|site| render_reconciled_panic_site_json(site, 4))
            .collect();
        format!("[\n{}\n  ]", items.join(",\n"))
    };

    format!(
        "{{\n\
         \x20 \"harness\": \"miri-difftest\",\n\
         \x20 \"oracle_comparison\": \"performed\",\n\
         \x20 \"mode\": {},\n\
         \x20 \"seed\": \"0x{:08x}\",\n\
         \x20 \"batches\": {},\n\
         \x20 \"batch_size\": {},\n\
         \x20 \"total_candidates\": {},\n\
         \x20 \"compiled_candidates\": {},\n\
         \x20 \"compile_failed_candidates\": {},\n\
         \x20 \"compile_pass_rate_pct\": {:.2},\n\
         \x20 \"compared_candidates\": {},\n\
         \x20 \"agree_count\": {},\n\
         \x20 \"diverge_count\": {},\n\
         \x20 \"not_compared_count\": {},\n\
         \x20 \"kernel_confirmed_divergences\": {},\n\
         \x20 \"miri_verdicts\": {},\n\
         \x20 \"anneal_outcomes\": {},\n\
         \x20 \"divergence_classes\": {},\n\
         \x20 \"witness_polarity_counts\": {},\n\
         \x20 \"not_compared_reasons\": {},\n\
         \x20 \"unmodeled_external_calls\": {},\n\
         \x20 \"mutator_applications\": {},\n\
         \x20 \"obs_path_signatures\": {},\n\
         \x20 \"item_outcomes\": {item_outcomes_json},\n\
         \x20 \"findings_count\": {},\n\
         \x20 \"findings\": {findings_json},\n\
         \x20 \"reconciled_panic_sites_count\": {},\n\
         \x20 \"reconciled_panic_sites\": {reconciled_json},\n\
         \x20 \"elapsed_ms\": {:.2}\n\
         }}\n",
        json_escape(&report.mode),
        report.seed,
        report.batches,
        report.batch_size,
        report.total_candidates,
        report.compiled_candidates,
        report.compile_failed_candidates,
        report.compile_pass_rate_pct,
        report.compared_candidates,
        report.agree_count,
        report.diverge_count,
        report.not_compared_count,
        report.kernel_confirmed_divergences,
        render_usize_map_json(&report.miri_verdicts, 2),
        render_usize_map_json(&report.anneal_outcomes, 2),
        render_usize_map_json(&report.divergence_classes, 2),
        render_usize_map_json(&report.witness_polarity_counts, 2),
        render_usize_map_json(&report.not_compared_reasons, 2),
        render_usize_map_json(&report.unmodeled_external_calls, 2),
        render_usize_map_json(&report.mutator_applications, 2),
        render_string_list_json(&report.obs_path_signatures, 2),
        report.findings.len(),
        report.reconciled_panic_sites.len(),
        report.elapsed_ms,
    )
}

/// Render the per-item verdicts of a run as a JSON object mapping each
/// evaluated item name to its verdict (`"agree"`, `"diverge"`, or
/// `"not_compared"`), Miri and Anneal outcome tags, and Lean `MirDiffTag`.
///
/// Every compiled candidate appears, so consumers can audit each manifest entry
/// (for example a `known_anneal_bug`) against the live outcome of its item.
fn render_item_outcomes_json(item_reports: &[ItemOracleReport]) -> String {
    if item_reports.is_empty() {
        return "{}".to_string();
    }
    let rows: Vec<String> = item_reports
        .iter()
        .map(|item_rep| {
            let verdict = match &item_rep.verdict {
                ComparisonVerdict::Agree => "agree",
                ComparisonVerdict::Diverge(_) => "diverge",
                ComparisonVerdict::NotCompared(_) => "not_compared",
            };
            let lean_tag = item_rep
                .anneal
                .to_lean_mir_diff_tag()
                .unwrap_or_else(|| "none".to_string());
            format!(
                "    {}: {{\"verdict\": {}, \"miri_outcome\": {}, \"anneal_outcome\": {}, \"anneal_lean_tag\": {}}}",
                json_escape(&item_rep.name),
                json_escape(verdict),
                json_escape(&item_rep.miri.summary_tag()),
                json_escape(&item_rep.anneal.summary_tag()),
                json_escape(&lean_tag),
            )
        })
        .collect();
    format!("{{\n{}\n  }}", rows.join(",\n"))
}

/// Render a [`MiriReconciledPanicSite`] as a JSON object, omitting its
/// kernel-checked theorem snippet.
fn render_reconciled_panic_site_json(site: &MiriReconciledPanicSite, indent: usize) -> String {
    let pad = " ".repeat(indent);
    let inner = " ".repeat(indent + 2);
    format!(
        "{pad}{{\n\
         {inner}\"fn_name\": {},\n\
         {inner}\"seed_name\": {},\n\
         {inner}\"batch_miri_pos\": {},\n\
         {inner}\"anneal_span\": {},\n\
         {inner}\"anneal_panic_frame\": {},\n\
         {inner}\"anneal_panic_message\": {},\n\
         {inner}\"kernel_confirmed\": {}\n\
         {pad}}}",
        json_escape(&site.fn_name),
        json_escape(&site.seed_name),
        render_opt_str_json(&site.batch_miri_pos),
        render_opt_str_json(&site.anneal_span),
        render_opt_str_json(&site.anneal_panic_frame),
        render_opt_str_json(&site.anneal_panic_message),
        site.kernel_confirmed,
    )
}

/// Render the human-readable Markdown report for a completed
/// [`MiriCampaignEvalReport`].
pub fn render_eval_report_markdown(report: &MiriCampaignEvalReport) -> String {
    let mut out = String::new();
    out.push_str("# `miri-difftest` Differential Oracle Report\n\n");
    out.push_str("- **Oracle comparison**: PERFORMED (live Miri `-Zmiri-tree-borrows` vs. Anneal `MirSemantics` + Lean 4 kernel confirmation)\n");
    out.push_str(&format!(
        "- **Mode**: `{}` | **Seed**: `0x{:08x}` (`{}` batches × `{}` batch size = `{}` generated)\n",
        report.mode, report.seed, report.batches, report.batch_size, report.total_candidates
    ));
    out.push_str(&format!(
        "- **Compiled with `rustc`**: `{}/{}` ({:.2}%, `{}` compile failures)\n",
        report.compiled_candidates,
        report.total_candidates,
        report.compile_pass_rate_pct,
        report.compile_failed_candidates
    ));
    out.push_str(&format!(
        "- **Compared**: `{}` | **Agree**: `{}` | **Diverge**: `{}` (`{}` kernel-confirmed via `by rfl`) | **NotCompared**: `{}`\n",
        report.compared_candidates,
        report.agree_count,
        report.diverge_count,
        report.kernel_confirmed_divergences,
        report.not_compared_count
    ));
    out.push_str(&format!(
        "- **Reconciled panic-macro sites** (counted in **Agree**): `{}`\n",
        report.reconciled_panic_sites.len()
    ));
    out.push_str(&format!(
        "- **Wall-clock time**: `{:.2} ms`\n\n",
        report.elapsed_ms
    ));

    out.push_str("## Miri Reference Verdicts\n\n");
    out.push_str("| Verdict | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.miri_verdicts {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Anneal Oracle Outcomes\n\n");
    out.push_str("| Outcome | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.anneal_outcomes {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Divergence Breakdown by Class\n\n");
    out.push_str("| Divergence Class | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.divergence_classes {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## Witness Polarity Breakdown\n\n");
    out.push_str("| Witness Polarity | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.witness_polarity_counts {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    out.push_str("\n## `NotCompared` Coverage Table\n\n");
    out.push_str("| Reason | Count |\n| :--- | ---: |\n");
    for (k, v) in &report.not_compared_reasons {
        out.push_str(&format!("| `{k}` | {v} |\n"));
    }

    if !report.unmodeled_external_calls.is_empty() {
        out.push_str("\n### Unmodeled External Calls\n\n");
        out.push_str("| Callee `DefPath` | Count |\n| :--- | ---: |\n");
        for (callee, cnt) in &report.unmodeled_external_calls {
            out.push_str(&format!("| `{callee}` | {cnt} |\n"));
        }
    }

    out.push_str("\n## Mutator Applications\n\n");
    out.push_str("| Mutator | Applications |\n| :--- | ---: |\n");
    for (name, count) in &report.mutator_applications {
        out.push_str(&format!("| `{name}` | {count} |\n"));
    }

    if !report.reconciled_panic_sites.is_empty() {
        out.push_str("\n## Reconciled Panic-Macro Sites\n\n");
        out.push_str("| Function | Miri Position | Anneal Span | Anneal Frame | Anneal Panic Message | Kernel Confirmed |\n");
        out.push_str("| :--- | :--- | :--- | :--- | :--- | :--- |\n");
        for site in &report.reconciled_panic_sites {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | {} | `{}` |\n",
                site.fn_name,
                site.batch_miri_pos.as_deref().unwrap_or("none"),
                site.anneal_span.as_deref().unwrap_or("none"),
                site.anneal_panic_frame.as_deref().unwrap_or("none"),
                site.anneal_panic_message
                    .as_deref()
                    .map(|m| format!("{m:?}").replace('`', "'").replace('|', "\\|"))
                    .unwrap_or_else(|| "none".to_string()),
                site.kernel_confirmed
            ));
        }
    }

    if !report.findings.is_empty() {
        out.push_str("\n## Divergences Detected\n\n");
        out.push_str(
            "| Finding ID | Function | Class | Polarity | Miri | Anneal | Kernel Confirmed | Shrink |\n",
        );
        out.push_str("| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |\n");
        for f in &report.findings {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` ({} -> {} mutators) |\n",
                f.finding_id,
                f.fn_name,
                f.divergence_class,
                f.witness_polarity,
                f.miri_outcome_tag,
                f.anneal_outcome_tag,
                f.kernel_confirmed,
                f.shrink_status,
                f.original_mutator_chain.len(),
                f.minimized_mutator_chain.len()
            ));
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::mutators_miri::{build_standalone_candidate_source, generate_miri_corpus_batch};

    #[test]
    fn partition_subject_callees_links_helpers_sorted_and_excludes_all_root_candidates() {
        let mut subject_pairs = vec![
            (
                "helper_add_ten".to_string(),
                "MiriDiffCorpus.helper_add_ten".to_string(),
            ),
            (
                "helper_add_ten".to_string(),
                "MiriDiffCorpus.helper_add_ten".to_string(),
            ),
            (
                "helper_alpha".to_string(),
                "MiriDiffCorpus.helper_alpha".to_string(),
            ),
        ];
        let mut specs = Vec::new();
        for idx in 0..800 {
            let name = format!("cand__b0_c{idx}");
            subject_pairs.push((name.clone(), format!("MiriDiffCorpus.{name}")));
            specs.push(OracleItemSpec::with_fuel(name, MIRI_DIFFTEST_CANDIDATE_FUEL));
        }

        let (captured_candidates, helpers) =
            partition_subject_callees("MiriDiffCorpus", &subject_pairs, &specs);
        assert_eq!(captured_candidates.len(), 800);
        assert_eq!(
            helpers,
            vec![
                "MiriDiffCorpus.helper_add_ten".to_string(),
                "MiriDiffCorpus.helper_alpha".to_string(),
            ]
        );
        for spec in &specs {
            assert!(
                !helpers.iter().any(|h| h.ends_with(&format!(".{}", spec.name))),
                "root candidate {} must never enter linkedCallees",
                spec.name
            );
        }
    }

    #[test]
    fn linked_probe_and_confirm_modules_wire_callees_and_extract_confirm_theorems() {
        let spec = OracleItemSpec::with_fuel("cand_call_helper", 256);
        let panic_spec = OracleItemSpec::with_fuel("cand_panic_msg", 256);
        let helpers = vec!["MiriDiffCorpus.helper_add_ten".to_string()];

        let probe_src = render_linked_anneal_probe_module(
            "MiriDiffCorpus",
            &[(spec.clone(), "MiriDiffCorpus.cand_call_helper".to_string())],
            &helpers,
        );
        assert!(probe_src.contains("import Mir.MiriDiffCorpus.helper_add_ten\n"));
        assert!(probe_src.contains("import Mir.MiriDiffCorpus.cand_call_helper\n"));
        assert!(probe_src.contains(
            "def linkedCallees : List CapturedMir :=\n  \
             [Mir.MiriDiffCorpus.helper_add_ten.body,\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'a>::from_str\",\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'_>::from_str\",\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'a>::from_str_nonconst\",\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'_>::from_str_nonconst\",\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'a>::new_const\",\n   \
             fmtArgumentsCtorStub \"core::fmt::Arguments::<'_>::new_const\"]\n"
        ));
        assert!(probe_src.contains(FMT_ARGUMENTS_CTOR_STUB_LEAN));
        assert!(probe_src.contains(PROBE_EXEC_LEAN));
        assert!(probe_src.contains(PANIC_MESSAGE_PROBE_LEAN));
        assert!(probe_src.contains("phase := MirPhaseTag.runtimePostCleanup"));
        assert!(
            probe_src
                .contains("initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees")
        );
        // The probe prints the frame and recovered message of a panicking item
        // on their own lines, in the formats that `parse_anneal_panic_frames`
        // and `parse_anneal_panic_messages` read.
        assert!(probe_src.contains(
            "  match tag with\n  \
             | .panic =>\n    \
             match probePanicOriginBoundedFrom fuel body none (.running s) with\n    \
             | some o =>\n      \
             let line := line ++ s!\"\\nANNEAL_PANIC_FRAME\\t{name}\\t{activeDefPath body o}\"\n      \
             match panicMessage? body o with\n      \
             | some bytes => line ++ s!\"\\nANNEAL_PANIC_MESSAGE\\t{name}\\t{bytes}\"\n      \
             | none => line\n    \
             | none => line\n  \
             | _ => line\n"
        ));
        assert_eq!(ANNEAL_PANIC_FRAME_PREFIX, "ANNEAL_PANIC_FRAME\t");
        assert_eq!(ANNEAL_PANIC_MESSAGE_PREFIX, "ANNEAL_PANIC_MESSAGE\t");

        let overflow_spec = OracleItemSpec::with_fuel("cand_overflow", 256);
        let frames = BTreeMap::from([
            (
                "cand_panic_msg".to_string(),
                "miri_diff_corpus::cand_panic_msg".to_string(),
            ),
            (
                "cand_overflow".to_string(),
                "miri_diff_corpus::cand_overflow".to_string(),
            ),
            // A frame or message recorded for an item whose outcome is not a
            // panic must not produce a theorem.
            ("cand_call_helper".to_string(), "unused".to_string()),
        ]);
        let messages = BTreeMap::from([
            ("cand_panic_msg".to_string(), b"hi \"there\"".to_vec()),
            ("cand_call_helper".to_string(), b"unused".to_vec()),
        ]);
        let confirm_src = render_linked_anneal_confirm_module(
            "MiriDiffCorpus",
            &[
                (
                    spec,
                    "MiriDiffCorpus.cand_call_helper".to_string(),
                    AnnealOutcome::PassScalar {
                        bits: 42,
                        size_bytes: 4,
                    },
                ),
                (
                    panic_spec,
                    "MiriDiffCorpus.cand_panic_msg".to_string(),
                    AnnealOutcome::Panic {
                        span: Some(SourceSpan {
                            file: "/rustlib/src/rust/library/core/src/panic.rs".to_string(),
                            start_line: 62,
                            start_col: 9,
                            end_line: 62,
                            end_col: 73,
                        }),
                    },
                ),
                (
                    overflow_spec,
                    "MiriDiffCorpus.cand_overflow".to_string(),
                    AnnealOutcome::Panic {
                        span: Some(SourceSpan {
                            file: "src/lib.rs".to_string(),
                            start_line: 4,
                            start_col: 5,
                            end_line: 4,
                            end_col: 14,
                        }),
                    },
                ),
            ],
            &helpers,
            &frames,
            &messages,
        )
        .expect("render confirm module");
        assert!(confirm_src.contains("import Mir.MiriDiffCorpus.helper_add_ten\n"));
        // The confirm module proves spans and messages with the same
        // definitions that the probe evaluated.
        assert!(confirm_src.contains(PROBE_EXEC_LEAN));
        assert!(confirm_src.contains(PANIC_MESSAGE_PROBE_LEAN));
        assert!(confirm_src.contains(
            "initMachineStateWithMemoryAndCallees Mir.MiriDiffCorpus.cand_call_helper.body [] emptyMemory linkedCallees"
        ));
        assert!(!confirm_src.contains("theorem confirm_message_cand_call_helper :"));
        assert!(!confirm_src.contains("theorem confirm_frame_cand_call_helper :"));
        assert!(!confirm_src.contains("theorem confirm_message_cand_overflow :"));
        assert!(confirm_src.contains(
            "theorem confirm_frame_cand_panic_msg :\n    \
             probePanicFrameBounded 256 Mir.MiriDiffCorpus.cand_panic_msg.body\n      \
             (.running (initMachineStateWithMemoryAndCallees Mir.MiriDiffCorpus.cand_panic_msg.body [] emptyMemory linkedCallees)) =\n      \
             some \"miri_diff_corpus::cand_panic_msg\" := by\n  \
             rfl\n"
        ));
        assert!(confirm_src.contains(
            "theorem confirm_message_cand_panic_msg :\n    \
             probePanicMessageBounded 256 Mir.MiriDiffCorpus.cand_panic_msg.body\n      \
             (.running (initMachineStateWithMemoryAndCallees Mir.MiriDiffCorpus.cand_panic_msg.body [] emptyMemory linkedCallees)) =\n      \
             some [104, 105, 32, 34, 116, 104, 101, 114, 101, 34] := by\n  \
             -- Anneal's panic message: \"hi \\\"there\\\"\"\n  \
             rfl\n"
        ));

        let extracted = extract_confirm_theorems(&confirm_src, "cand_call_helper");
        assert!(extracted.contains("def linkedCallees : List CapturedMir :="));
        assert!(extracted.contains("theorem confirm_tag_cand_call_helper :"));
        assert!(extracted.contains("theorem confirm_probe_cand_call_helper :"));
        assert!(extracted.contains(":= by\n  rfl"));
        assert!(!extracted.contains("theorem confirm_tag_cand_panic_msg :"));
        // Without a frame or message theorem the snippet needs no panic-origin
        // probe.
        assert!(!extracted.contains("def probePanicOriginBoundedFrom"));
        // `linkedCallees` names the synthetic stub and `confirm_probe_*` calls
        // `probeMirDiffExecBounded`, so the snippet carries both definitions
        // (and the rest of the run probe) ahead of the theorems.
        let order = |snippet: &str, needles: &[&str]| {
            let positions: Vec<usize> = needles
                .iter()
                .map(|n| {
                    snippet
                        .find(n)
                        .unwrap_or_else(|| panic!("snippet must contain {n:?}:\n{snippet}"))
                })
                .collect();
            assert!(
                positions.windows(2).all(|w| w[0] < w[1]),
                "out of order: {needles:?}\n{snippet}"
            );
        };
        order(
            &extracted,
            &[
                "def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=",
                "def linkedCallees : List CapturedMir :=",
                "def activeSpan (body : CapturedMir) (st : MirExecState) : String :=",
                "def isCleanupState (body : CapturedMir)",
                "def unwindOrigin\n",
                "def probeMirDiffExecBoundedFrom\n",
                "def probeMirDiffExecBounded\n",
                "theorem confirm_tag_cand_call_helper :",
                "theorem confirm_probe_cand_call_helper :",
            ],
        );
        assert!(extracted.contains(FMT_ARGUMENTS_CTOR_STUB_LEAN.trim()));
        assert!(extracted.contains(PROBE_EXEC_LEAN.trim()));

        let extracted_panic = extract_confirm_theorems(&confirm_src, "cand_panic_msg");
        order(
            &extracted_panic,
            &[
                "def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=",
                "def linkedCallees : List CapturedMir :=",
                "def activeSpan (body : CapturedMir) (st : MirExecState) : String :=",
                "def unwindOrigin\n",
                "def probeMirDiffExecBounded\n",
                "def panicMessageOfSlice? (allocs : List CapturedAllocation)",
                "def panicOperandVal? (cur : CapturedMir)",
                "def assertFailedPrefix? : Value → Option (List UInt8)",
                "def formatAssertFailedMessage?",
                "def panicMessage? (body : CapturedMir)",
                "def activeDefPath (body : CapturedMir)",
                "def probePanicOriginBoundedFrom\n",
                "def probePanicMessageBounded\n",
                "def probePanicFrameBounded\n",
                "theorem confirm_tag_cand_panic_msg :",
                "theorem confirm_probe_cand_panic_msg :",
                "theorem confirm_frame_cand_panic_msg :",
                "theorem confirm_message_cand_panic_msg :",
            ],
        );
        assert!(extracted_panic.contains(PANIC_MESSAGE_PROBE_LEAN.trim()));
        assert!(!extracted_panic.contains("theorem confirm_tag_cand_call_helper :"));

        // A panic without a recoverable message still has a kernel-checked
        // frame, and its snippet carries the panic-origin probe that the frame
        // theorem evaluates.
        let extracted_overflow = extract_confirm_theorems(&confirm_src, "cand_overflow");
        order(
            &extracted_overflow,
            &[
                "def probeMirDiffExecBounded\n",
                "def probePanicFrameBounded\n",
                "theorem confirm_probe_cand_overflow :",
                "theorem confirm_frame_cand_overflow :",
            ],
        );
        assert!(!extracted_overflow.contains("theorem confirm_message_cand_overflow :"));
    }

    #[test]
    fn fmt_arguments_ctor_stub_returns_its_message_slice() {
        // The stub's `_0` and `_1` are both `&'static str`, and its only
        // statement copies the argument into the return place.
        assert_eq!(
            FMT_ARGUMENTS_CTOR_STUB_LEAN
                .matches("ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }")
                .count(),
            2
        );
        assert!(FMT_ARGUMENTS_CTOR_STUB_LEAN.contains(
            "StatementKind.assign { local_ := 0, projection := [] }\n                \
             (Rvalue.use (Operand.copy { local_ := 1, projection := [] }))"
        ));
        assert_eq!(
            FMT_ARGUMENTS_CTOR_STUB_LEAN
                .matches("StatementKind.")
                .count(),
            1
        );
        assert!(FMT_ARGUMENTS_CTOR_STUB_LEAN.contains("TerminatorKind.return_"));
        // These blocks are copied verbatim into finding bundles, which split
        // `MiriOracleConfirm.lean` into blocks at blank lines.
        for block in [
            FMT_ARGUMENTS_CTOR_STUB_LEAN,
            PROBE_EXEC_LEAN,
            PANIC_MESSAGE_PROBE_LEAN,
        ] {
            assert!(!block.trim().contains("\n\n"), "{block}");
        }
    }

    #[test]
    fn parse_anneal_panic_messages_reads_byte_lists() {
        let stdout = "\
ANNEAL_PROBE\tcand_a\tpanic\t/rustlib/src/rust/library/core/src/panic.rs:62:9: 62:73\n\
ANNEAL_PANIC_MESSAGE\tcand_a\t[104, 105]\n\
ANNEAL_PROBE\tcand_b\tpass:unit\tnone\n\
ANNEAL_PROBE\tcand_c\tpanic\t/rustlib/src/rust/library/core/src/panic.rs:62:9: 62:73\n\
ANNEAL_PANIC_MESSAGE\tcand_c\t[]\r\n";
        let messages = parse_anneal_panic_messages(stdout).expect("parse messages");
        assert_eq!(
            messages,
            BTreeMap::from([
                ("cand_a".to_string(), b"hi".to_vec()),
                ("cand_c".to_string(), Vec::new()),
            ])
        );
        for bad in [
            "ANNEAL_PANIC_MESSAGE\n",
            "ANNEAL_PANIC_MESSAGE\t\n",
            "ANNEAL_PANIC_MESSAGE\t\t[104]\n",
            "ANNEAL_PANIC_MESSAGE\tcand_a\n",
            "ANNEAL_PANIC_MESSAGE\tcand_a\t104, 105\n",
            "ANNEAL_PANIC_MESSAGE\tcand_a\t[104, 256]\n",
            "ANNEAL_PANIC_MESSAGE\tcand_a\t[104,, 105]\n",
            "ANNEAL_PANIC_MESSAGE\tcand_a\t[1]\nANNEAL_PANIC_MESSAGE\tcand_a\t[2]\n",
        ] {
            assert!(parse_anneal_panic_messages(bad).is_err(), "{bad:?}");
        }
    }

    fn lib_with_candidates() -> String {
        "\
#![no_std]
pub fn cand_panic__b0_c0() {
    panic!(\"boom\");
}

pub fn cand_assert__b0_c1() -> u32 {
    let x: u32 = 7u32;
    assert!(x == 8u32, \"x must equal eight\");
    core::assert_eq!(x, 9u32, \"x must equal nine\");
    x
}

pub fn cand_plain__b0_c2() -> u32 {
    let a: [u32; 2] = [1, 2];
    let i: usize = 5;
    a[i] + 1u32
}
"
        .to_string()
    }

    /// `DefPath` of the top-level staged function `name`.
    fn frame_of(name: &str) -> String {
        format!("miri_diff_corpus::{name}")
    }

    fn panic_at(line: u32, col: u32) -> MiriOutcome {
        MiriOutcome::Panic {
            pos: Some(SourcePos {
                file: "src/lib.rs".to_string(),
                line,
                col,
            }),
            message: String::new(),
        }
    }

    fn anneal_panic_in(file: &str, line: u32) -> AnnealOutcome {
        AnnealOutcome::Panic {
            span: Some(SourceSpan {
                file: file.to_string(),
                start_line: line,
                start_col: 9,
                end_line: line,
                end_col: 73,
            }),
        }
    }

    #[test]
    fn staged_lib_source_indexes_top_level_fn_line_ranges() {
        let src = StagedLibSource::parse(&lib_with_candidates());
        assert_eq!(src.fn_line_range("cand_panic__b0_c0"), Some((2, 4)));
        assert_eq!(src.fn_line_range("cand_assert__b0_c1"), Some((6, 11)));
        assert_eq!(src.fn_line_range("cand_plain__b0_c2"), Some((13, 17)));
        assert_eq!(src.fn_line_range("missing"), None);
        assert_eq!(
            StagedLibSource::parse("pub fn broken( {").fn_line_range("broken"),
            None
        );
    }

    #[test]
    fn compare_difftest_reconciles_only_std_macro_panic_sites() {
        let src = StagedLibSource::parse(&lib_with_candidates());
        let std_panic = "/rustlib/src/rust/library/core/src/panic.rs";
        let std_macros = "/rustc/abc/library/core/src/macros/mod.rs";

        // `panic!` and `assert!` (bare or `core::`-qualified) call sites inside
        // the evaluated function reconcile with an Anneal span inside the
        // standard panic-macro definitions.
        for (name, line, col, file) in [
            ("cand_panic__b0_c0", 3, 5, std_panic),
            ("cand_assert__b0_c1", 8, 5, std_panic),
            ("cand_assert__b0_c1", 9, 5, std_macros),
        ] {
            let miri = panic_at(line, col);
            let anneal = anneal_panic_in(file, 62);
            assert!(matches!(
                compare_miri_and_anneal(&miri, &anneal),
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
            ));
            assert_eq!(
                compare_difftest_miri_and_anneal(
                    &miri,
                    &anneal,
                    None,
                    Some(&frame_of(name)),
                    &src,
                    name
                ),
                ComparisonVerdict::Agree,
                "{name} at {line}:{col}"
            );
        }

        let mismatch = |miri: &MiriOutcome, anneal: &AnnealOutcome, name: &str| {
            matches!(
                compare_difftest_miri_and_anneal(
                    miri,
                    anneal,
                    None,
                    Some(&frame_of(name)),
                    &src,
                    name
                ),
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
            )
        };
        // Anneal span in user code: never reconciled.
        assert!(mismatch(
            &panic_at(3, 5),
            &anneal_panic_in("src/lib.rs", 16),
            "cand_panic__b0_c0"
        ));
        // A user file that merely shares a suffix with a standard file.
        assert!(mismatch(
            &panic_at(3, 5),
            &anneal_panic_in("src/panic.rs", 1),
            "cand_panic__b0_c0"
        ));
        // Miri position outside the evaluated function's line range.
        assert!(mismatch(
            &panic_at(8, 5),
            &anneal_panic_in(std_panic, 62),
            "cand_panic__b0_c0"
        ));
        // Miri position on a line of the function that is not a panic-macro
        // invocation (an index expression), or at the wrong column.
        assert!(mismatch(
            &panic_at(16, 5),
            &anneal_panic_in(std_panic, 62),
            "cand_plain__b0_c2"
        ));
        assert!(mismatch(
            &panic_at(3, 6),
            &anneal_panic_in(std_panic, 62),
            "cand_panic__b0_c0"
        ));
        // Miri position in another file.
        let mut other_file = panic_at(3, 5);
        if let MiriOutcome::Panic { pos: Some(p), .. } = &mut other_file {
            p.file = "/rustc/abc/library/core/src/lib.rs".to_string();
        }
        assert!(mismatch(
            &other_file,
            &anneal_panic_in(std_panic, 62),
            "cand_panic__b0_c0"
        ));
        // A missing Miri position stays a mismatch.
        let no_pos = MiriOutcome::Panic {
            pos: None,
            message: String::new(),
        };
        assert!(mismatch(
            &no_pos,
            &anneal_panic_in(std_panic, 62),
            "cand_panic__b0_c0"
        ));

        // Verdicts other than `PanicSiteMismatch` pass through unchanged.
        let ub = AnnealOutcome::Ub {
            span: Some(SourceSpan {
                file: std_panic.to_string(),
                start_line: 62,
                start_col: 9,
                end_line: 62,
                end_col: 73,
            }),
        };
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &panic_at(3, 5),
                &ub,
                None,
                Some("miri_diff_corpus::cand_panic__b0_c0"),
                &src,
                "cand_panic__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
        ));

        // A line inside a multi-line string literal or block comment that
        // contains `panic!("...")` text, or a non-standard path such as
        // `foo::panic!` or `foo::core::panic!` (even when Miri's column points
        // at the trailing `panic!` or `core::panic!` segment), must never
        // reconcile; multi-line `core::\npanic!(...)` and inline comments
        // between `panic` and `!(` do reconcile at the invocation's first token.
        let spoofed_src = StagedLibSource::parse(
            "\
#![no_std]
pub fn cand_spoof__b0_c0() -> u32 {
    let _s: &str = \"
    panic!(\\\"in_string\\\");
\";
    /*
    panic!(\"in_comment\");
    */
    let panic: u32 = 1u32;
    if panic != 0u32 { 2u32 } else { 3u32 }
}

pub fn cand_paths__b0_c1() {
    foo::panic!(\"non_std\");
    ::panic!(\"rooted_bare\");
    foo::core::panic!(\"nested_core\");
    core::
        panic!(\"multiline_core\");
    panic/* inline comment */!(
        \"multiline_args\"
    );
}
",
        );
        for (line, col) in [(4, 5), (7, 5), (10, 8)] {
            assert!(
                matches!(
                    compare_difftest_miri_and_anneal(
                        &panic_at(line, col),
                        &anneal_panic_in(std_panic, 62),
                        None,
                        Some("miri_diff_corpus::cand_spoof__b0_c0"),
                        &spoofed_src,
                        "cand_spoof__b0_c0"
                    ),
                    ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
                ),
                "spoofed site at {line}:{col} must not reconcile"
            );
        }
        // Every column of `foo::panic!`, `::panic!`, and `foo::core::panic!`
        // (including the interior `panic!` and `core::panic!` segments) must be
        // rejected, as must the interior `panic!` line of multi-line
        // `core::\npanic!`.
        for (line, col) in [
            (14, 5),
            (14, 8),
            (14, 10),
            (15, 5),
            (15, 7),
            (16, 5),
            (16, 10),
            (16, 16),
            (18, 9),
        ] {
            assert!(
                matches!(
                    compare_difftest_miri_and_anneal(
                        &panic_at(line, col),
                        &anneal_panic_in(std_panic, 62),
                        None,
                        Some("miri_diff_corpus::cand_paths__b0_c1"),
                        &spoofed_src,
                        "cand_paths__b0_c1"
                    ),
                    ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
                ),
                "non-std or interior segment at {line}:{col} must not reconcile"
            );
        }
        // Only the leading token of `core::\npanic!` (17:5) and
        // `panic/* ... */!(` (19:5) reconciles.
        for (line, col) in [(17, 5), (19, 5)] {
            assert_eq!(
                compare_difftest_miri_and_anneal(
                    &panic_at(line, col),
                    &anneal_panic_in(std_panic, 62),
                    None,
                    Some("miri_diff_corpus::cand_paths__b0_c1"),
                    &spoofed_src,
                    "cand_paths__b0_c1"
                ),
                ComparisonVerdict::Agree,
                "valid macro start at {line}:{col} must reconcile"
            );
        }
    }

    #[test]
    fn compare_difftest_requires_recovered_panic_message_to_match_miri() {
        let src = StagedLibSource::parse(&lib_with_candidates());
        let std_panic = "/rustlib/src/rust/library/core/src/panic.rs";
        let anneal = anneal_panic_in(std_panic, 62);
        // `cand_assert__b0_c1` has two panic-macro call sites; Miri reports the
        // second one (`core::assert_eq!` on line 9) with its message.
        let miri = MiriOutcome::Panic {
            pos: Some(SourcePos {
                file: "src/lib.rs".to_string(),
                line: 9,
                col: 5,
            }),
            message: "x must equal nine".to_string(),
        };
        let verdict = |message: Option<&str>| {
            compare_difftest_miri_and_anneal(
                &miri,
                &anneal,
                message,
                Some("miri_diff_corpus::cand_assert__b0_c1"),
                &src,
                "cand_assert__b0_c1",
            )
        };

        // No recovered message: the site conditions alone decide.
        assert_eq!(verdict(None), ComparisonVerdict::Agree);
        // A recovered message must match Miri's first message line, ignoring
        // surrounding whitespace and any later lines.
        assert_eq!(verdict(Some("x must equal nine")), ComparisonVerdict::Agree);
        assert_eq!(
            verdict(Some("  x must equal nine \n")),
            ComparisonVerdict::Agree
        );
        assert_eq!(
            verdict(Some("x must equal nine\nsecond line")),
            ComparisonVerdict::Agree
        );
        // Anneal panicking with the first site's message is a different panic
        // than Miri's, even though both sites share the macro's span.
        for message in ["x must equal eight", "", "second line\nx must equal nine"] {
            assert!(
                matches!(
                    verdict(Some(message)),
                    ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
                ),
                "{message:?}"
            );
        }

        // An empty Miri message matches only an empty first line.
        let miri_empty = panic_at(3, 5);
        assert_eq!(
            compare_difftest_miri_and_anneal(
                &miri_empty,
                &anneal,
                Some("\nlater"),
                Some("miri_diff_corpus::cand_panic__b0_c0"),
                &src,
                "cand_panic__b0_c0"
            ),
            ComparisonVerdict::Agree
        );
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &miri_empty,
                &anneal,
                Some("boom"),
                Some("miri_diff_corpus::cand_panic__b0_c0"),
                &src,
                "cand_panic__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));

        // A matching message never rescues a site that fails the other
        // conditions.
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &miri,
                &anneal_panic_in("src/lib.rs", 9),
                Some("x must equal nine"),
                Some("miri_diff_corpus::cand_assert__b0_c1"),
                &src,
                "cand_assert__b0_c1"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &miri,
                &anneal,
                Some("x must equal nine"),
                Some("miri_diff_corpus::cand_panic__b0_c0"),
                &src,
                "cand_panic__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
    }

    #[test]
    fn compare_difftest_requires_anneal_panic_in_the_evaluated_function() {
        let src = StagedLibSource::parse(&lib_with_candidates());
        let std_panic = "/rustlib/src/rust/library/core/src/panic.rs";
        let miri = panic_at(3, 5);
        let anneal = anneal_panic_in(std_panic, 62);
        let verdict = |frame: Option<&str>| {
            compare_difftest_miri_and_anneal(&miri, &anneal, None, frame, &src, "cand_panic__b0_c0")
        };
        // Line 3 is directly in `cand_panic__b0_c0` (not inside a closure or
        // nested `fn`), so only `cand_panic__b0_c0` itself and its compiler
        // `panic_cold_*` formatting shim reconcile.
        for frame in [
            "miri_diff_corpus::cand_panic__b0_c0",
            "miri_diff_corpus::cand_panic__b0_c0::panic_cold_display",
        ] {
            assert_eq!(verdict(Some(frame)), ComparisonVerdict::Agree, "{frame}");
        }
        // A panic that began in another function—including a nested `fn` or
        // closure inside the candidate when Miri panicked in the outer body—or
        // in a stdlib/empty crate or unknown frame is a different panic than
        // Miri's, whatever its message.
        for frame in [
            Some("miri_diff_corpus::helper_panics"),
            Some("miri_diff_corpus::cand_panic__b0_c0_helper"),
            Some("miri_diff_corpus::cand_panic__b0_c0::{closure#0}"),
            Some("miri_diff_corpus::cand_panic__b0_c0::inner_helper"),
            Some("::cand_panic__b0_c0"),
            Some("core::cand_panic__b0_c0"),
            Some("std::cand_panic__b0_c0"),
            Some("cand_panic__b0_c0"),
            Some(""),
            None,
        ] {
            assert!(
                matches!(
                    verdict(frame),
                    ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
                ),
                "{frame:?}"
            );
        }

        // Nested `fn`s and closures reconcile only when `miri_pos` lies inside
        // that exact nested callable scope, never cross-matching with the outer
        // body or a sibling nested callable.
        let nested_src = StagedLibSource::parse(
            "\
#![no_std]
pub fn cand_nested__b0_c0() {
    fn inner() {
        panic!(\"same\");
    }
    let f = || {
        panic!(\"same\");
    };
    let _ = (inner, f);
    panic!(\"same\");
}
",
        );
        let at = |line: u32, col: u32, frame: &str| {
            compare_difftest_miri_and_anneal(
                &panic_at(line, col),
                &anneal,
                None,
                Some(frame),
                &nested_src,
                "cand_nested__b0_c0",
            )
        };
        let outer_frame = "miri_diff_corpus::cand_nested__b0_c0";
        let inner_frame = "miri_diff_corpus::cand_nested__b0_c0::inner";
        let closure_frame = "miri_diff_corpus::cand_nested__b0_c0::{closure#0}";
        let closure_cold_frame =
            "miri_diff_corpus::cand_nested__b0_c0::{closure#0}::panic_cold_display";

        // Line 4 col 9 is inside `fn inner()`.
        assert_eq!(at(4, 9, inner_frame), ComparisonVerdict::Agree);
        assert!(matches!(
            at(4, 9, outer_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            at(4, 9, closure_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));

        // Line 7 col 9 is inside `let f = || { ... }`.
        assert_eq!(at(7, 9, closure_frame), ComparisonVerdict::Agree);
        assert_eq!(at(7, 9, closure_cold_frame), ComparisonVerdict::Agree);
        assert!(matches!(
            at(7, 9, outer_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            at(7, 9, inner_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));

        // Line 10 col 5 is in the outer `cand_nested__b0_c0` body.
        assert_eq!(at(10, 5, outer_frame), ComparisonVerdict::Agree);
        assert!(matches!(
            at(10, 5, inner_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            at(10, 5, closure_frame),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
    }

    #[test]
    fn compare_difftest_rejects_user_fns_named_like_panic_shims() {
        // A user `fn` whose name merely starts with `panic_cold_` is a separate
        // callable: a panic that Anneal begins there does not match Miri's
        // panic in the outer body, although the compiler's own shim does.
        let src = StagedLibSource::parse(
            "\
#![no_std]
pub fn cand_shadow__b0_c0() {
    fn panic_cold_user() {
        panic!(\"same\");
    }
    let _ = panic_cold_user;
    panic!(\"same\");
}
",
        );
        let anneal = anneal_panic_in("/rustlib/src/rust/library/core/src/panic.rs", 62);
        let verdict = |line: u32, col: u32, frame: &str| {
            let miri = MiriOutcome::Panic {
                pos: Some(SourcePos {
                    file: "src/lib.rs".to_string(),
                    line,
                    col,
                }),
                message: "same".to_string(),
            };
            compare_difftest_miri_and_anneal(
                &miri,
                &anneal,
                Some("same"),
                Some(frame),
                &src,
                "cand_shadow__b0_c0",
            )
        };
        let outer = "miri_diff_corpus::cand_shadow__b0_c0";
        assert_eq!(verdict(7, 5, outer), ComparisonVerdict::Agree);
        assert_eq!(
            verdict(7, 5, &format!("{outer}::panic_cold_display")),
            ComparisonVerdict::Agree
        );
        assert!(matches!(
            verdict(7, 5, &format!("{outer}::panic_cold_user")),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        // Inside the user `fn`, its own frame matches exactly.
        assert_eq!(
            verdict(4, 9, &format!("{outer}::panic_cold_user")),
            ComparisonVerdict::Agree
        );
    }

    #[test]
    fn parse_anneal_panic_frames_reads_def_paths() {
        let stdout = "\
ANNEAL_PROBE\tcand_a\tpanic\t/rustlib/src/rust/library/core/src/panic.rs:62:9: 62:73\n\
ANNEAL_PANIC_FRAME\tcand_a\tmiri_diff_corpus::cand_a\n\
ANNEAL_PANIC_MESSAGE\tcand_a\t[104, 105]\n\
ANNEAL_PROBE\tcand_b\tpass:unit\tnone\n\
ANNEAL_PANIC_FRAME\tcand_c\tmiri_diff_corpus::helper\r\n";
        assert_eq!(
            parse_anneal_panic_frames(stdout).expect("parse frames"),
            BTreeMap::from([
                ("cand_a".to_string(), "miri_diff_corpus::cand_a".to_string()),
                ("cand_c".to_string(), "miri_diff_corpus::helper".to_string()),
            ])
        );
        for bad in [
            "ANNEAL_PANIC_FRAME\n",
            "ANNEAL_PANIC_FRAME\t\n",
            "ANNEAL_PANIC_FRAME\tcand_a\n",
            "ANNEAL_PANIC_FRAME\tcand_a\t \n",
            "ANNEAL_PANIC_FRAME\t\tmiri_diff_corpus::cand_a\n",
            "ANNEAL_PANIC_FRAME\tcand_a\tx::a\nANNEAL_PANIC_FRAME\tcand_a\tx::b\n",
        ] {
            assert!(parse_anneal_panic_frames(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn std_panic_macro_invocation_recognizes_bare_and_crate_qualified_paths() {
        for text in [
            "panic!(\"x\");",
            "assert!(a == b, \"m\");",
            "assert_eq!(a, b);",
            "assert_ne!(a, b);",
            "assert_matches!(a, 1);",
            "debug_assert!(a);",
            "debug_assert_eq!(a, b);",
            "debug_assert_ne!(a, b);",
            "debug_assert_matches!(a, 1);",
            "unreachable!()",
            "todo!()",
            "unimplemented!()",
            "core::panic!(\"x\")",
            "::std::assert!(a)",
            "panic ! (\"x\")",
            "panic![\"x\"]",
            "panic!{\"x\"}",
            "panic/* comment */!(\"x\")",
            "core::\npanic!(\"x\")",
        ] {
            assert!(starts_with_std_panic_macro_invocation(text), "{text}");
        }
        for text in [
            "my_panic!(\"x\")",
            "panicky!(\"x\")",
            "::panic!(\"x\")",
            "foo::panic!(\"x\")",
            "foo::core::panic!(\"x\")",
            "/* leading */ panic!(\"x\")",
            "panic(\"x\")",
            "panic != 0",
            "assert != true",
            "panic!",
            "panic! = 1",
            "a[i] + 1u32",
            "",
        ] {
            assert!(!starts_with_std_panic_macro_invocation(text), "{text}");
        }
    }

    #[test]
    fn discover_reproducer_candidate_fn_handles_multiline_and_extra_helpers() {
        let src = "\
#![no_std]
pub fn helper_add_ten() -> u32 { 10 }
pub fn extra_helper() -> u32 { 5 }
fn private_after() -> u32 { 1 }
pub fn target_cand_with_wrapped_parens(
) -> u32 {
    helper_add_ten() + extra_helper() + private_after()
}
pub fn parameterized_after(x: u32) -> u32 { x }
";
        assert_eq!(
            discover_reproducer_candidate_fn(src).as_deref(),
            Some("target_cand_with_wrapped_parens")
        );
    }


    fn corpus_seed_sources() -> Vec<String> {
        load_miri_diff_corpus_seeds()
            .into_iter()
            .map(|s| s.fn_source)
            .collect()
    }

    fn lib_pos(line: u32, col: u32) -> SourcePos {
        SourcePos {
            file: "src/lib.rs".to_string(),
            line,
            col,
        }
    }

    fn lib_span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: line,
            start_col: 9,
            end_line: line,
            end_col: 42,
        }
    }

    /// `missed_ub` report: Miri raises UB `miri_msg` at `line`, Anneal returns `anneal`.
    fn missed_ub_report(
        name: &str,
        line: u32,
        miri_msg: &str,
        anneal: AnnealOutcome,
        kernel_confirmed: bool,
    ) -> ItemOracleReport {
        ItemOracleReport {
            name: name.to_string(),
            fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
            miri: MiriOutcome::Ub {
                pos: Some(lib_pos(line, 14)),
                message: miri_msg.to_string(),
            },
            verdict: ComparisonVerdict::Diverge(DivergenceKind::MissedUb {
                miri_pos: Some(lib_pos(line, 14)),
                miri_msg: miri_msg.to_string(),
                anneal: anneal.summary_tag(),
            }),
            anneal,
            kernel_confirmed,
        }
    }

    fn agree_report(name: &str) -> ItemOracleReport {
        ItemOracleReport {
            name: name.to_string(),
            fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
            miri: MiriOutcome::PassScalar {
                bits: 10,
                size_bytes: 4,
            },
            anneal: AnnealOutcome::PassScalar {
                bits: 10,
                size_bytes: 4,
            },
            verdict: ComparisonVerdict::Agree,
            kernel_confirmed: true,
        }
    }

    /// Replays every subset of `cand`'s recorded steps and maps each replayed `fn_source`
    /// to its subset bitmask (bit `i` = original pass `i` kept). Returns `None` if two
    /// subsets replay to the same source (the mock oracle could not tell them apart).
    fn subset_source_map(
        cand: &GeneratedMiriCandidate,
        seed_refs: &[&str],
    ) -> Option<BTreeMap<String, u32>> {
        let (base, steps) = reconstruct_miri_mutation_steps(cand, seed_refs)?;
        let mut map = BTreeMap::new();
        for mask in 0u32..(1u32 << steps.len()) {
            let sub: Vec<RecordedMutationStep> = steps
                .iter()
                .enumerate()
                .filter(|(i, _)| (mask >> i) & 1 == 1)
                .map(|(_, s)| s.clone())
                .collect();
            let src = replay_miri_mutation_steps(cand, &base, &sub).fn_source;
            if map.insert(src, mask).is_some() {
                return None;
            }
        }
        Some(map)
    }

    /// First corpus candidate with exactly `n` mutators whose `2^n` subset replays are
    /// pairwise distinct.
    fn find_candidate_with_distinct_subsets(
        n: usize,
        seed_refs: &[&str],
    ) -> (GeneratedMiriCandidate, BTreeMap<String, u32>) {
        for batch_seed in 1u64..64 {
            for cand in generate_miri_corpus_batch(24, 0x5EED_0000 + batch_seed, 0) {
                if cand.applied_mutators.len() != n {
                    continue;
                }
                if let Some(map) = subset_source_map(&cand, seed_refs) {
                    return (cand, map);
                }
            }
        }
        panic!("no {n}-mutator corpus candidate with pairwise-distinct subset replays");
    }

    #[test]
    fn full_chain_replay_matches_generated_corpus_batch_identically() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let mut saw_multi_pass = false;
        let mut checked = 0usize;
        for (batch_idx, batch_seed) in [0xCAFE_BABE_1234_5678u64, 0x5EED_0001, 0x0BAD_F00D]
            .into_iter()
            .enumerate()
        {
            let batch = generate_miri_corpus_batch(16, batch_seed, batch_idx);
            assert_eq!(batch.len(), 16);
            for cand in &batch {
                if cand.applied_mutators.len() >= 2 {
                    saw_multi_pass = true;
                }
                let (base_parsed, steps) = reconstruct_miri_mutation_steps(cand, &seed_refs)
                    .expect("extract mutation steps for corpus candidate");
                assert_eq!(steps.len(), cand.applied_mutators.len());
                let replayed = replay_miri_mutation_steps(cand, &base_parsed, &steps);
                assert_eq!(
                    replayed.applied_mutators, cand.applied_mutators,
                    "replayed mutator chain must match candidate {}",
                    cand.fn_name
                );
                assert_eq!(
                    replayed.fn_source, cand.fn_source,
                    "full-chain AST replay must reproduce fn_source byte-for-byte for {}",
                    cand.fn_name
                );
                assert_eq!(
                    replayed.source, cand.source,
                    "full-chain AST replay must reproduce standalone source byte-for-byte for {}",
                    cand.fn_name
                );
                assert!(miri_candidate_replay_is_faithful(cand, &base_parsed, &steps));
                checked += 1;
            }
        }
        assert_eq!(checked, 48);
        assert!(saw_multi_pass, "expected multi-mutator candidates across 48 candidates");
    }

    #[test]
    fn replay_fidelity_rejects_tampered_and_hand_built_candidates_without_oracle_calls() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let batch = generate_miri_corpus_batch(16, 0x5EED_0001, 0);
        let cand = batch
            .iter()
            .find(|c| !c.applied_mutators.is_empty())
            .expect("mutated candidate")
            .clone();
        let report = missed_ub_report(
            &cand.fn_name,
            40,
            "constructing invalid value: encountered 0x02, but expected a boolean",
            AnnealOutcome::PassScalar {
                bits: 1,
                size_bytes: 4,
            },
            true,
        );

        // 1. Tampered source: the recorded steps no longer describe the program.
        let mut tampered = cand.clone();
        tampered.fn_source.push_str("\n// tampered\n");
        let (base, steps) =
            reconstruct_miri_mutation_steps(&tampered, &seed_refs).expect("extract steps");
        assert!(!miri_candidate_replay_is_faithful(&tampered, &base, &steps));

        // 2. Hand-built candidate (as in the integration suite's broken candidate).
        let broken_fn = "pub fn broken_cand__b0_c2() -> u32 {\n    7u32\n}\n";
        let hand_built = GeneratedMiriCandidate {
            id: 2,
            seed_index: 0,
            seed_name: "pass_integer_arith_basic".to_string(),
            fn_name: "broken_cand__b0_c2".to_string(),
            seed_u64: 0x9999,
            applied_mutators: vec!["ArithmeticCastMutator".to_string()],
            tracked_locals: Vec::new(),
            fn_source: broken_fn.to_string(),
            source: build_standalone_candidate_source(broken_fn),
        };

        // 3. Out-of-range seed index: refuse instead of replaying another seed.
        let mut bad_seed = cand.clone();
        bad_seed.seed_index = seed_refs.len() + 5;
        assert!(reconstruct_miri_mutation_steps(&bad_seed, &seed_refs).is_none());

        // 4. In-range seed index whose function name does not match `seed_name`: refuse.
        let mut mismatched_seed_name = cand.clone();
        mismatched_seed_name.seed_name = "nonexistent_seed_fn".to_string();
        assert!(reconstruct_miri_mutation_steps(&mismatched_seed_name, &seed_refs).is_none());

        // 5. Tampered standalone `source` with untouched `fn_source`: refuse.
        let mut tampered_standalone = cand.clone();
        tampered_standalone.source.push_str("\n// standalone tampered\n");
        assert!(!miri_candidate_replay_is_faithful(&tampered_standalone, &base, &steps));

        // 6. Non-canonical `pass_index` on recorded steps: refuse.
        let mut non_canonical_steps = steps.clone();
        non_canonical_steps[0].pass_index = 99;
        assert!(!miri_candidate_replay_is_faithful(
            &cand,
            &base,
            &non_canonical_steps
        ));

        // 7. A candidate whose PRNG schedule draws `MiriSeedDraw::NonFault` (`Pass` or `Panic`
        //    primary mode) cannot have mutated a faulting (`ub_*` / `panic_*`) corpus seed.
        let fault_seed_idx = seed_refs
            .iter()
            .position(|s| s.contains("pub fn ub_") || s.contains("pub fn panic_"))
            .expect("faulting corpus seed");
        let non_fault_cand = batch
            .iter()
            .find(|c| {
                !c.seed_name.starts_with("ub_")
                    && !c.seed_name.starts_with("panic_")
                    && (c.id + crate::mutators_miri::DetRng::new(c.seed_u64).gen_range(4)) % 4 < 2
            })
            .expect("candidate with Pass/Panic primary mode")
            .clone();
        let mut spoofed_fault_seed = non_fault_cand;
        spoofed_fault_seed.seed_index = fault_seed_idx;
        assert!(reconstruct_miri_mutation_steps(&spoofed_fault_seed, &seed_refs).is_none());

        for victim in [
            &tampered,
            &tampered_standalone,
            &hand_built,
            &bad_seed,
            &mismatched_seed_name,
            &spoofed_fault_seed,
        ] {
            let res = minimize_miri_candidate_mutations_with_compile_check(
                victim,
                &seed_refs,
                &report,
                |_| panic!("compile check must not run for an unfaithful replay"),
                |_| panic!("oracle must not run for an unfaithful replay"),
            );
            assert_eq!(res.status, MiriShrinkStatus::SkippedReplayMismatch);
            assert_eq!(res.minimized_mutator_chain, victim.applied_mutators);
            assert_eq!(res.minimized_candidate, *victim);
            assert_eq!(
                (res.shrink_evaluations, res.oracle_evaluations, res.compile_rejections),
                (0, 0, 0)
            );
        }
    }

    #[test]
    fn signature_match_is_span_and_digit_insensitive_but_class_tag_and_family_sensitive() {
        let scalar = AnnealOutcome::PassScalar {
            bits: 1,
            size_bytes: 4,
        };
        let original = missed_ub_report(
            "f",
            84,
            "constructing invalid value at alloc1234+0x8: encountered 0x02, but expected a boolean",
            scalar.clone(),
            true,
        );
        // Same divergence after an earlier statement was deleted: different line,
        // allocation id, offset, byte value, and returned scalar bits.
        let shifted = missed_ub_report(
            "f",
            52,
            "constructing invalid value at alloc77+0x4: encountered 0x03, but expected a boolean",
            AnnealOutcome::PassScalar {
                bits: 99,
                size_bytes: 4,
            },
            true,
        );
        assert!(discrepancy_signatures_match(&original, &shifted));

        // Bug slippage: same class and Anneal tag, different UB kind.
        let slipped = missed_ub_report(
            "f",
            52,
            "memory access failed: alloc77 has been freed, so this pointer is dangling",
            scalar.clone(),
            true,
        );
        assert!(!discrepancy_signatures_match(&original, &slipped));

        // Same class, different normalized Anneal tag (`MirDiffTag.panic`).
        let tag_changed = missed_ub_report(
            "f",
            52,
            "constructing invalid value at alloc77+0x4: encountered 0x03, but expected a boolean",
            AnnealOutcome::Panic {
                span: Some(lib_span(52)),
            },
            true,
        );
        assert!(!discrepancy_signatures_match(&original, &tag_changed));

        // Not kernel-confirmed while the original was.
        let mut unconfirmed = shifted.clone();
        unconfirmed.kernel_confirmed = false;
        assert!(!discrepancy_signatures_match(&original, &unconfirmed));

        // Different divergence class.
        let mut class_changed = shifted.clone();
        class_changed.verdict = ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
            miri_pos: Some(lib_pos(52, 14)),
            miri_msg: "x".to_string(),
            anneal_span: Some(lib_span(53)),
        });
        assert!(!discrepancy_signatures_match(&original, &class_changed));

        // Agreement never matches a divergence signature.
        assert!(!discrepancy_signatures_match(&original, &agree_report("f")));

        assert_eq!(
            normalize_diagnostic_message(
                "  panicked at src/lib.rs:12:5:  attempt to divide by zero "
            ),
            "panicked at src/lib.rs:N:N: attempt to divide by zero"
        );
        assert_eq!(normalize_diagnostic_message("encountered 0xFF_FF"), "encountered 0xN");
        assert_eq!(
            normalize_diagnostic_message(
                "transmuting between 4-byte type u32 and [u8; 4] at alloc128"
            ),
            "transmuting between N-byte type u32 and [u8; N] at allocN"
        );
        let width_u32 = missed_ub_report(
            "f",
            52,
            "invalid value of type u32 at alloc10",
            scalar.clone(),
            true,
        );
        let width_u8 = missed_ub_report(
            "f",
            52,
            "invalid value of type u8 at alloc10",
            scalar.clone(),
            true,
        );
        assert!(!discrepancy_signatures_match(&width_u32, &width_u8));
        // `translate_span_to_repro` must not underflow when `batch_start_line < repro_start_line`.
        let translated = translate_span_to_repro(&lib_span(7), 5, 14);
        assert_eq!((translated.start_line, translated.end_line), (16, 16));
    }

    /// `ddmin` over generated multi-pass candidates whose chains synthesize the
    /// Category 9 variants: a fake oracle reproduces the original discrepancy
    /// signature exactly when the replayed program still contains the variant's
    /// marker. The shrinker must return a replayable subsequence that keeps the
    /// marker and is 1-minimal: replaying it with any single kept pass removed
    /// loses the marker.
    #[test]
    fn ddmin_shrinks_category9_variant_chains_to_one_minimal_subsequences() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        const MARKERS: [&str; 16] = [
            "helper_unwind_guarded(",
            "helper_reborrow_return(",
            "let __cp_copied: u32 = __cp_x;",
            "NonCopyU32(",
            "NonCopyPairU32",
            "helper_reborrow_mid(",
            "helper_shared_mid(",
            "helper_unwind_mid(",
            "helper_frozen_reborrow_write_in_callee(",
            "ctlz_nonzero(",
            "saturating_add(",
            "three_way_compare(",
            "exact_div(",
            "arith_offset(",
            "write_bytes!(",
            "copy_nonoverlapping(",
        ];
        let miri_msg = "constructing invalid value: encountered 0x02, but expected a boolean";
        let anneal = AnnealOutcome::PassScalar {
            bits: 1,
            size_bytes: 4,
        };
        let mut covered = BTreeSet::new();
        for batch_idx in 0..96usize {
            if covered.len() == MARKERS.len() {
                break;
            }
            for cand in generate_miri_corpus_batch(12, 0xC9D0_0000 + batch_idx as u64, batch_idx) {
                if cand.applied_mutators.len() < 2 {
                    continue;
                }
                let Some((base, steps)) = reconstruct_miri_mutation_steps(&cand, &seed_refs) else {
                    continue;
                };
                let base_src = prettyplease::unparse(&base);
                for &marker in &MARKERS {
                    if covered.contains(marker)
                        || !cand.fn_source.contains(marker)
                        || base_src.contains(marker)
                    {
                        continue;
                    }
                    let original =
                        missed_ub_report(&cand.fn_name, 50, miri_msg, anneal.clone(), true);
                    let res = minimize_miri_candidate_mutations_with_compile_check(
                        &cand,
                        &seed_refs,
                        &original,
                        |_| true,
                        |sub| {
                            Some(if sub.fn_source.contains(marker) {
                                missed_ub_report(&sub.fn_name, 50, miri_msg, anneal.clone(), true)
                            } else {
                                agree_report(&sub.fn_name)
                            })
                        },
                    );
                    assert!(
                        matches!(
                            res.status,
                            MiriShrinkStatus::Minimized | MiriShrinkStatus::AlreadyOneMinimal
                        ),
                        "`{marker}`: unexpected status {:?}",
                        res.status
                    );
                    assert!(res.minimized_candidate.fn_source.contains(marker));
                    // Find the kept pass indices: the subsequences whose replay
                    // reproduces the minimized program byte for byte.
                    let n = steps.len();
                    let replay_mask = |mask: u32| {
                        let kept: Vec<RecordedMutationStep> = (0..n)
                            .filter(|i| mask & (1 << i) != 0)
                            .map(|i| steps[i].clone())
                            .collect();
                        replay_miri_mutation_steps(&cand, &base, &kept)
                    };
                    let kept_masks: Vec<u32> = (0..(1u32 << n))
                        .filter(|&mask| {
                            replay_mask(mask).fn_source == res.minimized_candidate.fn_source
                        })
                        .collect();
                    assert!(
                        !kept_masks.is_empty(),
                        "`{marker}`: the minimized program is not a replayable subsequence"
                    );
                    assert!(
                        kept_masks.iter().any(|&mask| {
                            (0..n)
                                .filter(|i| mask & (1 << i) != 0)
                                .all(|i| !replay_mask(mask & !(1 << i)).fn_source.contains(marker))
                        }),
                        "`{marker}`: minimized chain {:?} is not 1-minimal",
                        res.minimized_mutator_chain
                    );
                    covered.insert(marker);
                }
            }
        }
        assert!(
            covered.len() == MARKERS.len(),
            "expected ddmin coverage of every Category 9 variant, covered {covered:?}"
        );
    }

    #[test]
    fn shrinks_3_mutator_chain_rejecting_compile_failures_tag_changes_and_bug_slippage() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand3, subsets) = find_candidate_with_distinct_subsets(3, &seed_refs);
        let names = cand3.applied_mutators.clone();
        let bool_ub = |b: u32| {
            format!("constructing invalid value: encountered 0x0{b}, but expected a boolean")
        };
        let scalar = |bits: u128| AnnealOutcome::PassScalar {
            bits,
            size_bytes: 4,
        };
        let original = missed_ub_report(&cand3.fn_name, 88, &bool_ub(2), scalar(1), true);

        // Subset semantics (bit i = original pass i kept; pass 0 is the fault mutator):
        //   {0}       -> does not compile (rejected before the oracle),
        //   {0, 1}    -> same class, but Anneal panics (normalized tag changes),
        //   {0, 2}    -> same signature, shifted lines / different digits (accepted),
        //   no pass 0 -> different UB kind (bug slippage), or `[]` agrees.
        let compile_calls = RefCell::new(Vec::<u32>::new());
        let oracle_calls = RefCell::new(Vec::<u32>::new());
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand3,
            &seed_refs,
            &original,
            |sub| {
                let mask = subsets[&sub.fn_source];
                compile_calls.borrow_mut().push(mask);
                mask != 0b001
            },
            |sub| {
                let mask = subsets[&sub.fn_source];
                assert_ne!(mask, 0b001, "non-compiling subsequence reached the oracle");
                assert_ne!(mask, 0b111, "the full chain must never be re-evaluated");
                oracle_calls.borrow_mut().push(mask);
                let name = sub.fn_name.as_str();
                Some(match mask {
                    0b000 => agree_report(name),
                    0b011 => missed_ub_report(
                        name,
                        60,
                        &bool_ub(2),
                        AnnealOutcome::Panic {
                            span: Some(lib_span(61)),
                        },
                        true,
                    ),
                    0b101 => missed_ub_report(name, 52, &bool_ub(3), scalar(7), true),
                    _ => missed_ub_report(
                        name,
                        44,
                        "memory access failed: alloc9 has been freed, so this pointer is dangling",
                        scalar(1),
                        true,
                    ),
                })
            },
        );

        assert_eq!(res.status, MiriShrinkStatus::Minimized);
        assert_eq!(res.original_mutator_chain, names);
        assert_eq!(res.minimized_mutator_chain, vec![names[0].clone(), names[2].clone()]);
        assert_eq!(subsets[&res.minimized_candidate.fn_source], 0b101);
        assert_eq!(res.minimized_candidate.applied_mutators, res.minimized_mutator_chain);
        assert_eq!(res.minimized_report.miri, MiriOutcome::Ub {
            pos: Some(lib_pos(52, 14)),
            message: bool_ub(3),
        });
        let compile_calls = compile_calls.into_inner();
        let oracle_calls = oracle_calls.into_inner();
        assert!(compile_calls.contains(&0b001), "{{0}} must be compile-checked");
        assert_eq!(res.compile_rejections, compile_calls.iter().filter(|&&m| m == 0b001).count());
        assert_eq!(res.oracle_evaluations, oracle_calls.len());
        assert_eq!(res.shrink_evaluations, compile_calls.len());
        assert_eq!(res.shrink_evaluations, res.oracle_evaluations + res.compile_rejections);
        assert!(oracle_calls.contains(&0b000), "the unmutated seed `[]` must be evaluated");
        // 1-minimality of {0, 2}: both single deletions were judged and rejected.
        assert!(oracle_calls.contains(&0b100), "{{2}} must be evaluated and rejected");
        assert!(compile_calls.contains(&0b001), "{{0}} must be rejected by rustc");
        assert!(
            res.minimized_candidate.source.len() < cand3.source.len(),
            "minimized candidate source must be shorter than the 3-mutator source"
        );
    }

    /// [`MemoizedOracle`] (used by the live `minimize_miri_candidate_mutations`) is
    /// semantically transparent: the memoized shrink reaches the same minimized chain,
    /// program, report, and query counts as the unmemoized shrink, while forwarding each
    /// distinct program to the wrapped oracle exactly once.
    #[test]
    fn memoized_oracle_is_transparent_and_runs_each_distinct_program_once() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand3, subsets) = find_candidate_with_distinct_subsets(3, &seed_refs);
        let bool_ub = |b: u32| {
            format!("constructing invalid value: encountered 0x0{b}, but expected a boolean")
        };
        let scalar = |bits: u128| AnnealOutcome::PassScalar {
            bits,
            size_bytes: 4,
        };
        let original = missed_ub_report(&cand3.fn_name, 88, &bool_ub(2), scalar(1), true);
        // Same subset semantics as the bug-slippage test above.
        let oracle = |sub: &GeneratedMiriCandidate| -> Option<ItemOracleReport> {
            let name = sub.fn_name.as_str();
            Some(match subsets[&sub.fn_source] {
                0b000 => agree_report(name),
                0b011 => missed_ub_report(
                    name,
                    60,
                    &bool_ub(2),
                    AnnealOutcome::Panic {
                        span: Some(lib_span(61)),
                    },
                    true,
                ),
                0b101 => missed_ub_report(name, 52, &bool_ub(3), scalar(7), true),
                _ => missed_ub_report(
                    name,
                    44,
                    "memory access failed: alloc9 has been freed, so this pointer is dangling",
                    scalar(1),
                    true,
                ),
            })
        };
        let compiles = |sub: &GeneratedMiriCandidate| subsets[&sub.fn_source] != 0b001;

        let mut queried: Vec<u32> = Vec::new();
        let plain = minimize_miri_candidate_mutations_with_compile_check(
            &cand3,
            &seed_refs,
            &original,
            compiles,
            |sub| {
                queried.push(subsets[&sub.fn_source]);
                oracle(sub)
            },
        );

        let mut executed: Vec<u32> = Vec::new();
        let mut memo = MemoizedOracle::new(|sub: &GeneratedMiriCandidate| {
            executed.push(subsets[&sub.fn_source]);
            oracle(sub)
        });
        let memoized = minimize_miri_candidate_mutations_with_compile_check(
            &cand3,
            &seed_refs,
            &original,
            compiles,
            |sub| memo.eval(sub.fn_source.clone(), sub),
        );
        let (executed_runs, cache_hits) = (memo.executed_runs, memo.cache_hits);
        drop(memo);

        assert_eq!(plain.status, MiriShrinkStatus::Minimized);
        assert_eq!(memoized.status, plain.status);
        assert_eq!(memoized.minimized_mutator_chain, plain.minimized_mutator_chain);
        assert_eq!(memoized.minimized_candidate, plain.minimized_candidate);
        assert_eq!(memoized.minimized_report, plain.minimized_report);
        assert_eq!(
            (memoized.shrink_evaluations, memoized.oracle_evaluations, memoized.compile_rejections),
            (plain.shrink_evaluations, plain.oracle_evaluations, plain.compile_rejections),
        );
        // Without a memo every query executes.
        assert_eq!(plain.executed_oracle_runs, plain.oracle_evaluations);
        assert_eq!(plain.oracle_evaluations, queried.len());

        let distinct: std::collections::BTreeSet<u32> = queried.iter().copied().collect();
        assert!(
            distinct.len() < queried.len(),
            "the scenario must re-query an identical program across ddmin sweeps: {queried:?}"
        );
        assert_eq!(executed.len(), distinct.len(), "a program was executed twice: {executed:?}");
        assert_eq!(executed.iter().copied().collect::<std::collections::BTreeSet<u32>>(), distinct);
        assert_eq!(executed_runs, distinct.len());
        assert_eq!(cache_hits, queried.len() - distinct.len());
        assert_eq!(executed_runs + cache_hits, memoized.oracle_evaluations);
    }

    #[test]
    fn shrinks_3_mutator_chain_to_single_mutator_rejecting_compile_class_and_tag_changes() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand3, subsets) = find_candidate_with_distinct_subsets(3, &seed_refs);
        let names = cand3.applied_mutators.clone();
        let oob = |size: u32, end: u32| {
            format!(
                "out-of-bounds pointer arithmetic: alloc{size}{end} has size {size}, so pointer \
                 to {end} bytes starting at offset 0 is out-of-bounds"
            )
        };
        let original =
            missed_ub_report(&cand3.fn_name, 88, &oob(16, 20), AnnealOutcome::PassUnit, true);

        // Subset semantics (bit i = original pass i kept; pass 1 is the fault mutator):
        //   {0, 1} -> does not compile (must never reach the oracle),
        //   {0}    -> diverges with a different class (`ub_location_mismatch`),
        //   {2}    -> same class, but Anneal panics (normalized tag changes),
        //   {1, 2} -> same signature with shifted lines / digits (accepted),
        //   {1}    -> same signature with shifted lines / digits (accepted, 1-minimal),
        //   {} and {0, 2} -> agree.
        let compile_calls = RefCell::new(Vec::<u32>::new());
        let oracle_calls = RefCell::new(Vec::<u32>::new());
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand3,
            &seed_refs,
            &original,
            |sub| {
                let mask = subsets[&sub.fn_source];
                compile_calls.borrow_mut().push(mask);
                mask != 0b011
            },
            |sub| {
                let mask = subsets[&sub.fn_source];
                assert_ne!(mask, 0b011, "non-compiling subsequence reached the oracle");
                assert_ne!(mask, 0b111, "the full chain must never be re-evaluated");
                oracle_calls.borrow_mut().push(mask);
                let name = sub.fn_name.as_str();
                Some(match mask {
                    0b110 => missed_ub_report(name, 61, &oob(8, 12), AnnealOutcome::PassUnit, true),
                    0b010 => missed_ub_report(name, 34, &oob(4, 8), AnnealOutcome::PassUnit, true),
                    0b001 => ItemOracleReport {
                        name: name.to_string(),
                        fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
                        miri: MiriOutcome::Ub {
                            pos: Some(lib_pos(30, 14)),
                            message: oob(16, 20),
                        },
                        anneal: AnnealOutcome::Ub {
                            span: Some(lib_span(31)),
                        },
                        verdict: ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch {
                            miri_pos: Some(lib_pos(30, 14)),
                            miri_msg: oob(16, 20),
                            anneal_span: Some(lib_span(31)),
                        }),
                        kernel_confirmed: true,
                    },
                    0b100 => missed_ub_report(
                        name,
                        40,
                        &oob(16, 20),
                        AnnealOutcome::Panic {
                            span: Some(lib_span(41)),
                        },
                        true,
                    ),
                    _ => agree_report(name),
                })
            },
        );

        assert_eq!(res.status, MiriShrinkStatus::Minimized);
        assert_eq!(res.original_mutator_chain, names);
        assert_eq!(res.minimized_mutator_chain, vec![names[1].clone()]);
        assert_eq!(subsets[&res.minimized_candidate.fn_source], 0b010);
        assert_eq!(
            res.minimized_report.miri,
            MiriOutcome::Ub {
                pos: Some(lib_pos(34, 14)),
                message: oob(4, 8),
            }
        );
        let compile_calls = compile_calls.into_inner();
        let oracle_calls = oracle_calls.into_inner();
        assert!(compile_calls.contains(&0b011), "{{0, 1}} must be rejected by the compile check");
        assert!(oracle_calls.contains(&0b001), "class-changing {{0}} must be judged and rejected");
        assert!(oracle_calls.contains(&0b100), "tag-changing {{2}} must be judged and rejected");
        assert!(oracle_calls.contains(&0b110), "{{1, 2}} must be accepted on the way to {{1}}");
        assert!(oracle_calls.contains(&0b000), "the unmutated seed `[]` must be evaluated");
        assert_eq!(res.compile_rejections, compile_calls.iter().filter(|&&m| m == 0b011).count());
        assert_eq!(res.oracle_evaluations, oracle_calls.len());
        assert_eq!(res.shrink_evaluations, compile_calls.len());
    }

    /// `minimize_miri_candidate_mutations_with` (the brief's public entry point) runs the
    /// real `rustc` pre-check before every oracle call.
    #[test]
    fn minimize_with_runs_the_real_rustc_precheck_before_each_oracle_call() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let mut chosen: Option<(GeneratedMiriCandidate, BTreeMap<String, u32>)> = None;
        'search: for batch_seed in 1u64..64 {
            for cand in generate_miri_corpus_batch(24, 0x5EED_0000 + batch_seed, 0) {
                if cand.applied_mutators.len() != 2 {
                    continue;
                }
                let Some(map) = subset_source_map(&cand, &seed_refs) else {
                    continue;
                };
                let (base, steps) =
                    reconstruct_miri_mutation_steps(&cand, &seed_refs).expect("steps");
                let all_compile = (0u32..3).all(|mask| {
                    let sub: Vec<RecordedMutationStep> = steps
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| (mask >> i) & 1 == 1)
                        .map(|(_, s)| s.clone())
                        .collect();
                    let replayed = replay_miri_mutation_steps(&cand, &base, &sub);
                    compile_rust_snippet(
                        &format!("precheck_{mask}_{}", cand.fn_name),
                        &replayed.source,
                    )
                });
                if all_compile {
                    chosen = Some((cand, map));
                    break 'search;
                }
            }
        }
        let (cand, subsets) = chosen.expect("2-mutator candidate whose proper subsets all compile");
        let msg = "constructing invalid value: encountered 0x02, but expected a boolean";
        let original = missed_ub_report(&cand.fn_name, 50, msg, AnnealOutcome::PassUnit, true);
        let mut oracle_masks: Vec<u32> = Vec::new();
        let res = minimize_miri_candidate_mutations_with(&cand, &seed_refs, &original, |sub| {
            let mask = subsets[&sub.fn_source];
            oracle_masks.push(mask);
            Some(if mask == 0b01 {
                missed_ub_report(&sub.fn_name, 30, msg, AnnealOutcome::PassUnit, true)
            } else {
                agree_report(&sub.fn_name)
            })
        });
        assert_eq!(res.status, MiriShrinkStatus::Minimized);
        assert_eq!(res.minimized_mutator_chain, vec![cand.applied_mutators[0].clone()]);
        assert_eq!(subsets[&res.minimized_candidate.fn_source], 0b01);
        assert!(oracle_masks.contains(&0b00), "the unmutated seed `[]` must be evaluated");
        assert_eq!(res.compile_rejections, 0, "every proper subsequence compiles");
        assert_eq!(res.oracle_evaluations, oracle_masks.len());
        assert_eq!(res.shrink_evaluations, oracle_masks.len());
    }

    #[test]
    fn unmutated_seed_with_same_signature_shrinks_to_empty_chain_after_one_oracle_run() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand, subsets) = find_candidate_with_distinct_subsets(2, &seed_refs);
        let original = missed_ub_report(
            &cand.fn_name,
            70,
            "out-of-bounds pointer arithmetic: alloc5 has size 16, so pointer to 20 bytes starting at offset 0 is out-of-bounds",
            AnnealOutcome::PassUnit,
            true,
        );
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand,
            &seed_refs,
            &original,
            |_| true,
            |sub| {
                assert_eq!(subsets[&sub.fn_source], 0, "only `[]` should be evaluated");
                Some(missed_ub_report(
                    &sub.fn_name,
                    31,
                    "out-of-bounds pointer arithmetic: alloc2 has size 16, so pointer to 24 bytes starting at offset 0 is out-of-bounds",
                    AnnealOutcome::PassUnit,
                    true,
                ))
            },
        );
        assert_eq!(res.status, MiriShrinkStatus::Minimized);
        assert!(res.minimized_mutator_chain.is_empty());
        assert!(res.minimized_candidate.applied_mutators.is_empty());
        assert_eq!(subsets[&res.minimized_candidate.fn_source], 0);
        assert_eq!(
            (res.shrink_evaluations, res.oracle_evaluations, res.compile_rejections),
            (1, 1, 0)
        );
    }

    /// An oracle query that produces no report (for example a failed live
    /// pipeline run) is never mistaken for a rejection that licenses a
    /// 1-minimality claim.
    #[test]
    fn oracle_failures_make_the_miri_shrink_inconclusive() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand, subsets) = find_candidate_with_distinct_subsets(2, &seed_refs);
        let msg = "constructing invalid value: encountered 0x02, but expected a boolean";
        let original = missed_ub_report(&cand.fn_name, 50, msg, AnnealOutcome::PassUnit, true);

        // `[]` cannot be judged; `{1}` reproduces the signature.
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand,
            &seed_refs,
            &original,
            |_| true,
            |sub| match subsets[&sub.fn_source] {
                0b00 => None,
                0b10 => Some(missed_ub_report(
                    &sub.fn_name,
                    31,
                    msg,
                    AnnealOutcome::PassUnit,
                    true,
                )),
                _ => Some(agree_report(&sub.fn_name)),
            },
        );
        assert_eq!(res.status, MiriShrinkStatus::Inconclusive);
        assert!(res.is_reduced(), "the confirmed reduction is still reported");
        assert_eq!(res.minimized_mutator_chain, vec![cand.applied_mutators[1].clone()]);
        assert_eq!(subsets[&res.minimized_candidate.fn_source], 0b10);
        assert_eq!(res.oracle_failures, 1);

        // A shrink whose every query fails never claims 1-minimality.
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand,
            &seed_refs,
            &original,
            |_| true,
            |_| None,
        );
        assert_eq!(res.status, MiriShrinkStatus::Inconclusive);
        assert!(!res.is_reduced());
        assert_eq!(res.oracle_failures, res.oracle_evaluations);
        assert_eq!(res.minimized_candidate, cand);
        assert_eq!(res.minimized_report, original);
    }

    /// Report of a program that the oracle did not compare for `reason`, with
    /// Miri and Anneal outcomes that `compare_miri_and_anneal` maps to exactly
    /// that verdict.
    fn not_compared_report(name: &str, reason: &NotComparedReason) -> ItemOracleReport {
        let (miri, anneal) = match reason {
            NotComparedReason::MiriOracleError(msg) => {
                (MiriOutcome::OracleError(msg.clone()), AnnealOutcome::PassUnit)
            }
            NotComparedReason::CaptureFailed(msg) => (
                MiriOutcome::PassUnit,
                AnnealOutcome::CaptureOrLeanError(msg.clone()),
            ),
            NotComparedReason::ExternalCall(def_path) => (
                MiriOutcome::PassUnit,
                AnnealOutcome::ExternalCall {
                    def_path: def_path.clone(),
                    span: None,
                },
            ),
            NotComparedReason::Unsupported(span) => (
                MiriOutcome::PassUnit,
                AnnealOutcome::Unsupported { span: span.clone() },
            ),
            NotComparedReason::OutOfFuel(span) => (
                MiriOutcome::PassUnit,
                AnnealOutcome::OutOfFuel { span: span.clone() },
            ),
        };
        let verdict = compare_miri_and_anneal(&miri, &anneal);
        assert_eq!(verdict, ComparisonVerdict::NotCompared(reason.clone()));
        ItemOracleReport {
            name: name.to_string(),
            fuel: MIRI_DIFFTEST_CANDIDATE_FUEL,
            miri,
            anneal,
            verdict,
            kernel_confirmed: false,
        }
    }

    /// A report of an oracle failure (Miri or the capture / Lean pipeline
    /// failed) counts as an oracle failure, like a missing report, so it never
    /// licenses a 1-minimality claim. Anneal's deterministic `NotCompared`
    /// judgments (an external call, an unsupported construct, exhausted fuel)
    /// rule the signature out and stay ordinary rejections.
    #[test]
    fn not_compared_oracle_errors_are_failures_and_anneal_judgments_are_rejections() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand, subsets) = find_candidate_with_distinct_subsets(2, &seed_refs);
        let msg = "constructing invalid value: encountered 0x02, but expected a boolean";
        let original = missed_ub_report(&cand.fn_name, 50, msg, AnnealOutcome::PassUnit, true);
        let failures = [
            NotComparedReason::MiriOracleError("Miri did not emit 'MIRI_START'".to_string()),
            NotComparedReason::CaptureFailed("Lean probe execution failed".to_string()),
        ];
        let judgments = [
            NotComparedReason::ExternalCall("core::intrinsics::exact_div".to_string()),
            NotComparedReason::Unsupported(Some(lib_span(40))),
            NotComparedReason::OutOfFuel(Some(lib_span(41))),
        ];
        for reason in failures.iter().chain(&judgments) {
            let is_failure = failures.contains(reason);
            let report = not_compared_report(&cand.fn_name, reason);
            assert_eq!(miri_report_is_oracle_failure(&report), is_failure, "{reason:?}");

            // `[]` is not compared, `{1}` reproduces the signature, and `{0}`
            // agrees.
            let res = minimize_miri_candidate_mutations_with_compile_check(
                &cand,
                &seed_refs,
                &original,
                |_| true,
                |sub| {
                    Some(match subsets[&sub.fn_source] {
                        0b00 => not_compared_report(&sub.fn_name, reason),
                        0b10 => missed_ub_report(
                            &sub.fn_name,
                            31,
                            msg,
                            AnnealOutcome::PassUnit,
                            true,
                        ),
                        _ => agree_report(&sub.fn_name),
                    })
                },
            );
            assert!(res.is_reduced(), "{reason:?}");
            assert_eq!(res.minimized_mutator_chain, vec![cand.applied_mutators[1].clone()]);
            assert_eq!(subsets[&res.minimized_candidate.fn_source], 0b10);
            assert_eq!((res.shrink_evaluations, res.oracle_evaluations), (2, 2), "{reason:?}");
            if is_failure {
                assert_eq!(res.status, MiriShrinkStatus::Inconclusive, "{reason:?}");
                assert_eq!(res.oracle_failures, 1, "{reason:?}");
            } else {
                assert_eq!(res.status, MiriShrinkStatus::Minimized, "{reason:?}");
                assert_eq!(res.oracle_failures, 0, "{reason:?}");
            }
        }
    }

    /// `"item_outcomes"` maps every evaluated item, in report order, to its
    /// verdict, Miri and Anneal outcome tags, and Lean `MirDiffTag` (`"none"`
    /// when the Anneal side failed), with JSON-escaped strings.
    #[test]
    fn item_outcomes_json_maps_each_item_to_its_verdict_and_outcome_tags() {
        assert_eq!(render_item_outcomes_json(&[]), "{}");
        let msg = "constructing invalid value: encountered 0x02, but expected a boolean";
        let reports = [
            agree_report("agree_fn"),
            missed_ub_report(
                "diverge_fn",
                12,
                msg,
                AnnealOutcome::PassScalar {
                    bits: 2,
                    size_bytes: 1,
                },
                true,
            ),
            not_compared_report(
                "external_fn",
                &NotComparedReason::ExternalCall("core::intrinsics::exact_div".to_string()),
            ),
            not_compared_report(
                "capture_fn",
                &NotComparedReason::CaptureFailed("`lake build` failed: \"x\"".to_string()),
            ),
        ];
        let expected_rows = [
            r#"    "agree_fn": {"verdict": "agree", "miri_outcome": "pass:scalar:10:4", "anneal_outcome": "pass:scalar:10:4", "anneal_lean_tag": "(MirDiffTag.normalScalar 10 4)"}"#,
            r#"    "diverge_fn": {"verdict": "diverge", "miri_outcome": "ub@src/lib.rs:12:14", "anneal_outcome": "pass:scalar:2:1", "anneal_lean_tag": "(MirDiffTag.normalScalar 2 1)"}"#,
            r#"    "external_fn": {"verdict": "not_compared", "miri_outcome": "pass:unit", "anneal_outcome": "externalCall:core::intrinsics::exact_div", "anneal_lean_tag": "(MirDiffTag.externalCall \"core::intrinsics::exact_div\")"}"#,
            r#"    "capture_fn": {"verdict": "not_compared", "miri_outcome": "pass:unit", "anneal_outcome": "capture_error:`lake build` failed: \"x\"", "anneal_lean_tag": "none"}"#,
        ];
        assert_eq!(
            render_item_outcomes_json(&reports),
            format!("{{\n{}\n  }}", expected_rows.join(",\n"))
        );
    }

    #[test]
    fn translate_pos_and_span_to_repro_preserve_preamble_and_zero_end_lines() {
        let pos_body = SourcePos {
            file: "/tmp/stage/src/lib.rs".to_string(),
            line: 120,
            col: 9,
        };
        assert_eq!(
            translate_pos_to_repro(&pos_body, 100, 40),
            SourcePos {
                file: "src/lib.rs".to_string(),
                line: 60,
                col: 9,
            }
        );
        let pos_preamble = SourcePos {
            file: "./src/lib.rs".to_string(),
            line: 18,
            col: 5,
        };
        assert_eq!(
            translate_pos_to_repro(&pos_preamble, 100, 40),
            SourcePos {
                file: "src/lib.rs".to_string(),
                line: 18,
                col: 5,
            }
        );

        let span_zero_end = SourceSpan {
            file: "/tmp/stage/src/lib.rs".to_string(),
            start_line: 115,
            start_col: 4,
            end_line: 0,
            end_col: 0,
        };
        assert_eq!(
            translate_span_to_repro(&span_zero_end, 100, 40),
            SourceSpan {
                file: "src/lib.rs".to_string(),
                start_line: 55,
                start_col: 4,
                end_line: 0,
                end_col: 0,
            }
        );
    }

    #[test]
    fn single_mutator_chain_is_judged_by_a_real_evaluation_not_assumed_minimal() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand, _) = find_candidate_with_distinct_subsets(1, &seed_refs);
        let original = missed_ub_report(
            &cand.fn_name,
            70,
            "constructing invalid value: encountered 0x02, but expected a boolean",
            AnnealOutcome::PassScalar {
                bits: 2,
                size_bytes: 1,
            },
            true,
        );
        let mut oracle_calls = 0usize;
        let res = minimize_miri_candidate_mutations_with_compile_check(
            &cand,
            &seed_refs,
            &original,
            |_| true,
            |sub| {
                oracle_calls += 1;
                Some(agree_report(&sub.fn_name))
            },
        );
        assert_eq!(oracle_calls, 1);
        assert_eq!(res.status, MiriShrinkStatus::AlreadyOneMinimal);
        assert_eq!(res.minimized_mutator_chain, cand.applied_mutators);
        assert_eq!(res.minimized_candidate, cand);
        assert_eq!(res.minimized_report, original);
        assert_eq!(
            (res.shrink_evaluations, res.oracle_evaluations, res.compile_rejections),
            (1, 1, 0)
        );

        // Identity candidates and non-divergent reports are never shrunk.
        let mut identity = cand.clone();
        identity.applied_mutators.clear();
        for (c, r) in [(&identity, &original), (&cand, &agree_report(&cand.fn_name))] {
            let res = minimize_miri_candidate_mutations_with_compile_check(
                c,
                &seed_refs,
                r,
                |_| panic!("no compile check expected"),
                |_| panic!("no oracle run expected"),
            );
            assert_eq!(res.status, MiriShrinkStatus::SkippedNotApplicable);
            assert_eq!(res.shrink_evaluations, 0);
        }
    }

    /// Exercises the live single-candidate oracle plumbing used by the shrinker
    /// (staging crate, the helper-linked pipeline that `evaluate_miri_batches`
    /// runs, item lookup, artifact extraction) and checks that live shrinking
    /// reports honest evaluation counts.
    #[test]
    fn live_single_candidate_oracle_run_and_honest_live_shrink_counts() {
        let seed_sources = corpus_seed_sources();
        let seed_refs: Vec<&str> = seed_sources.iter().map(String::as_str).collect();
        let (cand, _) = find_candidate_with_distinct_subsets(1, &seed_refs);
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repository root")
            .to_path_buf();
        let toolchain = MiriToolchain::resolve(None, None, None).expect("resolve Miri toolchain");

        let live = evaluate_candidate_live(
            &cand,
            MIRI_DIFFTEST_CANDIDATE_FUEL,
            &toolchain,
            Some(&repo_root),
        )
        .expect("live oracle run on a corpus candidate");
        assert_eq!(live.report.name, cand.fn_name);
        assert!(
            !matches!(live.report.miri, MiriOutcome::OracleError(_)),
            "Miri must execute the staged candidate: {:?}",
            live.report.miri
        );
        assert!(
            !matches!(live.report.anneal, AnnealOutcome::CaptureOrLeanError(_)),
            "Anneal capture + Lean evaluation must succeed: {:?}",
            live.report.anneal
        );
        assert!(
            live.mir_neighborhood.contains(&cand.fn_name),
            "captured MIR neighborhood must describe `{}`",
            cand.fn_name
        );

        // A synthetic divergence the live oracle cannot reproduce on `[]`: shrinking must
        // conclude `AlreadyOneMinimal` after exactly one real oracle run.
        let synthetic = missed_ub_report(
            &cand.fn_name,
            70,
            "synthetic divergence that no live oracle run reproduces",
            AnnealOutcome::PassUnit,
            true,
        );
        let res = minimize_miri_candidate_mutations(&cand, &seed_refs, &synthetic, Some(&repo_root))
            .expect("live shrink");
        assert_eq!(res.status, MiriShrinkStatus::AlreadyOneMinimal);
        assert_eq!(
            (
                res.shrink_evaluations,
                res.oracle_evaluations,
                res.compile_rejections,
                res.executed_oracle_runs
            ),
            (1, 1, 0, 1)
        );
    }

    /// Probes for the 8-family semantic-mutant self-check, keyed by probe id (a
    /// mutant id, or the `probe["id"]` of a variant that needs its own program).
    /// Each exercises one check of Anneal's semantics on which the live engine
    /// agrees with Miri, so a mutant of the semantics that omits or perturbs that
    /// check diverges from Miri: the UB / panic probes (`bool` validity,
    /// `StorageDead`, pointer provenance, division by zero, wide shift exponents,
    /// the inline `exact_div` remainder and signed-overflow guards, the
    /// `ctlz_nonzero` zero guard, and an `FnEntry`-protected call whose callee
    /// writes the protected place through a raw alias) are killed by a mutant that
    /// returns normally (`missed_ub` / `panic_vs_return`), and the probes on which
    /// Miri returns normally (`Operand::Move` of a non-`Copy` wrapper under a
    /// `Reserved` child reborrow, and a caller write after an `FnEntry`-protected
    /// call returns) are killed by a mutant that faults spuriously
    /// (`false_positive_ub`). `scripts/run_diff_test_campaign.py` embeds
    /// byte-identical sources in `SEEDED_SEMANTIC_MUTANTS` (checked by
    /// `scripts/test_run_diff_test_campaign.py`).
    ///
    /// `provenance_frag` overwrites all 8 bytes of the stored pointer `p` with the
    /// integer `p as usize` through a `*mut usize` alias, so `p` keeps `x`'s live
    /// address but its bytes carry no provenance, and `*p` is UB only because the
    /// provenance is gone (Miri: "dangling pointer (it has no provenance)"). The
    /// `PROVENANCE_FRAG_CONTROL_PROBES` pin that the rewritten bytes are `x`'s
    /// address and that this address reads `x`'s value `7` once it has provenance,
    /// so a mutant that accepts the provenance-free pointer returns `7`
    /// (`missed_ub`) instead of trapping.
    const SEMANTIC_MUTANT_PROBES: [(&str, &str); 11] = [
        (
            "bool_valid_range",
            r#"pub fn probe_bool_valid_range() -> u32 {
    let mut b: bool = false;
    let p: *mut u8 = (&raw mut b) as *mut u8;
    unsafe { *p = 2u8; }
    b as u32
}
"#,
        ),
        (
            "storage_dead_tag",
            r#"pub fn probe_storage_dead_tag() -> u32 {
    let dangling: *const u32 = {
        let dead_local: u32 = 42u32;
        &raw const dead_local
    };
    unsafe { *dangling }
}
"#,
        ),
        (
            "provenance_frag",
            r#"pub fn probe_provenance_frag() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let addr: usize = p as usize;
    let slot: *mut usize = (&raw mut p) as *mut usize;
    unsafe {
        *slot = addr;
        *p
    }
}
"#,
        ),
        (
            "div_by_zero",
            r#"pub fn probe_div_by_zero() -> u32 {
    let num: u32 = 100u32;
    let den: u32 = 0u32;
    num / den
}
"#,
        ),
        (
            "wide_shift",
            r#"pub fn probe_wide_shift() -> u64 {
    let lhs: u64 = 1u64;
    let rhs: u64 = 1u64 << 32;
    unsafe { unchecked_shl(lhs, rhs) }
}
"#,
        ),
        (
            "move_triggers_tb_write",
            r#"pub fn probe_move_triggers_tb_write() -> u32 {
    let mut x: NonCopyU32 = NonCopyU32(10u32);
    let root: *mut NonCopyU32 = &raw mut x;
    let r: &mut NonCopyU32 = unsafe { &mut *root };
    let moved: NonCopyU32 = x;
    *r = NonCopyU32(32u32);
    (*r).0 + moved.0
}
"#,
        ),
        (
            "exact_div_rem_omitted",
            r#"pub fn probe_exact_div_rem_omitted() -> u32 {
    let lhs: u32 = 7u32;
    let rhs: u32 = 2u32;
    unsafe { exact_div(lhs, rhs) }
}
"#,
        ),
        (
            "exact_div_signed_overflow",
            r#"pub fn probe_exact_div_signed_overflow() -> i8 {
    let lhs: i8 = i8::MIN;
    let rhs: i8 = -1i8;
    unsafe { exact_div(lhs, rhs) }
}
"#,
        ),
        (
            "ctlz_nonzero_zero",
            r#"pub fn probe_ctlz_nonzero_zero() -> u32 {
    let zero: u32 = 0u32;
    unsafe { ctlz_nonzero(zero) }
}
"#,
        ),
        (
            "protector_release_order",
            r#"pub fn probe_protector_release_order() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let r0: &mut u32 = unsafe { &mut *raw };
    let delta: u32 = helper_reborrow_mid(r0, 7u32);
    *r0 = 20u32;
    unsafe {
        *raw = *r0 + delta;
        *raw
    }
}
"#,
        ),
        (
            "protector_conflict",
            r#"pub fn probe_protector_conflict() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let v: u32 = probe_helper_protected_alias_write(&x, raw);
    v + unsafe { *raw }
}

#[inline(never)]
fn probe_helper_protected_alias_write(_r: &u32, alias: *mut u32) -> u32 {
    unsafe {
        *alias = 8u32;
    }
    3u32
}
"#,
        ),
    ];

    /// Semantic-mutant probes that call a crate helper (`helper_reborrow_mid` from
    /// the corpus preamble, or the probe's own `probe_helper_protected_alias_write`).
    /// Only the helper-linked pipeline that `miri-difftest` and the shrinker run
    /// links intra-crate callees; `cargo_anneal::run_difftest_oracle_pipeline`
    /// stops at the call (`externalCall`), so these probes are pinned through the
    /// linked pipeline alone.
    const HELPER_LINKED_SEMANTIC_MUTANT_PROBES: [&str; 2] =
        ["protector_release_order", "protector_conflict"];

    /// Live outcome of every `SEMANTIC_MUTANT_PROBES` entry, as
    /// `(id, miri_tag, anneal_tag, anneal_lean_tag)` with source positions relative
    /// to the probe's first line (`ub@src/lib.rs:<line>:<col>`). These are the
    /// `reference_miri_outcome`, `baseline_anneal_outcome`, and
    /// `baseline_anneal_lean_tag` that `SEEDED_SEMANTIC_MUTANTS` in
    /// `scripts/run_diff_test_campaign.py` replays as the unmutated baseline
    /// (checked identical by `scripts/test_run_diff_test_campaign.py`), so the
    /// simulated self-check baselines are the real engine's outcomes.
    const SEMANTIC_MUTANT_PROBE_OUTCOMES: [(&str, &str, &str, &str); 11] = [
        (
            "bool_valid_range",
            "ub@src/lib.rs:5:5",
            "ub@src/lib.rs:5:5: 5:6",
            "MirDiffTag.ub",
        ),
        (
            "storage_dead_tag",
            "ub@src/lib.rs:6:14",
            "ub@src/lib.rs:6:14: 6:23",
            "MirDiffTag.ub",
        ),
        (
            "provenance_frag",
            "ub@src/lib.rs:8:9",
            "ub@src/lib.rs:8:9: 8:11",
            "MirDiffTag.ub",
        ),
        (
            "div_by_zero",
            "panic@src/lib.rs:4:5",
            "panic@src/lib.rs:4:5: 4:14",
            "MirDiffTag.panic",
        ),
        (
            "wide_shift",
            "ub@src/lib.rs:4:14",
            "ub@src/lib.rs:4:14: 4:37",
            "MirDiffTag.ub",
        ),
        (
            "move_triggers_tb_write",
            "pass:scalar:42:4",
            "pass:scalar:42:4",
            "(MirDiffTag.normalScalar 42 4)",
        ),
        (
            "exact_div_rem_omitted",
            "ub@src/lib.rs:4:14",
            "ub@src/lib.rs:4:14: 4:33",
            "MirDiffTag.ub",
        ),
        (
            "exact_div_signed_overflow",
            "ub@src/lib.rs:4:14",
            "ub@src/lib.rs:4:14: 4:33",
            "MirDiffTag.ub",
        ),
        (
            "ctlz_nonzero_zero",
            "ub@src/lib.rs:3:14",
            "ub@src/lib.rs:3:14: 3:32",
            "MirDiffTag.ub",
        ),
        (
            "protector_release_order",
            "pass:scalar:42:4",
            "pass:scalar:42:4",
            "(MirDiffTag.normalScalar 42 4)",
        ),
        (
            "protector_conflict",
            "ub@src/lib.rs:11:9",
            "ub@src/lib.rs:11:9: 11:22",
            "MirDiffTag.ub",
        ),
    ];

    /// Controls and known gaps for the probes on which Miri returns normally or
    /// faults through a protector, each `(name, source)`:
    /// 1. `probe_gap_move_subplace_reborrow_write` is `move_triggers_tb_write` with
    ///    `r` reborrowed from the sub-place pointer `&raw mut x.0` (an `&mut u32`)
    ///    instead of `&raw mut x`. Miri still returns `42`, but the live engine
    ///    already reports UB at the child write `*r = 32u32` (`false_positive_ub`),
    ///    so a "move emits a foreign write" mutant would be equivalent to the
    ///    current engine on that form and could never be killed: the probe uses the
    ///    whole-place reborrow, and this known gap stays pinned (kernel-confirmed).
    /// 2. `probe_ctrl_protector_unprotected_alias_write` performs the
    ///    `protector_conflict` write with `&x` an unprotected, unused local instead
    ///    of a protected argument: Miri returns `3 + 8`, so Miri's UB in
    ///    `probe_protector_conflict` is the `FnEntry` protector violation. The live
    ///    engine reports UB at the write either way (its sibling-root retag freeze
    ///    of `raw`, `tests/miri-diff/README.md`), a known `false_positive_ub`.
    const SEMANTIC_MUTANT_CONTROL_PROBES: [(&str, &str); 2] = [
        (
            "probe_gap_move_subplace_reborrow_write",
            r#"pub fn probe_gap_move_subplace_reborrow_write() -> u32 {
    let mut x: NonCopyU32 = NonCopyU32(10u32);
    let root: *mut u32 = &raw mut x.0;
    let r: &mut u32 = unsafe { &mut *root };
    let moved: NonCopyU32 = x;
    *r = 32u32;
    *r + moved.0
}
"#,
        ),
        (
            "probe_ctrl_protector_unprotected_alias_write",
            r#"pub fn probe_ctrl_protector_unprotected_alias_write() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let _r: &u32 = &x;
    unsafe {
        *raw = 8u32;
    }
    3u32 + unsafe { *raw }
}
"#,
        ),
    ];

    /// Controls for `probe_provenance_frag`, each `(name, source, returned value)`
    /// and required to agree with Miri on that `u32` return value:
    /// 1. `probe_ctrl_provenance_addr_preserved` rewrites `p` exactly as the probe
    ///    does and returns `1` because `p` still holds `x`'s address: the probe
    ///    dereferences `x`'s live allocation address, not an unmapped one.
    /// 2. `probe_ctrl_provenance_exposed_addr` rewrites `p` with the same `*slot = addr`
    ///    overwrite and then dereferences `(p as usize) as *const u32`, which restores
    ///    provenance via an exposing round trip and returns `x`'s value `7`: only the
    ///    missing provenance makes `*p` UB, so a semantics that accepts the
    ///    provenance-free pointer returns `7` instead of trapping (`missed_ub`).
    const PROVENANCE_FRAG_CONTROL_PROBES: [(&str, &str, u128); 2] = [
        (
            "probe_ctrl_provenance_addr_preserved",
            r#"pub fn probe_ctrl_provenance_addr_preserved() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let addr: usize = p as usize;
    let slot: *mut usize = (&raw mut p) as *mut usize;
    unsafe {
        *slot = addr;
        ((p as usize) == addr) as u32
    }
}
"#,
            1,
        ),
        (
            "probe_ctrl_provenance_exposed_addr",
            r#"pub fn probe_ctrl_provenance_exposed_addr() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let addr: usize = p as usize;
    let slot: *mut usize = (&raw mut p) as *mut usize;
    unsafe {
        *slot = addr;
        let forged: *const u32 = (p as usize) as *const u32;
        *forged
    }
}
"#,
            7,
        ),
    ];

    /// Partial-pointer-byte provenance variants on which the live engine currently
    /// diverges from Miri, pinned as known engine gaps:
    /// 1. `probe_gap_provenance_overwritten_byte`: overwrites one byte of a stored
    ///    pointer with `0u8` and dereferences it (`missed_ub`, returns `7`, because
    ///    `mergeByteProvenance` retains provenance from the remaining 7 bytes).
    /// 2. `probe_gap_provenance_u8_roundtrip`: loads one byte of a stored pointer as
    ///    `u8`, stores it back, and dereferences it (`ub_location_mismatch`: the
    ///    engine flags the `u8` load of a pointer byte, Miri the later dereference).
    /// 3. `probe_gap_provenance_mixed_fragments`: copies one byte of a pointer to `y`
    ///    over the first byte of a pointer to `x` and dereferences the mixed pointer
    ///    (`missed_ub`, returns `y`'s value `9`).
    const KNOWN_PROVENANCE_GAP_PROBES: [(&str, &str); 3] = [
        (
            "probe_gap_provenance_overwritten_byte",
            PROVENANCE_OVERWRITTEN_BYTE_PROBE,
        ),
        (
            "probe_gap_provenance_u8_roundtrip",
            PROVENANCE_U8_ROUNDTRIP_PROBE,
        ),
        (
            "probe_gap_provenance_mixed_fragments",
            PROVENANCE_MIXED_FRAGMENTS_PROBE,
        ),
    ];

    const PROVENANCE_OVERWRITTEN_BYTE_PROBE: &str = r#"pub fn probe_gap_provenance_overwritten_byte() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let byte_ptr: *mut u8 = (&raw mut p) as *mut u8;
    unsafe {
        *byte_ptr = 0u8;
        *p
    }
}
"#;

    const PROVENANCE_U8_ROUNDTRIP_PROBE: &str = r#"pub fn probe_gap_provenance_u8_roundtrip() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let byte_ptr: *mut u8 = (&raw mut p) as *mut u8;
    unsafe {
        let b0: u8 = *byte_ptr;
        *byte_ptr = b0;
        *p
    }
}
"#;

    const PROVENANCE_MIXED_FRAGMENTS_PROBE: &str = r#"pub fn probe_gap_provenance_mixed_fragments() -> u32 {
    let x: u32 = 7u32;
    let y: u32 = 9u32;
    let mut p: *const u32 = &raw const x;
    let q: *const u32 = &raw const y;
    let dst: *mut u8 = (&raw mut p) as *mut u8;
    let src: *const u8 = (&raw const q) as *const u8;
    unsafe {
        copy_nonoverlapping(src, dst, 1);
        *p
    }
}
"#;

    /// Run `fn_sources` through one live oracle pipeline in a fresh staging crate
    /// and return the staged crate source and the reports keyed by item name.
    fn run_probe_pipeline(
        label: &str,
        fn_sources: &[&str],
        names: &[String],
        pipeline: impl FnOnce(
            &DifftestOracleConfig,
            &[OracleItemSpec],
        ) -> Result<Vec<ItemOracleReport>, String>,
    ) -> (String, BTreeMap<String, ItemOracleReport>) {
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repository root")
            .to_path_buf();
        let toolchain = MiriToolchain::resolve(None, None, None).expect("resolve Miri toolchain");
        let staging_dir = create_staging_dir(label).expect("staging dir");
        let crate_source = build_standalone_candidate_source(&fn_sources.join("\n"));
        fs::write(staging_dir.join("src/lib.rs"), &crate_source).expect("write probes");
        let specs: Vec<OracleItemSpec> = names
            .iter()
            .map(|n| OracleItemSpec::with_fuel(n.clone(), MIRI_DIFFTEST_CANDIDATE_FUEL))
            .collect();
        let cfg = DifftestOracleConfig {
            corpus_root: staging_dir.clone(),
            capture_rustflags: DEFAULT_CAPTURE_RUSTFLAGS
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
            miri_flags: DEFAULT_MIRI_FLAGS.iter().map(|s| (*s).to_string()).collect(),
            anneal_repo_root: Some(repo_root),
            rustc_wrapper: None,
            toolchain,
        };
        let items = pipeline(&cfg, &specs);
        let _ = fs::remove_dir_all(&staging_dir);
        let by_name = items
            .unwrap_or_else(|e| panic!("live `{label}` oracle pipeline over the probes: {e}"))
            .into_iter()
            .map(|it| (it.name.clone(), it))
            .collect();
        (crate_source, by_name)
    }

    /// 1-based line of the first line of `source` that contains `needle`.
    fn line_of(source: &str, needle: &str) -> u32 {
        let idx = source
            .lines()
            .position(|l| l.contains(needle))
            .unwrap_or_else(|| panic!("`{needle}` not found in staged probe source"));
        u32::try_from(idx + 1).expect("line number fits u32")
    }

    /// Rewrite a live Miri outcome's `summary_tag` with its position relative to a
    /// probe whose first line is line `start` of the staged `src/lib.rs` (the form
    /// of `SEMANTIC_MUTANT_PROBE_OUTCOMES`).
    fn probe_relative_miri_tag(miri: &MiriOutcome, start: u32) -> String {
        match miri {
            MiriOutcome::Ub { pos: Some(pos), .. } => {
                format!(
                    "ub@{}",
                    translate_pos_to_repro(pos, start, 1).display_short()
                )
            }
            MiriOutcome::Panic { pos: Some(pos), .. } => {
                format!(
                    "panic@{}",
                    translate_pos_to_repro(pos, start, 1).display_short()
                )
            }
            other => other.summary_tag(),
        }
    }

    /// Rewrite a live Anneal outcome's `summary_tag` with its span relative to a
    /// probe whose first line is line `start` of the staged `src/lib.rs`.
    fn probe_relative_anneal_tag(anneal: &AnnealOutcome, start: u32) -> String {
        let rel = |kind: &str, span: &SourceSpan| {
            format!(
                "{kind}@{}",
                translate_span_to_repro(span, start, 1).display_short()
            )
        };
        match anneal {
            AnnealOutcome::Ub { span: Some(span) } => rel("ub", span),
            AnnealOutcome::Panic { span: Some(span) } => rel("panic", span),
            AnnealOutcome::Abort { span: Some(span) } => rel("abort", span),
            AnnealOutcome::Unsupported { span: Some(span) } => rel("unsupported", span),
            other => other.summary_tag(),
        }
    }

    /// Pins the live behavior of the semantic-mutant, provenance-control,
    /// semantic-mutant control, and pointer-fragment provenance probes, measured
    /// through both the helper-linked pipeline that `miri-difftest` and the
    /// shrinker run and `cargo_anneal::run_difftest_oracle_pipeline` (which must
    /// agree on every probe that calls no crate helper; the
    /// `HELPER_LINKED_SEMANTIC_MUTANT_PROBES` stop at an `externalCall` there).
    ///
    /// Every semantic-mutant probe must agree with Miri, with exactly the
    /// probe-relative Miri outcome, Anneal outcome (strict `FailureKind.ub` for
    /// every UB probe), and Lean tag that `SEMANTIC_MUTANT_PROBE_OUTCOMES` records,
    /// so a mutant that omits or perturbs the corresponding check is killable and
    /// `SEEDED_SEMANTIC_MUTANTS` replays the real engine: a probe pinned on a Miri
    /// UB or panic must exercise that fault, and a probe pinned on a Miri return
    /// must return a scalar. Each UB probe's Miri diagnostic names the check it
    /// exercises (the missing provenance, the `exact_div` remainder, the signed
    /// remainder overflow, `ctlz_nonzero` of zero, or the forbidden write access of
    /// the protector conflict). `probe_provenance_frag` must fail in Miri for lack
    /// of provenance, and both `PROVENANCE_FRAG_CONTROL_PROBES` must agree on their
    /// return values (the rewritten pointer holds `x`'s address, which reads `7`
    /// with provenance). The three provenance gap probes and the two
    /// `SEMANTIC_MUTANT_CONTROL_PROBES` are kernel-confirmed engine gaps, pinned
    /// exactly as measured: the overwritten-byte and mixed-fragment probes are
    /// `missed_ub` (the engine returns `7` and `9`), the `u8` round trip is a
    /// `ub_location_mismatch` (the engine flags the `u8` load of a pointer byte,
    /// Miri the later dereference), and the sub-place move and unprotected alias
    /// write are `false_positive_ub` at the child / raw write on which Miri returns
    /// `42` / `11`. When the engine changes on any probe, this test fails and the
    /// pin must be updated (a ratchet, like a `known_anneal_bug` entry).
    #[test]
    fn semantic_mutant_probes_agree_live_and_known_provenance_gaps_stay_pinned() {
        let gap_probes = KNOWN_PROVENANCE_GAP_PROBES;
        let fn_sources: Vec<&str> = SEMANTIC_MUTANT_PROBES
            .iter()
            .map(|(_, src)| *src)
            .chain(
                PROVENANCE_FRAG_CONTROL_PROBES
                    .iter()
                    .map(|(_, src, _)| *src),
            )
            .chain(gap_probes.iter().map(|(_, src)| *src))
            .chain(SEMANTIC_MUTANT_CONTROL_PROBES.iter().map(|(_, src)| *src))
            .collect();
        let names: Vec<String> = SEMANTIC_MUTANT_PROBES
            .iter()
            .map(|(id, _)| format!("probe_{id}"))
            .chain(
                PROVENANCE_FRAG_CONTROL_PROBES
                    .iter()
                    .map(|(name, _, _)| (*name).to_string()),
            )
            .chain(gap_probes.iter().map(|(name, _)| (*name).to_string()))
            .chain(
                SEMANTIC_MUTANT_CONTROL_PROBES
                    .iter()
                    .map(|(name, _)| (*name).to_string()),
            )
            .collect();
        let helper_linked: BTreeSet<String> = HELPER_LINKED_SEMANTIC_MUTANT_PROBES
            .iter()
            .map(|id| format!("probe_{id}"))
            .collect();
        let (crate_source, linked) =
            run_probe_pipeline("probes_linked", &fn_sources, &names, |cfg, specs| {
                run_linked_difftest_oracle_pipeline(cfg, specs).map(|run| run.report.items)
            });
        let (_, plain) = run_probe_pipeline("probes_plain", &fn_sources, &names, |cfg, specs| {
            cargo_anneal::run_difftest_oracle_pipeline(cfg, specs).map(|rep| rep.items)
        });

        let summarize = |item: &ItemOracleReport| {
            let verdict = match &item.verdict {
                ComparisonVerdict::Agree => "agree".to_string(),
                ComparisonVerdict::Diverge(kind) => divergence_class_slug(kind).to_string(),
                ComparisonVerdict::NotCompared(reason) => format!("not_compared:{reason:?}"),
            };
            (
                verdict,
                normalize_miri_outcome_family(&item.miri),
                item.anneal.summary_tag(),
                item.kernel_confirmed,
            )
        };
        for name in &names {
            if helper_linked.contains(name) {
                assert!(
                    matches!(
                        &plain[name].verdict,
                        ComparisonVerdict::NotCompared(NotComparedReason::ExternalCall(_))
                    ),
                    "the plain pipeline links no crate helper, so `{name}` must stop at an \
                     external call there: {:?}",
                    plain[name].verdict
                );
                continue;
            }
            assert_eq!(
                summarize(&linked[name]),
                summarize(&plain[name]),
                "pipelines disagree on `{name}`"
            );
        }

        assert_eq!(
            SEMANTIC_MUTANT_PROBE_OUTCOMES.map(|(id, ..)| id),
            SEMANTIC_MUTANT_PROBES.map(|(id, _)| id),
            "every semantic-mutant probe needs a pinned outcome"
        );
        for (id, miri_tag, anneal_tag, lean_tag) in SEMANTIC_MUTANT_PROBE_OUTCOMES {
            let fn_name = format!("probe_{id}");
            let start = line_of(&crate_source, &format!("pub fn {fn_name}()"));
            for (label, reports) in [("linked", &linked), ("plain", &plain)] {
                if label == "plain" && helper_linked.contains(&fn_name) {
                    continue;
                }
                let item = &reports[&fn_name];
                assert_eq!(
                    item.verdict,
                    ComparisonVerdict::Agree,
                    "probe `{id}` must agree with the unmutated engine ({label}): miri={:?} \
                     anneal={:?}",
                    item.miri,
                    item.anneal
                );
                if miri_tag.starts_with("pass:") {
                    assert!(
                        matches!(item.miri, MiriOutcome::PassScalar { .. }),
                        "probe `{id}` must return normally in Miri ({label}): {:?}",
                        item.miri
                    );
                } else {
                    assert!(
                        matches!(
                            item.miri,
                            MiriOutcome::Ub { .. } | MiriOutcome::Panic { .. }
                        ),
                        "probe `{id}` must exercise a UB / panic check ({label}): {:?}",
                        item.miri
                    );
                }
                assert_eq!(
                    (
                        probe_relative_miri_tag(&item.miri, start),
                        probe_relative_anneal_tag(&item.anneal, start),
                        item.anneal.to_lean_mir_diff_tag(),
                    ),
                    (
                        miri_tag.to_string(),
                        anneal_tag.to_string(),
                        Some(lean_tag.to_string()),
                    ),
                    "probe `{id}` live outcome ({label}) drifted from \
                     SEMANTIC_MUTANT_PROBE_OUTCOMES (and SEEDED_SEMANTIC_MUTANTS)"
                );
            }
        }

        // Each UB probe's Miri diagnostic names the check that its mutant omits.
        for (id, needles) in [
            (
                "exact_div_rem_omitted",
                &["exact_div", "without remainder"][..],
            ),
            (
                "exact_div_signed_overflow",
                &["overflow in signed remainder (dividing MIN by -1)"][..],
            ),
            ("ctlz_nonzero_zero", &["`ctlz_nonzero` called on 0"][..]),
            (
                "protector_conflict",
                &["write access through", "is forbidden"][..],
            ),
        ] {
            let item = &linked[&format!("probe_{id}")];
            assert!(
                matches!(&item.miri, MiriOutcome::Ub { message, .. }
                    if needles.iter().all(|n| message.contains(n))),
                "probe `{id}` must fail in Miri with {needles:?}: {:?}",
                item.miri
            );
        }

        // Known gaps and controls of the probes on which Miri returns normally or
        // faults through a protector (`SEMANTIC_MUTANT_CONTROL_PROBES`).
        for (name, returned, fault_line_needle) in [
            (
                "probe_gap_move_subplace_reborrow_write",
                42u128,
                "    *r = 32u32;",
            ),
            (
                "probe_ctrl_protector_unprotected_alias_write",
                11u128,
                "        *raw = 8u32;",
            ),
        ] {
            let fault_line = line_of(&crate_source, fault_line_needle);
            let item = &linked[name];
            assert!(
                matches!(
                    (&item.verdict, &item.miri, &item.anneal),
                    (
                        ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. }),
                        MiriOutcome::PassScalar { bits, size_bytes: 4 },
                        AnnealOutcome::Ub { span: Some(span) },
                    ) if *bits == returned && span.start_line == fault_line
                ) && item.kernel_confirmed,
                "known engine gap `{name}` changed (fixed?): verdict={:?} miri={:?} anneal={:?} \
                 kernel_confirmed={}; update the pin and the probe notes in \
                 SEEDED_SEMANTIC_MUTANTS",
                item.verdict,
                item.miri,
                item.anneal,
                item.kernel_confirmed
            );
        }

        let no_provenance = |item: &ItemOracleReport| {
            matches!(&item.miri, MiriOutcome::Ub { message, .. }
                if message.contains("dangling pointer (it has no provenance)"))
        };
        for (label, reports) in [("linked", &linked), ("plain", &plain)] {
            let frag = &reports["probe_provenance_frag"];
            assert!(
                no_provenance(frag) && matches!(frag.anneal, AnnealOutcome::Ub { .. }),
                "probe_provenance_frag must be UB for lack of provenance in Miri and strict UB \
                 in Anneal ({label}): miri={:?} anneal={:?}",
                frag.miri,
                frag.anneal
            );
            for (name, _, returned) in PROVENANCE_FRAG_CONTROL_PROBES {
                let item = &reports[name];
                let expected = (
                    MiriOutcome::PassScalar {
                        bits: returned,
                        size_bytes: 4,
                    },
                    AnnealOutcome::PassScalar {
                        bits: returned,
                        size_bytes: 4,
                    },
                );
                assert!(
                    item.verdict == ComparisonVerdict::Agree
                        && (item.miri.clone(), item.anneal.clone()) == expected,
                    "provenance control `{name}` must agree on returning {returned} ({label}): \
                     verdict={:?} miri={:?} anneal={:?}",
                    item.verdict,
                    item.miri,
                    item.anneal
                );
            }
        }
        for (name, returned) in [
            ("probe_gap_provenance_overwritten_byte", 7u128),
            ("probe_gap_provenance_mixed_fragments", 9u128),
        ] {
            let item = &linked[name];
            assert!(
                matches!(&item.verdict, ComparisonVerdict::Diverge(DivergenceKind::MissedUb { .. }))
                    && no_provenance(item)
                    && item.anneal
                        == AnnealOutcome::PassScalar {
                            bits: returned,
                            size_bytes: 4,
                        }
                    && item.kernel_confirmed,
                "known engine gap `{name}` changed (fixed?): verdict={:?} miri={:?} anneal={:?} \
                 kernel_confirmed={}; update the pin and consider promoting the probe",
                item.verdict,
                item.miri,
                item.anneal,
                item.kernel_confirmed
            );
        }

        let roundtrip = &linked["probe_gap_provenance_u8_roundtrip"];
        let load_line = line_of(&crate_source, "let b0: u8 = *byte_ptr;");
        let deref_line = load_line + 2;
        assert!(
            matches!(
                (&roundtrip.verdict, &roundtrip.miri, &roundtrip.anneal),
                (
                    ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch { .. }),
                    MiriOutcome::Ub { pos: Some(miri_pos), .. },
                    AnnealOutcome::Ub { span: Some(anneal_span) },
                ) if miri_pos.line == deref_line && anneal_span.start_line == load_line
            ) && no_provenance(roundtrip)
                && roundtrip.kernel_confirmed,
            "known engine gap `probe_gap_provenance_u8_roundtrip` changed (fixed?): verdict={:?} \
             miri={:?} anneal={:?} kernel_confirmed={}; update the pin and consider promoting \
             the probe",
            roundtrip.verdict,
            roundtrip.miri,
            roundtrip.anneal,
            roundtrip.kernel_confirmed
        );
    }

    #[test]
    fn finding_bundle_json_and_summary_serialize_shrink_metadata() {
        let dir = create_staging_dir("bundle_test").expect("create test dir");
        let mut bundle = MiriFindingBundle {
            finding_id: "finding_0000_test".to_string(),
            fn_name: "pass_integer_arith_basic__b0_c0".to_string(),
            seed_name: "pass_integer_arith_basic".to_string(),
            applied_mutators: vec!["RawPtrOffsetMutator".to_string()],
            original_mutator_chain: vec![
                "ArithmeticCastMutator".to_string(),
                "RawPtrOffsetMutator".to_string(),
                "PlaceProjectionWrapper".to_string(),
            ],
            minimized_mutator_chain: vec!["RawPtrOffsetMutator".to_string()],
            shrink_evaluations: 5,
            executed_oracle_runs: 3,
            shrink_status: MiriShrinkStatus::Minimized.slug().to_string(),
            divergence_class: "ub_location_mismatch".to_string(),
            witness_polarity: WitnessPolarity::ValueMismatch.as_str().to_string(),
            miri_outcome_tag: "ub@src/lib.rs:52:17".to_string(),
            miri_excerpt: "error: Undefined Behavior".to_string(),
            miri_pos: Some("src/lib.rs:52:17".to_string()),
            batch_miri_pos: Some("src/lib.rs:120:17".to_string()),
            anneal_outcome_tag: "ub@src/lib.rs:56:9:56:42".to_string(),
            anneal_lean_tag: "MirDiffTag.ub".to_string(),
            anneal_span: Some("src/lib.rs:56:9:56:42".to_string()),
            batch_anneal_span: Some("src/lib.rs:124:9:124:42".to_string()),
            mir_neighborhood: "def body : CapturedMir := ...".to_string(),
            kernel_confirmed: true,
            kernel_confirm_theorems: "theorem confirm_tag_x : ... := by\n  rfl".to_string(),
            mutant_source: "pub fn pass_integer_arith_basic__b0_c0() {}\n".to_string(),
            repro_path: None,
        };

        write_finding_bundle_to_dir(&dir, &mut bundle).expect("write finding bundle");
        let bundle_dir = dir.join("finding_0000_test");
        let finding_json =
            fs::read_to_string(bundle_dir.join("finding.json")).expect("read finding.json");
        let summary_md =
            fs::read_to_string(bundle_dir.join("SUMMARY.md")).expect("read SUMMARY.md");
        let _ = fs::remove_dir_all(&dir);

        assert!(finding_json.contains(
            "\"original_mutator_chain\": [\"ArithmeticCastMutator\", \"RawPtrOffsetMutator\", \"PlaceProjectionWrapper\"]"
        ));
        assert!(finding_json.contains("\"minimized_mutator_chain\": [\"RawPtrOffsetMutator\"]"));
        assert!(finding_json.contains("\"applied_mutators\": [\"RawPtrOffsetMutator\"]"));
        assert!(finding_json.contains("\"shrink_evaluations\": 5"));
        assert!(finding_json.contains("\"executed_oracle_runs\": 3"));
        assert!(finding_json.contains("\"shrink_status\": \"minimized\""));
        assert!(finding_json.contains("\"witness_polarity\": \"value_mismatch\""));
        assert!(summary_md.contains(
            "- **Original mutator chain**: `ArithmeticCastMutator, RawPtrOffsetMutator, PlaceProjectionWrapper`"
        ));
        assert!(summary_md.contains("- **Minimized mutator chain**: `RawPtrOffsetMutator`"));
        assert!(summary_md.contains(
            "- **Shrink evaluations**: `5` (live oracle runs executed: `3`)"
        ));
        assert!(summary_md.contains("- **Shrink status**: `minimized`"));
        assert!(summary_md.contains("- **Witness polarity**: `value_mismatch`"));
    }

    #[test]
    fn witness_polarity_classifies_full_cartesian_product_and_slugs_roundtrip() {
        for &slug in &WITNESS_POLARITY_NAMES {
            let parsed = WitnessPolarity::from_str_slug(slug).expect("parse polarity slug");
            assert_eq!(parsed.as_str(), slug);
            assert_eq!(parsed.to_string(), slug);
        }
        assert_eq!(WitnessPolarity::from_str_slug("unknown"), None);
        assert!(WitnessPolarity::UnsoundMissedFault.is_unsound());
        assert!(!WitnessPolarity::SoundConservativeAbstraction.is_unsound());
        assert!(!WitnessPolarity::ValueMismatch.is_unsound());
        assert!(!WitnessPolarity::HarnessOrExtractionError.is_unsound());

        let pos_a = SourcePos {
            file: "src/lib.rs".to_string(),
            line: 10,
            col: 5,
        };
        let span_a = SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: 10,
            start_col: 1,
            end_line: 10,
            end_col: 20,
        };
        let span_b = SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: 20,
            start_col: 1,
            end_line: 20,
            end_col: 20,
        };

        // 1. Agreements return None.
        assert_eq!(
            classify_witness_polarity(&MiriOutcome::PassUnit, &AnnealOutcome::PassUnit),
            None
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::PassScalar {
                    bits: 42,
                    size_bytes: 4
                },
                &AnnealOutcome::PassScalar {
                    bits: 42,
                    size_bytes: 4
                }
            ),
            None
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Ub {
                    pos: Some(pos_a.clone()),
                    message: "ub".to_string()
                },
                &AnnealOutcome::Ub {
                    span: Some(span_a.clone())
                }
            ),
            None
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Panic {
                    pos: Some(pos_a.clone()),
                    message: "panic".to_string()
                },
                &AnnealOutcome::Panic {
                    span: Some(span_a.clone())
                }
            ),
            None
        );

        // 2. UnsoundMissedFault: Miri UB or Panic vs Anneal Pass.
        for miri_fault in [
            MiriOutcome::Ub {
                pos: Some(pos_a.clone()),
                message: "ub".to_string(),
            },
            MiriOutcome::Panic {
                pos: Some(pos_a.clone()),
                message: "panic".to_string(),
            },
        ] {
            for anneal_pass in [
                AnnealOutcome::PassUnit,
                AnnealOutcome::PassScalar {
                    bits: 0,
                    size_bytes: 4,
                },
                AnnealOutcome::PassOther,
            ] {
                assert_eq!(
                    classify_witness_polarity(&miri_fault, &anneal_pass),
                    Some(WitnessPolarity::UnsoundMissedFault),
                    "expected UnsoundMissedFault for ({miri_fault:?}, {anneal_pass:?})"
                );
            }
        }

        // 3. SoundConservativeAbstraction: Miri Pass vs Anneal UB or Unsupported.
        for miri_pass in [
            MiriOutcome::PassUnit,
            MiriOutcome::PassScalar {
                bits: 7,
                size_bytes: 4,
            },
        ] {
            for anneal_cons in [
                AnnealOutcome::Ub {
                    span: Some(span_a.clone()),
                },
                AnnealOutcome::Unsupported {
                    span: Some(span_a.clone()),
                },
            ] {
                assert_eq!(
                    classify_witness_polarity(&miri_pass, &anneal_cons),
                    Some(WitnessPolarity::SoundConservativeAbstraction),
                    "expected SoundConservativeAbstraction for ({miri_pass:?}, {anneal_cons:?})"
                );
            }
        }

        // 4. ValueMismatch: wrong scalar value, ReturnVsPanic, UbLocationMismatch, PanicSiteMismatch, UB vs Panic.
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::PassScalar {
                    bits: 1,
                    size_bytes: 4
                },
                &AnnealOutcome::PassScalar {
                    bits: 2,
                    size_bytes: 4
                }
            ),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::PassUnit,
                &AnnealOutcome::Panic {
                    span: Some(span_a.clone())
                }
            ),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Ub {
                    pos: Some(pos_a.clone()),
                    message: "ub".to_string()
                },
                &AnnealOutcome::Ub {
                    span: Some(span_b.clone())
                }
            ),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Panic {
                    pos: Some(pos_a.clone()),
                    message: "panic".to_string()
                },
                &AnnealOutcome::Panic {
                    span: Some(span_b.clone())
                }
            ),
            Some(WitnessPolarity::ValueMismatch)
        );
        // Miri UB vs Anneal Panic is MissedUb (UnsoundMissedFault), while
        // Miri Panic vs Anneal UB is FalsePositiveUb (SoundConservativeAbstraction).
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Ub {
                    pos: Some(pos_a.clone()),
                    message: "ub".to_string()
                },
                &AnnealOutcome::Panic {
                    span: Some(span_a.clone())
                }
            ),
            Some(WitnessPolarity::UnsoundMissedFault)
        );
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Panic {
                    pos: Some(pos_a.clone()),
                    message: "panic".to_string()
                },
                &AnnealOutcome::Ub {
                    span: Some(span_a.clone())
                }
            ),
            Some(WitnessPolarity::SoundConservativeAbstraction)
        );

        // 5. HarnessOrExtractionError: OracleError, ExternalCall, OutOfFuel, CaptureOrLeanError, or Unsupported when Miri faulted.
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::OracleError("err".to_string()),
                &AnnealOutcome::PassUnit
            ),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );
        for anneal_err in [
            AnnealOutcome::ExternalCall {
                def_path: "foo::bar".to_string(),
                span: None,
            },
            AnnealOutcome::OutOfFuel { span: None },
            AnnealOutcome::CaptureOrLeanError("err".to_string()),
        ] {
            assert_eq!(
                classify_witness_polarity(&MiriOutcome::PassUnit, &anneal_err),
                Some(WitnessPolarity::HarnessOrExtractionError)
            );
        }
        assert_eq!(
            classify_witness_polarity(
                &MiriOutcome::Ub {
                    pos: Some(pos_a),
                    message: "ub".to_string()
                },
                &AnnealOutcome::Unsupported { span: Some(span_a) }
            ),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );

        // 6. Tag-based classifier matches structured classifier across all classes.
        assert_eq!(
            classify_outcome_tags_polarity("pass:unit", "pass:unit", Some("agree")),
            None
        );
        assert_eq!(
            classify_outcome_tags_polarity("ub@src/lib.rs:10:5", "pass:scalar:1:4", Some("missed_ub")),
            Some(WitnessPolarity::UnsoundMissedFault)
        );
        assert_eq!(
            classify_outcome_tags_polarity("panic@src/lib.rs:10:5", "pass:unit", Some("panic_vs_return")),
            Some(WitnessPolarity::UnsoundMissedFault)
        );
        assert_eq!(
            classify_outcome_tags_polarity("pass:scalar:1:4", "ub@src/lib.rs:10:5", Some("false_positive_ub")),
            Some(WitnessPolarity::SoundConservativeAbstraction)
        );
        assert_eq!(
            classify_outcome_tags_polarity("pass:scalar:1:4", "unsupported", Some("unsupported")),
            Some(WitnessPolarity::SoundConservativeAbstraction)
        );
        assert_eq!(
            classify_outcome_tags_polarity("ub@src/lib.rs:10:5", "unsupported", Some("unsupported")),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );
        assert_eq!(
            classify_outcome_tags_polarity("pass:scalar:1:4", "pass:scalar:2:4", Some("wrong_value")),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_outcome_tags_polarity("pass:unit", "externalCall:foo", Some("external_call")),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );
    }

    /// Independent restatement of the documented [`WitnessPolarity`] total map,
    /// written directly from the table in its doc comment rather than through
    /// [`compare_miri_and_anneal`].
    fn documented_witness_polarity(
        miri: &MiriOutcome,
        anneal: &AnnealOutcome,
    ) -> Option<WitnessPolarity> {
        use WitnessPolarity::*;
        let miri_returns = matches!(miri, MiriOutcome::PassUnit | MiriOutcome::PassScalar { .. });
        if matches!(miri, MiriOutcome::OracleError(_)) {
            return Some(HarnessOrExtractionError);
        }
        match anneal {
            AnnealOutcome::ExternalCall { .. }
            | AnnealOutcome::OutOfFuel { .. }
            | AnnealOutcome::CaptureOrLeanError(_) => return Some(HarnessOrExtractionError),
            AnnealOutcome::Unsupported { .. } => {
                return Some(if miri_returns {
                    SoundConservativeAbstraction
                } else {
                    HarnessOrExtractionError
                });
            }
            _ => {}
        }
        let site_in_span = |pos: &Option<SourcePos>, span: &Option<SourceSpan>| {
            matches!((pos, span), (Some(p), Some(s)) if s.contains_pos(p))
        };
        match (miri, anneal) {
            (MiriOutcome::PassUnit, AnnealOutcome::PassUnit) => None,
            (
                MiriOutcome::PassScalar { bits, size_bytes },
                AnnealOutcome::PassScalar {
                    bits: a_bits,
                    size_bytes: a_size,
                },
            ) if bits == a_bits && size_bytes == a_size => None,
            (_, AnnealOutcome::Ub { .. }) if miri_returns => Some(SoundConservativeAbstraction),
            (_, _) if miri_returns => Some(ValueMismatch),
            (MiriOutcome::Panic { pos, .. }, AnnealOutcome::Panic { span }) => {
                (!site_in_span(pos, span)).then_some(ValueMismatch)
            }
            (MiriOutcome::Panic { .. }, AnnealOutcome::Ub { .. }) => {
                Some(SoundConservativeAbstraction)
            }
            (MiriOutcome::Panic { .. }, _) => Some(UnsoundMissedFault),
            (MiriOutcome::Ub { pos, .. }, AnnealOutcome::Ub { span }) => {
                (!site_in_span(pos, span)).then_some(ValueMismatch)
            }
            (MiriOutcome::Ub { .. }, _) => Some(UnsoundMissedFault),
            _ => unreachable!("every Miri row is covered: {miri:?} vs {anneal:?}"),
        }
    }

    /// The verdict slug that a campaign report records for `verdict`: `agree`,
    /// the divergence class, or the not-compared reason key.
    fn verdict_slug(verdict: &ComparisonVerdict) -> &'static str {
        match verdict {
            ComparisonVerdict::Agree => "agree",
            ComparisonVerdict::Diverge(kind) => divergence_class_slug(kind),
            ComparisonVerdict::NotCompared(reason) => match reason {
                NotComparedReason::ExternalCall(_) => "external_call",
                NotComparedReason::Unsupported(_) => "unsupported",
                NotComparedReason::OutOfFuel(_) => "out_of_fuel",
                NotComparedReason::MiriOracleError(_) => "miri_oracle_error",
                NotComparedReason::CaptureFailed(_) => "capture_failed",
            },
        }
    }

    #[test]
    fn witness_polarity_total_map_matches_documented_table_and_tag_roundtrip() {
        let pos = |line: u32, col: u32| SourcePos {
            file: "src/lib.rs".to_string(),
            line,
            col,
        };
        let span = |line: u32, start_col: u32, end_col: u32| SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: line,
            start_col,
            end_line: line,
            end_col,
        };
        let miri_outcomes = vec![
            MiriOutcome::PassUnit,
            MiriOutcome::PassScalar {
                bits: 42,
                size_bytes: 4,
            },
            MiriOutcome::PassScalar {
                bits: 42,
                size_bytes: 8,
            },
            MiriOutcome::Panic {
                pos: Some(pos(10, 5)),
                message: "attempt to add with overflow".to_string(),
            },
            MiriOutcome::Panic {
                pos: None,
                message: "panicked".to_string(),
            },
            MiriOutcome::Ub {
                pos: Some(pos(10, 5)),
                message: "Undefined Behavior: protected tag".to_string(),
            },
            MiriOutcome::Ub {
                pos: None,
                message: "Undefined Behavior".to_string(),
            },
            MiriOutcome::OracleError("driver failed".to_string()),
        ];
        let anneal_outcomes = vec![
            AnnealOutcome::PassUnit,
            AnnealOutcome::PassScalar {
                bits: 42,
                size_bytes: 4,
            },
            AnnealOutcome::PassScalar {
                bits: 7,
                size_bytes: 4,
            },
            AnnealOutcome::PassOther,
            AnnealOutcome::Panic {
                span: Some(span(10, 1, 20)),
            },
            AnnealOutcome::Panic {
                span: Some(span(20, 1, 20)),
            },
            AnnealOutcome::Panic { span: None },
            AnnealOutcome::Abort {
                span: Some(span(10, 1, 20)),
            },
            AnnealOutcome::Ub {
                span: Some(span(10, 1, 20)),
            },
            AnnealOutcome::Ub {
                span: Some(span(20, 1, 20)),
            },
            AnnealOutcome::Ub { span: None },
            AnnealOutcome::Unsupported {
                span: Some(span(10, 1, 20)),
            },
            AnnealOutcome::Unsupported { span: None },
            AnnealOutcome::ExternalCall {
                def_path: "core::panicking::panic_fmt".to_string(),
                span: None,
            },
            AnnealOutcome::OutOfFuel { span: None },
            AnnealOutcome::CaptureOrLeanError("lake failed".to_string()),
        ];

        let mut seen: BTreeSet<Option<WitnessPolarity>> = BTreeSet::new();
        for miri in &miri_outcomes {
            // Summary tags parse back into an outcome with the same tag.
            let miri_tag = miri.summary_tag();
            let reparsed_miri = parse_miri_summary_tag(&miri_tag)
                .unwrap_or_else(|| panic!("Miri tag `{miri_tag}` must parse"));
            assert_eq!(reparsed_miri.summary_tag(), miri_tag);
            for anneal in &anneal_outcomes {
                let anneal_tag = anneal.summary_tag();
                let reparsed_anneal = parse_anneal_summary_tag(&anneal_tag)
                    .unwrap_or_else(|| panic!("Anneal tag `{anneal_tag}` must parse"));
                assert_eq!(reparsed_anneal.summary_tag(), anneal_tag);

                let expected = documented_witness_polarity(miri, anneal);
                seen.insert(expected);
                let verdict = compare_miri_and_anneal(miri, anneal);
                assert_eq!(
                    classify_witness_polarity(miri, anneal),
                    expected,
                    "structured classifier disagrees with the documented map for \
                     ({miri_tag}, {anneal_tag}) with verdict {verdict:?}"
                );
                assert_eq!(
                    classify_verdict_witness_polarity(miri, anneal, &verdict),
                    expected
                );
                assert_eq!(expected.is_none(), verdict.is_agree());
                // Tag-only classification (no verdict slug) recovers the same
                // polarity, including source-site containment for `panic`/`ub`.
                assert_eq!(
                    classify_outcome_tags_polarity(&miri_tag, &anneal_tag, None),
                    expected,
                    "tag classifier (no slug) disagrees for ({miri_tag}, {anneal_tag})"
                );
                // So does classification with the verdict slug a report records,
                // with and without the `not_compared_` prefix.
                let slug = verdict_slug(&verdict);
                assert_eq!(
                    classify_outcome_tags_polarity(&miri_tag, &anneal_tag, Some(slug)),
                    expected,
                    "tag classifier (slug `{slug}`) disagrees for ({miri_tag}, {anneal_tag})"
                );
                if verdict.is_not_compared() {
                    let prefixed = format!("not_compared_{slug}");
                    assert_eq!(
                        classify_outcome_tags_polarity(&miri_tag, &anneal_tag, Some(&prefixed)),
                        expected
                    );
                }
            }
        }
        // The sample product reaches agreement and all four polarity classes.
        assert!(seen.contains(&None));
        for pol in WitnessPolarity::ALL {
            assert!(seen.contains(&Some(pol)), "sample product never produced {pol}");
        }

        // `ALL` and `WITNESS_POLARITY_NAMES` list the same slugs in order.
        assert_eq!(
            WitnessPolarity::ALL.map(|p| p.as_str()),
            WITNESS_POLARITY_NAMES
        );

        // A Miri site inside Anneal's span agrees even though the tags differ
        // as strings; a missing location on either side is a mismatch.
        assert_eq!(
            classify_outcome_tags_polarity("ub@src/lib.rs:10:5", "ub@src/lib.rs:10:1: 10:20", None),
            None
        );
        assert_eq!(
            classify_outcome_tags_polarity("ub@src/lib.rs:10:5", "ub@src/lib.rs:11:1: 11:20", None),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_outcome_tags_polarity("ub", "ub@src/lib.rs:10:1: 10:20", None),
            Some(WitnessPolarity::ValueMismatch)
        );
        assert_eq!(
            classify_outcome_tags_polarity("panic@src/lib.rs:10:5", "panic", None),
            Some(WitnessPolarity::ValueMismatch)
        );
        // Unparseable tags cannot be compared semantically.
        for (m, a) in [
            ("pass", "pass:unit"),
            ("pass:unit", "passed"),
            ("ub@not-a-position", "ub@src/lib.rs:10:1: 10:20"),
            ("panicked", "panic"),
            ("pass:scalar:1", "pass:scalar:1:4"),
        ] {
            assert_eq!(
                classify_outcome_tags_polarity(m, a, None),
                Some(WitnessPolarity::HarnessOrExtractionError),
                "unparseable tags ({m}, {a}) must be a harness error"
            );
        }
        // A recognized slug wins over the tags (panic-site reconciliation keeps
        // a reconciled `agree`), and an unknown slug falls back to the tags.
        assert_eq!(
            classify_outcome_tags_polarity("panic@src/lib.rs:3:1", "panic@src/lib.rs:9:1: 9:5", Some("agree")),
            None
        );
        assert_eq!(
            classify_outcome_tags_polarity("ub@src/lib.rs:10:5", "pass:unit", Some("not_a_slug")),
            Some(WitnessPolarity::UnsoundMissedFault)
        );
        assert_eq!(
            classify_outcome_tags_polarity("panic@src/lib.rs:10:5", "unsupported", Some("unsupported")),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );
        assert_eq!(
            classify_outcome_tags_polarity("pass:unit", "unsupported", Some("compile_failed")),
            Some(WitnessPolarity::HarnessOrExtractionError)
        );
    }

    #[test]
    fn staged_helper_reachability_links_transitive_model_helper_chains_only() {
        // Generated batches and reproducers embed the preamble: only helpers that
        // the candidates reach (directly or through other helpers) are linked.
        let staged = format!(
            "{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n\
             pub fn cand__b0_c0() -> u32 {{\n    \
                 let mut s: u32 = 1u32;\n    \
                 helper_reborrow_mid(&mut s, 2u32)\n\
             }}\n"
        );
        let reached = staged_helper_fns_reachable_from_candidates(&staged, &[]);
        for helper in ["helper_reborrow_mid", "helper_reborrow_leaf"] {
            assert!(reached.contains(helper), "missing {helper}: {reached:?}");
        }
        for helper in [
            "helper_shared_mid",
            "helper_shared_leaf",
            "helper_unwind_mid",
            "helper_unwind_leaf",
            "helper_add_ten",
        ] {
            assert!(!reached.contains(helper), "unexpected {helper}: {reached:?}");
        }
        // A substring of a helper name is not a mention of the helper.
        let staged_substring = format!(
            "{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n\
             pub fn helper_shared_mid_like() -> u32 {{ 3u32 }}\n"
        );
        let reached = staged_helper_fns_reachable_from_candidates(&staged_substring, &[]);
        assert!(!reached.contains("helper_shared_mid"), "{reached:?}");
        assert!(reached.contains("helper_shared_mid_like"), "{reached:?}");
        // The identity corpus does not embed the preamble verbatim; when `items`
        // is empty every function it mentions is reachable, and when `items`
        // names a specific subset (`pass_direct_fn_call`), only the helpers
        // reachable from that subset (`helper_add_ten`) are linked.
        let corpus_reached = staged_helper_fns_reachable_from_candidates(
            crate::mutators_miri::RAW_MIRI_DIFF_CORPUS_RS,
            &[],
        );
        for helper in ["helper_add_ten", "helper_reborrow_mid", "helper_reborrow_leaf"] {
            assert!(corpus_reached.contains(helper), "corpus misses {helper}");
        }
        let subset_reached = staged_helper_fns_reachable_from_candidates(
            crate::mutators_miri::RAW_MIRI_DIFF_CORPUS_RS,
            &[OracleItemSpec::with_fuel("pass_direct_fn_call", 256)],
        );
        assert!(subset_reached.contains("helper_add_ten"), "{subset_reached:?}");
        for unrelated in [
            "helper_reborrow_mid",
            "helper_reborrow_leaf",
            "helper_shared_mid",
            "helper_unwind_mid",
            "helper_unwind_guarded",
        ] {
            assert!(
                !subset_reached.contains(unrelated),
                "subset run unexpectedly linked {unrelated}: {subset_reached:?}"
            );
        }
    }

    #[test]
    fn lean_confirm_failures_downgrade_only_on_resource_exhaustion() {
        for (signal, output) in [
            (
                false,
                "MiriOracleConfirm.lean:220:2: error: (deterministic) timeout at `whnf`, maximum \
                 number of heartbeats (2000000) has been reached\nUse `set_option maxHeartbeats \
                 <num>` to set the limit.",
            ),
            (false, "INTERNAL PANIC: out of memory"),
            (false, "error: (kernel) deep recursion detected"),
            (false, "error: maximum recursion depth has been reached"),
            (false, "Stack overflow detected. Aborting."),
            (true, ""),
        ] {
            assert!(
                lean_confirm_failure_is_resource_exhaustion(signal, output),
                "resource exhaustion not recognized: signal={signal} output={output:?}"
            );
        }
        for output in [
            "MiriOracleConfirm.lean:221:2: error: The rfl tactic failed. Possible reasons:\n- The \
             goal is not a reflexive relation",
            "error: type mismatch\n  rfl\nhas type\n  evalMirDiffTagBounded 512 body s = \
             evalMirDiffTagBounded 512 body s : Prop\nbut is expected to have type\n  \
             evalMirDiffTagBounded 512 body s = MirDiffTag.ub : Prop",
            "error: unknown identifier 'Mir.MiriDiffCorpus.cand.body'",
            "error: unknown module prefix 'Mir'",
        ] {
            assert!(
                !lean_confirm_failure_is_resource_exhaustion(false, output),
                "a rejected or ill-formed confirmation must abort, not downgrade: {output:?}"
            );
        }
    }

    #[test]
    fn witness_polarity_accounting_identity_detects_drift() {
        let zeros = |names: &[&str]| -> BTreeMap<String, usize> {
            names.iter().map(|k| (k.to_string(), 0)).collect()
        };
        let mut report = MiriCampaignEvalReport {
            mode: "seeded".to_string(),
            seed: 1,
            batches: 1,
            batch_size: 9,
            total_candidates: 9,
            compiled_candidates: 8,
            compile_failed_candidates: 1,
            compile_pass_rate_pct: 88.9,
            compared_candidates: 6,
            agree_count: 2,
            diverge_count: 4,
            not_compared_count: 3,
            kernel_confirmed_divergences: 4,
            miri_verdicts: BTreeMap::new(),
            anneal_outcomes: BTreeMap::new(),
            divergence_classes: zeros(&DIVERGENCE_CLASS_NAMES),
            witness_polarity_counts: zeros(&WITNESS_POLARITY_NAMES),
            not_compared_reasons: zeros(&NOT_COMPARED_REASON_NAMES),
            unmodeled_external_calls: BTreeMap::new(),
            mutator_applications: BTreeMap::new(),
            findings: Vec::new(),
            reconciled_panic_sites: Vec::new(),
            obs_path_signatures: Vec::new(),
            item_reports: Vec::new(),
            elapsed_ms: 0.0,
        };
        // 4 divergences: missed_ub, panic_vs_return, false_positive_ub,
        // wrong_value; 3 not compared: compile_failed, unsupported (Miri pass),
        // and unsupported (Miri ub).
        for class in ["missed_ub", "panic_vs_return", "false_positive_ub", "wrong_value"] {
            *report.divergence_classes.get_mut(class).unwrap() += 1;
        }
        *report.not_compared_reasons.get_mut("compile_failed").unwrap() += 1;
        *report.not_compared_reasons.get_mut("unsupported").unwrap() += 2;
        for (pol, n) in [
            (WitnessPolarity::UnsoundMissedFault, 2),
            (WitnessPolarity::SoundConservativeAbstraction, 2),
            (WitnessPolarity::ValueMismatch, 1),
            (WitnessPolarity::HarnessOrExtractionError, 2),
        ] {
            report
                .witness_polarity_counts
                .insert(pol.as_str().to_string(), n);
        }
        assert!(witness_polarity_accounting_holds(&report));

        // Each single-count drift breaks one identity.
        let mut drifted = report.clone();
        *drifted
            .witness_polarity_counts
            .get_mut("unsound_missed_fault")
            .unwrap() -= 1;
        *drifted.witness_polarity_counts.get_mut("value_mismatch").unwrap() += 1;
        assert!(!witness_polarity_accounting_holds(&drifted));

        let mut drifted = report.clone();
        *drifted
            .witness_polarity_counts
            .get_mut("sound_conservative_abstraction")
            .unwrap() += 2;
        *drifted
            .witness_polarity_counts
            .get_mut("harness_or_extraction_error")
            .unwrap() -= 2;
        assert!(
            !witness_polarity_accounting_holds(&drifted),
            "more conservative `unsupported` than `unsupported` candidates"
        );

        let mut drifted = report.clone();
        drifted.witness_polarity_counts.insert("unknown".to_string(), 0);
        assert!(!witness_polarity_accounting_holds(&drifted));

        let mut drifted = report.clone();
        drifted.not_compared_count += 1;
        assert!(!witness_polarity_accounting_holds(&drifted));

        // The rendered JSON and Markdown expose every canonical polarity key,
        // including the `Polarity` column in `## Divergences Detected`.
        let mut report_with_finding = report.clone();
        report_with_finding.findings.push(MiriFindingBundle {
            finding_id: "finding_0000_cand".to_string(),
            fn_name: "cand".to_string(),
            seed_name: "seed".to_string(),
            applied_mutators: Vec::new(),
            original_mutator_chain: Vec::new(),
            minimized_mutator_chain: Vec::new(),
            shrink_evaluations: 0,
            executed_oracle_runs: 0,
            shrink_status: "shrunk_to_1_minimal".to_string(),
            divergence_class: "missed_ub".to_string(),
            witness_polarity: "unsound_missed_fault".to_string(),
            miri_outcome_tag: "ub@src/lib.rs:10:5".to_string(),
            miri_excerpt: String::new(),
            miri_pos: Some("src/lib.rs:10:5".to_string()),
            batch_miri_pos: Some("src/lib.rs:10:5".to_string()),
            anneal_outcome_tag: "pass:scalar:0:4".to_string(),
            anneal_lean_tag: "MirDiffTag.passScalar 0 4".to_string(),
            anneal_span: None,
            batch_anneal_span: None,
            mir_neighborhood: String::new(),
            kernel_confirmed: true,
            kernel_confirm_theorems: String::new(),
            mutant_source: String::new(),
            repro_path: None,
        });
        let json = render_eval_report_json(&report_with_finding);
        let md = render_eval_report_markdown(&report_with_finding);
        for slug in WITNESS_POLARITY_NAMES {
            assert!(json.contains(&format!("\"{slug}\"")), "JSON missing {slug}");
            assert!(md.contains(&format!("| `{slug}` |")), "Markdown missing {slug}");
        }
        assert!(
            md.contains("| Finding ID | Function | Class | Polarity | Miri | Anneal | Kernel Confirmed | Shrink |"),
            "Markdown findings table missing Polarity column:\n{md}"
        );
        assert!(
            md.contains("| `finding_0000_cand` | `cand` | `missed_ub` | `unsound_missed_fault` |"),
            "Markdown findings row missing witness_polarity:\n{md}"
        );
    }

    #[test]
    fn extract_confirm_theorems_and_reachability_handle_unconfirmed_items_and_impl_macro_callees() {
        let confirm_src = "\
def linkedCallees : List CapturedMir :=
  [Mir.MiriDiffCorpus.helper_add_ten.body]

theorem confirm_tag_cand_ok :
    evalMirDiffTagBounded 512 Mir.MiriDiffCorpus.cand_ok.body linkedCallees =
      MirDiffTag.ub := by
  rfl
";
        assert!(
            extract_confirm_theorems(confirm_src, "cand_ok")
                .contains("theorem confirm_tag_cand_ok :"),
            "confirmed item must include its theorem and linkedCallees"
        );
        assert_eq!(
            extract_confirm_theorems(confirm_src, "cand_unconfirmed"),
            "",
            "unconfirmed item in a multi-item confirm module must not emit orphaned linkedCallees"
        );

        let staged = "\
macro_rules! call_via_macro {
    ($e:expr) => { helper_from_macro($e) };
}
struct Guard(u32);
impl Drop for Guard {
    fn drop(&mut self) {
        let _ = helper_from_drop(self.0);
    }
}
fn helper_from_macro(x: u32) -> u32 { x + 1 }
fn helper_from_drop(x: u32) -> u32 { x + 2 }
fn helper_from_nested(x: u32) -> u32 { x + 4 }
fn unrelated_helper(x: u32) -> u32 { x + 3 }
pub fn cand_entry() -> u32 {
    fn inner_nested(v: u32) -> u32 {
        helper_from_nested(v)
    }
    let _g = Guard(5);
    inner_nested(call_via_macro!(10))
}
";
        let specs = vec![OracleItemSpec {
            name: "cand_entry".to_string(),
            fuel: 512,
        }];
        let reached = staged_helper_fns_reachable_from_candidates(staged, &specs);
        assert!(reached.contains("cand_entry"));
        assert!(reached.contains("inner_nested"));
        assert!(reached.contains("helper_from_nested"));
        assert!(reached.contains("helper_from_macro"));
        assert!(reached.contains("helper_from_drop"));
        assert!(!reached.contains("unrelated_helper"));
    }

    #[test]
    fn helper_reachability_unions_same_named_fns_and_confirm_keeps_opaque_helpers() {
        // `cand_shadow`'s nested `helper_mid` (inside an `unsafe` block) is
        // indexed after the top-level `helper_mid`; reachability from
        // `cand_top` must still follow the top-level body to `helper_leaf`,
        // while `UnusedGuard`'s `drop` body must not leak `helper_unused_drop`
        // into `cand_shadow` (which only uses `Guard`).
        let lib_rs = "\
pub fn helper_leaf(v: u32) -> u32 { v }
pub fn helper_mid(v: u32) -> u32 { helper_leaf(v) }
fn helper_unrelated(v: u32) -> u32 { v + 1 }
fn helper_from_block_nested(v: u32) -> u32 { v + 2 }
fn helper_unused_drop(v: u32) -> u32 { v + 3 }
pub struct Guard(pub u32);
impl Drop for Guard {
    fn drop(&mut self) {}
}
pub struct UnusedGuard(pub u32);
impl Drop for UnusedGuard {
    fn drop(&mut self) {
        let _ = helper_unused_drop(self.0);
    }
}
pub fn cand_top() -> u32 {
    helper_mid(1u32)
}
pub fn cand_shadow() -> u32 {
    let _g = Guard(2u32);
    let inner_val = unsafe {
        fn helper_mid() -> u32 { helper_from_block_nested(7u32) }
        helper_mid()
    };
    inner_val + helper_unrelated(3u32)
}
";
        let spec = |name: &str| OracleItemSpec {
            name: name.to_string(),
            fuel: 128,
        };
        let reached = staged_helper_fns_reachable_from_candidates(lib_rs, &[spec("cand_top")]);
        for name in ["cand_top", "helper_mid", "helper_leaf"] {
            assert!(reached.contains(name), "missing {name}: {reached:?}");
        }
        for name in [
            "helper_unrelated",
            "helper_unused_drop",
            "drop",
            "cand_shadow",
        ] {
            assert!(!reached.contains(name), "unexpected {name}: {reached:?}");
        }

        let shadow_reached =
            staged_helper_fns_reachable_from_candidates(lib_rs, &[spec("cand_shadow")]);
        for name in [
            "cand_shadow",
            "helper_mid",
            "helper_from_block_nested",
            "helper_unrelated",
        ] {
            assert!(
                shadow_reached.contains(name),
                "missing {name}: {shadow_reached:?}"
            );
        }
        assert!(
            !shadow_reached.contains("helper_unused_drop"),
            "UnusedGuard::drop must not leak into cand_shadow: {shadow_reached:?}"
        );

        // `MiriOracleConfirm.lean` links, for `cand_top`, only the helpers it
        // reaches plus helpers that token reachability cannot rule out (a
        // derive-generated `eq` and a closure nested in `cand_top`), while
        // excluding items nested in `cand_shadow` and `Drop` impls for
        // unreached structs (`Guard`, `UnusedGuard`).
        let pairs: Vec<(String, String)> = [
            ("cand_top", "X.cand_top"),
            ("cand_shadow", "X.cand_shadow"),
            ("helper_leaf", "X.helper_leaf"),
            ("helper_mid", "X.helper_mid"),
            ("helper_mid", "X.cand_shadow.helper_mid"),
            ("helper_from_block_nested", "X.helper_from_block_nested"),
            ("helper_unrelated", "X.helper_unrelated"),
            ("helper_unused_drop", "X.helper_unused_drop"),
            ("drop", "X.Guard_as_core_ops_Drop_drop"),
            ("drop", "X.UnusedGuard_as_core_ops_Drop_drop"),
            ("eq", "X.Pair_as_core_cmp_PartialEq_eq"),
            ("{closure#0}", "X.cand_top__closure_0"),
            ("{closure#0}", "X.cand_shadow__closure_0"),
        ]
        .iter()
        .map(|(short, suffix)| (short.to_string(), suffix.to_string()))
        .collect();
        let entries = [spec("cand_top")];
        let (_, helpers) = partition_subject_callees("X", &pairs, &entries);
        let linked = confirm_helper_module_suffixes(lib_rs, "X", &pairs, &helpers, &entries);
        assert_eq!(
            linked,
            [
                "X.Pair_as_core_cmp_PartialEq_eq",
                "X.cand_top__closure_0",
                "X.helper_from_block_nested",
                "X.helper_leaf",
                "X.helper_mid",
            ],
            "helpers: {helpers:?}"
        );
        // For `cand_shadow`, the `Drop` impl of its `Guard`, its nested
        // `helper_mid` and closure, and its reachable helpers are linked, while
        // `UnusedGuard`'s `Drop` impl and `cand_top`'s closure are excluded.
        let shadow = [spec("cand_shadow")];
        let (_, helpers) = partition_subject_callees("X", &pairs, &shadow);
        let linked = confirm_helper_module_suffixes(lib_rs, "X", &pairs, &helpers, &shadow);
        assert_eq!(
            linked,
            [
                "X.Guard_as_core_ops_Drop_drop",
                "X.Pair_as_core_cmp_PartialEq_eq",
                "X.cand_shadow.helper_mid",
                "X.cand_shadow__closure_0",
                "X.helper_from_block_nested",
                "X.helper_leaf",
                "X.helper_mid",
                "X.helper_unrelated",
            ],
            "helpers: {helpers:?}"
        );
    }

    #[test]
    fn miri_lean_jobs_and_cgroup_memory_limits_handle_thresholds_overrides_and_stat() {
        const GIB_KIB: u64 = 1024 * 1024;

        // 32–36 GiB capsules clamp to 1 worker regardless of available memory.
        assert_eq!(
            miri_lean_jobs_for_memory(Some(32 * GIB_KIB), Some(30 * GIB_KIB)),
            1
        );
        assert_eq!(
            miri_lean_jobs_for_memory(Some(36 * GIB_KIB), Some(35 * GIB_KIB)),
            1
        );
        // Large host with < 24 GiB headroom -> 1 worker.
        assert_eq!(
            miri_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(20 * GIB_KIB)),
            1
        );
        // Up to 64 GiB total or < 48 GiB headroom -> 2 workers.
        assert_eq!(
            miri_lean_jobs_for_memory(Some(64 * GIB_KIB), Some(60 * GIB_KIB)),
            2
        );
        assert_eq!(
            miri_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(40 * GIB_KIB)),
            2
        );
        // > 64 GiB total and >= 48 GiB headroom -> 4 workers.
        assert_eq!(
            miri_lean_jobs_for_memory(Some(128 * GIB_KIB), Some(96 * GIB_KIB)),
            4
        );
        // Missing memory info defaults conservatively to 1.
        assert_eq!(miri_lean_jobs_for_memory(None, None), 1);
        assert_eq!(miri_lean_jobs_for_memory(Some(128 * GIB_KIB), None), 1);

        // `ANNEAL_MIRI_LEAN_JOBS` overrides memory heuristics and caps at 8.
        assert_eq!(
            resolve_miri_lean_jobs_with_env(Some("6"), Some(32 * GIB_KIB), Some(16 * GIB_KIB)),
            6
        );
        assert_eq!(
            resolve_miri_lean_jobs_with_env(Some("24"), Some(32 * GIB_KIB), Some(16 * GIB_KIB)),
            8
        );
        assert_eq!(
            resolve_miri_lean_jobs_with_env(Some("0"), Some(64 * GIB_KIB), Some(50 * GIB_KIB)),
            2
        );
        assert_eq!(
            resolve_miri_lean_jobs_with_env(Some("bogus"), Some(64 * GIB_KIB), Some(50 * GIB_KIB)),
            2
        );

        // `cgroup_memory_limits_kib` walks hierarchy, handles `"max"`, and uses `anon + shmem`.
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let root = env::temp_dir().join(format!(
            "anneal-miri-cgroup-test-{}-{nanos}",
            std::process::id()
        ));
        let scope = root.join("user.slice/app.slice/miri.scope");
        fs::create_dir_all(&scope).unwrap();
        fs::write(root.join("user.slice/memory.max"), "max\n").unwrap();
        fs::write(
            root.join("user.slice/app.slice/memory.max"),
            format!("{}\n", 48 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            root.join("user.slice/app.slice/memory.current"),
            format!("{}\n", 18 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            scope.join("memory.max"),
            format!("{}\n", 40 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            scope.join("memory.stat"),
            format!(
                "anon {}\nfile {}\nshmem {}\n",
                4 * GIB_KIB * 1024,
                28 * GIB_KIB * 1024,
                2 * GIB_KIB * 1024
            ),
        )
        .unwrap();
        let (limit, headroom) =
            cgroup_memory_limits_kib(&root, "0::/user.slice/app.slice/miri.scope\n");
        assert_eq!(limit, Some(40 * GIB_KIB));
        // Leaf headroom = 40 - (4 + 2) = 34 GiB; app.slice headroom (via memory.current) = 48 - 18 = 30 GiB.
        assert_eq!(headroom, Some(30 * GIB_KIB));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn chunked_miri_probe_stage_partitions_over_64_items_and_aggregates_frames_messages_and_omissions()
     {
        let items: Vec<(OracleItemSpec, String)> = (0..150)
            .map(|i| {
                let name = format!("cand_{i:03}");
                (
                    OracleItemSpec::with_fuel(name.clone(), 400),
                    format!("MiriDiffCorpus.{name}"),
                )
            })
            .collect();

        let observed_chunks: std::sync::Mutex<Vec<(usize, MiriStageRunKind, usize)>> =
            std::sync::Mutex::new(Vec::new());
        let mut outcomes = BTreeMap::new();
        let mut frames = BTreeMap::new();
        let mut messages = BTreeMap::new();

        let errors = aggregate_miri_probe_stage(
            &items,
            MIRI_PROBE_CHUNK_SIZE,
            2,
            |chunk_idx, run_kind, _label, chunk| {
                observed_chunks
                    .lock()
                    .unwrap()
                    .push((chunk_idx, run_kind, chunk.len()));
                let mut out = String::new();
                for (spec, _) in chunk {
                    if spec.name == "cand_130" {
                        // Deliberately omit ANNEAL_PROBE line for cand_130 in chunk 2.
                        continue;
                    } else if spec.name == "cand_070" {
                        out.push_str(&format!(
                            "ANNEAL_PROBE\t{}\tpanic\tsrc/lib.rs:70:5:70:20\n\
                             ANNEAL_PANIC_FRAME\t{}\tmiri_diff_corpus::cand_070\n\
                             ANNEAL_PANIC_MESSAGE\t{}\t[98, 111, 111, 109]\n",
                            spec.name, spec.name, spec.name
                        ));
                    } else {
                        out.push_str(&format!(
                            "ANNEAL_PROBE\t{}\tpass:scalar:42:4\tnone\n",
                            spec.name
                        ));
                    }
                }
                Ok(out)
            },
            &mut outcomes,
            &mut frames,
            &mut messages,
        );

        assert!(errors.is_empty(), "unexpected probe stage errors: {errors:?}");
        let mut recorded = observed_chunks.into_inner().unwrap();
        recorded.sort_by_key(|&(idx, _, _)| idx);
        assert_eq!(
            recorded,
            vec![
                (0, MiriStageRunKind::Chunk { wave_jobs: 2 }, 64),
                (1, MiriStageRunKind::Chunk { wave_jobs: 2 }, 64),
                (2, MiriStageRunKind::Chunk { wave_jobs: 1 }, 22),
            ],
            "150 items must split into 64 + 64 (2-worker wave) + 22 (1-worker trailing wave)"
        );
        assert_eq!(
            MiriStageRunKind::Chunk { wave_jobs: 2 }.active_workers(),
            2
        );
        assert_eq!(
            MiriStageRunKind::Chunk { wave_jobs: 1 }.active_workers(),
            1
        );
        assert_eq!(MiriStageRunKind::Fallback.active_workers(), 1);
        assert_eq!(MiriStageRunKind::Remainder.active_workers(), 1);
        assert_eq!(outcomes.len(), 150);
        assert_eq!(
            outcomes.get("cand_000"),
            Some(&AnnealOutcome::PassScalar {
                bits: 42,
                size_bytes: 4
            })
        );
        assert!(matches!(
            outcomes.get("cand_070"),
            Some(AnnealOutcome::Panic { .. })
        ));
        assert_eq!(
            frames.get("cand_070").map(String::as_str),
            Some("miri_diff_corpus::cand_070")
        );
        assert_eq!(messages.get("cand_070").map(Vec::as_slice), Some(&b"boom"[..]));
        match outcomes.get("cand_130") {
            Some(AnnealOutcome::CaptureOrLeanError(msg)) => {
                assert!(
                    msg.contains("Lean probe output omitted ANNEAL_PROBE line for 'cand_130'"),
                    "unexpected missing-probe error: {msg}"
                );
            }
            other => panic!("expected CaptureOrLeanError for omitted probe line, got {other:?}"),
        }
    }

    #[test]
    fn isolated_miri_stage_isolates_single_bad_candidate_and_trips_circuit_breaker_on_systematic_failure()
     {
        // 1. Single bad candidate in chunk 0 (out of 70 items across 2 chunks) is isolated
        //    to CaptureOrLeanError with stdout + stderr `✖` / `error:` diagnostics while all
        //    other 69 candidates succeed.
        let items: Vec<(OracleItemSpec, String)> = (0..70)
            .map(|i| {
                let name = format!("item_{i:03}");
                (
                    OracleItemSpec::with_fuel(name.clone(), 200),
                    format!("MiriDiffCorpus.{name}"),
                )
            })
            .collect();

        let stage = run_isolated_miri_stage(
            "MiriMirBuild",
            &items,
            MIRI_PROBE_CHUNK_SIZE,
            1,
            |(spec, _)| spec.name.as_str(),
            |_chunk_idx, _is_fallback, _label, chunk| {
                if chunk.iter().any(|(s, _)| s.name == "item_017") {
                    let stdout = (0..25)
                        .map(|k| format!("✔ [{k}/64] Built Mir.MiriDiffCorpus.ok_{k}"))
                        .chain([
                            "✖ [25/64] Building Mir.MiriDiffCorpus.item_017".to_string(),
                            "error: .anneal/generated/Mir/MiriDiffCorpus/item_017.lean:12:4: type mismatch".to_string(),
                        ])
                        .chain((26..55).map(|k| format!("info: trailing build line {k}")))
                        .collect::<Vec<_>>()
                        .join("\n");
                    let stderr = "error: Lake build failed with 1 target error";
                    return Err(format_lean_command_failure(
                        "lake build failed with status exit status: 1",
                        &stdout,
                        stderr,
                    ));
                }
                Ok(chunk.iter().map(|(s, _)| (s.name.clone(), ())).collect())
            },
        );
        assert_eq!(stage.results.len(), 69);
        assert_eq!(stage.failed_reasons.len(), 1);
        let bad_diag = stage
            .failed_reasons
            .get("item_017")
            .expect("item_017 must fail");
        assert!(
            bad_diag.contains("✖ [25/64] Building Mir.MiriDiffCorpus.item_017"),
            "stdout `✖` line in middle of log must be preserved: {bad_diag}"
        );
        assert!(
            bad_diag.contains("item_017.lean:12:4: type mismatch"),
            "stdout `error:` line in middle of log must be preserved: {bad_diag}"
        );
        assert!(
            bad_diag.contains("Lake build failed with 1 target error"),
            "stderr `error:` line must be preserved: {bad_diag}"
        );

        // 2. Systematic failure across 20 items (chunk_size = 8 -> 3 chunks) trips circuit
        //    breaker after `MIRI_FALLBACK_CIRCUIT_BREAKER` (4) consecutive fallback failures
        //    with 0 successes, then retries chunk 0's remainder once as a group; once that
        //    also fails, chunks 1 and 2 skip straight to the breaker diagnosis:
        //    total invocations = 3 chunks + 4 fallbacks + 1 remainder = 8 (not 3 + 20).
        let sys_items: Vec<(OracleItemSpec, String)> = (0..20)
            .map(|i| {
                let name = format!("sys_{i:02}");
                (OracleItemSpec::with_fuel(name.clone(), 200), name)
            })
            .collect();
        let calls = AtomicUsize::new(0);
        let sys_stage: IsolatedMiriStage<()> = run_isolated_miri_stage(
            "MiriOracleProbe",
            &sys_items,
            8,
            2,
            |(spec, _)| spec.name.as_str(),
            |_chunk_idx, _is_fallback, _label, _chunk| {
                calls.fetch_add(1, Ordering::SeqCst);
                Err(format_lean_command_failure(
                    "lake env lean failed",
                    "✖ broken toolchain",
                    "error: unknown package `Trusted`",
                ))
            },
        );
        assert_eq!(
            calls.load(Ordering::SeqCst),
            3 + MIRI_FALLBACK_CIRCUIT_BREAKER + 1,
            "expected 3 chunk runs + {MIRI_FALLBACK_CIRCUIT_BREAKER} fallback runs + 1 remainder \
             retry before the circuit breaker settles on a systematic failure"
        );
        assert!(sys_stage.results.is_empty());
        assert_eq!(sys_stage.failed_reasons.len(), 20);
        assert!(
            sys_stage
                .failed_reasons
                .get("sys_19")
                .is_some_and(|r| r.contains("consecutive fallback failures")
                    && r.contains("unknown package `Trusted`"))
        );
        assert!(
            sys_stage
                .failed_reasons
                .get("sys_04")
                .is_some_and(|r| r.contains("remainder retry `MiriOracleProbeRemainder_000` also failed")),
            "chunk 0's skipped items must record the failed remainder retry: {:?}",
            sys_stage.failed_reasons.get("sys_04")
        );

        // 3. Stale `MiriOracleProbe*` and `MiriOracleConfirm*` artifacts are cleaned without
        //    touching unrelated files.
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let tmp_oracle = env::temp_dir().join(format!(
            "anneal-miri-oracle-clean-{}-{nanos}",
            std::process::id()
        ));
        fs::create_dir_all(&tmp_oracle).unwrap();
        fs::write(tmp_oracle.join("MiriOracleProbe.lean"), "-- old").unwrap();
        fs::write(tmp_oracle.join("MiriOracleProbe_007.olean"), "old").unwrap();
        fs::write(tmp_oracle.join("MiriOracleConfirm_001.lean"), "-- old").unwrap();
        fs::write(tmp_oracle.join("KeepMe.txt"), "keep").unwrap();
        clean_oracle_files_with_prefixes(&tmp_oracle, &["MiriOracleProbe", "MiriOracleConfirm"]);
        assert!(!tmp_oracle.join("MiriOracleProbe.lean").exists());
        assert!(!tmp_oracle.join("MiriOracleProbe_007.olean").exists());
        assert!(!tmp_oracle.join("MiriOracleConfirm_001.lean").exists());
        assert!(tmp_oracle.join("KeepMe.txt").is_file());
        let _ = fs::remove_dir_all(&tmp_oracle);
    }

    #[test]
    fn isolated_miri_stage_remainder_retry_keeps_healthy_candidates_behind_leading_broken_ones() {
        let items: Vec<(OracleItemSpec, String)> = (0..20)
            .map(|i| {
                let name = format!("c_{i:02}");
                (OracleItemSpec::with_fuel(name.clone(), 1), name)
            })
            .collect();
        let run_with_broken = |broken: &'static [&'static str]| {
            let calls: std::sync::Mutex<Vec<(usize, MiriStageRunKind, usize)>> =
                std::sync::Mutex::new(Vec::new());
            let stage: IsolatedMiriStage<()> = run_isolated_miri_stage(
                "MiriMirBuild",
                &items,
                10,
                1,
                |(spec, _)| spec.name.as_str(),
                |chunk_idx, run_kind, _label, chunk| {
                    calls
                        .lock()
                        .unwrap()
                        .push((chunk_idx, run_kind, chunk.len()));
                    if let Some((bad, _)) =
                        chunk.iter().find(|(s, _)| broken.contains(&s.name.as_str()))
                    {
                        return Err(format!("error: Mir/{}.lean: unknown identifier", bad.name));
                    }
                    Ok(chunk.iter().map(|(s, _)| (s.name.clone(), ())).collect())
                },
            );
            (stage, calls.into_inner().unwrap())
        };

        // 1. A success before the broken candidates means the breaker never trips:
        //    2 chunk runs + 10 per-candidate fallbacks for chunk 0, no remainder retry.
        let (stage, calls) = run_with_broken(&["c_01", "c_02", "c_03", "c_04", "c_05", "c_06"]);
        assert_eq!(calls.len(), 2 + 10, "calls: {calls:?}");
        assert!(calls.iter().all(|&(_, kind, len)| {
            matches!(kind, MiriStageRunKind::Chunk { wave_jobs: 1 })
                || (kind == MiriStageRunKind::Fallback && len == 1)
        }));
        assert_eq!(stage.results.len(), 14);
        assert_eq!(
            stage.failed_reasons.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["c_01", "c_02", "c_03", "c_04", "c_05", "c_06"]
        );
        assert!(
            stage
                .failed_reasons
                .values()
                .all(|r| r.contains("unknown identifier") && !r.contains("fallback skipped"))
        );

        // 2. Four broken candidates leading chunk 0 trip the breaker, but the healthy
        //    remainder (c_04..c_09) is recovered by one group retry instead of being
        //    written off: 2 chunk runs + 4 fallbacks + 1 remainder run.
        let (stage, calls) = run_with_broken(&["c_00", "c_01", "c_02", "c_03"]);
        assert_eq!(
            calls,
            vec![
                (0, MiriStageRunKind::Chunk { wave_jobs: 1 }, 10),
                (1, MiriStageRunKind::Chunk { wave_jobs: 1 }, 10),
                (0, MiriStageRunKind::Fallback, 1),
                (0, MiriStageRunKind::Fallback, 1),
                (0, MiriStageRunKind::Fallback, 1),
                (0, MiriStageRunKind::Fallback, 1),
                (0, MiriStageRunKind::Remainder, 6),
            ]
        );
        assert_eq!(stage.results.len(), 16);
        assert_eq!(
            stage.failed_reasons.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["c_00", "c_01", "c_02", "c_03"]
        );

        // 3. A fifth broken candidate inside the remainder makes the retry fail too: the
        //    remainder is then written off with the breaker diagnosis (root cause kept).
        let (stage, calls) = run_with_broken(&["c_00", "c_01", "c_02", "c_03", "c_08"]);
        assert_eq!(calls.len(), 2 + 4 + 1, "calls: {calls:?}");
        assert_eq!(stage.results.len(), 10);
        let skipped = stage.failed_reasons.get("c_05").expect("c_05 must be written off");
        assert!(
            skipped.contains("per-candidate fallback skipped after 4 consecutive fallback failures")
                && skipped.contains("remainder retry `MiriMirBuildRemainder_000` also failed")
                && skipped.contains("Mir/c_00.lean: unknown identifier"),
            "unexpected breaker diagnosis: {skipped}"
        );
        assert!(
            stage
                .errors
                .iter()
                .any(|e| e.contains("skipped 6 per-candidate fallback run(s)")),
            "errors: {:?}",
            stage.errors
        );
    }

    #[test]
    fn miri_lake_build_threads_resolve_env_precedence_caps_and_caller_threads() {
        const GIB_KIB: u64 = 1024 * 1024;
        let threads = |base, mir_chunks| MiriLakeBuildThreads { base, mir_chunks };
        let (cg_total, roomy, tight) = (Some(19 * GIB_KIB), Some(15 * GIB_KIB), Some(2 * GIB_KIB));

        // Memory defaults: 15 GiB headroom in a 19 GiB cgroup on 8 cores -> 6 base
        // threads (1536 MiB / job, clamped to 6) and 4 for corpus `Mir.*` chunks;
        // 2 GiB headroom -> 1 thread everywhere.
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, None, None, cg_total, roomy, 8),
            threads(6, 4)
        );
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, None, None, cg_total, tight, 8),
            threads(1, 1)
        );
        // A caller's LEAN_NUM_THREADS lowers (never raises) the memory default;
        // invalid values are ignored.
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, None, Some("2"), cg_total, roomy, 8),
            threads(2, 2)
        );
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, None, Some("64"), cg_total, roomy, 8),
            threads(6, 4)
        );
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, None, Some("0"), cg_total, roomy, 8),
            threads(6, 4)
        );
        // CARGO_ANNEAL_LAKE_JOBS overrides the base budget (capped at 16) and the
        // caller's LEAN_NUM_THREADS; corpus chunk builds stay at most 4.
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, Some("32"), Some("1"), cg_total, tight, 8),
            threads(16, 4)
        );
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(None, Some(" 3 "), None, None, None, 8),
            threads(3, 3)
        );
        // ANNEAL_MIRI_LEAN_JOBS sets both budgets (capped at 8) and beats everything.
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(Some("12"), Some("2"), Some("1"), cg_total, tight, 8),
            threads(8, 8)
        );
        // Unknown memory with no overrides falls back to 2 threads.
        assert_eq!(
            resolve_miri_lake_build_threads_with_env(Some("bogus"), Some("0"), None, None, None, 8),
            threads(2, 2)
        );
    }

    #[test]
    fn stage0_build_plan_never_emits_the_mir_umbrella_and_chunks_overflowing_helpers() {
        let few: Vec<String> = vec![
            "MiriDiffCorpus.helper_add_ten".to_string(),
            "MiriDiffCorpus.helper_add_ten".to_string(),
            String::new(),
            "Common".to_string(),
            "MiriDiffCorpus.Wrapper_as_core_ops_Drop_drop".to_string(),
        ];
        assert_eq!(
            plan_miri_stage0_build_groups(true, &few),
            vec![vec![
                MIRI_SYMBOLIC_EVAL_MODULE.to_string(),
                "Mir.Common".to_string(),
                "Mir.MiriDiffCorpus.helper_add_ten".to_string(),
                "Mir.MiriDiffCorpus.Wrapper_as_core_ops_Drop_drop".to_string(),
            ]],
            "helpers are deduplicated, `Mir.Common` is not repeated, and an empty \
             suffix never yields a bare `Mir` / `Mir.` target"
        );
        assert_eq!(
            plan_miri_stage0_build_groups(false, &[]),
            vec![vec![MIRI_SYMBOLIC_EVAL_MODULE.to_string()]]
        );

        // Exactly MIRI_PROBE_CHUNK_SIZE helpers still share group 0 with the base targets.
        let many: Vec<String> = (0..150)
            .map(|i| format!("MiriDiffCorpus.cand_{i:03}__closure_0"))
            .collect();
        let exact = plan_miri_stage0_build_groups(false, &many[..MIRI_PROBE_CHUNK_SIZE]);
        assert_eq!(exact.len(), 1);
        assert_eq!(exact[0].len(), 1 + MIRI_PROBE_CHUNK_SIZE);

        // 150 helpers -> base group + 64 + 64 + 22, every target a concrete module.
        let plan = plan_miri_stage0_build_groups(true, &many);
        assert_eq!(
            plan.iter().map(Vec::len).collect::<Vec<_>>(),
            vec![2, 64, 64, 22]
        );
        assert!(
            plan.iter()
                .flatten()
                .all(|t| t == MIRI_SYMBOLIC_EVAL_MODULE || (t.starts_with("Mir.") && t.len() > 4)),
            "plan: {plan:?}"
        );
        assert_eq!(plan.iter().flatten().collect::<BTreeSet<_>>().len(), 152);
    }

    #[test]
    fn miri_candidate_build_targets_match_probe_imports_and_dedup() {
        let chunk = vec![
            (
                OracleItemSpec::with_fuel("cand_a".to_string(), 10),
                "MiriDiffCorpus.cand_a".to_string(),
            ),
            (OracleItemSpec::with_fuel("cand_b".to_string(), 10), String::new()),
            (
                OracleItemSpec::with_fuel("cand_a".to_string(), 10),
                "MiriDiffCorpus.cand_a".to_string(),
            ),
        ];
        let targets = miri_candidate_build_targets("MiriDiffCorpus", &chunk);
        assert_eq!(
            targets,
            vec![
                "Mir.MiriDiffCorpus.cand_a".to_string(),
                "Mir.MiriDiffCorpus.cand_b".to_string()
            ]
        );
        // Every Stage 1a target is a module the chunk's probe imports (so the probe
        // never needs an unbuilt `.olean`).
        let probe = render_linked_anneal_probe_module("MiriDiffCorpus", &chunk, &[]);
        for target in &targets {
            assert!(
                probe.contains(&format!("import {target}\n")),
                "probe must import {target}:\n{probe}"
            );
        }
    }

    #[test]
    fn chunked_miri_probe_stage_fallback_recovers_frames_and_isolates_the_failing_candidate() {
        let items: Vec<(OracleItemSpec, String)> = (0..70)
            .map(|i| {
                let name = format!("cand_{i:03}");
                (
                    OracleItemSpec::with_fuel(name.clone(), 400),
                    format!("MiriDiffCorpus.{name}"),
                )
            })
            .collect();
        let probe_line = |name: &str| -> String {
            if name == "cand_005" || name == "cand_066" {
                format!(
                    "ANNEAL_PROBE\t{name}\tpanic\tsrc/lib.rs:5:5:5:20\n\
                     ANNEAL_PANIC_FRAME\t{name}\tmiri_diff_corpus::{name}\n\
                     ANNEAL_PANIC_MESSAGE\t{name}\t[111, 104]\n"
                )
            } else {
                format!("ANNEAL_PROBE\t{name}\tpass:scalar:7:4\tnone\n")
            }
        };
        let calls: std::sync::Mutex<Vec<(usize, MiriStageRunKind, usize)>> =
            std::sync::Mutex::new(Vec::new());
        let mut outcomes = BTreeMap::new();
        let mut frames = BTreeMap::new();
        let mut messages = BTreeMap::new();

        let errors = aggregate_miri_probe_stage(
            &items,
            MIRI_PROBE_CHUNK_SIZE,
            2,
            |chunk_idx, run_kind, _label, chunk| {
                calls
                    .lock()
                    .unwrap()
                    .push((chunk_idx, run_kind, chunk.len()));
                if chunk.iter().any(|(s, _)| s.name == "cand_010") {
                    // Lean prints every other probe line, then exits non-zero on cand_010.
                    let mut stdout: String = chunk
                        .iter()
                        .filter(|(s, _)| s.name != "cand_010")
                        .map(|(s, _)| probe_line(&s.name))
                        .collect();
                    stdout.push_str(
                        "oracle/MiriOracleProbe_000.lean:42:0: error: (interpreter) unknown \
                         declaration 'Mir.MiriDiffCorpus.cand_010.body'\n",
                    );
                    return Err(format_lean_command_failure(
                        "Lean probe evaluation failed (exit status: 1)",
                        &stdout,
                        "error: Lean exited with code 1",
                    ));
                }
                Ok(chunk.iter().map(|(s, _)| probe_line(&s.name)).collect())
            },
            &mut outcomes,
            &mut frames,
            &mut messages,
        );

        let calls = calls.into_inner().unwrap();
        assert_eq!(calls.len(), 2 + MIRI_PROBE_CHUNK_SIZE, "calls: {calls:?}");
        assert_eq!(
            calls
                .iter()
                .filter(|&&(idx, kind, len)| {
                    idx == 0 && kind == MiriStageRunKind::Fallback && len == 1
                })
                .count(),
            MIRI_PROBE_CHUNK_SIZE,
            "only the failed chunk 0 falls back, one candidate at a time"
        );
        assert_eq!(outcomes.len(), 70);
        // Panic frames / messages survive both the fallback path (cand_005) and the
        // healthy chunk path (cand_066).
        for name in ["cand_005", "cand_066"] {
            assert!(matches!(outcomes.get(name), Some(AnnealOutcome::Panic { .. })));
            assert_eq!(
                frames.get(name).map(String::as_str),
                Some(format!("miri_diff_corpus::{name}").as_str())
            );
            assert_eq!(messages.get(name).map(Vec::as_slice), Some(&b"oh"[..]));
        }
        assert_eq!(frames.len(), 2);
        assert_eq!(messages.len(), 2);
        assert_eq!(
            outcomes.get("cand_011"),
            Some(&AnnealOutcome::PassScalar {
                bits: 7,
                size_bytes: 4
            })
        );
        match outcomes.get("cand_010") {
            Some(AnnealOutcome::CaptureOrLeanError(msg)) => {
                for needle in [
                    "MiriOracleProbeFallback_cand_010:",
                    "unknown declaration 'Mir.MiriDiffCorpus.cand_010.body'",
                    "error: Lean exited with code 1",
                ] {
                    assert!(msg.contains(needle), "missing `{needle}` in: {msg}");
                }
            }
            other => panic!("expected CaptureOrLeanError for cand_010, got {other:?}"),
        }
        assert_eq!(errors.len(), 2, "chunk + fallback diagnostics: {errors:?}");
        assert!(errors[0].starts_with("MiriOracleProbe_000:"));
        assert!(errors[1].starts_with("MiriOracleProbeFallback_cand_010:"));
    }

    #[test]
    fn chunked_miri_confirm_stage_bounds_modules_isolates_resource_exhaustion_and_fails_closed() {
        let entry = |name: &str| -> MiriConfirmEntry {
            (
                OracleItemSpec::with_fuel(name.to_string(), 100),
                format!("MiriDiffCorpus.{name}"),
                AnnealOutcome::PassScalar {
                    bits: 1,
                    size_bytes: 4,
                },
            )
        };
        let ok = || LeanConfirmRun {
            success: true,
            signal_terminated: false,
            status: "exit status: 0".to_string(),
            stdout: String::new(),
            stderr: String::new(),
        };
        let to_confirm: Vec<MiriConfirmEntry> =
            (0..40).map(|i| entry(&format!("div_{i:02}"))).collect();
        let written: std::sync::Mutex<BTreeMap<String, Vec<String>>> =
            std::sync::Mutex::new(BTreeMap::new());
        let ran: std::sync::Mutex<Vec<(String, usize)>> = std::sync::Mutex::new(Vec::new());

        let stage = run_chunked_miri_confirm_stage(
            &to_confirm,
            MIRI_CONFIRM_CHUNK_SIZE,
            2,
            |file_name, entries| {
                written.lock().unwrap().insert(
                    file_name.to_string(),
                    entries.iter().map(|e| e.0.name.clone()).collect(),
                );
                Ok(())
            },
            |file_name, active_workers| {
                ran.lock().unwrap().push((file_name.to_string(), active_workers));
                let names = written
                    .lock()
                    .unwrap()
                    .get(file_name)
                    .cloned()
                    .unwrap_or_default();
                if names.iter().any(|n| n == "div_20") {
                    // The chunk (and div_20 alone) exhausts Lean's heartbeat budget.
                    return Ok(LeanConfirmRun {
                        success: false,
                        signal_terminated: false,
                        status: "exit status: 1".to_string(),
                        stdout: "oracle/MiriOracleConfirm_001.lean:9:0: error: (deterministic) \
                                 timeout at `whnf`, maximum number of heartbeats (2000000) has \
                                 been reached"
                            .to_string(),
                        stderr: String::new(),
                    });
                }
                if names.len() > 1 && names.iter().any(|n| n == "div_33") {
                    // The 8-entry chunk is OOM-killed; each entry alone fits.
                    return Ok(LeanConfirmRun {
                        success: false,
                        signal_terminated: true,
                        status: "signal: 9 (SIGKILL)".to_string(),
                        stdout: String::new(),
                        stderr: String::new(),
                    });
                }
                Ok(ok())
            },
        )
        .expect("resource exhaustion must downgrade, not fail, the stage");

        let written = written.into_inner().unwrap();
        let chunk_modules: Vec<(&String, usize)> = written
            .iter()
            .filter(|(f, _)| f.starts_with("MiriOracleConfirm_"))
            .map(|(f, names)| (f, names.len()))
            .collect();
        assert_eq!(
            chunk_modules,
            vec![
                (&"MiriOracleConfirm_000.lean".to_string(), 16),
                (&"MiriOracleConfirm_001.lean".to_string(), 16),
                (&"MiriOracleConfirm_002.lean".to_string(), 8),
            ],
            "no Lean confirm process may hold more than MIRI_CONFIRM_CHUNK_SIZE theorems"
        );
        let fallback_modules: Vec<&Vec<String>> = written
            .iter()
            .filter(|(f, _)| f.starts_with("MiriOracleConfirmFallback_"))
            .map(|(_, names)| names)
            .collect();
        assert_eq!(fallback_modules.len(), 16 + 8);
        assert!(fallback_modules.iter().all(|names| names.len() == 1));
        let ran = ran.into_inner().unwrap();
        assert_eq!(ran.len(), 3 + 16 + 8);
        // Wave 0 runs 2 chunks concurrently (`active_workers == 2`); wave 1 has a
        // single trailing chunk (`active_workers == 1`); every per-entry fallback runs
        // serially (`active_workers == 1`) so it receives the full 1-worker RSS budget.
        for (mod_name, active_workers) in &ran {
            if mod_name == "MiriOracleConfirm_000.lean"
                || mod_name == "MiriOracleConfirm_001.lean"
            {
                assert_eq!(*active_workers, 2, "{mod_name} ran in a 2-worker wave");
            } else {
                assert_eq!(*active_workers, 1, "{mod_name} ran alone and must get 1-worker RSS budget");
            }
        }
        // A partial 3-chunk wave under `jobs = 4` passes `active_workers = 3` (never 4).
        let partial_workers: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());
        run_chunked_miri_confirm_stage(
            &to_confirm,
            MIRI_CONFIRM_CHUNK_SIZE,
            4,
            |_f, _e| Ok(()),
            |_f, active_workers| {
                partial_workers.lock().unwrap().push(active_workers);
                Ok(ok())
            },
        )
        .expect("3-chunk wave on 4-job budget");
        assert_eq!(partial_workers.into_inner().unwrap(), vec![3, 3, 3]);
        assert_eq!(
            stage.unconfirmed.keys().map(String::as_str).collect::<Vec<_>>(),
            vec!["div_20"]
        );
        // The downgrade carries its reason (module, status, and highlighted diagnostic).
        let reason = &stage.unconfirmed["div_20"];
        assert!(
            reason.starts_with("oracle/MiriOracleConfirmFallback_div_20.lean (exit status: 1): ")
                && reason.contains("maximum number of heartbeats"),
            "{reason}"
        );
        let confirmed: Vec<&str> = stage.confirmed.iter().map(|e| e.0.name.as_str()).collect();
        let expected: Vec<String> = (0..40)
            .filter(|&i| i != 20)
            .map(|i| format!("div_{i:02}"))
            .collect();
        assert_eq!(confirmed, expected.iter().map(String::as_str).collect::<Vec<_>>());

        // A kernel rejection (no resource marker) fails the stage closed, naming the
        // rejecting module and preserving the middle-of-log `error:` plus stderr.
        let rejection = run_chunked_miri_confirm_stage(
            &to_confirm[..3],
            MIRI_CONFIRM_CHUNK_SIZE,
            1,
            |_file_name, _entries| Ok(()),
            |file_name, _is_serial| {
                if file_name.starts_with("MiriOracleConfirm_") || file_name.contains("div_01") {
                    let mut stdout: String = (0..30)
                        .map(|k| format!("info: elaborating theorem {k}\n"))
                        .collect();
                    stdout.push_str(
                        "oracle/MiriOracleConfirm_000.lean:12:2: error: The rfl tactic failed \
                         for div_01\n",
                    );
                    stdout.extend((30..60).map(|k| format!("info: trailing {k}\n")));
                    return Ok(LeanConfirmRun {
                        success: false,
                        signal_terminated: false,
                        status: "exit status: 1".to_string(),
                        stdout,
                        stderr: "error: Lean exited with code 1".to_string(),
                    });
                }
                Ok(ok())
            },
        )
        .expect_err("a kernel rejection must fail the stage closed");
        for needle in [
            "Lean kernel confirmation rejected `div_01` in oracle/MiriOracleConfirmFallback_div_01.lean",
            "error: The rfl tactic failed for div_01",
            "error: Lean exited with code 1",
        ] {
            assert!(rejection.contains(needle), "missing `{needle}` in: {rejection}");
        }

        // A spawn failure propagates.
        let spawn_err = run_chunked_miri_confirm_stage(
            &to_confirm[..2],
            MIRI_CONFIRM_CHUNK_SIZE,
            1,
            |_file_name, _entries| Ok(()),
            |_file_name, _is_serial| Err("failed to execute 'lake env lean'".to_string()),
        )
        .expect_err("spawn failures must propagate");
        assert!(spawn_err.contains("failed to execute"));
    }

    #[test]
    fn format_lean_command_failure_surfaces_stdout_stderr_middle_errors_and_rustc_codes() {
        assert_eq!(
            format_lean_command_failure("lake build failed with status exit status: 1", "", "  \n"),
            "lake build failed with status exit status: 1\nstdout:\n(empty)\nstderr:\n(empty)"
        );

        let stdout: String = (0..30)
            .map(|k| format!("✔ [{k}/90] Built Mir.Ok_{k}\n"))
            .chain([
                "✖ [31/90] Building Mir.MiriDiffCorpus.cand_031\n".to_string(),
                "error: .anneal/generated/Mir/MiriDiffCorpus/cand_031.lean:3:2: unknown \
                 identifier\n"
                    .to_string(),
            ])
            .chain((32..90).map(|k| format!("✔ [{k}/90] Built Mir.Ok_{k}\n")))
            .collect();
        let stderr = "error[E0308]: mismatched types\n  --> src/lib.rs:4:5\nerror: Lake build failed";
        let msg = format_lean_command_failure("lake build failed", &stdout, stderr);
        let (head, rest) = msg.split_once("\nstdout:\n").expect("stdout section");
        assert!(head.starts_with("lake build failed\nerror_lines:\n"), "{head}");
        for needle in [
            "✖ [31/90] Building Mir.MiriDiffCorpus.cand_031",
            "cand_031.lean:3:2: unknown identifier",
            "error[E0308]: mismatched types",
            "error: Lake build failed",
        ] {
            assert!(head.contains(needle), "error_lines must contain `{needle}`: {head}");
        }
        let (stdout_part, stderr_part) = rest.split_once("\nstderr:\n").expect("stderr section");
        assert!(stdout_part.contains("lines elided; key error lines preserved below"));
        assert!(stdout_part.contains("✖ [31/90] Building Mir.MiriDiffCorpus.cand_031"));
        assert!(stdout_part.contains("✔ [0/90] Built Mir.Ok_0"));
        assert!(stdout_part.contains("✔ [89/90] Built Mir.Ok_89"));
        assert!(!stdout_part.contains("Built Mir.Ok_50\n"));
        assert_eq!(stderr_part, stderr);
        assert_eq!(
            extract_lean_error_lines("", stderr, 30),
            vec![
                "error[E0308]: mismatched types".to_string(),
                "error: Lake build failed".to_string()
            ]
        );

        // Ordinary Rust identifiers like `my_error[end]` must NOT false-match
        // `error[...]:`, while non-E bracketed diagnostics and fatal OOM / panic
        // crash lines without `error:` ARE highlighted.
        let mixed = "let x = my_error[end];\n\
                     error[internal]: compiler ICE\n\
                     out of memory\n\
                     PANIC at Lean.Kernel.whnf\n\
                     thread 'main' panicked at src/main.rs:1:1: boom\n";
        assert_eq!(
            extract_lean_error_lines(mixed, "", 30),
            vec![
                "error[internal]: compiler ICE".to_string(),
                "out of memory".to_string(),
                "PANIC at Lean.Kernel.whnf".to_string(),
                "thread 'main' panicked at src/main.rs:1:1: boom".to_string(),
            ]
        );
    }

    #[test]
    fn multi_group_confirm_module_and_probe_remainder_filenames_preserve_per_group_isolation() {
        // 1. Probe module naming distinguishes Chunk, Fallback, and Remainder so a
        //    multi-item Remainder slice never overwrites or blames the first item's
        //    single-candidate Fallback file.
        let sample_chunk = vec![
            (
                OracleItemSpec::with_fuel("cand_04".to_string(), 100),
                "X.cand_04".to_string(),
            ),
            (
                OracleItemSpec::with_fuel("cand_05".to_string(), 100),
                "X.cand_05".to_string(),
            ),
        ];
        assert_eq!(
            miri_probe_module_file_name(0, MiriStageRunKind::Chunk { wave_jobs: 1 }, &sample_chunk),
            "MiriOracleProbe_000.lean"
        );
        assert_eq!(
            miri_probe_module_file_name(0, MiriStageRunKind::Remainder, &sample_chunk),
            "MiriOracleProbeRemainder_000.lean"
        );
        assert_eq!(
            miri_probe_module_file_name(0, MiriStageRunKind::Fallback, &sample_chunk[..1]),
            "MiriOracleProbeFallback_cand_04.lean"
        );

        // 2. Multi-group `MiriOracleConfirm.lean` isolates each confirmed group's
        //    `linkedCallees` in its own namespace so `extract_confirm_theorems`
        //    returns the exact kernel-checked `linkedCallees` for each candidate
        //    without leaking another chunk's closures or `Drop` impls.
        let g0_entry: MiriConfirmEntry = (
            OracleItemSpec::with_fuel("cand_top".to_string(), 200),
            "X.cand_top".to_string(),
            AnnealOutcome::PassScalar {
                bits: 1,
                size_bytes: 4,
            },
        );
        let g1_entry: MiriConfirmEntry = (
            OracleItemSpec::with_fuel("cand_shadow".to_string(), 200),
            "X.cand_shadow".to_string(),
            AnnealOutcome::Panic { span: None },
        );
        let mut frames = BTreeMap::new();
        frames.insert("cand_shadow".to_string(), "x::cand_shadow".to_string());
        let mut messages = BTreeMap::new();
        messages.insert("cand_shadow".to_string(), b"msg".to_vec());

        let groups = vec![
            (
                vec![g0_entry],
                vec!["X.cand_top__closure_0".to_string(), "X.helper_leaf".to_string()],
            ),
            (
                vec![g1_entry],
                vec![
                    "X.Guard_as_core_ops_Drop_drop".to_string(),
                    "X.cand_shadow__closure_0".to_string(),
                ],
            ),
        ];
        let multi_src =
            render_multi_group_anneal_confirm_module("X", &groups, &frames, &messages).unwrap();
        assert!(multi_src.contains("namespace MiriOracleConfirm_000\n"));
        assert!(multi_src.contains("namespace MiriOracleConfirm_001\n"));

        let top_snippet = extract_confirm_theorems(&multi_src, "cand_top");
        assert!(top_snippet.contains("Mir.X.cand_top__closure_0.body"));
        assert!(top_snippet.contains("Mir.X.helper_leaf.body"));
        assert!(
            !top_snippet.contains("Guard_as_core_ops_Drop_drop"),
            "group 1's Drop impl must not contaminate group 0's extracted theorem:\n{top_snippet}"
        );
        assert!(
            !top_snippet.contains("cand_shadow__closure_0"),
            "group 1's closure must not contaminate group 0's extracted theorem:\n{top_snippet}"
        );
        assert!(top_snippet.contains("theorem confirm_tag_cand_top :"));
        assert!(!top_snippet.contains("theorem confirm_tag_cand_shadow :"));

        let shadow_snippet = extract_confirm_theorems(&multi_src, "cand_shadow");
        assert!(shadow_snippet.contains("Mir.X.Guard_as_core_ops_Drop_drop.body"));
        assert!(shadow_snippet.contains("Mir.X.cand_shadow__closure_0.body"));
        assert!(
            !shadow_snippet.contains("cand_top__closure_0"),
            "group 0's closure must not contaminate group 1's extracted theorem:\n{shadow_snippet}"
        );
        assert!(shadow_snippet.contains("theorem confirm_frame_cand_shadow :"));
        assert!(shadow_snippet.contains("theorem confirm_message_cand_shadow :"));
    }

    #[test]
    fn miri_lean_rss_budget_bounds_stage_cap_by_worker_headroom_share() {
        const GIB_KIB: u64 = 1024 * 1024;
        // The stage cap binds when headroom is ample.
        assert_eq!(
            miri_lean_rss_budget_kib(CONFIRM_LEAN_RSS_BUDGET_MIB, None, 1, Some(15 * GIB_KIB)),
            4 * GIB_KIB
        );
        assert_eq!(
            miri_lean_rss_budget_kib(PROBE_LEAN_RSS_BUDGET_MIB, None, 1, None),
            8 * GIB_KIB,
            "unknown headroom keeps the stage cap"
        );
        // 85% of each worker's share of the headroom binds when tighter.
        assert_eq!(
            miri_lean_rss_budget_kib(4096, None, 2, Some(6 * GIB_KIB)),
            6 * GIB_KIB / 2 / 100 * 85
        );
        // `ANNEAL_MIRI_LEAN_MAX_RSS_MIB` replaces the cap but stays headroom-bounded;
        // invalid values are ignored; the budget never drops below 512 MiB.
        assert_eq!(
            miri_lean_rss_budget_kib(4096, Some("12288"), 1, Some(64 * GIB_KIB)),
            12 * GIB_KIB
        );
        assert_eq!(
            miri_lean_rss_budget_kib(4096, Some("12288"), 1, Some(8 * GIB_KIB)),
            8 * GIB_KIB / 100 * 85
        );
        assert_eq!(
            miri_lean_rss_budget_kib(4096, Some("0"), 1, None),
            4 * GIB_KIB
        );
        assert_eq!(
            miri_lean_rss_budget_kib(4096, None, 4, Some(GIB_KIB)),
            512 * 1024
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn rss_budget_watchdog_captures_output_kills_process_trees_and_classifies_exhaustion() {
        use std::io::{BufRead, BufReader};
        use std::time::Duration;

        let pgrp_of_stat = |stat: &str| -> Option<u32> {
            stat.rfind(')')
                .and_then(|i| stat[i + 1..].split_whitespace().nth(2)?.parse().ok())
        };
        let harness_pgrp = fs::read_to_string(format!("/proc/{}/stat", std::process::id()))
            .ok()
            .and_then(|s| pgrp_of_stat(&s))
            .expect("harness pgrp");

        // 0. The budgeted run stays in the harness's process group, so Ctrl-C, a
        //    scheduler's `kill -- -pgid`, or `anneal-lean-run`'s session kill still
        //    reach `lake` / `lean` if the harness itself is interrupted.
        let mut pg_cmd = Command::new("sh");
        pg_cmd.arg("-c").arg("cat /proc/$$/stat");
        let pg = run_lean_with_rss_budget(&mut pg_cmd, Some(1 << 30)).expect("run sh");
        assert_eq!(
            pgrp_of_stat(&String::from_utf8_lossy(&pg.output.stdout)),
            Some(harness_pgrp),
            "budgeted runs must not leave the harness's process group"
        );

        // 1. Under budget: behaves like `Command::output`.
        let mut ok_cmd = Command::new("sh");
        ok_cmd
            .arg("-c")
            .arg("echo out-line; echo err-line >&2; exit 3");
        let ok = run_lean_with_rss_budget(&mut ok_cmd, Some(1 << 30)).expect("run sh");
        assert_eq!(ok.budget_exceeded_kib, None);
        assert_eq!(ok.output.status.code(), Some(3));
        assert_eq!(String::from_utf8_lossy(&ok.output.stdout), "out-line\n");
        assert_eq!(String::from_utf8_lossy(&ok.output.stderr), "err-line\n");

        // 2. Over budget: the tree is SIGKILLed promptly instead of running to completion.
        let start = Instant::now();
        let mut hog_cmd = Command::new("sleep");
        hog_cmd.arg("60");
        let killed = run_lean_with_rss_budget(&mut hog_cmd, Some(1)).expect("run sleep");
        assert!(killed.budget_exceeded_kib.is_some_and(|kib| kib > 1));
        assert!(killed.output.status.code().is_none(), "must be signal-terminated");
        assert!(start.elapsed() < Duration::from_secs(20));
        // ...and classifies as resource exhaustion, never as a kernel rejection.
        let confirm = LeanConfirmRun::from_budgeted_output(&killed, 4 * 1024 * 1024);
        assert!(!confirm.success && confirm.signal_terminated);
        assert!(
            confirm.stderr.contains("out of memory guard")
                && confirm.stderr.contains("exceeded the 4096 MiB budget"),
            "{}",
            confirm.stderr
        );
        assert!(lean_confirm_failure_is_resource_exhaustion(
            confirm.signal_terminated,
            &confirm.stderr
        ));

        // 3. `lake env lean` runs `lean` as a grandchild: the tree walk sees it and the
        //    kill reaches it (killing only the direct child would orphan the hog).
        let proc_state = |pid: u32| -> Option<char> {
            fs::read_to_string(format!("/proc/{pid}/stat"))
                .ok()
                .and_then(|s| s.rfind(')').and_then(|i| s[i + 1..].trim_start().chars().next()))
        };
        let wait_dead = |pid: u32, what: &str| {
            let deadline = Instant::now() + Duration::from_secs(5);
            loop {
                match proc_state(pid) {
                    None | Some('Z') | Some('X') => break,
                    Some(_) if Instant::now() < deadline => {
                        std::thread::sleep(Duration::from_millis(50))
                    }
                    Some(s) => panic!("{what} {pid} survived the tree kill (state {s})"),
                }
            }
        };
        let mut parent = Command::new("sh")
            .arg("-c")
            .arg("sleep 60 & echo $!; wait")
            .stdout(Stdio::piped())
            .spawn()
            .expect("spawn sh");
        let mut line = String::new();
        BufReader::new(parent.stdout.take().expect("stdout"))
            .read_line(&mut line)
            .expect("read grandchild pid");
        let grandchild: u32 = line.trim().parse().expect("grandchild pid");
        let mut tree = TrackedProcessTree::new(parent.id());
        assert!(tree.live_pids(true).contains(&grandchild));
        assert!(tree.rss_kib().is_some_and(|kib| kib > 0));
        tree.kill_all(&mut parent);
        assert!(parent.wait().expect("wait sh").code().is_none());
        wait_dead(grandchild, "grandchild");

        // 4. Without a dedicated process group, a descendant reparented after its
        //    intermediate parent exits stays tracked by pid + starttime: its RSS
        //    still counts and the kill still reaches it.
        let pid_file = env::temp_dir().join(format!(
            "anneal-miri-orphan-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let mut parent = Command::new("sh")
            .arg("-c")
            .arg(format!(
                "(sleep 60 </dev/null >/dev/null 2>&1 & echo $! > '{}'; sleep 1); sleep 60",
                pid_file.display()
            ))
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn orphaning sh");
        let mut tree = TrackedProcessTree::new(parent.id());
        let deadline = Instant::now() + Duration::from_secs(5);
        let orphan: u32 = loop {
            tree.live_pids(true);
            if let Some(pid) = fs::read_to_string(&pid_file)
                .ok()
                .and_then(|raw| raw.trim().parse::<u32>().ok())
                && tree.live_pids(true).contains(&pid)
            {
                break pid;
            }
            assert!(Instant::now() < deadline, "orphan-to-be never observed");
            std::thread::sleep(Duration::from_millis(50));
        };
        // Wait for the subshell to exit, reparenting `orphan` away from `parent`.
        let deadline = Instant::now() + Duration::from_secs(5);
        while process_tree_snapshot(parent.id())
            .iter()
            .any(|&(pid, _)| pid == orphan)
        {
            assert!(Instant::now() < deadline, "subshell never exited");
            std::thread::sleep(Duration::from_millis(50));
        }
        assert!(
            tree.live_pids(true).contains(&orphan),
            "a reparented descendant must stay tracked"
        );
        tree.kill_all(&mut parent);
        let _ = parent.wait();
        wait_dead(orphan, "reparented descendant");
        let _ = fs::remove_file(&pid_file);

        // 4b. PID-wraparound kill order: when Linux wraps PIDs past `pid_max`, a
        //     newer grandchild (`lean`, pid 1420) has a numerically smaller PID
        //     than an older intermediate parent (`lake`, pid 4_194_300), even
        //     within the same 10ms `starttime` tick. Ordering by `(starttime, seq)`
        //     still kills the leaf child before its parent.
        let mut wrapped = TrackedProcessTree::new(4_194_299);
        wrapped.record_process(4_194_299, 50_000);
        wrapped.record_process(4_194_300, 50_000); // intermediate parent
        wrapped.record_process(1_420, 50_000); // wrapped leaf child in same tick
        wrapped.record_process(900, 50_001); // even newer grandchild in next tick
        assert_eq!(
            wrapped.tracked_descendant_order_snapshot(),
            vec![900, 1_420, 4_194_300],
            "leaf descendants must die before older parents even across PID wraparound"
        );

        // 5. A clean exit observed after an over-budget sample stays a success.
        use std::os::unix::process::ExitStatusExt;
        let raced_ok = BudgetedOutput {
            output: std::process::Output {
                status: std::process::ExitStatus::from_raw(0),
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
            budget_exceeded_kib: Some(5 * 1024 * 1024),
        };
        let confirm_ok = LeanConfirmRun::from_budgeted_output(&raced_ok, 4 * 1024 * 1024);
        assert!(confirm_ok.success && !confirm_ok.signal_terminated);
        assert!(!confirm_ok.stderr.contains("out of memory guard"));
    }

    #[test]
    fn unexplained_kernel_rejections_fail_stage2_closed_even_when_killed_or_exhausted() {
        let killed_note = rss_budget_kill_note(4 * 1024 * 1024, 4200 * 1024);
        // Exact Lean v4.34.1 `:= by rfl` rejection (`Tactic \`rfl\` failed: ...`).
        let lean_v434_tactic_rfl_rejection = "oracle/MiriOracleConfirm_000.lean:12:2: error: \
             Tactic `rfl` failed: The left-hand side\n  1\nis not definitionally equal to the \
             right-hand side\n  2\n\n⊢ 1 = 2\n";
        assert!(lean_output_has_unexplained_kernel_rejection(
            lean_v434_tactic_rfl_rejection,
            &killed_note
        ));
        // Exact Lean v4.34.1 term-mode `rfl` rejection (`Not a definitional equality`)
        // and legacy Lean 4 `The rfl tactic failed` wording.
        assert!(lean_output_has_unexplained_kernel_rejection(
            "oracle/MiriOracleConfirm_000.lean:12:0: error: Not a definitional equality: \
             the left-hand side\n  1\nis not definitionally equal to the right-hand side\n  2\n",
            &killed_note
        ));
        assert!(lean_output_has_unexplained_kernel_rejection(
            "oracle/MiriOracleConfirm_000.lean:12:2: error: The rfl tactic failed. Possible \
             reasons:\n  the left-hand side and right-hand side are not definitionally equal\n",
            &killed_note
        ));
        // Cross-stream isolation: a headerless C++ runtime OOM line on `stderr`
        // (`LEAN PANIC: out of memory`) or a runtime crash line after an `error:`
        // block must NEVER merge into the preceding `stdout` `rfl` error block and
        // mask a kernel rejection.
        assert!(lean_output_has_unexplained_kernel_rejection(
            lean_v434_tactic_rfl_rejection,
            "LEAN PANIC: out of memory\n"
        ));
        assert!(lean_output_has_unexplained_kernel_rejection(
            &format!("{lean_v434_tactic_rfl_rejection}LEAN PANIC: out of memory\n"),
            ""
        ));
        // Exact Lean v4.34.1 `-M` cap error (`(kernel) excessive memory consumption detected`
        // and elaborator `excessive memory consumption detected at ...`) is classified as
        // resource exhaustion (`exit 1`, `signal_terminated = false`), never as a rejection.
        let lean_v434_minus_m_err =
            "oracle/MiriOracleConfirmFallback_y.lean:1:4: error: (kernel) excessive memory \
             consumption detected\n";
        assert!(!lean_output_has_unexplained_kernel_rejection(
            lean_v434_minus_m_err,
            ""
        ));
        assert!(lean_confirm_failure_is_resource_exhaustion(
            false,
            lean_v434_minus_m_err
        ));
        // A typeclass search that ran out of heartbeats or `-M` memory reports
        // `failed to synthesize` together with the resource diagnostic in one block:
        // exhaustion, not rejection.
        assert!(!lean_output_has_unexplained_kernel_rejection(
            "x.lean:3:0: error: failed to synthesize\n  Decidable p\n(deterministic) timeout at \
             `typeclass`, maximum number of heartbeats (20000) has been reached\n",
            ""
        ));
        assert!(!lean_output_has_unexplained_kernel_rejection(
            "x.lean:3:0: error: failed to synthesize\n  Decidable p\nexcessive memory \
             consumption detected at `typeclass`\n",
            ""
        ));
        // The watchdog's own note and pure resource errors are not rejections, nor is a
        // marker that only appears in a warning.
        assert!(!lean_output_has_unexplained_kernel_rejection("", &killed_note));
        assert!(!lean_output_has_unexplained_kernel_rejection(
            "x.lean:1:0: error: (kernel) deep recursion detected\n",
            ""
        ));
        assert!(!lean_output_has_unexplained_kernel_rejection(
            "x.lean:1:0: warning: unused variable `type mismatch`\n",
            ""
        ));
        // One pure rejection block wins even when another block is exhaustion.
        assert!(lean_output_has_unexplained_kernel_rejection(
            "a.lean:1:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats \
             (2000000) has been reached\na.lean:9:2: error: type mismatch\n  rfl\n",
            ""
        ));

        // Stage level: a budget-killed (or OOM-killed) run that already printed a Lean v4.34.1
        // `Tactic \`rfl\` failed` rejection fails closed; a killed run or a `-M` exit(1) run
        // without an unexplained rejection is downgraded with its reason.
        let entry = |name: &str| -> MiriConfirmEntry {
            (
                OracleItemSpec::with_fuel(name.to_string(), 100),
                format!("MiriDiffCorpus.{name}"),
                AnnealOutcome::PassScalar {
                    bits: 1,
                    size_bytes: 4,
                },
            )
        };
        let killed_run = |stdout: &str| LeanConfirmRun {
            success: false,
            signal_terminated: true,
            status: "signal: 9 (SIGKILL)".to_string(),
            stdout: stdout.to_string(),
            stderr: killed_note.clone(),
        };
        let rejected = run_chunked_miri_confirm_stage(
            &[entry("div_a")],
            MIRI_CONFIRM_CHUNK_SIZE,
            1,
            |_file_name, _entries| Ok(()),
            |_file_name, _active_workers| Ok(killed_run(lean_v434_tactic_rfl_rejection)),
        )
        .expect_err("a printed Lean v4.34.1 `Tactic rfl failed` rejection must fail closed despite the kill");
        assert!(
            rejected.contains("Lean kernel confirmation rejected `div_a`")
                && rejected.contains("Tactic `rfl` failed"),
            "{rejected}"
        );
        let downgraded = run_chunked_miri_confirm_stage(
            &[entry("div_b"), entry("div_c")],
            1,
            1,
            |_file_name, _entries| Ok(()),
            |file_name, _active_workers| {
                if file_name.contains("000") {
                    Ok(killed_run(""))
                } else {
                    Ok(LeanConfirmRun {
                        success: false,
                        signal_terminated: false,
                        status: "exit status: 1".to_string(),
                        stdout: lean_v434_minus_m_err.to_string(),
                        stderr: String::new(),
                    })
                }
            },
        )
        .expect("RSS watchdog kill and `-M` excessive memory consumption without rejection both downgrade");
        assert!(downgraded.confirmed.is_empty());
        assert!(
            downgraded
                .unconfirmed
                .get("div_b")
                .is_some_and(|reason| reason.contains("out of memory guard")),
            "{:?}",
            downgraded.unconfirmed
        );
        assert!(
            downgraded
                .unconfirmed
                .get("div_c")
                .is_some_and(|reason| reason.contains("excessive memory consumption")),
            "{:?}",
            downgraded.unconfirmed
        );
    }

    /// Classification against verbatim Lean v4.34.1 diagnostics captured from
    /// this toolchain (`lean` on scratch files): a failing `:= by rfl`, a
    /// heartbeat timeout (whose `Note:` / `Hint:` continuation is separated by
    /// blank lines), and `-M` exhaustion while kernel-checking theorems over
    /// imported definitions (the shape of every `MiriOracleConfirm*` module).
    ///
    /// Not covered on purpose: when `-M` is exhausted while checking a
    /// definition in the *same* file, a dependent theorem then reports
    /// `(kernel) declaration type mismatch`, which classifies as a rejection
    /// (fail closed). Confirm modules only define small helpers ahead of their
    /// theorems (whole modules peak at 0.6-1.1 GiB, far below `-M 4096`), so
    /// that cascade cannot arise there.
    #[test]
    fn stage2_classification_matches_verbatim_lean_v4_34_1_diagnostics() {
        const RFL_REJECTION: &str = "rfl_fail.lean:2:2: error: Tactic `rfl` failed: The \
                                     left-hand side\n  1\nis not definitionally equal to the \
                                     right-hand side\n  2\n\n⊢ 1 = 2\n";
        const HEARTBEAT_TIMEOUT: &str = "hb.lean:6:19: error: (deterministic) timeout at \
                                         `isDefEq`, maximum number of heartbeats (1) has been \
                                         reached\n\nNote: Use `set_option maxHeartbeats <num>` \
                                         to set the limit.\n\nHint: Additional diagnostic \
                                         information may be available using the `set_option \
                                         diagnostics true` command.\n";
        const MINUS_M_EXHAUSTION: &str = "Use.lean:2:8: error: (kernel) excessive memory \
                                          consumption detected\nUse.lean:4:8: error: (kernel) \
                                          excessive memory consumption detected\nUse.lean:6:8: \
                                          error: (kernel) excessive memory consumption \
                                          detected\n";

        assert!(lean_output_has_unexplained_kernel_rejection(RFL_REJECTION, ""));
        for resource_only in [HEARTBEAT_TIMEOUT, MINUS_M_EXHAUSTION] {
            assert!(!lean_output_has_unexplained_kernel_rejection(resource_only, ""));
            assert!(lean_confirm_failure_is_resource_exhaustion(false, resource_only));
        }
        // One theorem timing out never hides another theorem's rejection.
        let mixed = format!("{HEARTBEAT_TIMEOUT}{RFL_REJECTION}");
        assert!(lean_output_has_unexplained_kernel_rejection(&mixed, ""));

        let entry = |name: &str| -> MiriConfirmEntry {
            (
                OracleItemSpec::with_fuel(name.to_string(), 100),
                format!("MiriDiffCorpus.{name}"),
                AnnealOutcome::PassScalar {
                    bits: 1,
                    size_bytes: 4,
                },
            )
        };
        let exit1 = |stdout: &str| LeanConfirmRun {
            success: false,
            signal_terminated: false,
            status: "exit status: 1".to_string(),
            stdout: stdout.to_string(),
            stderr: String::new(),
        };
        let stage_for = |stdout: String| {
            run_chunked_miri_confirm_stage(
                &[entry("div_v")],
                MIRI_CONFIRM_CHUNK_SIZE,
                1,
                |_file_name, _entries| Ok(()),
                move |_file_name, _active_workers| Ok(exit1(&stdout)),
            )
        };
        for resource_only in [HEARTBEAT_TIMEOUT, MINUS_M_EXHAUSTION] {
            let stage = stage_for(resource_only.to_string())
                .expect("verbatim exhaustion output must downgrade, not abort");
            assert!(stage.unconfirmed.contains_key("div_v"), "{resource_only}");
        }
        for rejecting in [RFL_REJECTION.to_string(), mixed] {
            let err = stage_for(rejecting).expect_err("a verbatim rfl rejection must fail closed");
            assert!(err.contains("Tactic `rfl` failed"), "{err}");
        }
    }
}
