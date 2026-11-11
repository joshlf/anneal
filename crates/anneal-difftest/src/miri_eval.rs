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

use cargo_anneal::{
    ANNEAL_CAPTURE_FILTER_ENV, AnnealOutcome, CaptureDriverConfig, ComparisonVerdict,
    DEFAULT_CAPTURE_RUSTFLAGS, DEFAULT_MIRI_FLAGS, DEFAULT_ORACLE_FUEL, DifftestOracleConfig,
    DifftestOracleReport, DivergenceKind, ItemOracleReport, MiriOracleConfig, MiriOutcome,
    MiriToolchain, NotComparedReason, OracleItemSpec, ScaffoldConfig, SourcePos, SourceSpan,
    aggregate_unit_manifests, build_lake_build_command, compare_miri_and_anneal,
    derive_item_module_suffix, discover_zero_arg_pub_fns, normalize_path_against,
    parse_anneal_probe_output, resolve_rustc_wrapper, run_miri_oracle,
    scaffold_workspace_with_config, source_files_match,
};

use crate::mutators_miri::{
    GeneratedMiriCandidate, MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE,
};

/// Step fuel bound used for `miri-difftest` candidates (2 × `DEFAULT_ORACLE_FUEL`
/// so multi-pass mutations on loop seeds do not prematurely exhaust step fuel).
pub const MIRI_DIFFTEST_CANDIDATE_FUEL: u32 = DEFAULT_ORACLE_FUEL * 2;

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
/// `evalCallTerminator` evaluates the caller's argument operands before it
/// pushes a linked callee frame, so the `&'static str` argument is still checked
/// for UB. The body then assigns the placeholder `()` to `_0` and returns:
/// `Terminator.return_` requires an initialized `_0`, and the caller's later
/// `move` of the result into `core::panicking::panic_fmt` requires an
/// initialized destination local. Anneal models `panic_fmt` as an unwinding
/// panic that never reads its argument, so the placeholder cannot change any
/// outcome on that path. A program that inspects the returned value itself
/// diverges from Miri visibly rather than agreeing by accident.
///
/// These stubs appear only in `MiriOracleProbe.lean` and
/// `MiriOracleConfirm.lean`, after every captured helper body, so a captured
/// body with the same `DefPath` would take precedence in `findCallee?`. They
/// never enter a `Verify` certificate. The block contains no blank line, so
/// finding bundles can copy it verbatim from `MiriOracleConfirm.lean`.
pub const FMT_ARGUMENTS_CTOR_STUB_LEAN: &str = "\
-- Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,\n\
-- linked only by `miri-difftest` oracle modules. The caller has already\n\
-- evaluated the `&'static str` argument; this body stores the placeholder `()`\n\
-- in `_0` and returns, so the caller can pass the result to\n\
-- `core::panicking::panic_fmt`, which Anneal models as an unwinding panic\n\
-- without reading its argument.\n\
open Trusted.Rustc.V2026_06_01.Layout in\n\
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=\n  \
  { defPath := defPath\n    \
    phase := MirPhaseTag.runtimePostCleanup\n    \
    role := ContractRole.model\n    \
    argCount := 1\n    \
    localDecls :=\n      \
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.tuple [], layoutIdx := 0 }, debugName := Option.none },\n       \
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 1 }, debugName := Option.none }]\n    \
    basicBlocks :=\n      \
      [{ statements :=\n           \
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }\n                \
                (Rvalue.use (Operand.constant { ty := { kind := RigidTy.tuple [], layoutIdx := 0 }, val := ConstValue.zeroSized })),\n              \
              span := \"<dummy>\" }]\n         \
         terminator := { kind := TerminatorKind.return_, span := \"<dummy>\" }\n         \
         isCleanup := false }]\n    \
    fnAbi :=\n      \
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]\n        \
        ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.arbitrary [] [], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.ignore }\n        \
        conv := CallConv.rust\n        \
        canUnwind := false }\n    \
    layouts :=\n      \
      { pointerBits := 64\n        \
        isLittleEndian := true\n        \
        entries :=\n          \
          [{ size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.arbitrary [] [], variants := VariantsShape.single 0, isUninhabited := false },\n           \
           { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }\n    \
    allocations := [] }\n";

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

/// Staged `src/lib.rs` text indexed by the line range of each top-level `fn`
/// item and the non-literal token start coordinates in the file, used by
/// [`compare_difftest_miri_and_anneal`] to decide whether Miri's panic position
/// is a panic-macro call site inside the evaluated function.
#[derive(Debug, Clone, Default)]
pub struct StagedLibSource {
    lines: Vec<String>,
    fn_lines: BTreeMap<String, (usize, usize)>,
    token_starts: BTreeSet<(usize, usize)>,
}

fn collect_non_literal_token_starts(
    stream: proc_macro2::TokenStream,
    out: &mut BTreeSet<(usize, usize)>,
) {
    for tt in stream {
        match tt {
            proc_macro2::TokenTree::Ident(id) => {
                let start = id.span().start();
                out.insert((start.line, start.column + 1));
            }
            proc_macro2::TokenTree::Punct(p) => {
                let start = p.span().start();
                out.insert((start.line, start.column + 1));
            }
            proc_macro2::TokenTree::Group(g) => {
                collect_non_literal_token_starts(g.stream(), out);
            }
            proc_macro2::TokenTree::Literal(_) => {}
        }
    }
}

impl StagedLibSource {
    /// Index `lib_rs`, recording the 1-based inclusive line range from each
    /// top-level `fn` keyword to its closing brace and the 1-based `(line, col)`
    /// start positions of all non-literal tokens.
    ///
    /// A source that fails to parse indexes no functions, so no panic site in
    /// it is reconciled.
    pub fn parse(lib_rs: &str) -> Self {
        let mut token_starts = BTreeSet::new();
        let fn_lines = match syn::parse_file(lib_rs) {
            Ok(file) => {
                if let Ok(ts) = lib_rs.parse::<proc_macro2::TokenStream>() {
                    collect_non_literal_token_starts(ts, &mut token_starts);
                }
                file.items
                    .iter()
                    .filter_map(|item| match item {
                        syn::Item::Fn(func) => Some((
                            func.sig.ident.to_string(),
                            (
                                func.sig.fn_token.span.start().line,
                                func.block.brace_token.span.close().end().line,
                            ),
                        )),
                        _ => None,
                    })
                    .collect()
            }
            Err(_) => BTreeMap::new(),
        };
        Self {
            lines: lib_rs.lines().map(str::to_string).collect(),
            fn_lines,
            token_starts,
        }
    }

    /// Return the 1-based inclusive line range of the top-level `fn` item
    /// `fn_name`, if indexed.
    pub fn fn_line_range(&self, fn_name: &str) -> Option<(usize, usize)> {
        self.fn_lines.get(fn_name).copied()
    }

    /// Return `true` when `pos` lies in the staged `src/lib.rs`, within the
    /// line range of `fn_name`, at a real non-literal token starting an
    /// invocation of one of [`STD_PANIC_MACRO_NAMES`].
    fn is_panic_macro_call_site(&self, fn_name: &str, pos: &SourcePos) -> bool {
        let file = pos.file.replace('\\', "/");
        if file.strip_prefix("./").unwrap_or(&file) != "src/lib.rs" {
            return false;
        }
        let Some((first, last)) = self.fn_line_range(fn_name) else {
            return false;
        };
        let (line, col) = (pos.line as usize, pos.col as usize);
        if line < first || line > last || col == 0 || !self.token_starts.contains(&(line, col)) {
            return false;
        }
        let Some(text) = self.lines.get(line - 1) else {
            return false;
        };
        // Miri reports 1-based columns counted in characters.
        let invocation: String = text.chars().skip(col - 1).collect();
        starts_with_std_panic_macro_invocation(&invocation)
    }
}

/// Return `true` when `text` begins with an invocation of one of
/// [`STD_PANIC_MACRO_NAMES`], written bare (`assert!(...)`) or through
/// `core::` / `std::` (optionally rooted with `::`), followed by `!` and an
/// opening macro delimiter (`(`, `[`, or `{`).
fn starts_with_std_panic_macro_invocation(text: &str) -> bool {
    let mut rest = text;
    let rooted = rest.starts_with("::");
    if rooted {
        rest = &rest[2..];
    }
    let mut crate_qualified = false;
    for krate in ["core::", "std::"] {
        if let Some(after) = rest.strip_prefix(krate) {
            rest = after;
            crate_qualified = true;
            break;
        }
    }
    if rooted && !crate_qualified {
        return false;
    }
    let name_len = rest
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(rest.len());
    let (name, after_name) = rest.split_at(name_len);
    if !STD_PANIC_MACRO_NAMES.contains(&name) {
        return false;
    }
    let Some(after_bang) = after_name.trim_start().strip_prefix('!') else {
        return false;
    };
    matches!(
        after_bang.trim_start().chars().next(),
        Some('(' | '[' | '{')
    )
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
///    range of `fn_name`, at an invocation of `panic!`, `assert!`,
///    `assert_eq!`, `assert_ne!`, `debug_assert!`, `unreachable!`, `todo!`,
///    or `unimplemented!` (bare or through `core::` / `std::`).
///
/// Every other verdict is returned unchanged. In particular, a panic-site
/// mismatch whose Anneal span lies in user code (two different panicking
/// operations, or a `#[track_caller]` helper that Anneal attributes to its own
/// body) remains `Diverge(PanicSiteMismatch)`.
///
/// Every expansion of a standard macro shares the span of the macro's
/// definition, so these conditions cannot tell two panic-macro call sites in
/// the same function apart: if Anneal panics at a different `panic!` than Miri
/// does, the outcome still reconciles to `Agree`.
pub fn compare_difftest_miri_and_anneal(
    miri: &MiriOutcome,
    anneal: &AnnealOutcome,
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
            ..
        },
        AnnealOutcome::Panic {
            span: Some(anneal_span),
        },
    ) = (miri, anneal)
    else {
        return verdict;
    };
    if is_std_panic_macro_file(&anneal_span.file)
        && lib_src.is_panic_macro_call_site(fn_name, miri_pos)
    {
        ComparisonVerdict::Agree
    } else {
        verdict
    }
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
    /// Ordered list of AST mutators applied to produce this candidate.
    pub applied_mutators: Vec<String>,
    /// Canonical divergence class slug (`"wrong_value"`, `"false_positive_ub"`,
    /// `"missed_ub"`, `"panic_vs_return"`, `"return_vs_panic"`,
    /// `"ub_location_mismatch"`, or `"panic_site_mismatch"`).
    pub divergence_class: String,
    /// Concise Miri outcome tag.
    pub miri_outcome_tag: String,
    /// Human-readable Miri diagnostic excerpt (`MIRI_PASS:...`, panic message,
    /// or `error: Undefined Behavior: ...`).
    pub miri_excerpt: String,
    /// Miri fault/panic position translated to `repro.rs` line coordinates.
    pub miri_pos: Option<String>,
    /// Miri fault/panic position in the staged batch `src/lib.rs`.
    pub batch_miri_pos: Option<String>,
    /// Concise Anneal outcome tag.
    pub anneal_outcome_tag: String,
    /// Lean `MirDiffTag` constructor expression for this Anneal outcome.
    pub anneal_lean_tag: String,
    /// Anneal fault/panic span translated to `repro.rs` line coordinates.
    pub anneal_span: Option<String>,
    /// Anneal fault/panic span in the staged batch `src/lib.rs`.
    pub batch_anneal_span: Option<String>,
    /// Extracted neighborhood from `.anneal/generated/Mir/<Crate>/<Item>.lean`.
    pub mir_neighborhood: String,
    /// Whether the Lean 4 kernel confirmed `evalMirDiffTagBounded` and
    /// `probeMirDiffExecBounded` via `by rfl` in `MiriOracleConfirm.lean`.
    pub kernel_confirmed: bool,
    /// Kernel-checked `theorem confirm_tag_<fn_name>` and
    /// `theorem confirm_probe_<fn_name>` snippet from `MiriOracleConfirm.lean`.
    pub kernel_confirm_theorems: String,
    /// Standalone `#![no_std]` Rust reproducer source (`repro.rs`).
    pub mutant_source: String,
    /// Path to `repro.rs` on disk when `--findings-dir` was provided.
    pub repro_path: Option<PathBuf>,
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
    /// Count of divergences confirmed in the Lean 4 kernel (`by rfl`).
    pub kernel_confirmed_divergences: usize,
    /// Miri outcome counts (`pass`, `panic`, `ub`, `error`).
    pub miri_verdicts: BTreeMap<String, usize>,
    /// Anneal outcome counts (`pass`, `panic`, `ub`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `error`).
    pub anneal_outcomes: BTreeMap<String, usize>,
    /// Divergence counts by canonical class name.
    pub divergence_classes: BTreeMap<String, usize>,
    /// Not-compared counts by reason (`compile_failed`, `external_call`,
    /// `unsupported`, `out_of_fuel`, `miri_oracle_error`, `capture_failed`).
    pub not_compared_reasons: BTreeMap<String, usize>,
    /// Frequency table of unmodeled external call `DefPath`s encountered.
    pub unmodeled_external_calls: BTreeMap<String, usize>,
    /// Per-mutator application counts across all generated candidates.
    pub mutator_applications: BTreeMap<String, usize>,
    /// Detailed finding bundles for every `ComparisonVerdict::Diverge` item.
    pub findings: Vec<MiriFindingBundle>,
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
    if source_files_match(&pos.file, "src/lib.rs") && pos.line >= batch_start_line {
        SourcePos {
            file: "src/lib.rs".to_string(),
            line: pos.line - batch_start_line + repro_start_line,
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
    if source_files_match(&span.file, "src/lib.rs") && span.start_line >= batch_start_line {
        let delta = batch_start_line - repro_start_line;
        SourceSpan {
            file: "src/lib.rs".to_string(),
            start_line: span.start_line - delta,
            start_col: span.start_col,
            end_line: span.end_line.saturating_sub(delta),
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

/// Extract the `linkedCallees` definition and the `confirm_tag_<fn_name>` and
/// `confirm_probe_<fn_name>` theorems from `MiriOracleConfirm.lean` source,
/// preceded by the synthetic constructor stub definition when `linkedCallees`
/// refers to it, so the snippet names no definition local to the confirm module
/// that it does not also contain.
fn extract_confirm_theorems(confirm_src: &str, fn_name: &str) -> String {
    // Each block runs from its header to the first blank line; the generated
    // blocks contain no blank lines.
    let extract_block = |header: &str| -> Option<String> {
        let start_idx = confirm_src.find(header)?;
        let rest = &confirm_src[start_idx..];
        let end_rel = rest.find("\n\n").map(|i| i + 1).unwrap_or(rest.len());
        Some(rest[..end_rel].trim().to_string())
    };
    let callees_block = extract_block("def linkedCallees : List CapturedMir :=");
    let stub_block = match &callees_block {
        Some(callees) if callees.contains(FMT_ARGUMENTS_CTOR_STUB_NAME) => {
            FMT_ARGUMENTS_CTOR_STUB_LEAN
                .lines()
                .next()
                .and_then(&extract_block)
        }
        _ => None,
    };
    let tag_block = extract_block(&format!("theorem confirm_tag_{fn_name} :"));
    let probe_block = extract_block(&format!("theorem confirm_probe_{fn_name} :"));
    [stub_block, callees_block, tag_block, probe_block]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>()
        .join("\n\n")
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

fn run_lake_build_with_bin(
    lake_bin: &Path,
    dot_anneal_dir: &Path,
    targets: &[&str],
) -> Result<(), String> {
    let mut cmd = build_lake_build_command(lake_bin, dot_anneal_dir);
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
        return Err(format!(
            "lake build failed with status {} in {}:\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status,
            dot_anneal_dir.display()
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
           s!\"ANNEAL_PROBE\\t{{name}}\\t{{formatTag tag}}\\t{{span}}\"\n\n"
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

fn render_linked_anneal_confirm_module(
    crate_camel: &str,
    items: &[(OracleItemSpec, String, AnnealOutcome)],
    helper_module_suffixes: &[String],
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

    let callees_expr = render_linked_callees_expr(helper_module_suffixes);
    out.push_str(&format!(
        "\nset_option maxRecDepth 100000\n\
         set_option maxHeartbeats 2000000\n\n\
         namespace MiriOracleConfirm\n\n\
         open Trusted.Sequence\n\
         open Trusted.Rustc.V2026_06_01.MirAst\n\
         open Trusted.Rustc.V2026_06_01.MirSemantics\n\
         open Trusted.VerificationResult\n\
         open Anneal.Rustc.V2026_06_01.SymbolicEval\n\n\
         {FMT_ARGUMENTS_CTOR_STUB_LEAN}\n\
         def linkedCallees : List CapturedMir :=\n  {callees_expr}\n\n\
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
             | .vis (.inr (.inr (.call req))) _ => (.externalCall req.defPath, activeSpan body st)\n\n"
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
    }

    out.push_str("end MiriOracleConfirm\n");
    Ok(out)
}

fn run_linked_difftest_oracle_pipeline(
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

    let subject_records: Vec<_> = records
        .iter()
        .filter(|r| r.item_kind.as_str() == "subject")
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

    if !present_items.is_empty() {
        run_lake_build_with_bin(
            &lake_bin,
            &dot_anneal,
            &["Mir", "Anneal.Rustc.V2026_06_01.SymbolicEval"],
        )?;

        fs::create_dir_all(&oracle_dir)
            .map_err(|err| format!("failed to create {}: {}", oracle_dir.display(), err))?;
        let probe_path = oracle_dir.join("MiriOracleProbe.lean");
        let probe_src =
            render_linked_anneal_probe_module(&crate_camel, &present_items, &helper_module_suffixes);
        fs::write(&probe_path, &probe_src)
            .map_err(|err| format!("failed to write {}: {}", probe_path.display(), err))?;

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
        for (item, _) in &present_items {
            if let Some(outcome) = parsed.remove(&item.name) {
                anneal_outcomes.insert(item.name.clone(), outcome);
            } else {
                anneal_outcomes.insert(
                    item.name.clone(),
                    AnnealOutcome::CaptureOrLeanError(format!(
                        "Lean probe output omitted ANNEAL_PROBE line for '{}'",
                        item.name
                    )),
                );
            }
        }
    }

    let lib_rs_path = corpus_root.join("src/lib.rs");
    let lib_rs = fs::read_to_string(&lib_rs_path)
        .map_err(|err| format!("failed to read {}: {}", lib_rs_path.display(), err))?;
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
        let verdict = compare_difftest_miri_and_anneal(&miri, &anneal, &lib_src, &spec.name);
        // A reconciled panic-macro site agrees only through the panic-site rule
        // in `compare_difftest_miri_and_anneal`, so its Anneal outcome and span
        // are confirmed in the kernel, like a divergence's, rather than resting
        // on the compiled `#eval` probe alone.
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
        let confirm_path = oracle_dir.join("MiriOracleConfirm.lean");
        let confirm_src = render_linked_anneal_confirm_module(
            &crate_camel,
            &to_confirm,
            &helper_module_suffixes,
        )?;
        fs::write(&confirm_path, &confirm_src)
            .map_err(|err| format!("failed to write {}: {}", confirm_path.display(), err))?;

        let confirm_out = Command::new(&lake_bin)
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
        if !confirm_out.status.success() {
            let stdout = String::from_utf8_lossy(&confirm_out.stdout);
            let stderr = String::from_utf8_lossy(&confirm_out.stderr);
            return Err(format!(
                "Lean kernel confirmation failed in {} ({}):\n{}\n{}",
                confirm_path.display(),
                confirm_out.status,
                stdout,
                stderr
            ));
        }
        Some(confirm_path)
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

fn discover_reproducer_candidate_fn(source: &str) -> Option<String> {
    if let Ok(parsed) = syn::parse_file(source) {
        let mut pub_zero_arg = Vec::new();
        for item in parsed.items {
            if let syn::Item::Fn(func) = item
                && matches!(func.vis, syn::Visibility::Public(_))
                && func.sig.inputs.is_empty()
            {
                let name = func.sig.ident.to_string();
                if name != "helper_add_ten" {
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
        .filter(|name| name != "helper_add_ten")
        .last()
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
         - **Divergence class**: `{}`\n\
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
        if finding.applied_mutators.is_empty() {
            "identity (none)".to_string()
        } else {
            finding.applied_mutators.join(", ")
        },
        finding.divergence_class,
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
pub fn evaluate_miri_batches(
    mode: &str,
    seed: u64,
    batches: &[Vec<GeneratedMiriCandidate>],
    batch_size: usize,
    findings_dir: Option<&Path>,
    anneal_repo_root: Option<&Path>,
) -> Result<MiriCampaignEvalReport, String> {
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

    let oracle_report = match run_linked_difftest_oracle_pipeline(&oracle_cfg, &item_specs) {
        Ok(rep) => rep,
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
    let mut kernel_confirmed_divergences = 0usize;
    let mut obs_path_signatures_set = std::collections::BTreeSet::new();

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

        match &item_rep.verdict {
            ComparisonVerdict::Agree => {}
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
                if item_rep.kernel_confirmed {
                    kernel_confirmed_divergences += 1;
                }

                if let Some((cand, batch_start_line)) = cand_by_name.get(&item_rep.name) {
                    let raw_miri_pos = match &item_rep.miri {
                        MiriOutcome::Panic { pos, .. } | MiriOutcome::Ub { pos, .. } => {
                            pos.as_ref()
                        }
                        _ => None,
                    };
                    let batch_miri_pos = raw_miri_pos.map(SourcePos::display_short);
                    let repro_miri_pos = raw_miri_pos
                        .map(|p| translate_pos_to_repro(p, *batch_start_line, repro_start_line))
                        .map(|p| p.display_short());

                    let raw_anneal_span = item_rep.anneal.span();
                    let batch_anneal_span = raw_anneal_span.map(SourceSpan::display_short);
                    let repro_anneal_span = raw_anneal_span
                        .map(|s| translate_span_to_repro(s, *batch_start_line, repro_start_line))
                        .map(|s| s.display_short());

                    let miri_outcome_tag = match &item_rep.miri {
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

                    let anneal_outcome_tag = match &item_rep.anneal {
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
                        format_miri_excerpt(&item_rep.miri, repro_miri_pos.as_deref());
                    let anneal_lean_tag = item_rep
                        .anneal
                        .to_lean_mir_diff_tag()
                        .unwrap_or_else(|| "none".to_string());
                    let mir_neighborhood = extract_mir_neighborhood(
                        &staging_dir,
                        &oracle_report.crate_camel,
                        &item_rep.name,
                    );
                    let kernel_confirm_theorems =
                        extract_confirm_theorems(&confirm_src, &item_rep.name);

                    let finding_id = format!("finding_{:04}_{}", findings.len(), item_rep.name);
                    let mut bundle = MiriFindingBundle {
                        finding_id,
                        fn_name: item_rep.name.clone(),
                        seed_name: cand.seed_name.clone(),
                        applied_mutators: cand.applied_mutators.clone(),
                        divergence_class: class_slug,
                        miri_outcome_tag,
                        miri_excerpt,
                        miri_pos: repro_miri_pos,
                        batch_miri_pos,
                        anneal_outcome_tag,
                        anneal_lean_tag,
                        anneal_span: repro_anneal_span,
                        batch_anneal_span,
                        mir_neighborhood,
                        kernel_confirmed: item_rep.kernel_confirmed,
                        kernel_confirm_theorems,
                        mutant_source: cand.source.clone(),
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
            }
        }
    }

    let _ = fs::remove_dir_all(&staging_dir);

    let agree_count = oracle_report.agree_count;
    let diverge_count = oracle_report.diverge_count;
    let compared_candidates = agree_count + diverge_count;
    let not_compared_count = compile_failed_candidates + oracle_report.not_compared_count;
    let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;

    Ok(MiriCampaignEvalReport {
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
        not_compared_reasons,
        unmodeled_external_calls,
        mutator_applications,
        findings,
        obs_path_signatures: obs_path_signatures_set.into_iter().collect(),
        item_reports: oracle_report.items,
        elapsed_ms,
    })
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
    let mut report = res?;
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
    let mutators_json = finding
        .applied_mutators
        .iter()
        .map(|m| json_escape(m))
        .collect::<Vec<_>>()
        .join(", ");
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
         {inner}\"divergence_class\": {},\n\
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
        json_escape(&finding.divergence_class),
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
         \x20 \"not_compared_reasons\": {},\n\
         \x20 \"unmodeled_external_calls\": {},\n\
         \x20 \"mutator_applications\": {},\n\
         \x20 \"obs_path_signatures\": {},\n\
         \x20 \"findings_count\": {},\n\
         \x20 \"findings\": {findings_json},\n\
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
        render_usize_map_json(&report.not_compared_reasons, 2),
        render_usize_map_json(&report.unmodeled_external_calls, 2),
        render_usize_map_json(&report.mutator_applications, 2),
        render_string_list_json(&report.obs_path_signatures, 2),
        report.findings.len(),
        report.elapsed_ms,
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

    if !report.findings.is_empty() {
        out.push_str("\n## Divergences Detected\n\n");
        out.push_str("| Finding ID | Function | Class | Miri | Anneal | Kernel Confirmed |\n");
        out.push_str("| :--- | :--- | :--- | :--- | :--- | :--- |\n");
        for f in &report.findings {
            out.push_str(&format!(
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |\n",
                f.finding_id,
                f.fn_name,
                f.divergence_class,
                f.miri_outcome_tag,
                f.anneal_outcome_tag,
                f.kernel_confirmed
            ));
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(probe_src.contains("phase := MirPhaseTag.runtimePostCleanup"));
        assert!(probe_src.contains(
            "initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees"
        ));

        let confirm_src = render_linked_anneal_confirm_module(
            "MiriDiffCorpus",
            &[(
                spec,
                "MiriDiffCorpus.cand_call_helper".to_string(),
                AnnealOutcome::PassScalar {
                    bits: 42,
                    size_bytes: 4,
                },
            )],
            &helpers,
        )
        .expect("render confirm module");
        assert!(confirm_src.contains("import Mir.MiriDiffCorpus.helper_add_ten\n"));
        assert!(confirm_src.contains(
            "initMachineStateWithMemoryAndCallees Mir.MiriDiffCorpus.cand_call_helper.body [] emptyMemory linkedCallees"
        ));
        let extracted = extract_confirm_theorems(&confirm_src, "cand_call_helper");
        assert!(extracted.contains("def linkedCallees : List CapturedMir :="));
        assert!(extracted.contains("theorem confirm_tag_cand_call_helper :"));
        assert!(extracted.contains("theorem confirm_probe_cand_call_helper :"));
        assert!(extracted.contains(":= by\n  rfl"));
        // `linkedCallees` names the synthetic stub, so the snippet must carry the
        // stub's definition ahead of it.
        let stub_at = extracted
            .find("def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=")
            .expect("snippet must define fmtArgumentsCtorStub");
        let callees_at = extracted
            .find("def linkedCallees : List CapturedMir :=")
            .expect("snippet must define linkedCallees");
        assert!(stub_at < callees_at);
        assert!(extracted.contains(FMT_ARGUMENTS_CTOR_STUB_LEAN.trim()));
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
                compare_difftest_miri_and_anneal(&miri, &anneal, &src, name),
                ComparisonVerdict::Agree,
                "{name} at {line}:{col}"
            );
        }

        let mismatch = |miri: &MiriOutcome, anneal: &AnnealOutcome, name: &str| {
            matches!(
                compare_difftest_miri_and_anneal(miri, anneal, &src, name),
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
            compare_difftest_miri_and_anneal(&panic_at(3, 5), &ub, &src, "cand_panic__b0_c0"),
            ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
        ));

        // A line inside a multi-line string literal or block comment that
        // contains `panic!("...")` text does not start at a non-literal token,
        // so it must never reconcile.
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
",
        );
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &panic_at(4, 5),
                &anneal_panic_in(std_panic, 62),
                &spoofed_src,
                "cand_spoof__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &panic_at(7, 5),
                &anneal_panic_in(std_panic, 62),
                &spoofed_src,
                "cand_spoof__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
        assert!(matches!(
            compare_difftest_miri_and_anneal(
                &panic_at(10, 8),
                &anneal_panic_in(std_panic, 62),
                &spoofed_src,
                "cand_spoof__b0_c0"
            ),
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ));
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
        ] {
            assert!(starts_with_std_panic_macro_invocation(text), "{text}");
        }
        for text in [
            "my_panic!(\"x\")",
            "panicky!(\"x\")",
            "::panic!(\"x\")",
            "foo::panic!(\"x\")",
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
}
