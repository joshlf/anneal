//! Untrusted CLI orchestration library for `cargo-anneal` (#103 §2, §5).
//!
//! `cargo-anneal` sits outside `trusted/`. It coordinates three stages of the
//! verification workflow without participating in the kernel soundness gate:
//!
//! 1. **Extraction (`driver`)**: invokes `cargo check` with
//!    `RUSTC_WORKSPACE_WRAPPER` pointing to `anneal-rustc-capture`, passes
//!    `--cfg anodized_embed_specs`, and aggregates per-unit
//!    `UnitCaptureManifest.json` files into the root `CaptureManifest.json`
//!    handshake verified by `trusted/audit/check_trusted.py`.
//! 2. **Scaffolding (`obligations`, `scaffold`)**: populates disposable
//!    compiler-generated Lean modules under `.anneal/generated/` (`Mir/`,
//!    `Obligations/`, `Verify/`) and optionally initializes starter templates
//!    under `anneal/proofs/` without overwriting existing authored files.
//! 3. **Verification (`verify`)**: synchronizes generated assembly with
//!    authored files in `anneal/proofs/`, runs `lake build` in `.anneal/` to
//!    check `Verify.<Item>.verified : VerificationResult Obligations.<Item>.claim`
//!    in the Lean 4 kernel, and runs `trusted/audit/TrustedBoundary.lean` in
//!    `verify-audit` mode to enforce anti-cheat rules and classify conditional
//!    `Assumptions.<Item>` axioms.

extern crate self as cargo_anneal;

pub mod agent;
pub mod correspondence_bugs;
pub mod driver;
pub mod fault_census;
pub mod minirust_sync;
pub mod miri_diff;
pub mod miri_oracle;
pub mod obligations;
pub mod scaffold;
pub mod setup;
pub mod trace_observer;

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anneal_rustc_capture::{CaptureManifest, CapturedItemKind, UnitTargetRecord};

pub use agent::{
    LockedFileDigest, LockedUnitRecord, SPEC_LOCK_REL_PATH, SPEC_LOCK_SCHEMA_V1,
    SpecLockManifest, check_specs_non_vacuous, check_specs_non_vacuous_with_records,
    compute_spec_lock_manifest_digest, is_canonical_mir_fragment_tag, is_lowercase_sha256_hex,
    lock_workspace_specs, lock_workspace_specs_with_mutable, lock_workspace_specs_with_options,
    parse_spec_lock_manifest, render_agent_context, run_agent_sandbox,
    serialize_spec_lock_manifest, verify_spec_lock, verify_spec_lock_with_options,
};
pub use correspondence_bugs::{
    CorrespondenceBugsSubcommand, CorrespondenceGapEntry, CorrespondenceGapsRegistry,
    CorrespondenceMatrix, CorrespondenceMatrixCell, ExpectedTier, FileIssueOptions,
    FileIssueOutcome, FormattedGitHubIssue, GapKind, LintReport, MiriDiffCrossCheckReport,
    cross_check_miri_diff, file_github_issue, format_github_issue, is_vacuous_guard_predicate,
    lint_correspondence_gaps, lint_correspondence_gaps_with_vendor_root,
    load_correspondence_gaps, load_correspondence_matrix,
    parse_correspondence_bugs_args, parse_correspondence_gaps, parse_correspondence_matrix,
    run_correspondence_bugs_cli,
};
pub use driver::{
    ANNEAL_CAPTURE_FILTER_ENV, ANODIZED_EMBED_SPECS_CFG, CaptureDriverConfig,
    aggregate_unit_manifests, build_cargo_check_command, invoke_cargo_capture,
    load_captured_unit_records, merge_rustflags, parse_capture_manifest,
    parse_unit_capture_manifest, resolve_rustc_wrapper, run_cargo_capture,
    serialize_unit_capture_manifest,
};
pub use fault_census::{
    CalleeClosure, CensusScanError, CoverageVerdict, FaultCensusReceipt, FaultMutationProbe,
    FaultSite, ItemCoverageInput, MirFaultClass, MultiItemCoverageVerdict, ProbeExecutionReport,
    PropertyDescriptor, PropertyRegistry, PropertyStatus, ProtoBasicBlock, ProtoMirBody,
    ProtoOperand, ProtoPlace, ProtoProjectionElem, ProtoRvalue, ProtoStatement, ProtoStatementKind,
    ProtoTerminator, ProtoTerminatorKind, census_lean_mir_def, census_lean_mir_module,
    census_mir_fault_sites, census_stmt_fault_classes, census_terminator_fault_classes,
    parse_lean_captured_mir_def, parse_lean_mir_module_body_strict, reconcile_lean_mir_coverage,
    reconcile_multi_item_coverage,
    reconcile_obligation_coverage, run_all_false_proof_probes, run_false_proof_probe,
    run_property_registry_unemitted_probe,
};
pub use minirust_sync::{
    DeclChangeKind, DeclDiffEntry, ExtractedSpecDecl, LockVerificationReport, LockedSpecFile,
    MiniRustSyncSubcommand, SnapshotDiffReport, SnapshotLockEntry, SpecDeclKind,
    UpstreamMiniRustLock, diff_snapshot_directories, extract_snapshot_declarations,
    load_upstream_lock, parse_minirust_sync_args, parse_upstream_lock,
    render_snapshot_diff_markdown, render_sync_status_report, run_minirust_sync_cli,
    verify_upstream_lock,
};
pub use miri_diff::{
    KnownAnnealBugSpec, MiriDiffConfig, MiriDiffManifest, MiriDiffPanicCertificate, MiriDiffReport,
    MiriDiffTestEntry, MiriDiffVerdictSpec, load_miri_diff_manifest, parse_miri_diff_manifest,
    render_miri_diff_crate_verify_module, render_miri_diff_report, render_miri_diff_verify_module,
    render_miri_diff_verify_module_with_callees,
    render_miri_diff_verify_module_with_panic_certificate, run_miri_diff_suite,
    stage_miri_diff_workspace, verify_miri_diff_ub_locations,
};
pub use miri_oracle::{
    ALLOW_MISSING_MIRI_ENV, AnnealOracleConfig, AnnealOutcome, ComparisonVerdict,
    DEFAULT_CAPTURE_RUSTFLAGS, DEFAULT_MIRI_FLAGS, DEFAULT_MIRI_SETUP_TIMEOUT_SECS,
    DEFAULT_ORACLE_FUEL, DifftestOracleConfig, DifftestOracleReport, DivergenceKind,
    ItemOracleReport, MIRI_SETUP_BIN_ENV, MIRI_SETUP_LOCK_TIMEOUT_ENV, MIRI_SETUP_TIMEOUT_ENV,
    MiriOracleConfig, MiriOutcome, MiriToolchain, NotComparedReason, OracleItemSpec, SourcePos,
    SourceSpan,
    compare_miri_and_anneal, confirm_anneal_outcomes_in_kernel, discover_zero_arg_pub_fns,
    ensure_miri_sysroot_initialized, ensure_miri_sysroot_initialized_with,
    parse_anneal_probe_output, parse_miri_process_output, render_anneal_confirm_module,
    render_anneal_probe_module, render_miri_driver_source, run_anneal_oracle,
    run_difftest_oracle_pipeline, run_miri_oracle, source_files_match,
};
pub use obligations::{
    AuthoredItemModules, CalleeContractRef, ObligationSiteKind, SubjectObligationBundle,
    TaggedObligationSite, compute_bundle_fault_census_receipt,
    compute_subject_fault_coverage_receipt, derive_item_module_suffix,
    emit_mir_obligation_fault_sites, emit_obligation_fault_sites_for_body,
    emit_obligation_tagged_fault_sites_for_body, group_subject_obligations,
    module_suffix_to_rel_path, render_crate_verify_module, render_obligations_module,
    render_obligations_module_with_census, render_obligations_module_with_options,
    render_proof_template, render_proof_template_with_options, render_specs_template,
    render_verify_module, render_verify_module_with_options,
};
pub use scaffold::{
    LEAN_TOOLCHAIN, MirFragment, MirFragmentClassification, MirLiftingProfile, ScaffoldConfig,
    ScaffoldReport, analyze_mir_lifting_profile, analyze_workspace_lifting_profile,
    classify_mir_fragment, compute_fragment_spec_digest, compute_workspace_bundle_fault_census,
    detect_authored_item_modules, refresh_workspace_assembly, render_lakefile_toml,
    render_mir_fragment_diagnostic, render_proof_template_with_hints,
    render_scaffold_lifting_hints, scaffold_init_proof_templates, scaffold_init_spec_templates,
    scaffold_workspace, scaffold_workspace_with_config,
};
pub use trace_observer::{
    __anneal_mir_rt_branch, __anneal_mir_rt_call_begin, __anneal_mir_rt_call_end_normal,
    __anneal_mir_rt_push_arg, __anneal_mir_rt_ret, BatchTraceEvalCase, EnvAction, EnvSchedule,
    FromScheduleBytes, MIR_CALL_TOKEN_PASSTHROUGH_INLINED, MIR_CALL_TOKEN_SCHEDULED_RETURN,
    RawByteTraceJson, RawCallEventJson, RawOutcomeJson, RawTraceEventJson, RecordedEvent,
    RecordedOutcome, RecordedRawTrace, RecordedShadowAlloc, ScheduleError, ShadowAllocEntryJson,
    TraceCapture, TraceCheckModuleConfig, TraceObserverSpec, TraceRecorder, capture_value_bytes,
    decode_recorded_raw_trace_hex, encode_recorded_raw_trace_hex, observe_boundary_call,
    parse_batch_trace_probe_output, render_batch_trace_eval_lean_module,
    render_batch_trace_probe_lean_module, render_raw_byte_trace_lean,
    render_raw_byte_trace_lean_def, render_raw_outcome_lean, render_shadow_provenance_table_lean,
    render_tampered_outcome_diag_lean_snippet, render_trace_check_lean_module,
    render_trace_diag_eval_lean_snippet, value_as_raw_bytes,
};

/// Top-level subcommand selected on the `cargo anneal` command line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CliSubcommand {
    /// Run `cargo check` under `anneal-rustc-capture` and aggregate
    /// `UnitCaptureManifest.json` files into `CaptureManifest.json`.
    Extract,
    /// Extract (or load existing unit manifests) and scaffold `.anneal/` and
    /// `anneal/proofs/`.
    Scaffold,
    /// Extract, scaffold, and invoke `lake build` plus the `TrustedBoundary`
    /// anti-cheat audit inside `.anneal/`.
    Verify,
    /// Extract, scaffold, and write `.anneal/spec-lock.json` locking captured
    /// MIR digests, `anneal/proofs/Specs/**`, and
    /// `anneal/proofs/Assumptions/**`.
    LockSpecs,
    /// Extract, scaffold, and print a structured Markdown context report for an
    /// AI proof-authoring agent.
    AgentContext,
    /// Enforce `.anneal/spec-lock.json`, deterministically regenerate
    /// `.anneal/generated/`, and run `lake build` plus the `TrustedBoundary`
    /// anti-cheat audit.
    AgentVerify,
    /// Run a proof-authoring agent command inside an OS-level `bwrap`
    /// read-only sandbox where only `anneal/proofs/Proof/`, `target/`,
    /// `.anneal/.lake/`, and `/tmp` (plus `src/` when `mutable_subjects` is
    /// non-empty) are mounted writable.
    AgentSandbox,
    /// Install or resolve the pinned Anneal omnibus toolchain archive under
    /// `~/.anneal/toolchain/` (`cargo anneal setup [--local-archive <PATH>]`).
    Setup,
    /// Stage all 4 Anneal workspace crates (`anneal-spec-macros`,
    /// `anneal-spec`, `anneal-rustc-capture`, and `cargo-anneal` with bundled
    /// `lean-root/`) for vendoring into Fuchsia's `//third_party/rust_crates`.
    VendorFuchsia,
    /// Manage non-correspondence gap registry validation, Markdown issue
    /// rendering, and opt-in manual issue filing (`cargo anneal correspondence-bugs`).
    CorrespondenceBugs,
    /// Verify upstream MiniRust lockfiles, diff snapshots, and render sync
    /// status reports offline (`cargo anneal minirust-sync`).
    MiniRustSync,
    /// Generate a ready-to-use `#[anneal_spec::external_spec(for = <target>)]`
    /// Rust declaration snippet (`cargo anneal generate-external-spec <target> [--output <path>]`).
    GenerateExternalSpec,
    /// Print CLI usage instructions.
    Help,
    /// Print the `cargo-anneal` package version.
    Version,
}

/// Parsed command-line options for `cargo anneal`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliOptions {
    /// Selected subcommand.
    pub subcommand: CliSubcommand,
    /// Target Cargo workspace root directory.
    pub workspace_root: PathBuf,
    /// Optional explicit `--manifest-path` forwarded to `cargo check`.
    pub manifest_path: Option<PathBuf>,
    /// Directory holding per-unit capture manifests (`<target>/anneal/units` by
    /// default).
    pub units_dir: PathBuf,
    /// Optional explicit path to `anneal-rustc-capture`.
    pub rustc_wrapper: Option<PathBuf>,
    /// Optional explicit path to the Anneal repository root containing
    /// `trusted/lean` and `theory`.
    pub anneal_repo_root: Option<PathBuf>,
    /// When true, aggregate existing `UnitCaptureManifest.json` files in
    /// `units_dir` without re-running `cargo check`.
    pub from_existing_units: bool,
    /// When true, create starter `anneal/proofs/Specs/<Item>.lean` templates
    /// for items that do not yet have authored specification files on disk.
    pub init_specs: bool,
    /// When true, create starter `anneal/proofs/Proof/<Item>.lean` templates
    /// for items that do not yet have authored proof files on disk.
    pub init_proofs: bool,
    /// When true, allow `Verify.<Item>.verified` proofs to depend on axioms
    /// declared in `Assumptions.<Item>` modules (classified as
    /// `VerificationStatus::VerifiedConditional`).
    pub allow_assumptions: bool,
    /// When true, allow `Proof.<Item>` modules to use `native_decide` during
    /// provisional exploration (classified as
    /// `VerificationStatus::ProvisionalNative`).
    pub allow_provisional_native: bool,
    /// When true (or when `subcommand == CliSubcommand::AgentVerify`), enforce
    /// `.anneal/spec-lock.json` and regenerate `.anneal/generated/` before
    /// running Lake.
    pub locked_specs: bool,
    /// Optional external lockfile path (`--lock-file <PATH>`) for `lock-specs`,
    /// `agent-verify`, `verify --locked-specs`, or `agent-sandbox`, allowing a
    /// harness to store the trusted lock outside the agent's writable directory.
    pub lock_file: Option<PathBuf>,
    /// Optional Git revision (`--lock-git-ref <REV>`, e.g. `HEAD`) from which
    /// `.anneal/spec-lock.json` is loaded during `agent-verify` / `verify
    /// --locked-specs`, preventing an agent from overwriting the on-disk lockfile.
    pub lock_git_ref: Option<String>,
    /// Optional local `.tar.zst` archive path (`--local-archive <PATH>`) for
    /// `cargo anneal setup`.
    pub local_archive: Option<PathBuf>,
    /// Optional output directory (`--out-dir <DIR>`) for
    /// `cargo anneal vendor-fuchsia`.
    pub out_dir: Option<PathBuf>,
    /// Optional item filter (`--item <filter>`) restricting `agent-context` or
    /// `verify` targets by `def_id` or `item_module_suffix`.
    pub item_filter: Option<String>,
    /// Optional comma-separated subject pattern (`--allow-impl-edit <filter>`)
    /// recorded by `lock-specs` permitting designated subject implementation
    /// bodies to change while keeping all contracts SHA-256 locked.
    pub allow_impl_edit: Option<String>,
    /// Optional comma-separated pattern filter restricting captured items via
    /// `ANNEAL_CAPTURE_FILTER`.
    pub filter: Option<String>,
    /// Extra arguments forwarded to `cargo check` (or command arguments for
    /// `agent-sandbox`) after `--`.
    pub extra_cargo_args: Vec<String>,
}

/// Verification outcome for a single `Verify.<Item>` module after kernel replay
/// and constant-closure inspection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationStatus {
    /// `Verify.<Item>.verified` is proved unconditionally (depends at most on
    /// `propext`).
    VerifiedUnconditional,
    /// `Verify.<Item>.verified` is proved conditionally on explicit axioms
    /// declared in `Assumptions.*` modules.
    VerifiedConditional {
        /// Fully qualified names of all `Assumptions.*` axioms reached in the
        /// transitive constant closure of `Verify.<Item>.verified`.
        assumptions: Vec<String>,
    },
    /// `Verify.<Item>.verified` is a scoped UB-exception certificate
    /// (`UbExceptionVerificationResult`).
    VerifiedUbException {
        /// Any `Assumptions.*` axioms reached in the transitive constant closure
        /// of `Verify.<Item>.verified`.
        assumptions: Vec<String>,
    },
    /// `Verify.<Item>.verified` was checked under `--provisional` /
    /// `--allow-provisional-native` and relies on `native_decide` trust axioms.
    ProvisionalNative {
        /// Names of native decide axioms or `Assumptions.*` axioms reached in
        /// the transitive constant closure of `Verify.<Item>.verified`.
        axioms: Vec<String>,
    },
    /// `Verify.<Item>` failed fault-site coverage reconciliation (one or more
    /// syntactic fault sites were unmapped/undischarged or a required
    /// `MirFaultClass` is not `PropertyStatus::EmittedAndVerified` in the
    /// `PropertyRegistry`).
    UnknownUnmappedFaultSite {
        /// Fault sites in `census` that were omitted from `discharged` or whose
        /// fault class is not `PropertyStatus::EmittedAndVerified`.
        missing_sites: Vec<fault_census::FaultSite>,
        /// Distinct `MirFaultClass` categories present in `census` whose status
        /// in `PropertyRegistry` is not `PropertyStatus::EmittedAndVerified`.
        unemitted_classes: Vec<fault_census::MirFaultClass>,
        /// Diagnostic summary explaining why coverage reconciliation failed.
        reason: String,
    },
}

impl VerificationStatus {
    /// Return the canonical status tag for this verification outcome.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::VerifiedUnconditional => "UNCONDITIONAL",
            Self::VerifiedConditional { .. } => "CONDITIONAL",
            Self::VerifiedUbException { .. } => "UB_EXCEPTION",
            Self::ProvisionalNative { .. } => "PROVISIONAL_NATIVE",
            Self::UnknownUnmappedFaultSite { .. } => "UNKNOWN(UNMAPPED_FAULT_SITE)",
        }
    }
}

/// Per-item verification audit entry returned by `verify_workspace`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemVerificationReport {
    /// Full Lean module name (for example, `"Verify.CanaryPkg.identity_u32"`).
    pub verify_module: String,
    /// Kernel and constant-closure classification for this item.
    pub status: VerificationStatus,
}

/// Summary of a completed `verify_workspace` run across all `Verify.*` modules.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VerificationReport {
    /// Per-item verification statuses ordered by `verify_module`.
    pub items: Vec<ItemVerificationReport>,
}

impl VerificationReport {
    /// Look up the `VerificationStatus` for a full `Verify.<Item>` module name
    /// or an `<Item>` suffix.
    pub fn status_for(&self, module_or_suffix: &str) -> Option<&VerificationStatus> {
        let normalized = if module_or_suffix.starts_with("Verify.") {
            module_or_suffix.to_string()
        } else {
            format!("Verify.{module_or_suffix}")
        };
        self.items
            .iter()
            .find(|item| item.verify_module == normalized)
            .map(|item| &item.status)
    }
}

/// Configuration for `verify_workspace_with_config`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyConfig {
    /// Root directory of the target Rust workspace or crate.
    pub workspace_root: PathBuf,
    /// Optional directory containing pre-captured `UnitCaptureManifest.json`
    /// and `Mir/` files for Cargo-free GN/Bazel verification.
    pub units_dir: Option<PathBuf>,
    /// Optional explicit path to the Anneal repository root containing
    /// `trusted/audit/TrustedBoundary.lean`.
    pub anneal_repo_root: Option<PathBuf>,
    /// Whether conditional proofs reaching `Assumptions.*` axioms are permitted.
    pub allow_assumptions: bool,
    /// Whether provisional proofs using `native_decide` in `Proof.*` modules
    /// are permitted (`VerificationStatus::ProvisionalNative`).
    pub allow_provisional_native: bool,
    /// Optional comma-separated item filter restricting `lake build` and
    /// `TrustedBoundary` auditing to matching `Verify.<Item>` modules.
    pub item_filter: Option<String>,
    /// Optional property coverage registry mapping each `MirFaultClass` to its
    /// verification status (`PropertyRegistry::all_verified()` when `None`).
    pub property_registry: Option<fault_census::PropertyRegistry>,
    /// Optional fault sites simulated as dropped from the discharged set
    /// (for fail-closed negative testing).
    pub simulated_dropped_fault_sites: std::collections::BTreeSet<FaultSite>,
}

impl VerifyConfig {
    /// Create a strict `VerifyConfig` (`allow_assumptions == false`) rooted at
    /// `workspace_root`.
    pub fn new(workspace_root: impl Into<PathBuf>) -> Self {
        Self {
            workspace_root: workspace_root.into(),
            units_dir: None,
            anneal_repo_root: None,
            allow_assumptions: false,
            allow_provisional_native: false,
            item_filter: None,
            property_registry: None,
            simulated_dropped_fault_sites: std::collections::BTreeSet::new(),
        }
    }

    /// Set a pre-captured `units_dir` for Cargo-free GN/Bazel verification.
    pub fn with_units_dir(mut self, units_dir: impl Into<PathBuf>) -> Self {
        self.units_dir = Some(units_dir.into());
        self
    }

    /// Configure whether conditional proofs reaching `Assumptions.*` axioms are
    /// permitted.
    pub fn with_allow_assumptions(mut self, allow_assumptions: bool) -> Self {
        self.allow_assumptions = allow_assumptions;
        self
    }

    /// Configure whether provisional proofs using `native_decide` are permitted.
    pub fn with_allow_provisional_native(mut self, allow_provisional_native: bool) -> Self {
        self.allow_provisional_native = allow_provisional_native;
        self
    }

    /// Set an explicit Anneal repository root path.
    pub fn with_anneal_repo_root(mut self, anneal_repo_root: impl Into<PathBuf>) -> Self {
        self.anneal_repo_root = Some(anneal_repo_root.into());
        self
    }

    /// Restrict verification to `Verify.<Item>` modules matching `item_filter`.
    pub fn with_item_filter(mut self, item_filter: Option<String>) -> Self {
        self.item_filter = item_filter;
        self
    }

    /// Override the `PropertyRegistry` used by fault-site coverage reconciliation.
    pub fn with_property_registry(mut self, property_registry: fault_census::PropertyRegistry) -> Self {
        self.property_registry = Some(property_registry);
        self
    }

    /// Simulate dropping specific fault sites from the obligation pipeline's
    /// `discharged` set during coverage reconciliation.
    pub fn with_dropped_fault_sites(
        mut self,
        dropped: std::collections::BTreeSet<FaultSite>,
    ) -> Self {
        self.simulated_dropped_fault_sites = dropped;
        self
    }
}

/// Lexically normalize `path` against `base_dir`, resolving relative paths,
/// `.`, and `..` components without requiring the target path to exist on disk.
pub fn normalize_path_against(base_dir: &Path, path: &Path) -> PathBuf {
    let combined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base_dir.join(path)
    };
    let mut out = PathBuf::new();
    for comp in combined.components() {
        match comp {
            std::path::Component::Prefix(p) => out.push(p.as_os_str()),
            std::path::Component::RootDir => out.push(comp.as_os_str()),
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                let can_pop = matches!(
                    out.components().next_back(),
                    Some(std::path::Component::Normal(_))
                );
                if can_pop {
                    out.pop();
                } else if !out.has_root() {
                    out.push("..");
                }
            }
            std::path::Component::Normal(part) => out.push(part),
        }
    }
    if out.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        out
    }
}

/// Normalize a wrapper executable path against `base_dir` unless it is a bare
/// program name intended for `PATH` lookup (single normal component that does
/// not exist as a relative file in `base_dir`).
pub(crate) fn normalize_wrapper_path(base_dir: &Path, wrapper: &Path) -> PathBuf {
    if wrapper.is_absolute() {
        return normalize_path_against(base_dir, wrapper);
    }
    let is_single_normal = wrapper.components().count() == 1
        && matches!(
            wrapper.components().next(),
            Some(std::path::Component::Normal(_))
        );
    let candidate = base_dir.join(wrapper);
    if !is_single_normal || candidate.is_file() {
        normalize_path_against(base_dir, wrapper)
    } else {
        wrapper.to_path_buf()
    }
}

/// Parse command-line arguments for `cargo-anneal`, stripping the leading
/// `"anneal"` token when invoked as a Cargo subcommand (`cargo anneal ...`).
pub fn parse_cli_args<I, S>(args: I) -> Result<CliOptions, String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let raw: Vec<String> = args.into_iter().map(|s| s.as_ref().to_string()).collect();
    let mut slice = raw.as_slice();
    if !slice.is_empty() {
        slice = &slice[1..];
    }
    if slice.first().map(String::as_str) == Some("anneal") {
        slice = &slice[1..];
    }

    let default_root = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut subcommand: Option<CliSubcommand> = None;
    let mut workspace_root: Option<PathBuf> = None;
    let mut manifest_path: Option<PathBuf> = None;
    let mut units_dir: Option<PathBuf> = None;
    let mut rustc_wrapper: Option<PathBuf> = None;
    let mut anneal_repo_root: Option<PathBuf> = None;
    let mut from_existing_units = false;
    let mut init_specs = false;
    let mut init_proofs = false;
    let mut allow_assumptions = false;
    let mut allow_provisional_native = false;
    let mut locked_specs = false;
    let mut lock_file: Option<PathBuf> = None;
    let mut lock_git_ref: Option<String> = None;
    let mut local_archive: Option<PathBuf> = None;
    let mut out_dir: Option<PathBuf> = None;
    let mut item_filter_patterns: Vec<String> = Vec::new();
    let mut allow_impl_edit_patterns: Vec<String> = Vec::new();
    let mut filter_patterns: Vec<String> = Vec::new();
    let mut extra_cargo_args = Vec::new();

    let mut i = 0;
    while i < slice.len() {
        let arg = &slice[i];
        match arg.as_str() {
            "-h" | "--help" | "help" => {
                subcommand = Some(CliSubcommand::Help);
                i += 1;
            }
            "-V" | "--version" | "version" => {
                subcommand = Some(CliSubcommand::Version);
                i += 1;
            }
            "extract" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::Extract);
                i += 1;
            }
            "scaffold" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::Scaffold);
                i += 1;
            }
            "verify" | "check" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::Verify);
                i += 1;
            }
            "lock-specs" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::LockSpecs);
                i += 1;
            }
            "agent-context" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::AgentContext);
                i += 1;
            }
            "agent-verify" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::AgentVerify);
                locked_specs = true;
                i += 1;
            }
            "agent-sandbox" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::AgentSandbox);
                i += 1;
            }
            "setup" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::Setup);
                i += 1;
            }
            "vendor-fuchsia" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::VendorFuchsia);
                i += 1;
            }
            "correspondence-bugs" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::CorrespondenceBugs);
                extra_cargo_args.extend(slice[i + 1..].iter().cloned());
                break;
            }
            "minirust-sync" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::MiniRustSync);
                extra_cargo_args.extend(slice[i + 1..].iter().cloned());
                break;
            }
            "generate-external-spec" if subcommand.is_none() => {
                subcommand = Some(CliSubcommand::GenerateExternalSpec);
                i += 1;
            }
            "--workspace-root" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --workspace-root".to_string())?;
                workspace_root = Some(PathBuf::from(val));
                i += 1;
            }
            s if s.starts_with("--workspace-root=") => {
                let val = s["--workspace-root=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --workspace-root".to_string());
                }
                workspace_root = Some(PathBuf::from(val));
                i += 1;
            }
            "--manifest-path" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --manifest-path".to_string())?;
                manifest_path = Some(PathBuf::from(val));
                i += 1;
            }
            s if s.starts_with("--manifest-path=") => {
                let val = s["--manifest-path=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --manifest-path".to_string());
                }
                manifest_path = Some(PathBuf::from(val));
                i += 1;
            }
            "--units-dir" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --units-dir".to_string())?;
                units_dir = Some(PathBuf::from(val));
                i += 1;
            }
            s if s.starts_with("--units-dir=") => {
                let val = s["--units-dir=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --units-dir".to_string());
                }
                units_dir = Some(PathBuf::from(val));
                i += 1;
            }
            "--wrapper" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --wrapper".to_string())?;
                rustc_wrapper = Some(PathBuf::from(val));
                i += 1;
            }
            s if s.starts_with("--wrapper=") => {
                let val = s["--wrapper=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --wrapper".to_string());
                }
                rustc_wrapper = Some(PathBuf::from(val));
                i += 1;
            }
            "--anneal-root" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --anneal-root".to_string())?;
                anneal_repo_root = Some(PathBuf::from(val));
                i += 1;
            }
            s if s.starts_with("--anneal-root=") => {
                let val = s["--anneal-root=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --anneal-root".to_string());
                }
                anneal_repo_root = Some(PathBuf::from(val));
                i += 1;
            }
            "--item" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --item".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --item".to_string());
                }
                item_filter_patterns.push(trimmed.to_string());
                i += 1;
            }
            s if s.starts_with("--item=") => {
                let val = s["--item=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --item".to_string());
                }
                item_filter_patterns.push(val.to_string());
                i += 1;
            }
            "--allow-impl-edit" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --allow-impl-edit".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --allow-impl-edit".to_string());
                }
                allow_impl_edit_patterns.push(trimmed.to_string());
                i += 1;
            }
            s if s.starts_with("--allow-impl-edit=") => {
                let val = s["--allow-impl-edit=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --allow-impl-edit".to_string());
                }
                allow_impl_edit_patterns.push(val.to_string());
                i += 1;
            }
            "--filter" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --filter".to_string())?;
                let trimmed = val.trim();
                if !trimmed.is_empty() {
                    filter_patterns.push(trimmed.to_string());
                }
                i += 1;
            }
            s if s.starts_with("--filter=") => {
                let val = s["--filter=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --filter".to_string());
                }
                filter_patterns.push(val.to_string());
                i += 1;
            }
            "--from-units" | "--skip-capture" => {
                from_existing_units = true;
                i += 1;
            }
            "--init-specs" => {
                init_specs = true;
                i += 1;
            }
            "--init-proofs" => {
                init_proofs = true;
                i += 1;
            }
            "--allow-assumptions" | "--allow-ub-exceptions" => {
                allow_assumptions = true;
                i += 1;
            }
            "--provisional" | "--allow-provisional-native" => {
                allow_provisional_native = true;
                i += 1;
            }
            "--locked-specs" => {
                locked_specs = true;
                i += 1;
            }
            "--lock-file" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --lock-file".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --lock-file".to_string());
                }
                lock_file = Some(PathBuf::from(trimmed));
                locked_specs = true;
                i += 1;
            }
            s if s.starts_with("--lock-file=") => {
                let val = s["--lock-file=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --lock-file".to_string());
                }
                lock_file = Some(PathBuf::from(val));
                locked_specs = true;
                i += 1;
            }
            "--lock-git-ref" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --lock-git-ref".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --lock-git-ref".to_string());
                }
                lock_git_ref = Some(trimmed.to_string());
                locked_specs = true;
                i += 1;
            }
            s if s.starts_with("--lock-git-ref=") => {
                let val = s["--lock-git-ref=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --lock-git-ref".to_string());
                }
                lock_git_ref = Some(val.to_string());
                locked_specs = true;
                i += 1;
            }
            "--local-archive" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --local-archive".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() || trimmed.starts_with('-') {
                    return Err("missing value for --local-archive".to_string());
                }
                local_archive = Some(PathBuf::from(trimmed));
                i += 1;
            }
            s if s.starts_with("--local-archive=") => {
                let val = s["--local-archive=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --local-archive".to_string());
                }
                local_archive = Some(PathBuf::from(val));
                i += 1;
            }
            "--out-dir" | "--output" | "-o" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --out-dir/--output".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --out-dir/--output".to_string());
                }
                out_dir = Some(PathBuf::from(trimmed));
                i += 1;
            }
            s if s.starts_with("--out-dir=") || s.starts_with("--output=") => {
                let (_, val) = s.split_once('=').unwrap_or((s, ""));
                let val = val.trim();
                if val.is_empty() {
                    return Err("missing value for --out-dir/--output".to_string());
                }
                out_dir = Some(PathBuf::from(val));
                i += 1;
            }
            "--" => {
                extra_cargo_args.extend(slice[i + 1..].iter().cloned());
                break;
            }
            other => {
                if subcommand.is_none() {
                    return Err(format!(
                        "unknown subcommand '{other}' (expected 'extract', 'scaffold', 'verify', 'check', 'lock-specs', 'agent-context', 'agent-verify', 'agent-sandbox', 'setup', 'vendor-fuchsia', 'correspondence-bugs', 'minirust-sync', or 'generate-external-spec')"
                    ));
                }
                if subcommand == Some(CliSubcommand::Setup) {
                    return Err(format!("unknown setup argument '{other}'"));
                }
                extra_cargo_args.push(other.to_string());
                i += 1;
            }
        }
    }

    let resolved_manifest_path = manifest_path
        .as_deref()
        .map(|mp| normalize_path_against(&default_root, mp));
    let resolved_root = if let Some(ref root) = workspace_root {
        normalize_path_against(&default_root, root)
    } else if let Some(ref mp) = resolved_manifest_path
        && let Some(parent) = mp.parent()
        && !parent.as_os_str().is_empty()
    {
        parent.to_path_buf()
    } else {
        default_root.clone()
    };
    let resolved_units = units_dir
        .as_deref()
        .map(|u| normalize_path_against(&default_root, u))
        .unwrap_or_else(|| resolved_root.join("target").join("anneal").join("units"));
    let resolved_wrapper = rustc_wrapper
        .as_deref()
        .map(|w| normalize_wrapper_path(&default_root, w));
    let resolved_anneal_root = anneal_repo_root
        .as_deref()
        .map(|r| normalize_path_against(&default_root, r));
    let resolved_lock_file = lock_file
        .as_deref()
        .map(|lf| normalize_path_against(&default_root, lf));
    let resolved_local_archive = local_archive
        .as_deref()
        .map(|la| normalize_path_against(&default_root, la));
    let resolved_out_dir = out_dir
        .as_deref()
        .map(|od| normalize_path_against(&default_root, od));

    let item_filter = if item_filter_patterns.is_empty() {
        None
    } else {
        Some(item_filter_patterns.join(","))
    };
    let allow_impl_edit = if allow_impl_edit_patterns.is_empty() {
        None
    } else {
        Some(allow_impl_edit_patterns.join(","))
    };
    let filter = if filter_patterns.is_empty() {
        None
    } else {
        Some(filter_patterns.join(","))
    };

    Ok(CliOptions {
        subcommand: subcommand.unwrap_or(CliSubcommand::Help),
        workspace_root: resolved_root,
        manifest_path: resolved_manifest_path,
        units_dir: resolved_units,
        rustc_wrapper: resolved_wrapper,
        anneal_repo_root: resolved_anneal_root,
        from_existing_units,
        init_specs,
        init_proofs,
        allow_assumptions,
        allow_provisional_native,
        locked_specs,
        lock_file: resolved_lock_file,
        lock_git_ref,
        local_archive: resolved_local_archive,
        out_dir: resolved_out_dir,
        item_filter,
        allow_impl_edit,
        filter,
        extra_cargo_args,
    })
}

/// Format the human-readable `--help` message for `cargo anneal`.
pub fn cli_usage() -> &'static str {
    "Usage: cargo anneal <SUBCOMMAND> [OPTIONS] [-- <CARGO_ARGS>...]\n\n\
     Subcommands:\n  \
       setup               Install the pinned Anneal toolchain archive under ~/.anneal/toolchain/\n  \
       vendor-fuchsia      Stage workspace crates + lean-root/ for Fuchsia //third_party/rust_crates\n  \
       extract             Capture MIR via anneal-rustc-capture and aggregate CaptureManifest.json\n  \
       scaffold            Generate .anneal/generated/ modules and ensure anneal/proofs/ exists\n  \
       verify              Extract, scaffold, build with Lake, and audit the TrustedBoundary\n  \
       check               Alias for 'verify'\n  \
       lock-specs          Lock MIR digests, Specs/**, and Assumptions/** in .anneal/spec-lock.json\n  \
       agent-context       Render structured Markdown context for an AI proof-authoring agent\n  \
       agent-verify        Enforce .anneal/spec-lock.json, regenerate .anneal/generated/, and verify\n  \
       agent-sandbox       Run an agent command inside a bwrap read-only sandbox (-- <COMMAND>...)\n  \
       correspondence-bugs Offline non-correspondence gap linter & opt-in manual issue formatter/filer\n  \
       minirust-sync       Offline upstream MiniRust lock verifier, snapshot differ, and status reporter\n  \
       generate-external-spec  Generate a ready-to-use #[anneal_spec::external_spec(for = <target>)] snippet\n\n\
     Options:\n  \
       --local-archive <PATH>  Install 'setup' from a local .tar.zst toolchain archive\n  \
       --out-dir <DIR>         Output directory for 'vendor-fuchsia'\n  \
       --workspace-root <DIR>  Target Cargo workspace root\n  \
       --manifest-path <PATH>  Path to Cargo.toml\n  \
       --units-dir <DIR>       Directory for per-unit capture artifacts\n  \
       --wrapper <PATH>        Path to anneal-rustc-capture executable\n  \
       --anneal-root <DIR>     Path to Anneal checkout containing trusted/lean and theory\n  \
       --item <PATTERN>        Filter items in 'agent-context' or 'verify' by def_id or module suffix\n  \
       --allow-impl-edit <PAT> Allow designated subject body edits in 'lock-specs'\n  \
       --filter <PATTERN>      Comma-separated item filter (passed via ANNEAL_CAPTURE_FILTER)\n  \
       --from-units            Use existing UnitCaptureManifest.json files without cargo check\n  \
       --skip-capture          Alias for '--from-units' (Cargo-free GN/Bazel verification)\n  \
       --init-specs            Create starter anneal/proofs/Specs/<Item>.lean templates\n  \
       --init-proofs           Create starter anneal/proofs/Proof/<Item>.lean templates\n  \
       --allow-assumptions     Permit conditional proofs that depend on Assumptions.<Item> axioms\n  \
       --provisional           Permit provisional Proof.<Item> proofs using native_decide\n  \
       --locked-specs          Enforce .anneal/spec-lock.json before running Lake\n  \
       --lock-file <PATH>      Read or write spec-lock manifest at <PATH> (outside workspace)\n  \
       --lock-git-ref <REV>    Verify .anneal/spec-lock.json against Git revision <REV> (e.g. HEAD)\n  \
       -h, --help              Print help\n  \
       -V, --version           Print version\n"
}

/// Render a deterministic human-readable summary of a completed MIR capture
/// phase.
///
/// Summarizes captured Rust source files, total MIR targets, subject item
/// count, companion item counts (`requires`, `ensures`, `qualifiers`,
/// `external_spec`, `model`, `invariant`, `unsafe_trait_impl`), and the sorted
/// list of subject `def_id -> lean_module_name` mappings.
pub fn render_extract_report(
    manifest: &CaptureManifest,
    records: &[UnitTargetRecord],
) -> String {
    let mut subject_count = 0usize;
    let mut requires_count = 0usize;
    let mut ensures_count = 0usize;
    let mut qualifiers_count = 0usize;
    let mut external_spec_count = 0usize;
    let mut model_count = 0usize;
    let mut invariant_count = 0usize;
    let mut unsafe_trait_impl_count = 0usize;
    let mut subjects: Vec<(&str, &str)> = Vec::new();

    for record in records {
        match record.item_kind {
            CapturedItemKind::Subject => {
                subject_count += 1;
                subjects.push((
                    record.target.def_id.as_str(),
                    record.lean_module_name.as_str(),
                ));
            }
            CapturedItemKind::InlineSpecRequires => requires_count += 1,
            CapturedItemKind::InlineSpecEnsures => ensures_count += 1,
            CapturedItemKind::InlineSpecQualifiers => qualifiers_count += 1,
            CapturedItemKind::ExternalSpec => external_spec_count += 1,
            CapturedItemKind::Model => model_count += 1,
            CapturedItemKind::TypeInvariant => invariant_count += 1,
            CapturedItemKind::UnsafeTraitImpl => {
                unsafe_trait_impl_count += 1;
                subjects.push((
                    record.target.def_id.as_str(),
                    record.lean_module_name.as_str(),
                ));
            }
            CapturedItemKind::Callee => {}
        }
    }
    subjects.sort_by(|a, b| a.0.cmp(b.0));

    let mut out = String::new();
    out.push_str("Anneal Extract Summary:\n");
    out.push_str(&format!(
        "  Rust source files: {}\n",
        manifest.rust_sources.len()
    ));
    out.push_str(&format!("  Total MIR targets: {}\n", manifest.targets.len()));
    out.push_str(&format!("  Subject items: {subject_count}\n"));
    out.push_str(&format!(
        "  Companion items: requires: {requires_count}, ensures: {ensures_count}, qualifiers: {qualifiers_count}, external_spec: {external_spec_count}, model: {model_count}, invariant: {invariant_count}, unsafe_trait_impl: {unsafe_trait_impl_count}\n"
    ));
    if !subjects.is_empty() {
        out.push_str("  Subject mappings:\n");
        for (def_id, lean_mod) in subjects {
            out.push_str(&format!("    {def_id} -> {lean_mod}\n"));
        }
    }
    out
}

/// Render a deterministic human-readable summary of a workspace scaffolding
/// run.
///
/// Summarizes generated disposable `.anneal/generated/` modules (`Mir`,
/// `Obligations`, `Verify`) and durable `anneal/proofs/` files (`created
/// Specs`, `preserved Specs`, `created Proof`, `preserved Proof`).
pub fn render_scaffold_report(report: &ScaffoldReport) -> String {
    let mut out = String::new();
    out.push_str("Anneal Scaffold Summary:\n");
    out.push_str(&format!(
        "  Generated (.anneal/generated/): Mir: {}, Obligations: {}, Verify: {}\n",
        report.generated_mir_files.len(),
        report.generated_obligation_files.len(),
        report.generated_verify_files.len(),
    ));
    out.push_str(&format!(
        "  Durable (anneal/proofs/): created Specs: {}, preserved Specs: {}, created Proof: {}, preserved Proof: {}\n",
        report.created_spec_files.len(),
        report.preserved_spec_files.len(),
        report.created_proof_files.len(),
        report.preserved_proof_files.len(),
    ));
    out
}

/// Render a deterministic human-readable summary of a written
/// `.anneal/spec-lock.json` manifest and verify non-vacuity checks.
pub fn render_lock_specs_report(
    workspace_root: &Path,
    lock_path: &Path,
) -> Result<String, String> {
    let raw = fs::read_to_string(lock_path).map_err(|err| {
        format!(
            "failed to read spec-lock manifest {}: {}",
            lock_path.display(),
            err
        )
    })?;
    let manifest = parse_spec_lock_manifest(&raw)?;
    agent::verify_spec_lock_manifest_integrity(&manifest, &lock_path.display().to_string())?;
    check_specs_non_vacuous(workspace_root)?;
    let display_path = lock_path
        .strip_prefix(workspace_root)
        .unwrap_or(lock_path)
        .display();

    let mut out = String::new();
    out.push_str("Anneal Spec-Lock Summary:\n");
    out.push_str(&format!("  Lock file: {display_path}\n"));
    out.push_str(&format!(
        "  Locked MIR targets: {}\n",
        manifest.locked_records.len()
    ));
    out.push_str(&format!(
        "  Locked Specs files: {}\n",
        manifest.locked_specs_files.len()
    ));
    out.push_str(&format!(
        "  Locked Assumptions files: {}\n",
        manifest.locked_assumptions_files.len()
    ));
    if !manifest.mutable_subjects.is_empty() {
        out.push_str(&format!(
            "  Mutable subject bodies: {}\n",
            manifest.mutable_subjects.join(", ")
        ));
    }
    out.push_str("  Non-vacuity check: PASS\n");
    Ok(out)
}

/// Render a deterministic human-readable summary of a completed workspace
/// verification and `TrustedBoundary` kernel-replay run.
pub fn render_verification_report(report: &VerificationReport) -> String {
    let mut unconditional_count = 0usize;
    let mut conditional_count = 0usize;
    let mut ub_exception_count = 0usize;
    let mut provisional_count = 0usize;
    let mut unmapped_count = 0usize;
    let mut out = String::new();
    out.push_str("Anneal Verification Summary:\n");
    for item in &report.items {
        match &item.status {
            VerificationStatus::VerifiedUnconditional => {
                unconditional_count += 1;
                out.push_str(&format!("  {}: UNCONDITIONAL\n", item.verify_module));
            }
            VerificationStatus::VerifiedConditional { assumptions } => {
                conditional_count += 1;
                out.push_str(&format!(
                    "  {}: CONDITIONAL [{}]\n",
                    item.verify_module,
                    assumptions.join(", ")
                ));
            }
            VerificationStatus::VerifiedUbException { assumptions } => {
                ub_exception_count += 1;
                if assumptions.is_empty() {
                    out.push_str(&format!("  {}: UB_EXCEPTION\n", item.verify_module));
                } else {
                    out.push_str(&format!(
                        "  {}: UB_EXCEPTION [{}]\n",
                        item.verify_module,
                        assumptions.join(", ")
                    ));
                }
            }
            VerificationStatus::ProvisionalNative { axioms } => {
                provisional_count += 1;
                if axioms.is_empty() {
                    out.push_str(&format!(
                        "  {}: PROVISIONAL_NATIVE\n",
                        item.verify_module
                    ));
                } else {
                    out.push_str(&format!(
                        "  {}: PROVISIONAL_NATIVE [{}]\n",
                        item.verify_module,
                        axioms.join(", ")
                    ));
                }
            }
            VerificationStatus::UnknownUnmappedFaultSite { reason, .. } => {
                unmapped_count += 1;
                if reason.is_empty() {
                    out.push_str(&format!(
                        "  {}: UNKNOWN(UNMAPPED_FAULT_SITE)\n",
                        item.verify_module
                    ));
                } else {
                    out.push_str(&format!(
                        "  {}: UNKNOWN(UNMAPPED_FAULT_SITE) [{reason}]\n",
                        item.verify_module
                    ));
                }
            }
        }
    }
    let mut totals = format!("{unconditional_count} unconditional, {conditional_count} conditional");
    if ub_exception_count > 0 {
        totals.push_str(&format!(", {ub_exception_count} ub_exception"));
    }
    if provisional_count > 0 {
        totals.push_str(&format!(", {provisional_count} provisional_native"));
    }
    if unmapped_count > 0 {
        totals.push_str(&format!(", {unmapped_count} unknown_unmapped_fault_site"));
    }
    out.push_str(&format!("  Totals: {totals}\n"));
    out.push_str("  TrustedBoundary kernel replay: PASS\n");
    out
}

/// Execute the parsed `CliOptions`.
pub fn execute_cli(options: &CliOptions) -> Result<(), String> {
    match options.subcommand {
        CliSubcommand::Help => {
            print!("{}", cli_usage());
            Ok(())
        }
        CliSubcommand::Version => {
            println!("cargo-anneal {}", env!("CARGO_PKG_VERSION"));
            Ok(())
        }
        CliSubcommand::Extract => {
            let (manifest, records) = run_extract_phase(options)?;
            print!("{}", render_extract_report(&manifest, &records));
            Ok(())
        }
        CliSubcommand::Scaffold => {
            let (_manifest, records) = run_extract_phase(options)?;
            let scaffold_cfg = ScaffoldConfig {
                workspace_root: options.workspace_root.clone(),
                units_dir: Some(options.units_dir.clone()),
                anneal_repo_root: options.anneal_repo_root.clone(),
                init_spec_templates: options.init_specs,
                init_proof_templates: options.init_proofs,
            };
            let report = scaffold_workspace_with_config(&scaffold_cfg, &records)?;
            print!("{}", render_scaffold_report(&report));
            Ok(())
        }
        CliSubcommand::LockSpecs => {
            let (_manifest, records) = run_extract_phase(options)?;
            let scaffold_cfg = ScaffoldConfig {
                workspace_root: options.workspace_root.clone(),
                units_dir: Some(options.units_dir.clone()),
                anneal_repo_root: options.anneal_repo_root.clone(),
                init_spec_templates: options.init_specs,
                init_proof_templates: options.init_proofs,
            };
            scaffold_workspace_with_config(&scaffold_cfg, &records)?;
            let mutable_patterns: Vec<String> = options
                .allow_impl_edit
                .as_deref()
                .map(|s| vec![s.to_string()])
                .unwrap_or_default();
            let lock_path = agent::lock_workspace_specs_with_units_dir(
                &options.workspace_root,
                &records,
                &mutable_patterns,
                options.lock_file.as_deref(),
                Some(&options.units_dir),
            )?;
            let report = render_lock_specs_report(&options.workspace_root, &lock_path)?;
            print!("{report}");
            Ok(())
        }
        CliSubcommand::AgentContext => {
            let (_manifest, records) = run_extract_phase(options)?;
            let scaffold_cfg = ScaffoldConfig {
                workspace_root: options.workspace_root.clone(),
                units_dir: Some(options.units_dir.clone()),
                anneal_repo_root: options.anneal_repo_root.clone(),
                init_spec_templates: options.init_specs,
                init_proof_templates: options.init_proofs,
            };
            scaffold_workspace_with_config(&scaffold_cfg, &records)?;
            let context = render_agent_context(
                &options.workspace_root,
                &records,
                options.item_filter.as_deref(),
            )?;
            print!("{context}");
            Ok(())
        }
        CliSubcommand::Verify | CliSubcommand::AgentVerify => {
            let report = verify_workspace_with_options(options)?;
            print!("{}", render_verification_report(&report));
            ensure_fault_site_coverage_reconciled(&report)?;
            Ok(())
        }
        CliSubcommand::AgentSandbox => {
            run_agent_sandbox(
                &options.workspace_root,
                options.lock_file.as_deref(),
                &options.extra_cargo_args,
            )?;
            Ok(())
        }
        CliSubcommand::Setup => {
            let root = setup::install(options.local_archive.clone())?;
            println!("Installed Anneal toolchain at {}", root.display());
            Ok(())
        }
        CliSubcommand::VendorFuchsia => {
            let out_dir = options.out_dir.as_deref().ok_or_else(|| {
                "vendor-fuchsia requires --out-dir <DIR>".to_string()
            })?;
            let repo_root = options
                .anneal_repo_root
                .clone()
                .or_else(default_anneal_repo_root)
                .unwrap_or_else(|| options.workspace_root.clone());
            let staged = vendor_fuchsia_crates(&repo_root, out_dir)?;
            for dir in &staged {
                println!("Vendored {}", dir.display());
            }
            Ok(())
        }
        CliSubcommand::CorrespondenceBugs => {
            let sub = correspondence_bugs::parse_correspondence_bugs_args(&options.extra_cargo_args)?;
            let out = correspondence_bugs::run_correspondence_bugs_cli(&sub)?;
            print!("{out}");
            Ok(())
        }
        CliSubcommand::MiniRustSync => {
            let sub = minirust_sync::parse_minirust_sync_args(&options.extra_cargo_args)?;
            let out = minirust_sync::run_minirust_sync_cli(&sub)?;
            print!("{out}");
            Ok(())
        }
        CliSubcommand::GenerateExternalSpec => {
            let target = options
                .extra_cargo_args
                .first()
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .or(options.item_filter.as_deref())
                .ok_or_else(|| {
                    "generate-external-spec requires a <target> function path argument".to_string()
                })?;
            let snippet = generate_external_spec_snippet(
                &options.workspace_root,
                Some(&options.units_dir),
                target,
            )?;
            if let Some(ref output_path) = options.out_dir {
                if let Some(parent) = output_path.parent()
                    && !parent.as_os_str().is_empty()
                {
                    fs::create_dir_all(parent).map_err(|err| {
                        format!(
                            "failed to create output directory {}: {}",
                            parent.display(),
                            err
                        )
                    })?;
                }
                fs::write(output_path, &snippet).map_err(|err| {
                    format!(
                        "failed to write external spec snippet to {}: {}",
                        output_path.display(),
                        err
                    )
                })?;
            } else {
                print!("{snippet}");
            }
            Ok(())
        }
    }
}

/// Generate a ready-to-use `#[anneal_spec::external_spec(for = <target>)]` Rust
/// declaration snippet for `target` by inspecting captured MIR modules under
/// `.anneal/generated/Mir/` or `units_dir`, workspace `.rs` source files, or
/// standard `core` signatures.
pub fn generate_external_spec_snippet(
    workspace_root: &Path,
    units_dir: Option<&Path>,
    target: &str,
) -> Result<String, String> {
    let trimmed_target = target.trim();
    if trimmed_target.is_empty() {
        return Err("target function path must not be empty".to_string());
    }

    let normalized_lookup = normalize_external_spec_lookup_target(trimmed_target);
    let short_ident = normalized_lookup
        .rsplit_once("::")
        .map(|(_, id)| id)
        .unwrap_or(&normalized_lookup)
        .trim_matches(|c: char| !c.is_ascii_alphanumeric() && c != '_');
    let spec_fn_name = format!(
        "external_spec_{}",
        if short_ident.is_empty() {
            "target"
        } else {
            short_ident
        }
    );

    if let Some((abi, generics, params, ret_ty)) =
        find_signature_in_captured_mir(workspace_root, units_dir, trimmed_target, &normalized_lookup)
            .or_else(|| find_signature_in_rust_sources(workspace_root, short_ident))
            .or_else(|| {
                builtin_core_signature(trimmed_target, &normalized_lookup)
                    .map(|(g, p, r)| (None, g, p, r))
            })
    {
        return Ok(format_external_spec_snippet_with_abi_and_generics(
            trimmed_target,
            &spec_fn_name,
            abi.as_deref(),
            &generics,
            &params,
            &ret_ty,
        ));
    }

    Ok(format_external_spec_snippet(
        trimmed_target,
        &spec_fn_name,
        &[],
        "()",
    ))
}

fn normalize_external_spec_lookup_target(raw: &str) -> String {
    let collapsed = raw
        .split_whitespace()
        .collect::<String>()
        .replace("::<impl[", "::<impl [");
    let trimmed = collapsed
        .trim_start_matches("::")
        .strip_prefix("crate::")
        .or_else(|| collapsed.trim_start_matches("::").strip_prefix("self::"))
        .unwrap_or(collapsed.trim_start_matches("::"));
    let core_normalized = if let Some(rest) = trimmed.strip_prefix("std::") {
        format!("core::{rest}")
    } else {
        trimmed.to_string()
    };
    if let Some(rest) = core_normalized.strip_prefix("<[")
        && let Some((elem, after)) = rest.split_once("]>::")
        && !elem.is_empty()
        && !after.is_empty()
    {
        return format!("core::slice::<impl [T]>::{after}");
    }
    if let Some(rest) = core_normalized.strip_prefix("core::slice::<impl [")
        && let Some((elem, after)) = rest.split_once("]>::")
        && !elem.is_empty()
        && !after.is_empty()
    {
        return format!("core::slice::<impl [T]>::{after}");
    }
    core_normalized
}

fn format_external_spec_snippet(
    target: &str,
    spec_fn_name: &str,
    params: &[(String, String)],
    ret_ty: &str,
) -> String {
    format_external_spec_snippet_with_abi_and_generics(target, spec_fn_name, None, &[], params, ret_ty)
}

fn format_external_spec_snippet_with_abi_and_generics(
    target: &str,
    spec_fn_name: &str,
    abi: Option<&str>,
    generics: &[String],
    params: &[(String, String)],
    ret_ty: &str,
) -> String {
    let params_str = params
        .iter()
        .map(|(name, ty)| format!("{name}: {ty}"))
        .collect::<Vec<_>>()
        .join(", ");
    // A returned reference needs an explicit lifetime when no parameter can
    // supply one through elision (for example `from_raw_parts_mut(*mut T,
    // usize) -> &mut [T]`); `'static` unifies with the target's free lifetime
    // parameter in the signature check.
    let params_have_refs = params.iter().any(|(_, ty)| ty.contains('&'));
    let ret_ty = if params_have_refs {
        ret_ty.to_string()
    } else {
        add_static_lifetimes(ret_ty)
    };
    let ret_suffix = if ret_ty.is_empty() || ret_ty == "()" {
        String::new()
    } else {
        format!(" -> {ret_ty}")
    };
    let generics_suffix = if generics.is_empty() {
        String::new()
    } else {
        format!("<{}>", generics.join(", "))
    };
    let ensures_ret_ty = if ret_ty.is_empty() { "()" } else { ret_ty.as_str() };
    let collapsed_target = target
        .split_whitespace()
        .collect::<String>()
        .replace("::<impl[", "::<impl [");
    let rust_for_target = if let Some(rest) = collapsed_target
        .strip_prefix("core::slice::<impl [")
        .or_else(|| collapsed_target.strip_prefix("std::slice::<impl ["))
        && let Some((raw_elem, method)) = rest.split_once("]>::")
        && !raw_elem.is_empty()
        && !method.is_empty()
    {
        let elem = if generics.iter().any(|g| g == "T") {
            "T"
        } else if raw_elem != "T" {
            raw_elem
        } else {
            "u8"
        };
        format!("<[{elem}]>::{method}")
    } else {
        target.to_string()
    };
    let abi_prefix = match abi.map(str::trim).filter(|a| !a.is_empty() && !a.eq_ignore_ascii_case("Rust")) {
        Some(a) => format!("unsafe extern \"{a}\" fn"),
        None => "unsafe fn".to_string(),
    };
    format!(
        "// Generated by `cargo anneal generate-external-spec {target}`.\n\
         // Optional clauses: `requires: <pred>, ensures: |ret: {ensures_ret_ty}| <pred>`.\n\
         // The declaration is `unsafe` so that its signature check accepts both safe\n\
         // and `unsafe` targets (a safe function item coerces to an `unsafe fn` pointer).\n\
         #[anneal_spec::external_spec(for = {rust_for_target})]\n\
         {abi_prefix} {spec_fn_name}{generics_suffix}({params_str}){ret_suffix};\n"
    )
}

/// Give every elided reference in the Rust type string `ty` the `'static`
/// lifetime (`&[u8]` -> `&'static [u8]`, `&mut T` -> `&'static mut T`).
fn add_static_lifetimes(ty: &str) -> String {
    let mut out = String::with_capacity(ty.len() + 8);
    let mut chars = ty.chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '&' && chars.peek().is_some_and(|next| *next != '\'') {
            out.push_str("'static ");
            while chars.peek().is_some_and(|next| next.is_whitespace()) {
                chars.next();
            }
        }
    }
    out
}

fn find_signature_in_captured_mir(
    workspace_root: &Path,
    units_dir: Option<&Path>,
    raw_target: &str,
    normalized_target: &str,
) -> Option<(Option<String>, Vec<String>, Vec<(String, String)>, String)> {
    let mut candidate_dirs = Vec::new();
    let gen_mir = workspace_root.join(".anneal/generated/Mir");
    if gen_mir.is_dir() {
        candidate_dirs.push(gen_mir);
    }
    if let Some(u_dir) = units_dir
        && u_dir.is_dir()
    {
        candidate_dirs.push(u_dir.to_path_buf());
    }
    let default_units = workspace_root.join("target/anneal/units");
    if default_units.is_dir() && !candidate_dirs.contains(&default_units) {
        candidate_dirs.push(default_units);
    }

    let mut lean_files = Vec::new();
    for dir in &candidate_dirs {
        collect_mir_lean_files(dir, &mut lean_files);
    }
    lean_files.sort();

    let collapsed_raw = raw_target
        .split_whitespace()
        .collect::<String>()
        .replace("::<impl[", "::<impl [");
    let explicit_slice_elem = collapsed_raw
        .strip_prefix("<[")
        .and_then(|r| r.split_once("]>::"))
        .map(|(t, _)| t.trim())
        .or_else(|| {
            collapsed_raw
                .strip_prefix("core::slice::<impl [")
                .or_else(|| collapsed_raw.strip_prefix("std::slice::<impl ["))
                .and_then(|r| r.split_once("]>::"))
                .map(|(t, _)| t.trim())
        })
        .filter(|t| !t.is_empty() && *t != "T");

    let suffix_match = format!("::{normalized_target}");
    for file in &lean_files {
        let Ok(txt) = fs::read_to_string(file) else {
            continue;
        };
        let Some(def_path) = extract_lean_mir_def_path(&txt) else {
            continue;
        };
        if def_path == raw_target
            || def_path == normalized_target
            || def_path.ends_with(&suffix_match)
        {
            let t_override = explicit_slice_elem.or_else(|| {
                if def_path.starts_with("core::slice::")
                    && !collapsed_raw.starts_with("<[T]>::")
                    && !collapsed_raw.contains("<impl [T]>::")
                {
                    Some("u8")
                } else {
                    None
                }
            });
            if let Some(sig) = parse_lean_mir_signature(&txt, t_override) {
                return Some(sig);
            }
        }
    }
    None
}

fn collect_mir_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_mir_lean_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            out.push(path);
        }
    }
}

fn extract_lean_mir_def_path(txt: &str) -> Option<String> {
    let marker = "defPath := \"";
    let pos = txt.find(marker)?;
    let after = &txt[pos + marker.len()..];
    let end = after.find('"')?;
    Some(after[..end].to_string())
}

fn extract_lean_call_conv(conv_expr: &str) -> Option<String> {
    let mut trimmed = conv_expr.trim();
    while has_enclosing_parens(trimmed) {
        trimmed = trimmed[1..trimmed.len() - 1].trim();
    }
    match trimmed {
        "CallConv.c" | ".c" | "Abi.c" => Some("C".to_string()),
        _ => {
            if let Some(after) = trimmed
                .strip_prefix("CallConv.other \"")
                .or_else(|| trimmed.strip_prefix(".other \""))
                .or_else(|| trimmed.strip_prefix("Abi.other \""))
                && let Some(end_q) = after.find('"')
            {
                let abi = after[..end_q].trim();
                if !abi.is_empty() && !abi.eq_ignore_ascii_case("Rust") {
                    return Some(abi.to_string());
                }
            }
            None
        }
    }
}

fn parse_lean_mir_signature(
    txt: &str,
    param_t_override: Option<&str>,
) -> Option<(Option<String>, Vec<String>, Vec<(String, String)>, String)> {
    let arg_marker = "argCount := ";
    let arg_pos = txt.find(arg_marker)?;
    let after_arg = &txt[arg_pos + arg_marker.len()..];
    let arg_digits: String = after_arg
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    let arg_count: usize = arg_digits.parse().ok()?;

    let mut declared_generics = Vec::new();
    if let Some(gp_pos) = txt.find("genericParams :=") {
        let after_gp = &txt[gp_pos..];
        let gp_end = after_gp.find("localDecls :=").unwrap_or(after_gp.len());
        let gp_section = &after_gp[..gp_end];
        let mut search = gp_section;
        let name_marker = "name := \"";
        while let Some(n_pos) = search.find(name_marker) {
            let after_n = &search[n_pos + name_marker.len()..];
            if let Some(end_q) = after_n.find('"') {
                let g_name = &after_n[..end_q];
                if !g_name.is_empty()
                    && g_name != "Self"
                    && !g_name.starts_with('\'')
                    && !declared_generics.iter().any(|g| g == g_name)
                {
                    declared_generics.push(g_name.to_string());
                }
                search = &after_n[end_q + 1..];
            } else {
                break;
            }
        }
    }

    let decls_marker = "localDecls :=";
    let decls_pos = txt.find(decls_marker)?;
    let header_before_decls = &txt[..decls_pos];
    let abi = header_before_decls.find("conv := ").and_then(|c_pos| {
        let after_c = &header_before_decls[c_pos + "conv := ".len()..];
        let end_c = after_c
            .find(", canUnwind")
            .or_else(|| after_c.find('}'))
            .unwrap_or(after_c.len());
        extract_lean_call_conv(&after_c[..end_c])
    });
    let mut rest = &txt[decls_pos + decls_marker.len()..];
    if param_t_override.is_none() {
        let decls_end = rest.find("basicBlocks :=").unwrap_or(rest.len());
        let decls_section = &rest[..decls_end];
        for param_marker in ["RigidTy.param ", ".param "] {
            let mut search = decls_section;
            while let Some(p_pos) = search.find(param_marker) {
                let after_p = &search[p_pos + param_marker.len()..];
                let after_digits = after_p.trim_start_matches(|c: char| c.is_ascii_digit() || c == ' ');
                if let Some(after_q) = after_digits.strip_prefix('"')
                    && let Some(end_q) = after_q.find('"')
                {
                    let g_name = &after_q[..end_q];
                    if !g_name.is_empty()
                        && g_name != "Self"
                        && !g_name.starts_with('\'')
                        && !declared_generics.iter().any(|g| g == g_name)
                    {
                        declared_generics.push(g_name.to_string());
                    }
                    search = &after_q[end_q + 1..];
                } else {
                    search = after_p;
                }
            }
        }
    }
    let mut decl_tys = Vec::with_capacity(arg_count + 1);

    let kind_marker = "ty := { kind := ";
    let layout_marker = ", layoutIdx :=";
    for idx in 0..=arg_count {
        let k_pos = rest.find(kind_marker)?;
        let after_k = &rest[k_pos + kind_marker.len()..];
        let l_pos = after_k.find(layout_marker)?;
        let kind_expr = after_k[..l_pos].trim();
        let rust_ty = lean_rigid_ty_to_rust_with_override(kind_expr, param_t_override);
        let after_l = &after_k[l_pos + layout_marker.len()..];
        let ty_close_brace = after_l.find('}')?;
        let after_ty = &after_l[ty_close_brace + 1..];
        let decl_close_brace = after_ty.find('}')?;
        let decl_tail = &after_ty[..decl_close_brace];
        let ident = if idx == 0 {
            "_ret".to_string()
        } else {
            let mut extracted = None;
            for marker in [
                "userIdent := (Option.some \"",
                "userIdent := some \"",
                "debugName := (Option.some \"",
                "debugName := some \"",
            ] {
                if let Some(u_pos) = decl_tail.find(marker) {
                    let after_u = &decl_tail[u_pos + marker.len()..];
                    if let Some(end) = after_u.find('"') {
                        let candidate = &after_u[..end];
                        if !candidate.is_empty() && candidate != "self" {
                            extracted = Some(candidate.to_string());
                            break;
                        }
                    }
                }
            }
            extracted.unwrap_or_else(|| format!("arg{idx}"))
        };
        decl_tys.push((ident, rust_ty));
        rest = &after_ty[decl_close_brace + 1..];
    }

    let ret_ty = decl_tys.first()?.1.clone();
    let params: Vec<(String, String)> = decl_tys.into_iter().skip(1).collect();
    let used_generics: Vec<String> = declared_generics
        .into_iter()
        .filter(|g| {
            type_mentions_ident(&ret_ty, g)
                || params.iter().any(|(_, ty)| type_mentions_ident(ty, g))
        })
        .collect();
    Some((abi, used_generics, params, ret_ty))
}

fn type_mentions_ident(ty: &str, ident: &str) -> bool {
    ty.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|tok| tok == ident)
}

fn split_top_level_comma(s: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    let mut in_quotes = false;
    for (idx, ch) in s.char_indices() {
        if ch == '"' {
            in_quotes = !in_quotes;
            continue;
        }
        if in_quotes {
            continue;
        }
        match ch {
            '(' | '[' | '<' | '{' => depth += 1,
            ')' | ']' | '>' | '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                let piece = s[start..idx].trim();
                if !piece.is_empty() {
                    parts.push(piece);
                }
                start = idx + 1;
            }
            _ => {}
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        parts.push(tail);
    }
    parts
}

fn has_enclosing_parens(s: &str) -> bool {
    if !(s.starts_with('(') && s.ends_with(')')) {
        return false;
    }
    let mut depth = 0usize;
    let mut in_quotes = false;
    for (idx, ch) in s.char_indices() {
        if ch == '"' {
            in_quotes = !in_quotes;
            continue;
        }
        if in_quotes {
            continue;
        }
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && idx + 1 < s.len() {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

fn split_last_balanced_token(s: &str) -> Option<(&str, &str)> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return None;
    }
    let last_ch = trimmed.chars().next_back()?;
    if matches!(last_ch, ')' | ']' | '}') {
        let open_ch = match last_ch {
            ')' => '(',
            ']' => '[',
            _ => '{',
        };
        let mut depth = 0usize;
        let mut in_quotes = false;
        let mut open_idx = None;
        for (idx, ch) in trimmed.char_indices().rev() {
            if ch == '"' {
                in_quotes = !in_quotes;
                continue;
            }
            if in_quotes {
                continue;
            }
            if ch == last_ch {
                depth += 1;
            } else if ch == open_ch {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    open_idx = Some(idx);
                    break;
                }
            }
        }
        let idx = open_idx?;
        let head = trimmed[..idx].trim();
        let tail = trimmed[idx..].trim();
        if head.is_empty() {
            None
        } else {
            Some((head, tail))
        }
    } else {
        let last_ws = trimmed.rfind(char::is_whitespace)?;
        let head = trimmed[..last_ws].trim();
        let tail = trimmed[last_ws..].trim();
        if head.is_empty() || tail.is_empty() {
            None
        } else {
            Some((head, tail))
        }
    }
}

/// Parse a Lean `List` expression formatted either with bracket syntax
/// (`[a, b]`, `[]`) or with constructor syntax (`(List.cons a (List.cons b List.nil))`,
/// `List.nil`, `.nil`, as emitted by `anneal-rustc-capture::lean_emit`).
fn parse_lean_list_expr(raw: &str) -> Option<Vec<&str>> {
    let mut curr = raw.trim();
    let mut items = Vec::new();
    loop {
        while has_enclosing_parens(curr) {
            curr = curr[1..curr.len() - 1].trim();
        }
        if matches!(curr, "List.nil" | ".nil" | "[]") {
            return Some(items);
        }
        if curr.starts_with('[') && curr.ends_with(']') {
            let inner = &curr[1..curr.len() - 1];
            items.extend(split_top_level_comma(inner));
            return Some(items);
        }
        let after_cons = curr
            .strip_prefix("List.cons ")
            .or_else(|| curr.strip_prefix(".cons "))?;
        let (head, tail) = split_last_balanced_token(after_cons)?;
        items.push(head);
        curr = tail;
    }
}

fn lean_rigid_ty_to_rust_with_override(expr: &str, param_t_override: Option<&str>) -> String {
    let mut trimmed = expr.trim();
    while has_enclosing_parens(trimmed) {
        trimmed = &trimmed[1..trimmed.len() - 1];
        trimmed = trimmed.trim();
    }
    match trimmed {
        "RigidTy.bool" | ".bool" => "bool".to_string(),
        "RigidTy.char" | ".char" => "char".to_string(),
        "RigidTy.str" | ".str" => "str".to_string(),
        "RigidTy.never" | ".never" => "!".to_string(),
        "RigidTy.uint UintTy.u8" | ".uint .u8" => "u8".to_string(),
        "RigidTy.uint UintTy.u16" | ".uint .u16" => "u16".to_string(),
        "RigidTy.uint UintTy.u32" | ".uint .u32" => "u32".to_string(),
        "RigidTy.uint UintTy.u64" | ".uint .u64" => "u64".to_string(),
        "RigidTy.uint UintTy.u128" | ".uint .u128" => "u128".to_string(),
        "RigidTy.uint UintTy.usize" | ".uint .usize" => "usize".to_string(),
        "RigidTy.int IntTy.i8" | ".int .i8" => "i8".to_string(),
        "RigidTy.int IntTy.i16" | ".int .i16" => "i16".to_string(),
        "RigidTy.int IntTy.i32" | ".int .i32" => "i32".to_string(),
        "RigidTy.int IntTy.i64" | ".int .i64" => "i64".to_string(),
        "RigidTy.int IntTy.i128" | ".int .i128" => "i128".to_string(),
        "RigidTy.int IntTy.isize" | ".int .isize" => "isize".to_string(),
        "RigidTy.float FloatTy.f16" | ".float .f16" => "f16".to_string(),
        "RigidTy.float FloatTy.f32" | ".float .f32" => "f32".to_string(),
        "RigidTy.float FloatTy.f64" | ".float .f64" => "f64".to_string(),
        "RigidTy.float FloatTy.f128" | ".float .f128" => "f128".to_string(),
        "RigidTy.tuple List.nil" | ".tuple []" | ".tuple List.nil" | ".tuple .nil" => {
            "()".to_string()
        }
        _ => {
            if let Some(inner) = trimmed
                .strip_prefix("RigidTy.ref Mutability.not ")
                .or_else(|| trimmed.strip_prefix(".ref .not "))
            {
                format!(
                    "&{}",
                    lean_rigid_ty_to_rust_with_override(inner, param_t_override)
                )
            } else if let Some(inner) = trimmed
                .strip_prefix("RigidTy.ref Mutability.mut ")
                .or_else(|| trimmed.strip_prefix(".ref .mut "))
            {
                format!(
                    "&mut {}",
                    lean_rigid_ty_to_rust_with_override(inner, param_t_override)
                )
            } else if let Some(inner) = trimmed
                .strip_prefix("RigidTy.rawPtr Mutability.not ")
                .or_else(|| trimmed.strip_prefix(".rawPtr .not "))
            {
                format!(
                    "*const {}",
                    lean_rigid_ty_to_rust_with_override(inner, param_t_override)
                )
            } else if let Some(inner) = trimmed
                .strip_prefix("RigidTy.rawPtr Mutability.mut ")
                .or_else(|| trimmed.strip_prefix(".rawPtr .mut "))
            {
                format!(
                    "*mut {}",
                    lean_rigid_ty_to_rust_with_override(inner, param_t_override)
                )
            } else if let Some(inner) = trimmed
                .strip_prefix("RigidTy.slice ")
                .or_else(|| trimmed.strip_prefix(".slice "))
            {
                format!(
                    "[{}]",
                    lean_rigid_ty_to_rust_with_override(inner, param_t_override)
                )
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.array ")
                .or_else(|| trimmed.strip_prefix(".array "))
                && let Some(last_space) = after.rfind(' ')
                && after[last_space + 1..].chars().all(|c| c.is_ascii_digit())
            {
                let elem_expr = &after[..last_space];
                let len_str = &after[last_space + 1..];
                format!(
                    "[{}; {len_str}]",
                    lean_rigid_ty_to_rust_with_override(elem_expr, param_t_override)
                )
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.tuple ")
                .or_else(|| trimmed.strip_prefix(".tuple "))
                && let Some(raw_elems) = parse_lean_list_expr(after)
            {
                let elems: Vec<String> = raw_elems
                    .into_iter()
                    .map(|e| lean_rigid_ty_to_rust_with_override(e, param_t_override))
                    .collect();
                if elems.is_empty() {
                    "()".to_string()
                } else if elems.len() == 1 {
                    format!("({},)", elems[0])
                } else {
                    format!("({})", elems.join(", "))
                }
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.adt \"")
                .or_else(|| trimmed.strip_prefix(".adt \""))
                .or_else(|| trimmed.strip_prefix("RigidTy.alias \""))
                .or_else(|| trimmed.strip_prefix(".alias \""))
                && let Some(end_q) = after.find('"')
            {
                let adt_path = &after[..end_q];
                let rest_args = after[end_q + 1..].trim();
                if let Some(raw_args) = parse_lean_list_expr(rest_args) {
                    let args: Vec<String> = raw_args
                        .into_iter()
                        .map(|e| lean_rigid_ty_to_rust_with_override(e, param_t_override))
                        .collect();
                    if args.is_empty() {
                        adt_path.to_string()
                    } else {
                        format!("{adt_path}<{}>", args.join(", "))
                    }
                } else {
                    adt_path.to_string()
                }
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.dynamic \"")
                .or_else(|| trimmed.strip_prefix(".dynamic \""))
                && let Some(end_q) = after.find('"')
            {
                format!("dyn {}", &after[..end_q])
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.foreign \"")
                .or_else(|| trimmed.strip_prefix(".foreign \""))
                && let Some(end_q) = after.find('"')
            {
                after[..end_q].to_string()
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.fnPtr ")
                .or_else(|| trimmed.strip_prefix(".fnPtr "))
                && let Some((before_conv, conv_tok)) = split_last_balanced_token(after)
                && let Some((before_safety, safety_tok)) = split_last_balanced_token(before_conv)
                && let Some((inputs_expr, output_expr)) = split_last_balanced_token(before_safety)
                && let Some(raw_inputs) = parse_lean_list_expr(inputs_expr)
            {
                let inputs: Vec<String> = raw_inputs
                    .into_iter()
                    .map(|e| lean_rigid_ty_to_rust_with_override(e, param_t_override))
                    .collect();
                let out_ty = lean_rigid_ty_to_rust_with_override(output_expr, param_t_override);
                let abi_part = extract_lean_call_conv(conv_tok)
                    .map(|a| format!("extern \"{a}\" "))
                    .unwrap_or_default();
                let prefix = if safety_tok.contains("unsafe") {
                    format!("unsafe {abi_part}fn")
                } else {
                    format!("{abi_part}fn")
                };
                if out_ty == "()" {
                    format!("{prefix}({})", inputs.join(", "))
                } else {
                    format!("{prefix}({}) -> {out_ty}", inputs.join(", "))
                }
            } else if let Some(after) = trimmed
                .strip_prefix("RigidTy.param ")
                .or_else(|| trimmed.strip_prefix(".param "))
                && let Some(q1) = after.find('"')
                && let Some(q2) = after[q1 + 1..].find('"')
            {
                let param_name = &after[q1 + 1..q1 + 1 + q2];
                if param_name == "T"
                    && let Some(override_ty) = param_t_override
                {
                    override_ty.to_string()
                } else {
                    param_name.to_string()
                }
            } else {
                "usize".to_string()
            }
        }
    }
}

fn parse_extern_abi_from_header(header: &str) -> Option<String> {
    for (idx, _) in header.match_indices("extern") {
        let before_ok = header[..idx]
            .chars()
            .next_back()
            .is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'));
        let after = &header[idx + "extern".len()..];
        let after_ok = after
            .chars()
            .next()
            .is_none_or(|c| c.is_whitespace() || c == '"');
        if before_ok && after_ok {
            let trimmed = after.trim_start();
            if let Some(rest_q) = trimmed.strip_prefix('"')
                && let Some(end_q) = rest_q.find('"')
            {
                let abi = &rest_q[..end_q];
                if !abi.is_empty() && !abi.eq_ignore_ascii_case("Rust") {
                    return Some(abi.to_string());
                }
                return None;
            }
            return Some("C".to_string());
        }
    }
    None
}

fn extract_rust_fn_abi(prefix: &str) -> Option<String> {
    let item_start = prefix.rfind(['{', '}', ';']).map(|i| i + 1).unwrap_or(0);
    if let Some(abi) = parse_extern_abi_from_header(&prefix[item_start..]) {
        return Some(abi);
    }
    let mut depth = 0usize;
    let mut in_quotes = false;
    let mut open_brace_idx = None;
    for (idx, ch) in prefix.char_indices().rev() {
        if ch == '"' {
            in_quotes = !in_quotes;
            continue;
        }
        if in_quotes {
            continue;
        }
        if ch == '}' {
            depth += 1;
        } else if ch == '{' {
            if depth == 0 {
                open_brace_idx = Some(idx);
                break;
            }
            depth -= 1;
        }
    }
    if let Some(brace_pos) = open_brace_idx {
        let block_before = &prefix[..brace_pos];
        let hdr_start = block_before
            .rfind(['{', '}', ';'])
            .map(|i| i + 1)
            .unwrap_or(0);
        return parse_extern_abi_from_header(&block_before[hdr_start..]);
    }
    None
}

fn find_signature_in_rust_sources(
    workspace_root: &Path,
    short_ident: &str,
) -> Option<(Option<String>, Vec<String>, Vec<(String, String)>, String)> {
    if short_ident.is_empty() {
        return None;
    }
    let src_dir = workspace_root.join("src");
    let mut rs_files = Vec::new();
    collect_rs_files(&src_dir, &mut rs_files);
    rs_files.sort();
    let needle = format!("fn {short_ident}");
    for file in &rs_files {
        let Ok(txt) = fs::read_to_string(file) else {
            continue;
        };
        // Match `fn <short_ident>` only as a whole item name: the preceding
        // character must not continue an identifier and the following one must
        // open the generic or parameter list, so that `fn helper` does not
        // match `fn helper_add` or `my_fn helper`.
        let found = txt.match_indices(&needle).find(|&(pos, _)| {
            let before_ok = txt[..pos]
                .chars()
                .next_back()
                .is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'));
            let after_ok = txt[pos + needle.len()..]
                .chars()
                .find(|c| !c.is_whitespace())
                .is_some_and(|c| c == '(' || c == '<');
            before_ok && after_ok
        });
        if let Some((pos, _)) = found {
            let abi = extract_rust_fn_abi(&txt[..pos]);
            let after = &txt[pos + needle.len()..];
            let open_paren = after.find('(')?;
            let mut generics = Vec::new();
            let before_paren = after[..open_paren].trim();
            if before_paren.starts_with('<') && before_paren.ends_with('>') {
                let inner_gen = &before_paren[1..before_paren.len() - 1];
                for part in split_top_level_comma(inner_gen) {
                    let clean = part.split(':').next().unwrap_or(part).trim();
                    if !clean.is_empty() && !clean.starts_with('\'') {
                        generics.push(clean.to_string());
                    }
                }
            }
            let mut paren_depth = 0usize;
            let mut close_paren = None;
            for (idx, ch) in after[open_paren..].char_indices() {
                match ch {
                    '(' => paren_depth += 1,
                    ')' => {
                        paren_depth = paren_depth.saturating_sub(1);
                        if paren_depth == 0 {
                            close_paren = Some(open_paren + idx);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let close_paren = close_paren?;
            let raw_params = &after[open_paren + 1..close_paren];
            let mut params = Vec::new();
            for (idx, part) in split_top_level_comma(raw_params).into_iter().enumerate() {
                let p = part.trim();
                if p.is_empty() {
                    continue;
                }
                if let Some((name, ty)) = p.split_once(':') {
                    let clean_name = name.trim().trim_start_matches("mut ").trim();
                    params.push((clean_name.to_string(), ty.trim().to_string()));
                } else if p.contains("self") {
                    params.push((
                        "this".to_string(),
                        p.replace("self", "Self").trim().to_string(),
                    ));
                } else {
                    params.push((format!("arg{}", idx + 1), p.to_string()));
                }
            }
            let after_paren = &after[close_paren + 1..];
            let end_sig = after_paren.find(['{', ';']).unwrap_or(after_paren.len());
            let sig_tail = after_paren[..end_sig].trim();
            let ret_ty = if let Some(ret) = sig_tail.strip_prefix("->") {
                ret.split("where").next().unwrap_or(ret).trim().to_string()
            } else {
                "()".to_string()
            };
            return Some((abi, generics, params, ret_ty));
        }
    }
    None
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

fn builtin_core_signature(
    raw_target: &str,
    normalized_target: &str,
) -> Option<(Vec<String>, Vec<(String, String)>, String)> {
    let collapsed_raw = raw_target
        .split_whitespace()
        .collect::<String>()
        .replace("::<impl[", "::<impl [");
    let explicit_elem = collapsed_raw
        .strip_prefix("<[")
        .and_then(|r| r.split_once("]>::"))
        .map(|(t, _)| t.trim())
        .or_else(|| {
            collapsed_raw
                .strip_prefix("core::slice::<impl [")
                .or_else(|| collapsed_raw.strip_prefix("std::slice::<impl ["))
                .and_then(|r| r.split_once("]>::"))
                .map(|(t, _)| t.trim())
        })
        .filter(|t| !t.is_empty());
    let (generics, elem_ty) = match explicit_elem {
        Some("T") => (vec!["T".to_string()], "T"),
        Some(ty) => (Vec::new(), ty),
        None => (Vec::new(), "u8"),
    };
    let (params, ret_ty) = match normalized_target {
        "core::slice::<impl [T]>::len" => (
            vec![("slice".to_string(), format!("&[{elem_ty}]"))],
            "usize".to_string(),
        ),
        "core::slice::<impl [T]>::is_empty" => (
            vec![("slice".to_string(), format!("&[{elem_ty}]"))],
            "bool".to_string(),
        ),
        "core::slice::<impl [T]>::as_ptr" => (
            vec![("slice".to_string(), format!("&[{elem_ty}]"))],
            format!("*const {elem_ty}"),
        ),
        "core::slice::<impl [T]>::as_mut_ptr" => (
            vec![("slice".to_string(), format!("&mut [{elem_ty}]"))],
            format!("*mut {elem_ty}"),
        ),
        "core::slice::from_raw_parts" => (
            vec![
                ("data".to_string(), format!("*const {elem_ty}")),
                ("len".to_string(), "usize".to_string()),
            ],
            format!("&'static [{elem_ty}]"),
        ),
        "core::slice::from_raw_parts_mut" => (
            vec![
                ("data".to_string(), format!("*mut {elem_ty}")),
                ("len".to_string(), "usize".to_string()),
            ],
            format!("&'static mut [{elem_ty}]"),
        ),
        _ => return None,
    };
    Some((generics, params, ret_ty))
}

/// Run extraction, optional `.anneal/spec-lock.json` enforcement, deterministic
/// `.anneal/generated/` regeneration, Lake kernel checking, and
/// `TrustedBoundary` auditing according to `options`.
pub fn verify_workspace_with_options(options: &CliOptions) -> Result<VerificationReport, String> {
    let (_manifest, records) = run_extract_phase(options)?;
    let enforce_lock =
        options.locked_specs || options.subcommand == CliSubcommand::AgentVerify;

    let (locked_manifest, has_locked_ub_exceptions) = if enforce_lock {
        let lock = agent::verify_spec_lock_with_units_dir(
            &options.workspace_root,
            &records,
            options.lock_file.as_deref(),
            options.lock_git_ref.as_deref(),
            Some(&options.units_dir),
        )?;
        let has_ub_exc = lock.locked_specs_files.iter().any(|entry| {
            fs::read_to_string(options.workspace_root.join(&entry.rel_path))
                .ok()
                .is_some_and(|txt| {
                    txt.contains("UbExceptionItemSpec") || txt.contains("refineUbExceptionSpec")
                })
        });
        if lock.locked_assumptions_files.is_empty()
            && !has_ub_exc
            && options.allow_assumptions
        {
            return Err(
                "spec-lock violation: --allow-assumptions is forbidden because .anneal/spec-lock.json locks zero Assumptions files"
                    .to_string(),
            );
        }
        let generated_dir = options.workspace_root.join(".anneal/generated");
        let _ = fs::remove_dir_all(generated_dir.join("Obligations"));
        let _ = fs::remove_dir_all(generated_dir.join("Verify"));
        (Some(lock), has_ub_exc)
    } else {
        (None, false)
    };

    let scaffold_cfg = ScaffoldConfig {
        workspace_root: options.workspace_root.clone(),
        units_dir: Some(options.units_dir.clone()),
        anneal_repo_root: options.anneal_repo_root.clone(),
        init_spec_templates: if enforce_lock {
            false
        } else {
            options.init_specs
        },
        init_proof_templates: if enforce_lock {
            false
        } else {
            options.init_proofs
        },
    };
    scaffold_workspace_with_config(&scaffold_cfg, &records)?;

    if enforce_lock {
        verify_generated_mir_digests(&options.workspace_root, &records)?;
    } else {
        check_specs_non_vacuous_with_records(&options.workspace_root, &records)?;
    }

    let has_locked_rust_trusted = locked_manifest.as_ref().is_some_and(|lock| {
        lock.locked_records.iter().any(|r| {
            r.def_id
                .contains("__ANNEAL_EXT_SPEC_TARGET___anneal_attr_trusted_")
        })
    });

    let effective_allow_assumptions = match &locked_manifest {
        Some(lock) => {
            if !lock.locked_assumptions_files.is_empty() || has_locked_rust_trusted {
                options.allow_assumptions
            } else {
                has_locked_ub_exceptions
            }
        }
        None => options.allow_assumptions,
    };

    let verify_cfg = VerifyConfig {
        workspace_root: options.workspace_root.clone(),
        units_dir: Some(options.units_dir.clone()),
        anneal_repo_root: options.anneal_repo_root.clone(),
        allow_assumptions: effective_allow_assumptions,
        allow_provisional_native: options.allow_provisional_native,
        item_filter: options.item_filter.clone(),
        property_registry: None,
        simulated_dropped_fault_sites: std::collections::BTreeSet::new(),
    };
    let report = verify_workspace_with_config(&verify_cfg)?;

    if let Some(ref lock) = locked_manifest
        && lock.locked_assumptions_files.is_empty()
        && !has_locked_rust_trusted
    {
        for item in &report.items {
            if let VerificationStatus::VerifiedConditional { ref assumptions } = item.status {
                return Err(format!(
                    "spec-lock violation: item '{}' is VerifiedConditional ({}) when .anneal/spec-lock.json locks zero Assumptions files",
                    item.verify_module,
                    assumptions.join(", ")
                ));
            }
        }
    }

    Ok(report)
}

fn verify_generated_mir_digests(
    workspace_root: &Path,
    records: &[anneal_rustc_capture::UnitTargetRecord],
) -> Result<(), String> {
    let generated_mir_root = workspace_root.join(".anneal/generated/Mir");
    for record in records {
        if record.target.mir_module_sha256.is_empty() {
            continue;
        }
        let suffix = derive_item_module_suffix(record);
        let rel_path = module_suffix_to_rel_path(&suffix);
        let placed_path = generated_mir_root.join(&rel_path);
        let bytes = fs::read(&placed_path).map_err(|err| {
            format!(
                "failed to read generated MIR module {}: {}",
                placed_path.display(),
                err
            )
        })?;
        let actual_hash = anneal_rustc_capture::sha256_hex(&bytes);
        if actual_hash != record.target.mir_module_sha256 {
            return Err(format!(
                "spec-lock violation: generated MIR file {} failed SHA-256 verification (expected {}, got {})",
                placed_path.display(),
                record.target.mir_module_sha256,
                actual_hash
            ));
        }
    }
    Ok(())
}

fn run_extract_phase(
    options: &CliOptions,
) -> Result<
    (
        anneal_rustc_capture::CaptureManifest,
        Vec<anneal_rustc_capture::UnitTargetRecord>,
    ),
    String,
> {
    let default_units = options
        .workspace_root
        .join("target")
        .join("anneal")
        .join("units");
    let has_cargo_manifest = options
        .manifest_path
        .as_ref()
        .is_some_and(|mp| mp.is_file())
        || options.workspace_root.join("Cargo.toml").is_file();
    let use_precaptured_units = options.from_existing_units
        || (options.subcommand != CliSubcommand::Extract
            && driver::has_captured_unit_manifests(&options.units_dir)
            && (!has_cargo_manifest || options.units_dir != default_units));

    if use_precaptured_units {
        load_captured_unit_records(&options.units_dir)
    } else {
        let driver_cfg = CaptureDriverConfig {
            workspace_root: options.workspace_root.clone(),
            manifest_path: options.manifest_path.clone(),
            units_dir: options.units_dir.clone(),
            rustc_wrapper: options.rustc_wrapper.clone(),
            filter: options.filter.clone(),
            extra_cargo_args: options.extra_cargo_args.clone(),
        };
        invoke_cargo_capture(&driver_cfg)
    }
}

/// Synchronize generated assembly modules in `<workspace_root>/.anneal`, invoke
/// `lake build`, and run the strict `TrustedBoundary` anti-cheat audit
/// (`allow_assumptions == false`).
pub fn verify_workspace(workspace_root: &Path) -> Result<VerificationReport, String> {
    let config = VerifyConfig::new(workspace_root);
    verify_workspace_with_config(&config)
}

/// Synchronize generated assembly modules in `<config.workspace_root>/.anneal`,
/// invoke `lake build`, and run the `TrustedBoundary` anti-cheat audit plus
/// fault-site coverage reconciliation (`reconcile_multi_item_coverage`)
/// according to `config`.
pub fn verify_workspace_with_config(config: &VerifyConfig) -> Result<VerificationReport, String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let workspace_root = normalize_path_against(&base_dir, &config.workspace_root);
    let anneal_repo_root = config
        .anneal_repo_root
        .as_deref()
        .map(|r| normalize_path_against(&base_dir, r));
    if let Some(ref raw_units_dir) = config.units_dir {
        let units_dir = normalize_path_against(&base_dir, raw_units_dir);
        if !workspace_root.join(".anneal/generated/Verify").is_dir()
            && driver::has_captured_unit_manifests(&units_dir)
        {
            let (_manifest, records) = load_captured_unit_records(&units_dir)?;
            let scaffold_cfg = ScaffoldConfig {
                workspace_root: workspace_root.clone(),
                units_dir: Some(units_dir),
                anneal_repo_root: anneal_repo_root.clone(),
                init_spec_templates: false,
                init_proof_templates: false,
            };
            scaffold_workspace_with_config(&scaffold_cfg, &records)?;
        }
    }
    refresh_workspace_assembly(&workspace_root)?;
    let dot_anneal = workspace_root.join(".anneal");
    let matched_targets = resolve_filtered_verify_modules(&workspace_root, config.item_filter.as_deref())?;
    if config.item_filter.is_some() {
        run_lake_verify_targets(&dot_anneal, &matched_targets)?;
    } else {
        run_lake_verify(&dot_anneal)?;
    }
    let mut report = run_trusted_boundary_verify_audit_with_options(
        &workspace_root,
        anneal_repo_root.as_deref(),
        config.allow_assumptions,
        config.allow_provisional_native,
        config.item_filter.as_deref(),
        &matched_targets,
    )?;
    let effective_registry = config
        .property_registry
        .clone()
        .unwrap_or_else(PropertyRegistry::all_verified);
    apply_fault_site_coverage_reconciliation(
        &workspace_root,
        &mut report,
        &effective_registry,
        &config.simulated_dropped_fault_sites,
    );
    Ok(report)
}

/// Parse the `def defaultCallees : List CapturedMir := ...` table of a generated
/// `Obligations/<Item>.lean` module into the `Mir.<Callee>` module suffixes it links
/// into `s.memory.callees` (`[Mir.<A>.body, Mir.<B>.body]` or `.nil`).
///
/// `[adv ep1-B1]` / `[adv ep1-A1]`: delegates to the comment- and string-aware Lean
/// lexer parser [`fault_census::parse_obligations_default_callees`] so comments can
/// never inject or duplicate a `defaultCallees` table.
fn extract_default_callee_suffixes_from_obligations(ob_text: &str) -> Result<Vec<String>, String> {
    fault_census::parse_obligations_default_callees(ob_text)
}

/// Resolve the explicit external callees of a generated `Obligations/<Item>.lean`
/// module: `#[external_spec]` targets bound by `externalSpecCallContract` and the
/// `DefPath`s of sibling `called_callees` imported as `Obligations.<Callee>`
/// (including `#[spec(trusted)]` siblings), read strictly from their
/// `Mir/<Callee>.lean`.
///
/// `[adv ep1-A2]`: fails closed (`Err`) on self-imports (`Obligations.<Item>`),
/// unused `import Obligations.<Callee>` headers without a corresponding
/// `Obligations.<Callee>.defaultCallContract` reference (or vice versa), and
/// missing or malformed/comment-spoofed sibling `Mir/<Callee>.lean` modules.
fn extract_external_callee_def_paths_from_obligations(
    subject_suffix: &str,
    links: &fault_census::ObligationsCalleeLinks,
    mir_root: &Path,
    obligations_root: &Path,
) -> Result<Vec<String>, String> {
    if !links.unlinked_external_spec_errors.is_empty()
        || links.external_spec_contracts.len() < links.external_spec_targets.len()
    {
        return Err(format!(
            "Obligations module for {subject_suffix} contains unlinked or malformed `externalSpecCallContract` expressions: {:?}",
            links.unlinked_external_spec_errors
        ));
    }
    let mut out = Vec::new();
    for ext in &links.external_spec_contracts {
        if ext.sidecar_mir_suffix == subject_suffix {
            return Err(format!(
                "Obligations module for {subject_suffix} binds `externalSpecCallContract` `{}` to its own MIR body `Mir.{subject_suffix}.body`",
                ext.def_ident
            ));
        }
        if !links
            .imported_mir_suffixes
            .iter()
            .any(|m| m == &ext.sidecar_mir_suffix)
        {
            return Err(format!(
                "Obligations module for {subject_suffix} binds `externalSpecCallContract` `{}` to `Mir.{}.body` without `import Mir.{}`",
                ext.def_ident, ext.sidecar_mir_suffix, ext.sidecar_mir_suffix
            ));
        }
        if !links
            .referenced_external_contract_idents
            .iter()
            .any(|r| r == &ext.def_ident)
        {
            return Err(format!(
                "Obligations module for {subject_suffix} declares `def {}` (`externalSpecCallContract \"{}\"`) without referencing `{}.holdsOn`",
                ext.def_ident, ext.target_def_path, ext.def_ident
            ));
        }
        let sidecar_mir_path = mir_root.join(module_suffix_to_rel_path(&ext.sidecar_mir_suffix));
        let sidecar_src = fs::read_to_string(&sidecar_mir_path).map_err(|err| {
            format!(
                "missing sidecar MIR module {} for `externalSpecCallContract` `{}`: {err}",
                sidecar_mir_path.display(),
                ext.def_ident
            )
        })?;
        let sidecar_meta = fault_census::parse_lean_mir_module_metadata_strict(&sidecar_src)
            .map_err(|err| {
                format!(
                    "MIR fault-census scan error in sidecar {}: {err}",
                    ext.sidecar_mir_suffix
                )
            })?;
        if sidecar_meta.body.def_path.is_empty() {
            return Err(format!(
                "sidecar MIR module {} has an empty `defPath`",
                sidecar_mir_path.display()
            ));
        }
        match &sidecar_meta.role {
            fault_census::ProtoContractRole::ExternalSpec(role_target)
                if role_target == &ext.target_def_path => {}
            other_role => {
                return Err(format!(
                    "sidecar `Mir.{}` for `externalSpecCallContract \"{}\"` has role `{other_role:?}` instead of `ContractRole.externalSpec \"{}\"`",
                    ext.sidecar_mir_suffix, ext.target_def_path, ext.target_def_path
                ));
            }
        }
        if !out.contains(&ext.target_def_path) {
            out.push(ext.target_def_path.clone());
        }
    }
    for callee_suffix in &links.imported_obligation_suffixes {
        if callee_suffix == subject_suffix {
            return Err(format!(
                "Obligations module for {subject_suffix} self-imports `Obligations.{callee_suffix}`"
            ));
        }
        if !links
            .referenced_callee_contracts
            .iter()
            .any(|c| c == callee_suffix)
        {
            return Err(format!(
                "Obligations module for {subject_suffix} imports `Obligations.{callee_suffix}` without referencing `Obligations.{callee_suffix}.defaultCallContract`"
            ));
        }
        let callee_ob_path = obligations_root.join(module_suffix_to_rel_path(callee_suffix));
        if !callee_ob_path.is_file() {
            return Err(format!(
                "missing sibling Obligations module {} for `import Obligations.{callee_suffix}`",
                callee_ob_path.display()
            ));
        }
        let callee_mir_path = mir_root.join(module_suffix_to_rel_path(callee_suffix));
        let src = fs::read_to_string(&callee_mir_path).map_err(|err| {
            format!(
                "missing MIR module {} for imported sibling `Obligations.{callee_suffix}`: {err}",
                callee_mir_path.display()
            )
        })?;
        let cbody = parse_lean_mir_module_body_strict(&src).map_err(|err| {
            format!(
                "MIR fault-census scan error in imported sibling callee {callee_suffix}: {err}"
            )
        })?;
        if cbody.def_path.is_empty() {
            return Err(format!(
                "imported sibling callee {callee_suffix} has an empty `defPath` in {}",
                callee_mir_path.display()
            ));
        }
        if !out.contains(&cbody.def_path) {
            out.push(cbody.def_path);
        }
    }
    for contract_callee in &links.referenced_callee_contracts {
        if !links
            .imported_obligation_suffixes
            .iter()
            .any(|c| c == contract_callee)
        {
            return Err(format!(
                "Obligations module for {subject_suffix} references `Obligations.{contract_callee}.defaultCallContract` without `import Obligations.{contract_callee}`"
            ));
        }
    }
    Ok(out)
}

fn unmapped_fault_site_status(reason: String) -> VerificationStatus {
    VerificationStatus::UnknownUnmappedFaultSite {
        missing_sites: Vec::new(),
        unemitted_classes: Vec::new(),
        reason,
    }
}

/// Fail closed (`Err`) when any audited item was downgraded to
/// `VerificationStatus::UnknownUnmappedFaultSite` by fault-site coverage
/// reconciliation, so `cargo anneal verify` / `agent-verify` never exit
/// successfully on an unreconciled item.
pub fn ensure_fault_site_coverage_reconciled(report: &VerificationReport) -> Result<(), String> {
    let unmapped: Vec<String> = report
        .items
        .iter()
        .filter_map(|item| match &item.status {
            VerificationStatus::UnknownUnmappedFaultSite { reason, .. } => Some(format!(
                "{}: UNKNOWN(UNMAPPED_FAULT_SITE) ({reason})",
                item.verify_module
            )),
            _ => None,
        })
        .collect();
    if unmapped.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "fault-site coverage reconciliation failed: {}",
            unmapped.join(", ")
        ))
    }
}

fn apply_fault_site_coverage_reconciliation(
    workspace_root: &Path,
    report: &mut VerificationReport,
    registry: &PropertyRegistry,
    dropped_sites: &std::collections::BTreeSet<FaultSite>,
) {
    let generated_root = workspace_root.join(".anneal/generated");
    let mir_root = generated_root.join("Mir");
    let obligations_root = generated_root.join("Obligations");

    for item in &mut report.items {
        // Crate-level rollups (`CrateVerify`) carry no subject body of their own;
        // every item they aggregate is reconciled through its own `Verify.<Item>`.
        let Some(suffix) = item.verify_module.strip_prefix("Verify.").map(str::to_string) else {
            continue;
        };
        // `[adv ep1-B1]`: only the subject's *own* `#[spec(trusted)]` contract
        // (`Assumptions.<Item>.rust_trusted_contract`) or a UB-exception claim relaxes
        // callee closure. An item that merely depends on some trusted callee's
        // contract is still strictly reconciled against `Mir/<Item>.lean` +
        // `defaultCallees`, and modular (`MirCallE`) items get no implicit externals:
        // every non-inline callee must be an `#[external_spec]` contract or an
        // imported sibling `Obligations.<Callee>`.
        let own_trusted_contract = format!("Assumptions.{suffix}.rust_trusted_contract");
        let subject_is_assumed = match &item.status {
            VerificationStatus::VerifiedConditional { assumptions } => {
                assumptions.iter().any(|a| a == &own_trusted_contract)
            }
            VerificationStatus::VerifiedUbException { .. } => true,
            _ => false,
        };

        let rel_path = module_suffix_to_rel_path(&suffix);
        let mir_path = mir_root.join(&rel_path);
        let ob_path = obligations_root.join(&rel_path);
        let verify_path = generated_root.join("Verify").join(&rel_path);

        // Fail closed: every audited per-item module must have its captured body.
        let subject_mir_src = match fs::read_to_string(&mir_path) {
            Ok(src) => src,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!(
                    "missing MIR module {} for {suffix}: {err}",
                    mir_path.display()
                ));
                continue;
            }
        };
        let subject_meta = match fault_census::parse_lean_mir_module_metadata_strict(&subject_mir_src)
        {
            Ok(meta) => meta,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!(
                    "MIR fault-census scan error in {suffix}: {err}"
                ));
                continue;
            }
        };
        if subject_meta.body.def_path.is_empty() {
            item.status = unmapped_fault_site_status(format!(
                "subject MIR module {} for {suffix} has an empty `defPath`",
                mir_path.display()
            ));
            continue;
        }
        let verify_text = match fs::read_to_string(&verify_path) {
            Ok(text) => text,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!(
                    "missing Verify module {} for {suffix}: {err}",
                    verify_path.display()
                ));
                continue;
            }
        };
        if let Err(err) = fault_census::validate_verify_module_certificate(&verify_text, &suffix) {
            item.status = unmapped_fault_site_status(err);
            continue;
        }
        let ob_text = match fs::read_to_string(&ob_path) {
            Ok(text) => text,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!(
                    "missing Obligations module {} for {suffix}: {err}",
                    ob_path.display()
                ));
                continue;
            }
        };

        let callee_suffixes = match extract_default_callee_suffixes_from_obligations(&ob_text) {
            Ok(suffixes) => suffixes,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!("{suffix}: {err}"));
                continue;
            }
        };
        let links = match fault_census::scan_obligations_callee_links(&ob_text) {
            Ok(links) => links,
            Err(err) => {
                item.status = unmapped_fault_site_status(format!(
                    "Obligations module for {suffix} failed the Lean lexer: {err}"
                ));
                continue;
            }
        };
        // The emitted claim must be about this very body: if the Obligations module
        // never references `Mir.<Item>.body` or any claim record binds `body :=` /
        // `implBody :=` to another body, nothing in it discharges the subject's sites.
        let claim_covers_subject = links.referenced_mir_bodies.iter().any(|s| s == &suffix)
            && !links.claim_mir_bodies.is_empty()
            && links.non_mir_claim_bodies.is_empty()
            && links.claim_mir_bodies.iter().all(|s| s == &suffix);
        if !claim_covers_subject {
            item.status = unmapped_fault_site_status(format!(
                "Obligations module for {suffix} never references `Mir.{suffix}.body` across all claim definitions (claim_mir_bodies={:?}, non_mir={:?}), so no emitted obligation discharges its fault sites",
                links.claim_mir_bodies, links.non_mir_claim_bodies
            ));
            continue;
        }
        // Every claim record must bind `callees := defaultCallees` (or `implCallees := defaultCallees`,
        // `specCallees := defaultCallees`) and `claim_body_field_count == claim_callees_field_count`
        // so a claim cannot omit `callees` / `specCallees` or bypass `defaultCallees` with `.nil`,
        // `[]`, or a trailing expression (`defaultCallees.drop 1`).
        if links.claim_callees_bindings.is_empty()
            || links.claim_body_field_count != links.claim_callees_field_count
            || !links
                .claim_callees_bindings
                .iter()
                .all(|b| b == "defaultCallees")
        {
            item.status = unmapped_fault_site_status(format!(
                "Obligations module for {suffix} overrides claim `callees` (bindings={:?}, body_fields={}, callees_fields={}) instead of `defaultCallees`",
                links.claim_callees_bindings,
                links.claim_body_field_count,
                links.claim_callees_field_count
            ));
            continue;
        }
        // `[adv ep1-B3]`: enforce per-definition canonical claim structure across all 16
        // monomorphic, equivalence, instantiated (`*For`), and polymorphic (`poly*`)
        // claim definitions so positional `Claim.mk` / `⟨...⟩` constructors, `{ ... with ... }`
        // struct updates, or tampered `poly*Claim` propositions cannot slip past global
        // field-count equality.
        if let Err(err) = fault_census::validate_obligations_canonical_claims(&ob_text, &suffix) {
            item.status = unmapped_fault_site_status(err);
            continue;
        }
        let explicit_external = match extract_external_callee_def_paths_from_obligations(
            &suffix,
            &links,
            &mir_root,
            &obligations_root,
        ) {
            Ok(ext) => ext,
            Err(err) => {
                item.status = unmapped_fault_site_status(err);
                continue;
            }
        };

        let mut callee_metas = Vec::new();
        let mut scan_err_reasons = Vec::new();
        for callee_suffix in callee_suffixes {
            let callee_rel = module_suffix_to_rel_path(&callee_suffix);
            let callee_mir_path = mir_root.join(&callee_rel);
            let callee_src = match fs::read_to_string(&callee_mir_path) {
                Ok(src) => src,
                Err(err) => {
                    scan_err_reasons.push(format!(
                        "missing MIR module for callee {callee_suffix}: {err}"
                    ));
                    continue;
                }
            };
            match fault_census::parse_lean_mir_module_metadata_strict(&callee_src) {
                Ok(cmeta) => {
                    if cmeta.body.def_path.is_empty() {
                        scan_err_reasons.push(format!(
                            "MIR module for callee {callee_suffix} has an empty `defPath`"
                        ));
                        continue;
                    }
                    callee_metas.push(cmeta);
                }
                Err(err) => {
                    scan_err_reasons.push(format!(
                        "MIR fault-census scan error in callee {callee_suffix}: {err}"
                    ));
                }
            }
        }
        if !scan_err_reasons.is_empty() {
            item.status = unmapped_fault_site_status(scan_err_reasons.join("; "));
            continue;
        }

        let callee_bodies: Vec<fault_census::ProtoMirBody> =
            callee_metas.iter().map(|m| m.body.clone()).collect();
        let closure = obligations::build_batch_callee_closure(
            &subject_meta.body,
            &callee_bodies,
            &explicit_external,
            subject_is_assumed,
        );
        let (items, extra_reasons) = obligations::assemble_batch_items_and_check_trait_closure(
            &subject_meta,
            &callee_metas,
            &closure,
            dropped_sites,
        );
        if !extra_reasons.is_empty() {
            item.status = unmapped_fault_site_status(extra_reasons.join("; "));
            continue;
        }

        let verdict = reconcile_multi_item_coverage(&items, &closure, registry);
        if let MultiItemCoverageVerdict::UnknownUnmappedFaultSite {
            failed_items,
            unsupported_reasons,
        } = verdict
        {
            let mut missing_sites = Vec::new();
            let mut unemitted_set = std::collections::BTreeSet::new();
            for (_def_path, item_verdict) in failed_items {
                if let CoverageVerdict::UnknownUnmappedFaultSite {
                    missing_sites: m_sites,
                    unemitted_classes: u_classes,
                    ..
                } = item_verdict
                {
                    for s in m_sites {
                        if !missing_sites.contains(&s) {
                            missing_sites.push(s);
                        }
                    }
                    unemitted_set.extend(u_classes);
                }
            }
            item.status = VerificationStatus::UnknownUnmappedFaultSite {
                missing_sites,
                unemitted_classes: unemitted_set.into_iter().collect(),
                reason: unsupported_reasons.join("; "),
            };
        }
    }
}

fn resolve_filtered_verify_modules(
    workspace_root: &Path,
    item_filter: Option<&str>,
) -> Result<Vec<String>, String> {
    let verify_root = workspace_root.join(".anneal/generated/Verify");
    let mut verify_files = Vec::new();
    collect_lean_files_recursive(&verify_root, &mut verify_files)?;
    verify_files.sort();

    let patterns: Vec<&str> = item_filter
        .map(|f| {
            f.split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect()
        })
        .unwrap_or_default();

    let mut modules = Vec::new();
    for vf in &verify_files {
        let rel = vf
            .strip_prefix(&verify_root)
            .map_err(|err| format!("failed to strip verify prefix: {err}"))?;
        let suffix = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");
        let mod_name = format!("Verify.{suffix}");
        if patterns.is_empty() {
            modules.push(mod_name);
        } else {
            let def_id = fs::read_to_string(vf)
                .ok()
                .and_then(|t| {
                    t.lines()
                        .find_map(|l| l.strip_prefix("-- @anneal-def-id: ").map(|r| r.trim().to_string()))
                })
                .unwrap_or_default();
            if patterns
                .iter()
                .any(|pat| suffix.contains(pat) || mod_name.contains(pat) || def_id.contains(pat))
            {
                modules.push(mod_name);
            }
        }
    }

    if !patterns.is_empty() && modules.is_empty() {
        return Err(format!(
            "no Verify.<Item> modules matched --item '{}'",
            item_filter.unwrap_or_default()
        ));
    }
    Ok(modules)
}

/// Invoke `lake build` in `dot_anneal_dir` to type-check generated and authored
/// verification modules in Lean 4.
pub fn run_lake_verify(dot_anneal_dir: &Path) -> Result<(), String> {
    run_lake_verify_targets(dot_anneal_dir, &[])
}

/// Invoke `lake build` (optionally restricted to explicit module `targets`) in
/// `dot_anneal_dir`.
pub fn run_lake_verify_targets(dot_anneal_dir: &Path, targets: &[String]) -> Result<(), String> {
    let lake_bin = resolve_lake_binary();
    let mut cmd = build_lake_build_command(&lake_bin, dot_anneal_dir);
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

/// Parses `(MemTotal, MemAvailable)` in KiB from `/proc/meminfo` contents.
///
/// When `MemAvailable:` is absent (as on older kernels), falls back to
/// `MemFree: + Cached:`.
pub fn parse_meminfo_kib(meminfo: &str) -> (Option<u64>, Option<u64>) {
    let field = |name: &str| {
        meminfo.lines().find_map(|line| {
            line.strip_prefix(name)?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
    };
    let total = field("MemTotal:");
    let avail = field("MemAvailable:").or_else(|| {
        field("MemFree:").map(|free| free.saturating_add(field("Cached:").unwrap_or(0)))
    });
    (total, avail)
}

fn read_u64_file(path: &Path) -> Option<u64> {
    let raw = fs::read_to_string(path).ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed == "max" {
        return None;
    }
    trimmed.split_whitespace().next()?.parse::<u64>().ok()
}

fn min_opt_u64(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) => x,
        (None, y) => y,
    }
}

/// Parses non-reclaimable working-set usage (`anon + shmem`, in bytes) from
/// cgroup v2 `memory.stat` contents. Returns `None` if neither `anon` nor
/// `shmem` is present.
pub fn parse_cgroup_memory_stat_used_bytes(stat_text: &str) -> Option<u64> {
    let mut anon: Option<u64> = None;
    let mut shmem: Option<u64> = None;
    for line in stat_text.lines() {
        let mut parts = line.split_whitespace();
        let Some(key) = parts.next() else {
            continue;
        };
        let Some(val_str) = parts.next() else {
            continue;
        };
        if parts.next().is_some() {
            continue;
        }
        match key {
            "anon" => anon = val_str.parse::<u64>().ok(),
            "shmem" => shmem = val_str.parse::<u64>().ok(),
            _ => {}
        }
    }
    if anon.is_none() && shmem.is_none() {
        None
    } else {
        Some(anon.unwrap_or(0).saturating_add(shmem.unwrap_or(0)))
    }
}

/// Returns `(limit_kib, headroom_kib)` for the tightest cgroup v2 memory bound
/// between this process's cgroup (`0::<rel>` in `proc_self_cgroup`) and
/// `cgroup_root`, where headroom subtracts non-reclaimable `anon + shmem` from
/// `memory.stat` (falling back to `memory.current` when `memory.stat` is absent).
///
/// Each level's bound is the smaller of `memory.max` (the OOM-kill limit) and
/// `memory.high` (the throttling threshold above which the kernel stalls the
/// cgroup in direct reclaim), with `"max"` meaning unbounded for either file,
/// so a slice whose `memory.high` sits below its `memory.max` (as systemd
/// `user.slice` commonly configures) caps concurrency before workers thrash.
pub fn cgroup_memory_limits_kib(
    cgroup_root: &Path,
    proc_self_cgroup: &str,
) -> (Option<u64>, Option<u64>) {
    if !cgroup_root.is_dir() {
        return (None, None);
    }
    let Some(raw_rel) = proc_self_cgroup
        .lines()
        .map(str::trim)
        .find_map(|line| line.strip_prefix("0::"))
    else {
        return (None, None);
    };
    let rel = raw_rel
        .trim()
        .strip_suffix(" (deleted)")
        .unwrap_or(raw_rel.trim())
        .trim()
        .trim_start_matches('/');
    if Path::new(rel).components().any(|c| {
        matches!(
            c,
            std::path::Component::ParentDir
                | std::path::Component::RootDir
                | std::path::Component::Prefix(_)
        )
    }) {
        return (None, None);
    }

    let mut dir = if rel.is_empty() {
        cgroup_root.to_path_buf()
    } else {
        cgroup_root.join(rel)
    };

    let read_level_used = |d: &Path| -> Option<u64> {
        fs::read_to_string(d.join("memory.stat"))
            .ok()
            .and_then(|s| parse_cgroup_memory_stat_used_bytes(&s))
            .or_else(|| read_u64_file(&d.join("memory.current")))
    };

    let mut descendant_used_bytes: Option<u64> = None;
    let mut limit_kib: Option<u64> = None;
    let mut headroom_kib: Option<u64> = None;
    while dir.starts_with(cgroup_root) {
        if dir.is_dir() {
            let lvl_used = read_level_used(&dir);
            if let Some(u) = lvl_used {
                descendant_used_bytes =
                    Some(descendant_used_bytes.map_or(u, |prev| prev.max(u)));
            }
            let level_bound = min_opt_u64(
                read_u64_file(&dir.join("memory.max")),
                read_u64_file(&dir.join("memory.high")),
            );
            if let Some(bound) = level_bound {
                let used = lvl_used.or(descendant_used_bytes).unwrap_or(0);
                limit_kib = min_opt_u64(limit_kib, Some(bound / 1024));
                headroom_kib =
                    min_opt_u64(headroom_kib, Some(bound.saturating_sub(used) / 1024));
            }
        }
        if dir == cgroup_root || !dir.pop() {
            break;
        }
    }
    (limit_kib, headroom_kib)
}

/// cgroup v1 reports an unlimited `memory.limit_in_bytes` as `PAGE_COUNTER_MAX`
/// pages (`0x7FFF_FFFF_FFFF_F000` on 4 KiB-page kernels); treat anything at or
/// above 2^62 bytes as unbounded.
const CGROUP_V1_UNLIMITED_BYTES: u64 = 1 << 62;

/// Parses non-reclaimable usage (in bytes) from cgroup v1 `memory.stat`:
/// hierarchical `total_rss + total_shmem` when present, else the cgroup-local
/// `rss + shmem`. Returns `None` if none of those keys are present.
pub fn parse_cgroup_v1_memory_stat_used_bytes(stat_text: &str) -> Option<u64> {
    let mut fields: std::collections::BTreeMap<&str, u64> = std::collections::BTreeMap::new();
    for line in stat_text.lines() {
        let mut parts = line.split_whitespace();
        if let (Some(key), Some(val), None) = (parts.next(), parts.next(), parts.next())
            && let Ok(v) = val.parse::<u64>()
        {
            fields.insert(key, v);
        }
    }
    let sum = |rss: &str, shmem: &str| -> Option<u64> {
        match (fields.get(rss), fields.get(shmem)) {
            (None, None) => None,
            (r, s) => Some(r.copied().unwrap_or(0).saturating_add(s.copied().unwrap_or(0))),
        }
    };
    sum("total_rss", "total_shmem").or_else(|| sum("rss", "shmem"))
}

/// Parses `hierarchical_memory_limit` (in bytes, when `< CGROUP_V1_UNLIMITED_BYTES`)
/// from cgroup v1 `memory.stat`. In bind-mounted Kubernetes / Docker v1
/// containers whose memory cap is set on an enclosing pod cgroup rather than
/// the container leaf, `memory.limit_in_bytes` at the container mount root
/// reads `unlimited`, while `hierarchical_memory_limit` in `memory.stat`
/// exposes the effective ancestor limit.
pub fn parse_cgroup_v1_memory_stat_limit_bytes(stat_text: &str) -> Option<u64> {
    for line in stat_text.lines() {
        let mut parts = line.split_whitespace();
        if let (Some("hierarchical_memory_limit"), Some(val), None) =
            (parts.next(), parts.next(), parts.next())
            && let Ok(v) = val.parse::<u64>()
            && v < CGROUP_V1_UNLIMITED_BYTES
        {
            return Some(v);
        }
    }
    None
}

/// cgroup v1 counterpart of [`cgroup_memory_limits_kib`], used when the
/// unified hierarchy exposes no memory bound (legacy or hybrid hosts and
/// containers): walks this process's `memory` controller path (the
/// `<id>:<controllers>:<path>` line of `proc_self_cgroup` whose controller list
/// contains `memory`) from the leaf up to `memory_root` (normally
/// `/sys/fs/cgroup/memory`), reading `memory.limit_in_bytes` and subtracting
/// `memory.stat` `total_rss + total_shmem` (falling back to
/// `memory.usage_in_bytes`). As in a cgroup-namespaced v2 container, a path
/// that does not exist under the mount (because the container sees its own
/// cgroup as the root) walks up to `memory_root`, whose limit is then the
/// container's.
pub fn cgroup_v1_memory_limits_kib(
    memory_root: &Path,
    proc_self_cgroup: &str,
) -> (Option<u64>, Option<u64>) {
    if !memory_root.is_dir() {
        return (None, None);
    }
    let Some(raw_rel) = proc_self_cgroup.lines().map(str::trim).find_map(|line| {
        let mut fields = line.splitn(3, ':');
        let (_id, controllers, path) = (fields.next()?, fields.next()?, fields.next()?);
        controllers
            .split(',')
            .any(|c| c == "memory")
            .then_some(path)
    }) else {
        return (None, None);
    };
    let rel = raw_rel
        .trim()
        .strip_suffix(" (deleted)")
        .unwrap_or(raw_rel.trim())
        .trim()
        .trim_start_matches('/');
    if Path::new(rel).components().any(|c| {
        matches!(
            c,
            std::path::Component::ParentDir
                | std::path::Component::RootDir
                | std::path::Component::Prefix(_)
        )
    }) {
        return (None, None);
    }
    let mut dir = if rel.is_empty() {
        memory_root.to_path_buf()
    } else {
        memory_root.join(rel)
    };
    let mut descendant_used_bytes: Option<u64> = None;
    let mut limit_kib: Option<u64> = None;
    let mut headroom_kib: Option<u64> = None;
    while dir.starts_with(memory_root) {
        if dir.is_dir() {
            let stat_text = fs::read_to_string(dir.join("memory.stat")).ok();
            let lvl_used = stat_text
                .as_deref()
                .and_then(parse_cgroup_v1_memory_stat_used_bytes)
                .or_else(|| read_u64_file(&dir.join("memory.usage_in_bytes")));
            if let Some(u) = lvl_used {
                descendant_used_bytes = Some(descendant_used_bytes.map_or(u, |prev| prev.max(u)));
            }
            let direct_bound = read_u64_file(&dir.join("memory.limit_in_bytes"))
                .filter(|&b| b < CGROUP_V1_UNLIMITED_BYTES);
            let hier_bound = stat_text
                .as_deref()
                .and_then(parse_cgroup_v1_memory_stat_limit_bytes);
            if let Some(bound) = min_opt_u64(direct_bound, hier_bound) {
                let used = lvl_used.or(descendant_used_bytes).unwrap_or(0);
                limit_kib = min_opt_u64(limit_kib, Some(bound / 1024));
                headroom_kib =
                    min_opt_u64(headroom_kib, Some(bound.saturating_sub(used) / 1024));
            }
        }
        if dir == memory_root || !dir.pop() {
            break;
        }
    }
    (limit_kib, headroom_kib)
}

/// Computes the default Lake worker concurrency (`LEAN_NUM_THREADS`) from
/// effective total / available memory (in KiB) and logical CPU count:
/// `(effective_avail_mib / 1536).clamp(1, 6)` bounded by
/// `(effective_total_mib / 2048).max(1)` and `cpu_cores`, defaulting to `2`
/// when memory info is unavailable.
pub fn resolve_default_lake_jobs(
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    cpu_cores: usize,
) -> usize {
    let cpu_cap = cpu_cores.clamp(1, 6);
    if total_kib.is_none() && avail_kib.is_none() {
        return 2.min(cpu_cap);
    }
    let by_avail = avail_kib
        .map(|k| ((k / 1024) / 1536).clamp(1, 6) as usize)
        .unwrap_or(2);
    let by_total = total_kib
        .map(|k| ((k / 1024) / 2048).clamp(1, 6) as usize)
        .unwrap_or(6);
    by_avail.min(by_total).min(cpu_cap)
}

/// Resolves the `LEAN_NUM_THREADS` value that `build_lake_build_command` should
/// set given `CARGO_ANNEAL_LAKE_JOBS`, whether `LEAN_NUM_THREADS` is already
/// present in the caller's environment, and effective memory/CPU budgets.
///
/// - When `CARGO_ANNEAL_LAKE_JOBS` parses to an integer `>= 1`, returns
///   `Some(parsed.min(16))`.
/// - Otherwise, if `lean_num_threads_is_set` is `true`, returns `None` so the
///   caller's explicit `LEAN_NUM_THREADS` is preserved.
/// - Otherwise, returns `Some(resolve_default_lake_jobs(total_kib, avail_kib, cpu_cores))`.
pub fn resolve_lake_build_threads_env(
    cargo_anneal_lake_jobs: Option<&str>,
    lean_num_threads_is_set: bool,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    cpu_cores: usize,
) -> Option<usize> {
    if let Some(raw) = cargo_anneal_lake_jobs
        && let Ok(parsed) = raw.trim().parse::<usize>()
        && parsed >= 1
    {
        return Some(parsed.min(16));
    }
    if lean_num_threads_is_set {
        return None;
    }
    Some(resolve_default_lake_jobs(total_kib, avail_kib, cpu_cores))
}

/// Probes host `/proc/meminfo` intersected with `/proc/self/cgroup` (the
/// tighter of each level's `memory.max` / `memory.high`, minus `memory.stat`
/// `anon + shmem`; or, when the unified hierarchy exposes no bound, the cgroup
/// v1 `memory.limit_in_bytes` minus `total_rss + total_shmem`) in KiB.
pub fn probe_effective_memory_kib() -> (Option<u64>, Option<u64>) {
    let (mut total_kib, mut avail_kib) = fs::read_to_string("/proc/meminfo")
        .map(|s| parse_meminfo_kib(&s))
        .unwrap_or((None, None));
    if let Ok(self_cgroup) = fs::read_to_string("/proc/self/cgroup") {
        let (v2_limit, v2_headroom) =
            cgroup_memory_limits_kib(Path::new("/sys/fs/cgroup"), &self_cgroup);
        // Intersect with cgroup v1 (`/sys/fs/cgroup/memory`, a single non-dir stat on
        // pure v2 hosts) so both pure-v1 containers and hybrid v1+v2 hosts whose tightest
        // memory cap lives on the v1 `memory` controller hierarchy are honored.
        let (v1_limit, v1_headroom) =
            cgroup_v1_memory_limits_kib(Path::new("/sys/fs/cgroup/memory"), &self_cgroup);
        let cg_limit = min_opt_u64(v2_limit, v1_limit);
        let cg_headroom = min_opt_u64(v2_headroom, v1_headroom);
        total_kib = min_opt_u64(total_kib, cg_limit);
        avail_kib = min_opt_u64(avail_kib, cg_headroom);
    }
    (total_kib, avail_kib)
}

/// Lake environment variables that `cargo anneal` sets for `lake build` unless
/// the caller has already set them.
///
/// Every `.anneal/` workspace compiles the same `Trusted` and `Anneal`
/// libraries from the Anneal checkout, which takes about a minute per crate.
/// Lake's local artifact cache (`LAKE_ARTIFACT_CACHE`) stores build products
/// content-addressed under the Lean toolchain (or `LAKE_CACHE_DIR`), so every
/// crate after the first reuses them. `LAKE_RESTORE_ARTIFACTS` keeps a copy of
/// each artifact in the workspace's `.lake/build`, where the `TrustedBoundary`
/// audit imports `.olean` files through `LEAN_PATH`; without it the cache would
/// be the only copy. Set either variable yourself (for example
/// `LAKE_ARTIFACT_CACHE=false`) to override these defaults.
pub const LAKE_CACHE_ENV_DEFAULTS: &[(&str, &str)] = &[
    ("LAKE_ARTIFACT_CACHE", "true"),
    ("LAKE_RESTORE_ARTIFACTS", "true"),
];

fn build_lake_build_command_with_inputs(
    lake_bin: &Path,
    dot_anneal_dir: &Path,
    is_cache_env_set: impl Fn(&str) -> bool,
    cargo_lake_jobs: Option<&str>,
    lean_threads_set: bool,
    total_kib: Option<u64>,
    avail_kib: Option<u64>,
    cpu_cores: usize,
) -> Command {
    let mut cmd = Command::new(lake_bin);
    cmd.arg("build").current_dir(dot_anneal_dir);
    for (key, value) in LAKE_CACHE_ENV_DEFAULTS {
        if !is_cache_env_set(key) {
            cmd.env(key, value);
        }
    }
    if let Some(jobs) = resolve_lake_build_threads_env(
        cargo_lake_jobs,
        lean_threads_set,
        total_kib,
        avail_kib,
        cpu_cores,
    ) {
        cmd.env("LEAN_NUM_THREADS", jobs.to_string());
    }
    cmd
}

/// Build the `lake build` command for `dot_anneal_dir`, applying
/// `LAKE_CACHE_ENV_DEFAULTS` for variables the environment leaves unset and
/// bounding Lake worker concurrency via `LEAN_NUM_THREADS` (note: Lean v4.34.1
/// `lake build` has no `-j` CLI flag).
pub fn build_lake_build_command(lake_bin: &Path, dot_anneal_dir: &Path) -> Command {
    let cargo_lake_jobs = env::var("CARGO_ANNEAL_LAKE_JOBS").ok();
    let lean_threads_set = env::var_os("LEAN_NUM_THREADS").is_some();
    let has_explicit_threads = lean_threads_set
        || cargo_lake_jobs
            .as_deref()
            .and_then(|s| s.trim().parse::<usize>().ok())
            .is_some_and(|n| n >= 1);
    let (total_kib, avail_kib) = if has_explicit_threads {
        (None, None)
    } else {
        probe_effective_memory_kib()
    };
    let cpu_cores = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4);
    build_lake_build_command_with_inputs(
        lake_bin,
        dot_anneal_dir,
        |key| env::var_os(key).is_some(),
        cargo_lake_jobs.as_deref(),
        lean_threads_set,
        total_kib,
        avail_kib,
        cpu_cores,
    )
}

pub(crate) fn run_trusted_boundary_verify_audit(
    workspace_root: &Path,
    anneal_repo_root: Option<&Path>,
    allow_assumptions: bool,
    item_filter: Option<&str>,
    verify_modules: &[String],
) -> Result<VerificationReport, String> {
    run_trusted_boundary_verify_audit_with_options(
        workspace_root,
        anneal_repo_root,
        allow_assumptions,
        false,
        item_filter,
        verify_modules,
    )
}

pub(crate) fn run_trusted_boundary_verify_audit_with_options(
    workspace_root: &Path,
    anneal_repo_root: Option<&Path>,
    allow_assumptions: bool,
    allow_provisional_native: bool,
    item_filter: Option<&str>,
    verify_modules: &[String],
) -> Result<VerificationReport, String> {
    let dot_anneal = workspace_root.join(".anneal");
    if verify_modules.is_empty() {
        return Ok(VerificationReport::default());
    }

    let generated_root = dot_anneal.join("generated");
    let proofs_root = workspace_root.join("anneal").join("proofs");
    let mut source_entries = Vec::new();

    let mut generated_files = Vec::new();
    collect_lean_files_recursive(&generated_root, &mut generated_files)?;
    generated_files.sort();
    for gf in &generated_files {
        let rel = gf
            .strip_prefix(&generated_root)
            .map_err(|err| format!("failed to strip generated prefix: {err}"))?;
        let mod_name = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");
        if item_filter.is_some() && mod_name == "CrateVerify" {
            continue;
        }
        source_entries.push((mod_name, gf.clone()));
    }

    let mut proof_files = Vec::new();
    collect_lean_files_recursive(&proofs_root, &mut proof_files)?;
    proof_files.sort();
    for pf in &proof_files {
        let rel = pf
            .strip_prefix(&proofs_root)
            .map_err(|err| format!("failed to strip proofs prefix: {err}"))?;
        let mod_name = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(".");
        source_entries.push((mod_name, pf.clone()));
    }

    let trusted_boundary_lean =
        resolve_trusted_boundary_lean(workspace_root, anneal_repo_root)?;
    let lake_bin = resolve_lake_binary();

    let mut cmd = Command::new(&lake_bin);
    cmd.arg("env")
        .arg("lean")
        .arg("--run")
        .arg(&trusted_boundary_lean)
        .arg("verify-audit")
        .arg(format!(
            "--allow-assumptions={}",
            if allow_assumptions { "true" } else { "false" }
        ))
        .arg(format!(
            "--allow-provisional-native={}",
            if allow_provisional_native { "true" } else { "false" }
        ))
        .arg(format!("--verify-modules={}", verify_modules.join(",")));
    if item_filter.is_none() && generated_root.join("CrateVerify.lean").is_file() {
        cmd.arg("--crate-rollup-modules=CrateVerify");
    }

    for (mod_name, src_path) in &source_entries {
        cmd.arg(format!("--source={mod_name}={}", src_path.display()));
    }
    cmd.current_dir(&dot_anneal);

    let output = cmd.output().map_err(|err| {
        format!(
            "failed to execute TrustedBoundary verify-audit via '{}': {}",
            lake_bin.display(),
            err
        )
    })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "TrustedBoundary verify-audit failed in {} (status {}):\n{}{}",
            dot_anneal.display(),
            output.status,
            stdout,
            stderr
        ));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut items = Vec::new();
    for line in stdout.lines() {
        let Some(rest) = line.strip_prefix("VERIFY_AUDIT_ITEM\t") else {
            continue;
        };
        let parts: Vec<&str> = rest.split('\t').collect();
        if parts.len() < 2 {
            continue;
        }
        let verify_module = parts[0].to_string();
        let status = match parts[1] {
            "VerifiedUnconditional" => VerificationStatus::VerifiedUnconditional,
            "VerifiedConditional" => {
                let assumptions = parts
                    .get(2)
                    .copied()
                    .unwrap_or("")
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(String::from)
                    .collect();
                VerificationStatus::VerifiedConditional { assumptions }
            }
            "VerifiedUbException" => {
                let assumptions = parts
                    .get(2)
                    .copied()
                    .unwrap_or("")
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(String::from)
                    .collect();
                VerificationStatus::VerifiedUbException { assumptions }
            }
            "ProvisionalNative" => {
                let axioms = parts
                    .get(2)
                    .copied()
                    .unwrap_or("")
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(String::from)
                    .collect();
                VerificationStatus::ProvisionalNative { axioms }
            }
            other => {
                return Err(format!(
                    "unexpected VERIFY_AUDIT_ITEM status '{other}' for {verify_module}"
                ));
            }
        };
        items.push(ItemVerificationReport {
            verify_module,
            status,
        });
    }

    Ok(VerificationReport { items })
}

fn collect_lean_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to read dir entry: {err}"))?;
        let path = entry.path();
        if path.is_dir() {
            collect_lean_files_recursive(&path, out)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
            out.push(path);
        }
    }
    Ok(())
}

/// Resolve the Anneal Lean root directory containing `trusted/lean`,
/// `trusted/audit`, and `theory` in priority order:
/// 1. `ANNEAL_REPO_ROOT` (or `ANNEAL_ROOT`) environment variable,
/// 2. `<CARGO_MANIFEST_DIR>/lean-root` (vendored Fuchsia `cargo-anneal-<ver>`),
/// 3. `<current_exe_dir>/../share/anneal` or `<current_exe_dir>/lean-root`,
/// 4. `<CARGO_MANIFEST_DIR>/../..` (Anneal Git repository checkout),
/// 5. `<installed_toolchain>/share/anneal`.
pub fn default_anneal_repo_root() -> Option<PathBuf> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let is_valid_lean_root = |dir: &Path| -> bool {
        dir.join("trusted/lean").is_dir() && dir.join("theory").is_dir()
    };

    for env_key in ["ANNEAL_REPO_ROOT", "ANNEAL_ROOT"] {
        if let Ok(env_root) = env::var(env_key)
            && !env_root.trim().is_empty()
        {
            let candidate = normalize_path_against(&base_dir, Path::new(env_root.trim()));
            if is_valid_lean_root(&candidate) {
                return Some(candidate);
            }
        }
    }

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let vendored_lean_root = manifest_dir.join("lean-root");
    if is_valid_lean_root(&vendored_lean_root) {
        return Some(vendored_lean_root);
    }

    if let Ok(current_exe) = env::current_exe()
        && let Some(exe_dir) = current_exe.parent()
    {
        if let Some(exe_parent) = exe_dir.parent() {
            let share_anneal = exe_parent.join("share/anneal");
            if is_valid_lean_root(&share_anneal) {
                return Some(share_anneal);
            }
        }
        let exe_lean_root = exe_dir.join("lean-root");
        if is_valid_lean_root(&exe_lean_root) {
            return Some(exe_lean_root);
        }
    }

    if let Some(repo_root) = manifest_dir.parent().and_then(|p| p.parent())
        && is_valid_lean_root(repo_root)
    {
        return Some(repo_root.to_path_buf());
    }

    if let Some(toolchain_root) = setup::resolve_installed_toolchain() {
        let share_anneal = toolchain_root.join("share/anneal");
        if is_valid_lean_root(&share_anneal) {
            return Some(share_anneal);
        }
    }

    None
}

/// Stage all 4 Anneal workspace crates (`anneal-spec-macros-<ver>`,
/// `anneal-spec-<ver>`, `anneal-rustc-capture-<ver>`, and `cargo-anneal-<ver>`
/// with bundled `lean-root/`) into `out_dir` for vendoring into Fuchsia's
/// `//third_party/rust_crates`.
pub fn vendor_fuchsia_crates(
    anneal_repo_root: &Path,
    out_dir: &Path,
) -> Result<Vec<PathBuf>, String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let repo_root = normalize_path_against(&base_dir, anneal_repo_root);
    let dest_root = normalize_path_against(&base_dir, out_dir);
    fs::create_dir_all(&dest_root).map_err(|err| {
        format!(
            "failed to create vendor output directory {}: {}",
            dest_root.display(),
            err
        )
    })?;

    let ver = env!("CARGO_PKG_VERSION");
    let crates: [(&str, &str); 4] = [
        ("anneal-spec-macros", "crates/anneal-spec-macros"),
        ("anneal-spec", "crates/anneal-spec"),
        ("anneal-rustc-capture", "trusted/rustc-capture"),
        ("cargo-anneal", "crates/cargo-anneal"),
    ];

    let mut staged_dirs = Vec::with_capacity(crates.len());
    for (crate_name, rel_crate_dir) in crates {
        let src_crate_dir = repo_root.join(rel_crate_dir);
        let dst_crate_dir = dest_root.join(format!("{crate_name}-{ver}"));
        if dst_crate_dir.exists() {
            fs::remove_dir_all(&dst_crate_dir).map_err(|err| {
                format!(
                    "failed to clean existing vendored crate {}: {}",
                    dst_crate_dir.display(),
                    err
                )
            })?;
        }
        fs::create_dir_all(&dst_crate_dir).map_err(|err| {
            format!(
                "failed to create vendored crate directory {}: {}",
                dst_crate_dir.display(),
                err
            )
        })?;

        let raw_toml = fs::read_to_string(src_crate_dir.join("Cargo.toml")).map_err(|err| {
            format!(
                "failed to read {}/Cargo.toml: {}",
                src_crate_dir.display(),
                err
            )
        })?;
        let rewritten_toml = raw_toml
            .replace(
                "path = \"../anneal-spec-macros\"",
                &format!("path = \"../anneal-spec-macros-{ver}\""),
            )
            .replace(
                "path = \"../../trusted/rustc-capture\"",
                &format!("path = \"../anneal-rustc-capture-{ver}\""),
            );
        fs::write(dst_crate_dir.join("Cargo.toml"), rewritten_toml).map_err(|err| {
            format!(
                "failed to write {}/Cargo.toml: {}",
                dst_crate_dir.display(),
                err
            )
        })?;

        copy_dir_filtered_recursive(&src_crate_dir.join("src"), &dst_crate_dir.join("src"))?;

        for license_name in ["LICENSE-BSD", "LICENSE-APACHE", "LICENSE-MIT"] {
            let src_lic = repo_root.join(license_name);
            if src_lic.is_file() {
                fs::copy(&src_lic, dst_crate_dir.join(license_name)).map_err(|err| {
                    format!(
                        "failed to copy {} into {}: {}",
                        src_lic.display(),
                        dst_crate_dir.display(),
                        err
                    )
                })?;
            }
        }

        if crate_name == "cargo-anneal" {
            let lean_root_dst = dst_crate_dir.join("lean-root");
            copy_dir_filtered_recursive(
                &repo_root.join("trusted/lean"),
                &lean_root_dst.join("trusted/lean"),
            )?;
            copy_dir_filtered_recursive(
                &repo_root.join("trusted/audit"),
                &lean_root_dst.join("trusted/audit"),
            )?;
            copy_dir_filtered_recursive(
                &repo_root.join("theory"),
                &lean_root_dst.join("theory"),
            )?;
            for rel_file in ["examples/lakefile.toml", "examples/lean-toolchain", "lean-toolchain"] {
                let src_file = repo_root.join(rel_file);
                if src_file.is_file() {
                    let dst_file = lean_root_dst.join(rel_file);
                    if let Some(parent) = dst_file.parent() {
                        fs::create_dir_all(parent).map_err(|err| {
                            format!("failed to create {}: {}", parent.display(), err)
                        })?;
                    }
                    fs::copy(&src_file, &dst_file).map_err(|err| {
                        format!("failed to copy {}: {}", src_file.display(), err)
                    })?;
                    if rel_file == "examples/lean-toolchain"
                        && !lean_root_dst.join("lean-toolchain").is_file()
                    {
                        fs::copy(&src_file, lean_root_dst.join("lean-toolchain")).map_err(
                            |err| format!("failed to copy {}: {}", src_file.display(), err),
                        )?;
                    }
                }
            }
        }

        write_cargo_checksum_json(&dst_crate_dir)?;
        staged_dirs.push(dst_crate_dir);
    }

    Ok(staged_dirs)
}

fn copy_dir_filtered_recursive(src: &Path, dst: &Path) -> Result<(), String> {
    if !src.is_dir() {
        return Err(format!("source directory does not exist: {}", src.display()));
    }
    fs::create_dir_all(dst)
        .map_err(|err| format!("failed to create directory {}: {}", dst.display(), err))?;
    let mut entries: Vec<PathBuf> = fs::read_dir(src)
        .map_err(|err| format!("failed to read directory {}: {}", src.display(), err))?
        .filter_map(|e| e.ok().map(|d| d.path()))
        .collect();
    entries.sort();
    for entry in entries {
        let Some(name) = entry.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if matches!(name, ".lake" | "target" | "__pycache__" | ".git") {
            continue;
        }
        let dst_path = dst.join(name);
        if entry.is_dir() {
            copy_dir_filtered_recursive(&entry, &dst_path)?;
        } else if entry.is_file() {
            fs::copy(&entry, &dst_path).map_err(|err| {
                format!(
                    "failed to copy {} to {}: {}",
                    entry.display(),
                    dst_path.display(),
                    err
                )
            })?;
        }
    }
    Ok(())
}

fn collect_all_files_recursive(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !dir.is_dir() {
        return Ok(());
    }
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .map_err(|err| format!("failed to read directory {}: {}", dir.display(), err))?
        .filter_map(|e| e.ok().map(|d| d.path()))
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_all_files_recursive(&path, out)?;
        } else if path.is_file() {
            out.push(path);
        }
    }
    Ok(())
}

fn write_cargo_checksum_json(crate_dir: &Path) -> Result<(), String> {
    let checksum_path = crate_dir.join(".cargo-checksum.json");
    if checksum_path.exists() {
        let _ = fs::remove_file(&checksum_path);
    }
    let mut files = Vec::new();
    collect_all_files_recursive(crate_dir, &mut files)?;
    files.sort();

    let mut entries = Vec::with_capacity(files.len());
    for file in files {
        let rel = file
            .strip_prefix(crate_dir)
            .map_err(|err| format!("failed to strip prefix: {err}"))?;
        let rel_slash = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let bytes = fs::read(&file)
            .map_err(|err| format!("failed to read {}: {}", file.display(), err))?;
        let digest = anneal_rustc_capture::sha256_hex(&bytes);
        let escaped = anneal_rustc_capture::manifest::escape_json(&rel_slash);
        entries.push(format!("\"{escaped}\":\"{digest}\""));
    }
    let json = format!("{{\"files\":{{{}}},\"package\":null}}\n", entries.join(","));
    fs::write(&checksum_path, json)
        .map_err(|err| format!("failed to write {}: {}", checksum_path.display(), err))
}

fn resolve_trusted_boundary_lean(
    workspace_root: &Path,
    anneal_repo_root: Option<&Path>,
) -> Result<PathBuf, String> {
    let base_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    if let Some(root) = anneal_repo_root {
        let abs_root = normalize_path_against(&base_dir, root);
        let candidate = abs_root.join("trusted/audit/TrustedBoundary.lean");
        if candidate.is_file() {
            return Ok(candidate);
        }
    }

    for env_key in ["ANNEAL_REPO_ROOT", "ANNEAL_ROOT"] {
        if let Ok(env_root) = env::var(env_key)
            && !env_root.trim().is_empty()
        {
            let abs_env_root = normalize_path_against(&base_dir, Path::new(env_root.trim()));
            let candidate = abs_env_root.join("trusted/audit/TrustedBoundary.lean");
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }

    let abs_workspace_root = normalize_path_against(&base_dir, workspace_root);
    let mut current: Option<&Path> = Some(&abs_workspace_root);
    while let Some(dir) = current {
        let candidate = dir.join("trusted/audit/TrustedBoundary.lean");
        if candidate.is_file() {
            return Ok(candidate);
        }
        current = dir.parent();
    }

    if let Some(repo_root) = default_anneal_repo_root() {
        let candidate = repo_root.join("trusted/audit/TrustedBoundary.lean");
        if candidate.is_file() {
            return Ok(candidate);
        }
    }

    Err(format!(
        "could not locate trusted/audit/TrustedBoundary.lean from {}",
        workspace_root.display()
    ))
}

pub(crate) fn resolve_lake_binary() -> PathBuf {
    if let Ok(lake_env) = env::var("LAKE")
        && !lake_env.trim().is_empty()
    {
        return PathBuf::from(lake_env);
    }
    if let Some(toolchain_root) = setup::resolve_installed_toolchain() {
        let bundled = toolchain_root.join("lean/bin/lake");
        if bundled.is_file() {
            return bundled;
        }
    }
    if let Ok(home) = env::var("HOME") {
        let pinned = PathBuf::from(home)
            .join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lake");
        if pinned.is_file() {
            return pinned;
        }
    }
    PathBuf::from("lake")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lake_build_command_enables_the_artifact_cache_unless_overridden() {
        let cmd = build_lake_build_command(Path::new("lake"), Path::new("/tmp/ws/.anneal"));
        let envs: Vec<(String, Option<String>)> = cmd
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|v| v.to_string_lossy().into_owned()),
                )
            })
            .collect();
        for (key, value) in LAKE_CACHE_ENV_DEFAULTS {
            if env::var_os(key).is_some() {
                // The ambient environment wins; the command must not override it.
                assert!(
                    !envs.iter().any(|(k, _)| k == key),
                    "{key} is set in the environment and must be left alone"
                );
            } else {
                assert!(
                    envs.iter()
                        .any(|(k, v)| k == key && v.as_deref() == Some(*value)),
                    "expected {key}={value} on the lake build command"
                );
            }
        }
        let args: Vec<String> = cmd
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect();
        assert_eq!(args, vec!["build".to_string()]);
        assert!(
            !args.iter().any(|a| a.starts_with("-j")),
            "Lean v4.34.1 `lake build` has no `-j` CLI flag: {args:?}"
        );
        if env::var("CARGO_ANNEAL_LAKE_JOBS")
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
            .is_some_and(|n| n >= 1)
        {
            assert!(
                envs.iter().any(|(k, v)| k == "LEAN_NUM_THREADS" && v.is_some()),
                "CARGO_ANNEAL_LAKE_JOBS must set LEAN_NUM_THREADS on the command"
            );
        } else if env::var_os("LEAN_NUM_THREADS").is_some() {
            assert!(
                !envs.iter().any(|(k, _)| k == "LEAN_NUM_THREADS"),
                "explicit caller LEAN_NUM_THREADS must be preserved when CARGO_ANNEAL_LAKE_JOBS is unset"
            );
        } else {
            assert!(
                envs.iter().any(|(k, v)| {
                    k == "LEAN_NUM_THREADS"
                        && v.as_deref()
                            .and_then(|s| s.parse::<usize>().ok())
                            .is_some_and(|n| (1..=6).contains(&n))
                }),
                "default LEAN_NUM_THREADS in 1..=6 must be set when unset in env: {envs:?}"
            );
        }
        assert_eq!(cmd.get_current_dir(), Some(Path::new("/tmp/ws/.anneal")));
    }

    #[test]
    fn default_lake_jobs_and_cgroup_memory_clamping_handle_stat_max_and_overrides() {
        use std::time::{SystemTime, UNIX_EPOCH};

        const MIB_KIB: u64 = 1024;
        const GIB_KIB: u64 = 1024 * 1024;

        // 1. `parse_meminfo_kib` reads MemTotal + MemAvailable and falls back to MemFree + Cached.
        assert_eq!(
            parse_meminfo_kib(
                "MemTotal:       19996672 kB\nMemFree:         2000000 kB\nMemAvailable:   15631360 kB\n"
            ),
            (Some(19_996_672), Some(15_631_360))
        );
        assert_eq!(
            parse_meminfo_kib("MemTotal: 8388608 kB\nMemFree: 1048576 kB\nCached: 2097152 kB\n"),
            (Some(8_388_608), Some(3_145_728))
        );
        assert_eq!(parse_meminfo_kib("unparseable\n"), (None, None));

        // 2. `resolve_default_lake_jobs` clamps by available memory (1536 MiB/job in 1..=6),
        //    total memory (2048 MiB/job), and CPU cores, defaulting to 2 when memory is unknown.
        assert_eq!(resolve_default_lake_jobs(None, None, 8), 2);
        assert_eq!(resolve_default_lake_jobs(None, None, 1), 1);
        assert_eq!(
            resolve_default_lake_jobs(Some(16 * GIB_KIB), Some(1024 * MIB_KIB), 8),
            1,
            "< 1536 MiB available must clamp to 1 job"
        );
        assert_eq!(
            resolve_default_lake_jobs(Some(16 * GIB_KIB), Some(3072 * MIB_KIB), 8),
            2,
            "3072 MiB available -> 2 jobs"
        );
        assert_eq!(
            resolve_default_lake_jobs(Some(16 * GIB_KIB), Some(6144 * MIB_KIB), 8),
            4,
            "6144 MiB available -> 4 jobs"
        );
        assert_eq!(
            resolve_default_lake_jobs(Some(32 * GIB_KIB), Some(24 * GIB_KIB), 8),
            6,
            ">= 9 GiB available on >= 12 GiB host clamps at 6 jobs"
        );
        assert_eq!(
            resolve_default_lake_jobs(Some(4 * GIB_KIB), Some(16 * GIB_KIB), 8),
            2,
            "total memory cap (4096 / 2048 = 2) bounds jobs even when avail is larger"
        );
        assert_eq!(
            resolve_default_lake_jobs(Some(32 * GIB_KIB), Some(24 * GIB_KIB), 3),
            3,
            "CPU core count bounds jobs"
        );

        // 3. `resolve_lake_build_threads_env`: CARGO_ANNEAL_LAKE_JOBS overrides (capped at 16),
        //    invalid values fall through, and explicit caller LEAN_NUM_THREADS is preserved.
        assert_eq!(
            resolve_lake_build_threads_env(Some("5"), true, Some(16 * GIB_KIB), Some(8 * GIB_KIB), 8),
            Some(5)
        );
        assert_eq!(
            resolve_lake_build_threads_env(Some("32"), false, Some(16 * GIB_KIB), Some(8 * GIB_KIB), 8),
            Some(16),
            "CARGO_ANNEAL_LAKE_JOBS must cap at 16"
        );
        assert_eq!(
            resolve_lake_build_threads_env(Some("0"), true, Some(16 * GIB_KIB), Some(8 * GIB_KIB), 8),
            None,
            "CARGO_ANNEAL_LAKE_JOBS=0 is invalid and must preserve caller LEAN_NUM_THREADS"
        );
        assert_eq!(
            resolve_lake_build_threads_env(Some("not-a-number"), true, Some(16 * GIB_KIB), Some(8 * GIB_KIB), 8),
            None
        );
        assert_eq!(
            resolve_lake_build_threads_env(None, true, Some(16 * GIB_KIB), Some(8 * GIB_KIB), 8),
            None,
            "caller LEAN_NUM_THREADS must be preserved when CARGO_ANNEAL_LAKE_JOBS is unset"
        );
        assert_eq!(
            resolve_lake_build_threads_env(None, false, Some(16 * GIB_KIB), Some(6144 * MIB_KIB), 8),
            Some(4)
        );

        // 4. `cgroup_memory_limits_kib` walks from leaf up to cgroup_root, handles `"max"`,
        //    subtracts `anon + shmem` from `memory.stat` (ignoring reclaimable `file` cache),
        //    and falls back to `memory.current` when `memory.stat` is absent.
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let cg_root = env::temp_dir().join(format!(
            "cargo-anneal-cgroup-test-{}-{nanos}",
            std::process::id()
        ));
        let slice_dir = cg_root.join("user.slice");
        let app_dir = slice_dir.join("app.slice");
        let scope_dir = app_dir.join("lean.scope");
        fs::create_dir_all(&scope_dir).expect("create cgroup test hierarchy");

        // Root and app.slice have `"max"` (unbounded).
        fs::write(cg_root.join("memory.max"), "max\n").unwrap();
        fs::write(app_dir.join("memory.max"), "max\n").unwrap();
        // user.slice has 16 GiB max and no memory.stat, falling back to memory.current = 10 GiB -> 6 GiB headroom.
        fs::write(slice_dir.join("memory.max"), format!("{}\n", 16 * GIB_KIB * 1024)).unwrap();
        fs::write(
            slice_dir.join("memory.current"),
            format!("{}\n", 10 * GIB_KIB * 1024),
        )
        .unwrap();
        // lean.scope has 12 GiB max (tightest limit), memory.current = 11 GiB (due to 9 GiB file cache),
        // but memory.stat has anon = 1 GiB + shmem = 1 GiB -> 2 GiB non-reclaimable -> 10 GiB headroom at leaf.
        fs::write(scope_dir.join("memory.max"), format!("{}\n", 12 * GIB_KIB * 1024)).unwrap();
        fs::write(
            scope_dir.join("memory.current"),
            format!("{}\n", 11 * GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(
            scope_dir.join("memory.stat"),
            format!(
                "anon {}\nfile {}\nshmem {}\n",
                GIB_KIB * 1024,
                9 * GIB_KIB * 1024,
                GIB_KIB * 1024
            ),
        )
        .unwrap();

        let (limit_kib, headroom_kib) = cgroup_memory_limits_kib(
            &cg_root,
            "1:name=systemd:/foo\n0::/user.slice/app.slice/lean.scope (deleted)\n",
        );
        assert_eq!(limit_kib, Some(12 * GIB_KIB));
        assert_eq!(
            headroom_kib,
            Some(6 * GIB_KIB),
            "leaf headroom is 10 GiB (via anon+shmem), parent user.slice headroom is 6 GiB (via memory.current fallback)"
        );

        // If user.slice also has `"max"`, leaf's `memory.stat` headroom (12 - 2 = 10 GiB) wins over `memory.current`.
        fs::write(slice_dir.join("memory.max"), "max\n").unwrap();
        let (limit2, headroom2) =
            cgroup_memory_limits_kib(&cg_root, "0::/user.slice/app.slice/lean.scope\n");
        assert_eq!(limit2, Some(12 * GIB_KIB));
        assert_eq!(headroom2, Some(10 * GIB_KIB));

        // Missing leaf directory still walks upward through intermediate slice limits.
        fs::write(slice_dir.join("memory.max"), format!("{}\n", 8 * GIB_KIB * 1024)).unwrap();
        let (limit3, headroom3) = cgroup_memory_limits_kib(
            &cg_root,
            "0::/user.slice/app.slice/nonexistent-leaf.scope\n",
        );
        assert_eq!(limit3, Some(8 * GIB_KIB));
        assert_eq!(headroom3, Some(0)); // user.slice had memory.current = 10 GiB > 8 GiB -> saturating 0

        // When an ancestor has a bound without readable usage files, it subtracts the
        // tightest (maximum) usage observed across all descendants on the path, not
        // merely the leaf's usage.
        let _ = fs::remove_file(slice_dir.join("memory.current"));
        fs::write(
            app_dir.join("memory.stat"),
            format!("anon {}\nshmem {}\n", 5 * GIB_KIB * 1024, GIB_KIB * 1024),
        )
        .unwrap();
        fs::write(slice_dir.join("memory.max"), format!("{}\n", 16 * GIB_KIB * 1024)).unwrap();
        fs::write(scope_dir.join("memory.max"), "max\n").unwrap();
        let (limit_anc, headroom_anc) =
            cgroup_memory_limits_kib(&cg_root, "0::/user.slice/app.slice/lean.scope\n");
        assert_eq!(limit_anc, Some(16 * GIB_KIB));
        assert_eq!(
            headroom_anc,
            Some(10 * GIB_KIB),
            "ancestor without own usage must subtract max descendant usage (6 GiB at app.slice > 2 GiB at leaf)"
        );
        let _ = fs::remove_file(app_dir.join("memory.stat"));

        // When all levels have `"max"`, both limit and headroom are None.
        fs::write(slice_dir.join("memory.max"), "max\n").unwrap();
        fs::write(scope_dir.join("memory.max"), "max\n").unwrap();
        assert_eq!(
            cgroup_memory_limits_kib(&cg_root, "0::/user.slice/app.slice/lean.scope\n"),
            (None, None)
        );
        // Path traversal is rejected.
        assert_eq!(
            cgroup_memory_limits_kib(&cg_root, "0::/user.slice/../../etc\n"),
            (None, None)
        );
        // Unknown available memory with known total falls back conservatively to 2 (bounded by total).
        assert_eq!(resolve_default_lake_jobs(Some(32 * GIB_KIB), None, 8), 2);
        assert_eq!(resolve_default_lake_jobs(Some(1 * GIB_KIB), None, 8), 1);

        // 5. `build_lake_build_command_with_inputs` deterministically configures `Command`
        //    env vars (`LAKE_CACHE_ENV_DEFAULTS` + `LEAN_NUM_THREADS`) and never passes `-j`.
        use std::collections::BTreeMap;
        let cmd_default = build_lake_build_command_with_inputs(
            Path::new("lake"),
            Path::new("/tmp/ws/.anneal"),
            |_| false,
            None,
            false,
            Some(16 * GIB_KIB),
            Some(4608 * MIB_KIB),
            8,
        );
        let envs_default: BTreeMap<String, Option<String>> = cmd_default
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|val| val.to_string_lossy().into_owned()),
                )
            })
            .collect();
        assert_eq!(
            envs_default.get("LEAN_NUM_THREADS"),
            Some(&Some("3".to_string()))
        );
        assert_eq!(
            envs_default.get("LAKE_ARTIFACT_CACHE"),
            Some(&Some("true".to_string()))
        );
        assert_eq!(
            envs_default.get("LAKE_RESTORE_ARTIFACTS"),
            Some(&Some("true".to_string()))
        );
        assert!(
            !cmd_default
                .get_args()
                .any(|a| a.to_string_lossy().starts_with("-j"))
        );

        let cmd_preserve_caller = build_lake_build_command_with_inputs(
            Path::new("lake"),
            Path::new("/tmp/ws/.anneal"),
            |k| k == "LAKE_ARTIFACT_CACHE",
            None,
            true,
            Some(16 * GIB_KIB),
            Some(4608 * MIB_KIB),
            8,
        );
        let envs_preserve: BTreeMap<String, Option<String>> = cmd_preserve_caller
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|val| val.to_string_lossy().into_owned()),
                )
            })
            .collect();
        assert!(!envs_preserve.contains_key("LEAN_NUM_THREADS"));
        assert!(!envs_preserve.contains_key("LAKE_ARTIFACT_CACHE"));
        assert_eq!(
            envs_preserve.get("LAKE_RESTORE_ARTIFACTS"),
            Some(&Some("true".to_string()))
        );

        let cmd_override = build_lake_build_command_with_inputs(
            Path::new("lake"),
            Path::new("/tmp/ws/.anneal"),
            |_| false,
            Some("99"),
            true,
            Some(16 * GIB_KIB),
            Some(1024 * MIB_KIB),
            2,
        );
        let envs_override: BTreeMap<String, Option<String>> = cmd_override
            .get_envs()
            .map(|(k, v)| {
                (
                    k.to_string_lossy().into_owned(),
                    v.map(|val| val.to_string_lossy().into_owned()),
                )
            })
            .collect();
        assert_eq!(
            envs_override.get("LEAN_NUM_THREADS"),
            Some(&Some("16".to_string()))
        );

        let _ = fs::remove_dir_all(&cg_root);
    }

    #[test]
    fn cgroup_memory_limits_honor_memory_high_throttle_threshold_below_memory_max() {
        use std::time::{SystemTime, UNIX_EPOCH};

        const GIB: u64 = 1024 * 1024 * 1024;
        const GIB_KIB: u64 = 1024 * 1024;

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let cg_root = env::temp_dir().join(format!(
            "cargo-anneal-cgroup-high-test-{}-{nanos}",
            std::process::id()
        ));
        let slice = cg_root.join("user.slice");
        let service = slice.join("rshelld.service");
        let leaf = service.join("server");
        fs::create_dir_all(&leaf).expect("create cgroup test hierarchy");

        // Mirrors a systemd capsule: `user.slice` throttles at `memory.high`
        // (19 GiB) below its `memory.max` (20 GiB); the service and leaf are
        // unbounded (`"max"` for both files).
        fs::write(slice.join("memory.max"), format!("{}\n", 20 * GIB)).unwrap();
        fs::write(slice.join("memory.high"), format!("{}\n", 19 * GIB)).unwrap();
        fs::write(
            slice.join("memory.stat"),
            format!("anon {}\nfile {}\nshmem {}\n", 3 * GIB, 6 * GIB, GIB),
        )
        .unwrap();
        for dir in [&service, &leaf] {
            fs::write(dir.join("memory.max"), "max\n").unwrap();
            fs::write(dir.join("memory.high"), "max\n").unwrap();
        }
        let proc_self_cgroup = "0::/user.slice/rshelld.service/server\n";

        // `memory.high` (19 GiB) is the binding bound; headroom = 19 - (3 + 1) = 15 GiB
        // (reclaimable `file` cache is not subtracted).
        assert_eq!(
            cgroup_memory_limits_kib(&cg_root, proc_self_cgroup),
            (Some(19 * GIB_KIB), Some(15 * GIB_KIB))
        );

        // A leaf `memory.high` below every `memory.max` binds even when the leaf's
        // `memory.max` is `"max"`; the leaf has no `memory.stat`, so its own
        // `memory.current` (2 GiB) is subtracted.
        fs::write(leaf.join("memory.high"), format!("{}\n", 6 * GIB)).unwrap();
        fs::write(leaf.join("memory.current"), format!("{}\n", 2 * GIB)).unwrap();
        assert_eq!(
            cgroup_memory_limits_kib(&cg_root, proc_self_cgroup),
            (Some(6 * GIB_KIB), Some(4 * GIB_KIB))
        );
        // ...and therefore bounds the default Lake concurrency: 4096 MiB / 1536 -> 2
        // jobs, and 6144 MiB / 2048 -> at most 3 jobs.
        assert_eq!(
            resolve_default_lake_jobs(Some(6 * GIB_KIB), Some(4 * GIB_KIB), 8),
            2
        );

        // With every `memory.high` back at `"max"`, `memory.max` (20 GiB) binds again.
        fs::write(leaf.join("memory.high"), "max\n").unwrap();
        fs::write(slice.join("memory.high"), "max\n").unwrap();
        assert_eq!(
            cgroup_memory_limits_kib(&cg_root, proc_self_cgroup),
            (Some(20 * GIB_KIB), Some(16 * GIB_KIB))
        );

        let _ = fs::remove_dir_all(&cg_root);
    }

    #[test]
    fn cgroup_v1_memory_limits_cover_legacy_and_hybrid_containers() {
        use std::time::{SystemTime, UNIX_EPOCH};

        const GIB: u64 = 1024 * 1024 * 1024;
        const GIB_KIB: u64 = 1024 * 1024;
        const V1_UNLIMITED: &str = "9223372036854771712\n";

        // `memory.stat` keys: hierarchical totals win over cgroup-local values,
        // reclaimable `cache` / `total_cache` are ignored.
        assert_eq!(
            parse_cgroup_v1_memory_stat_used_bytes(
                "cache 100\nrss 10\nshmem 1\ntotal_cache 900\ntotal_rss 40\ntotal_shmem 2\n"
            ),
            Some(42)
        );
        assert_eq!(
            parse_cgroup_v1_memory_stat_used_bytes("cache 100\nrss 10\nshmem 1\n"),
            Some(11)
        );
        assert_eq!(parse_cgroup_v1_memory_stat_used_bytes("cache 100\n"), None);

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let memory_root = env::temp_dir().join(format!(
            "cargo-anneal-cgroup-v1-test-{}-{nanos}",
            std::process::id()
        ));
        let docker = memory_root.join("docker");
        let container = docker.join("abc123");
        fs::create_dir_all(&container).expect("create cgroup v1 test hierarchy");
        fs::write(memory_root.join("memory.limit_in_bytes"), V1_UNLIMITED).unwrap();
        fs::write(docker.join("memory.limit_in_bytes"), V1_UNLIMITED).unwrap();
        // The container is limited to 8 GiB with 1.5 GiB non-reclaimable usage and
        // 4 GiB of reclaimable page cache.
        fs::write(container.join("memory.limit_in_bytes"), format!("{}\n", 8 * GIB)).unwrap();
        fs::write(
            container.join("memory.stat"),
            format!(
                "cache {}\nrss {}\nshmem {}\ntotal_cache {}\ntotal_rss {}\ntotal_shmem {}\n",
                4 * GIB,
                GIB,
                GIB / 2,
                4 * GIB,
                GIB,
                GIB / 2
            ),
        )
        .unwrap();
        fs::write(container.join("memory.usage_in_bytes"), format!("{}\n", 6 * GIB)).unwrap();

        // Hybrid host: the unified `0::` line exposes no memory controller, the v1
        // `memory` controller (possibly co-mounted, e.g. `memory,hugetlb`) does.
        let proc_self_cgroup = "12:cpu,cpuacct:/docker/abc123\n\
                                11:memory,hugetlb:/docker/abc123\n\
                                0::/docker/abc123\n";
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, proc_self_cgroup),
            (Some(8 * GIB_KIB), Some(6 * GIB_KIB + GIB_KIB / 2)),
            "8 GiB - (1 GiB rss + 0.5 GiB shmem); page cache is reclaimable"
        );
        // Without `memory.stat`, `memory.usage_in_bytes` (6 GiB) is subtracted.
        fs::remove_file(container.join("memory.stat")).unwrap();
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, proc_self_cgroup),
            (Some(8 * GIB_KIB), Some(2 * GIB_KIB))
        );
        // Inside the container the mount shows its own cgroup as the root, so the
        // host-relative path does not exist: the walk climbs to the mount root,
        // whose limit is the container's.
        fs::write(memory_root.join("memory.limit_in_bytes"), format!("{}\n", 4 * GIB)).unwrap();
        fs::write(memory_root.join("memory.usage_in_bytes"), format!("{}\n", GIB)).unwrap();
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, "4:memory:/kubepods/pod-xyz/ctr\n"),
            (Some(4 * GIB_KIB), Some(3 * GIB_KIB))
        );
        // No `memory` controller line, unlimited everywhere, or path traversal -> None.
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, "0::/docker/abc123\n"),
            (None, None)
        );
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, "3:memory:/docker/../../etc\n"),
            (None, None)
        );
        fs::write(memory_root.join("memory.limit_in_bytes"), V1_UNLIMITED).unwrap();
        fs::write(container.join("memory.limit_in_bytes"), V1_UNLIMITED).unwrap();
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, proc_self_cgroup),
            (None, None)
        );
        // Bind-mounted pod container where `memory.limit_in_bytes` is unlimited at the
        // container leaf, while `memory.stat`'s `hierarchical_memory_limit` exposes the
        // enclosing pod's 3 GiB cap.
        fs::write(
            memory_root.join("memory.stat"),
            format!(
                "hierarchical_memory_limit {}\ntotal_rss {}\ntotal_shmem 0\n",
                3 * GIB,
                GIB
            ),
        )
        .unwrap();
        assert_eq!(
            cgroup_v1_memory_limits_kib(&memory_root, "4:memory:/kubepods/pod-xyz/ctr\n"),
            (Some(3 * GIB_KIB), Some(2 * GIB_KIB))
        );
        fs::remove_file(memory_root.join("memory.stat")).unwrap();
        // The unified-hierarchy walk sees no `memory.max` in a v1 mount layout, which
        // is what makes `probe_effective_memory_kib` fall back to v1.
        assert_eq!(
            cgroup_memory_limits_kib(&memory_root, proc_self_cgroup),
            (None, None)
        );

        let _ = fs::remove_dir_all(&memory_root);
    }

    #[test]
    fn cli_parser_handles_cargo_subcommand_prefix_and_flags() {
        let opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "extract",
            "--workspace-root",
            "/tmp/demo",
            "--units-dir",
            "/tmp/demo/units",
            "--",
            "--all-targets",
        ])
        .expect("parse cargo anneal extract");
        assert_eq!(opts.subcommand, CliSubcommand::Extract);
        assert_eq!(opts.workspace_root, PathBuf::from("/tmp/demo"));
        assert_eq!(opts.units_dir, PathBuf::from("/tmp/demo/units"));
        assert_eq!(opts.extra_cargo_args, vec!["--all-targets".to_string()]);

        let scaffold_opts = parse_cli_args([
            "cargo-anneal",
            "scaffold",
            "--manifest-path",
            "/tmp/pkg/Cargo.toml",
            "--from-units",
        ])
        .expect("parse direct scaffold");
        assert_eq!(scaffold_opts.subcommand, CliSubcommand::Scaffold);
        assert_eq!(scaffold_opts.workspace_root, PathBuf::from("/tmp/pkg"));
        assert_eq!(
            scaffold_opts.manifest_path,
            Some(PathBuf::from("/tmp/pkg/Cargo.toml"))
        );
        assert!(scaffold_opts.from_existing_units);

        let verify_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "verify",
            "--allow-assumptions",
            "--init-proofs",
        ])
        .expect("parse verify");
        assert_eq!(verify_opts.subcommand, CliSubcommand::Verify);
        assert!(verify_opts.allow_assumptions);
        assert!(verify_opts.init_proofs);
        assert_eq!(verify_opts.filter, None);
    }

    #[test]
    fn cli_parser_supports_filter_and_check_subcommands() {
        let extract_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "extract",
            "--filter",
            "checked_scale",
        ])
        .expect("parse extract --filter");
        assert_eq!(extract_opts.subcommand, CliSubcommand::Extract);
        assert_eq!(extract_opts.filter.as_deref(), Some("checked_scale"));

        let scaffold_opts = parse_cli_args([
            "cargo-anneal",
            "scaffold",
            "--filter=Ptr::try_from",
            "--filter",
            "try_read_from",
        ])
        .expect("parse scaffold with multiple --filter flags");
        assert_eq!(scaffold_opts.subcommand, CliSubcommand::Scaffold);
        assert_eq!(
            scaffold_opts.filter.as_deref(),
            Some("Ptr::try_from,try_read_from")
        );

        let check_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "check",
            "--filter",
            "Ptr::try_from",
            "--allow-assumptions",
        ])
        .expect("parse check --filter");
        assert_eq!(check_opts.subcommand, CliSubcommand::Verify);
        assert_eq!(check_opts.filter.as_deref(), Some("Ptr::try_from"));
        assert!(check_opts.allow_assumptions);

        let err_missing =
            parse_cli_args(["cargo-anneal", "verify", "--filter"]).expect_err("missing filter val");
        assert!(err_missing.contains("missing value for --filter"));
    }

    #[test]
    fn cli_parser_rejects_unknown_subcommand() {
        let err =
            parse_cli_args(["cargo-anneal", "anneal", "bogus"]).expect_err("must reject bogus");
        assert!(err.contains("unknown subcommand 'bogus'"));
    }

    #[test]
    fn cli_setup_and_help_argument_validation() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &[][..],
                &["help"],
                &["-h"],
                &["--help"],
                &["setup", "-h"],
                &["setup", "--help"],
                &["help", "setup"],
            ] {
                let opts = parse_cli_args([prefix, suffix].concat()).expect("help must parse");
                assert_eq!(opts.subcommand, CliSubcommand::Help);
            }
            for suffix in ["-V", "--version", "version"] {
                let opts = parse_cli_args([prefix, &[suffix]].concat()).expect("version must parse");
                assert_eq!(opts.subcommand, CliSubcommand::Version);
            }
        }

        let setup_default = parse_cli_args(["cargo-anneal", "setup"]).expect("parse setup");
        assert_eq!(setup_default.subcommand, CliSubcommand::Setup);
        assert_eq!(setup_default.local_archive, None);

        let setup_local = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "setup",
            "--local-archive",
            "/tmp/local archive.tar.zst",
        ])
        .expect("parse setup --local-archive");
        assert_eq!(setup_local.subcommand, CliSubcommand::Setup);
        assert_eq!(
            setup_local.local_archive,
            Some(PathBuf::from("/tmp/local archive.tar.zst"))
        );

        for malformed in [
            &["unknown"][..],
            &["--unknown"],
            &["setup", "--unknown"],
            &["setup", "--local-archive"],
            &["setup", "--local-archive", "--unknown"],
        ] {
            parse_cli_args([&["cargo-anneal"], malformed].concat())
                .expect_err("malformed setup/CLI arguments must fail");
        }
    }

    #[test]
    fn cli_parser_supports_agent_subcommands_and_locked_specs_flags() {
        let lock_opts = parse_cli_args(["cargo-anneal", "anneal", "lock-specs", "--from-units"])
            .expect("parse lock-specs");
        assert_eq!(lock_opts.subcommand, CliSubcommand::LockSpecs);
        assert!(lock_opts.from_existing_units);
        assert!(!lock_opts.locked_specs);

        let ctx_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "agent-context",
            "--item",
            "CanaryPkg.identity_u32",
            "--item=const_forty_two",
        ])
        .expect("parse agent-context");
        assert_eq!(ctx_opts.subcommand, CliSubcommand::AgentContext);
        assert_eq!(
            ctx_opts.item_filter.as_deref(),
            Some("CanaryPkg.identity_u32,const_forty_two")
        );

        let agent_verify_opts = parse_cli_args(["cargo-anneal", "anneal", "agent-verify"])
            .expect("parse agent-verify");
        assert_eq!(agent_verify_opts.subcommand, CliSubcommand::AgentVerify);
        assert!(agent_verify_opts.locked_specs);

        let verify_locked_opts =
            parse_cli_args(["cargo-anneal", "verify", "--locked-specs"])
                .expect("parse verify --locked-specs");
        assert_eq!(verify_locked_opts.subcommand, CliSubcommand::Verify);
        assert!(verify_locked_opts.locked_specs);

        let missing_item =
            parse_cli_args(["cargo-anneal", "agent-context", "--item"]).expect_err("missing item");
        assert!(missing_item.contains("missing value for --item"));

        let init_specs_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "scaffold",
            "--init-specs",
            "--init-proofs",
        ])
        .expect("parse scaffold --init-specs --init-proofs");
        assert_eq!(init_specs_opts.subcommand, CliSubcommand::Scaffold);
        assert!(init_specs_opts.init_specs);
        assert!(init_specs_opts.init_proofs);
        assert!(cli_usage().contains("--init-specs"));

        let hardened_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "agent-verify",
            "--lock-file=/tmp/external-lock.json",
            "--lock-git-ref=HEAD",
            "--provisional",
        ])
        .expect("parse agent-verify with --lock-file, --lock-git-ref, --provisional");
        assert_eq!(hardened_opts.subcommand, CliSubcommand::AgentVerify);
        assert_eq!(
            hardened_opts.lock_file,
            Some(PathBuf::from("/tmp/external-lock.json"))
        );
        assert_eq!(hardened_opts.lock_git_ref.as_deref(), Some("HEAD"));
        assert!(hardened_opts.allow_provisional_native);

        let sandbox_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "agent-sandbox",
            "--lock-file",
            "/tmp/external-lock.json",
            "--",
            "bash",
            "-c",
            "echo ok",
        ])
        .expect("parse agent-sandbox");
        assert_eq!(sandbox_opts.subcommand, CliSubcommand::AgentSandbox);
        assert_eq!(
            sandbox_opts.lock_file,
            Some(PathBuf::from("/tmp/external-lock.json"))
        );
        assert_eq!(
            sandbox_opts.extra_cargo_args,
            vec!["bash".to_string(), "-c".to_string(), "echo ok".to_string()]
        );
    }

    #[test]
    fn cli_parser_normalizes_relative_manifest_path_and_path_flags() {
        let cwd = env::current_dir().expect("read current_dir");

        // Relative `--manifest-path examples/tutor/Cargo.toml` must resolve
        // `manifest_path`, `workspace_root`, and `units_dir` to absolute paths
        // so child `cargo check` and `lake` commands (which change working
        // directory to `workspace_root` / `.anneal`) do not double-apply the
        // relative prefix.
        let rel_mp_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "extract",
            "--manifest-path",
            "examples/tutor/Cargo.toml",
        ])
        .expect("parse relative --manifest-path");
        let expected_tutor_root = cwd.join("examples/tutor");
        assert_eq!(rel_mp_opts.workspace_root, expected_tutor_root);
        assert_eq!(
            rel_mp_opts.manifest_path,
            Some(expected_tutor_root.join("Cargo.toml"))
        );
        assert_eq!(
            rel_mp_opts.units_dir,
            expected_tutor_root.join("target/anneal/units")
        );

        // Bare `--manifest-path Cargo.toml` (where `Path::new("Cargo.toml").parent()`
        // would be `""` before normalization) must resolve `workspace_root` to
        // `cwd` and `manifest_path` to `<cwd>/Cargo.toml`.
        let bare_mp_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "verify",
            "--manifest-path",
            "Cargo.toml",
        ])
        .expect("parse bare Cargo.toml --manifest-path");
        assert_eq!(bare_mp_opts.workspace_root, cwd);
        assert_eq!(bare_mp_opts.manifest_path, Some(cwd.join("Cargo.toml")));
        assert_eq!(bare_mp_opts.units_dir, cwd.join("target/anneal/units"));

        // `=`-syntax and `.` / `..` components on path flags.
        let eq_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "agent-verify",
            "--manifest-path=./examples/tutor/../tutor/Cargo.toml",
            "--units-dir=./examples/tutor/custom_units",
            "--wrapper=target/debug/anneal-rustc-capture",
            "--anneal-root=.",
        ])
        .expect("parse = path flags");
        assert_eq!(eq_opts.workspace_root, expected_tutor_root);
        assert_eq!(
            eq_opts.manifest_path,
            Some(expected_tutor_root.join("Cargo.toml"))
        );
        assert_eq!(
            eq_opts.units_dir,
            expected_tutor_root.join("custom_units")
        );
        assert_eq!(
            eq_opts.rustc_wrapper,
            Some(cwd.join("target/debug/anneal-rustc-capture"))
        );
        assert_eq!(eq_opts.anneal_repo_root, Some(cwd));
    }

    #[test]
    fn report_renderers_produce_deterministic_summaries() {
        use anneal_rustc_capture::{
            CaptureManifest, CapturedItemKind, CapturedTarget, UnitTargetRecord,
        };
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        let manifest = CaptureManifest {
            schema: 1,
            compilation_succeeded: true,
            rust_sources: vec![("src/lib.rs".to_string(), "a".repeat(64))],
            targets: vec![
                CapturedTarget {
                    def_id: "demo::id".to_string(),
                    mir_module_path: "Mir/Demo/id.lean".to_string(),
                    mir_module_sha256: "b".repeat(64),
                },
                CapturedTarget {
                    def_id: "demo::__anodized_fn_requires_id".to_string(),
                    mir_module_path: "Mir/Demo/__anodized_fn_requires_id.lean".to_string(),
                    mir_module_sha256: "c".repeat(64),
                },
                CapturedTarget {
                    def_id: "demo::__anodized_fn_ensures_id".to_string(),
                    mir_module_path: "Mir/Demo/__anodized_fn_ensures_id.lean".to_string(),
                    mir_module_sha256: "d".repeat(64),
                },
            ],
        };
        let records = vec![
            UnitTargetRecord {
                target: manifest.targets[0].clone(),
                lean_module_name: "Mir.Demo.id".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: manifest.targets[1].clone(),
                lean_module_name: "Mir.Demo.__anodized_fn_requires_id".to_string(),
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some("demo::id".to_string()),
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: manifest.targets[2].clone(),
                lean_module_name: "Mir.Demo.__anodized_fn_ensures_id".to_string(),
                item_kind: CapturedItemKind::InlineSpecEnsures,
                associated_subject_def_id: Some("demo::id".to_string()),
                trait_impls: Vec::new(),
            },
        ];

        let extract_report = render_extract_report(&manifest, &records);
        assert!(extract_report.contains("Rust source files: 1"));
        assert!(extract_report.contains("Total MIR targets: 3"));
        assert!(extract_report.contains("Subject items: 1"));
        assert!(extract_report.contains("requires: 1, ensures: 1, qualifiers: 0, external_spec: 0, model: 0, invariant: 0, unsafe_trait_impl: 0"));
        assert!(extract_report.contains("demo::id -> Mir.Demo.id"));

        let scaffold_report = render_scaffold_report(&ScaffoldReport {
            generated_mir_files: vec![PathBuf::from("a"), PathBuf::from("b"), PathBuf::from("c")],
            generated_obligation_files: vec![PathBuf::from("o")],
            generated_assumption_files: Vec::new(),
            generated_verify_files: vec![PathBuf::from("v")],
            generated_fault_census_files: Vec::new(),
            created_spec_files: vec![PathBuf::from("s1")],
            preserved_spec_files: Vec::new(),
            created_proof_files: vec![PathBuf::from("p1")],
            preserved_proof_files: Vec::new(),
            lakefile_path: PathBuf::from(".anneal/lakefile.toml"),
            toolchain_path: PathBuf::from(".anneal/lean-toolchain"),
        });
        assert!(scaffold_report.contains("Mir: 3, Obligations: 1, Verify: 1"));
        assert!(scaffold_report.contains(
            "created Specs: 1, preserved Specs: 0, created Proof: 1, preserved Proof: 0"
        ));

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let ws = env::temp_dir().join(format!(
            "cargo-anneal-lock-report-{}-{}",
            std::process::id(),
            nanos
        ));
        fs::create_dir_all(&ws).expect("create temp ws");
        let lock_path = lock_workspace_specs(&ws, &records).expect("write spec-lock.json");
        let lock_report =
            render_lock_specs_report(&ws, &lock_path).expect("render lock-specs report");
        assert!(lock_report.contains("Lock file: .anneal/spec-lock.json"));
        assert!(lock_report.contains("Locked MIR targets: 3"));
        assert!(lock_report.contains("Locked Specs files: 0"));
        assert!(lock_report.contains("Locked Assumptions files: 0"));
        assert!(lock_report.contains("Non-vacuity check: PASS"));
        // The tutor-rendered report format is unchanged; the fragment
        // certificates live in `.anneal/spec-lock.json` (records without a
        // SHA-matching captured MIR module are certified fail-closed).
        assert!(!lock_report.contains("spec_digest"), "{lock_report}");
        let locked = parse_spec_lock_manifest(&fs::read_to_string(&lock_path).expect("read lock"))
            .expect("parse lock");
        let digest = locked.spec_digest.clone().expect("manifest spec_digest");
        assert_eq!(digest, compute_spec_lock_manifest_digest(&locked));
        assert!(
            locked
                .locked_records
                .iter()
                .all(|rec| rec.mir_fragment.as_deref() == Some("full_mir")),
            "{locked:?}"
        );
        // The report refuses a lock file that fails its integrity check.
        let mut forged = locked.clone();
        forged.mutable_subjects = vec![forged.locked_records[0].def_id.clone()];
        fs::write(&lock_path, forged.to_json_string()).expect("write forged lock");
        let report_err =
            render_lock_specs_report(&ws, &lock_path).expect_err("tampered lock must not report");
        assert!(report_err.contains("manifest spec_digest mismatch"), "{report_err}");
        // ... and one with an unsupported schema, even under a recomputed digest.
        let mut wrong_schema = locked.clone();
        wrong_schema.schema = "anneal.spec-lock.v0".to_string();
        wrong_schema.spec_digest = Some(agent::compute_spec_lock_manifest_digest(&wrong_schema));
        fs::write(&lock_path, wrong_schema.to_json_string()).expect("write wrong-schema lock");
        let report_err = render_lock_specs_report(&ws, &lock_path)
            .expect_err("unsupported schema must not report");
        assert!(report_err.contains("unsupported schema 'anneal.spec-lock.v0'"), "{report_err}");
        let _ = fs::remove_dir_all(&ws);

        let verify_report = render_verification_report(&VerificationReport {
            items: vec![
                ItemVerificationReport {
                    verify_module: "Verify.Demo.id".to_string(),
                    status: VerificationStatus::VerifiedUnconditional,
                },
                ItemVerificationReport {
                    verify_module: "Verify.Demo.ext".to_string(),
                    status: VerificationStatus::VerifiedConditional {
                        assumptions: vec!["Assumptions.Demo.ext.ax".to_string()],
                    },
                },
            ],
        });
        assert!(verify_report.contains("Verify.Demo.id: UNCONDITIONAL"));
        assert!(verify_report.contains("Verify.Demo.ext: CONDITIONAL [Assumptions.Demo.ext.ax]"));
        assert!(verify_report.contains("Totals: 1 unconditional, 1 conditional"));
        assert!(verify_report.contains("TrustedBoundary kernel replay: PASS"));

        let provisional_report = render_verification_report(&VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: "Verify.Demo.native".to_string(),
                status: VerificationStatus::ProvisionalNative {
                    axioms: vec!["Proof.Demo.native.verified._native.native_decide.ax_1_1".to_string()],
                },
            }],
        });
        assert!(provisional_report.contains(
            "Verify.Demo.native: PROVISIONAL_NATIVE [Proof.Demo.native.verified._native.native_decide.ax_1_1]"
        ));
        assert!(provisional_report.contains("Totals: 0 unconditional, 0 conditional, 1 provisional_native"));
    }

    #[test]
    fn execute_cli_extract_and_scaffold_end_to_end_preserves_authored_files() {
        use anneal_rustc_capture::{
            CapturedItemKind, CapturedTarget, MIR_DIALECT_V2026_06_01, RUSTC_VERSION_STRING,
            UnitCaptureManifest, UnitTargetRecord, sha256_hex,
        };
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let workspace = env::temp_dir().join(format!(
            "cargo-anneal-cli-e2e-{}-{}",
            std::process::id(),
            nanos
        ));
        let units_dir = workspace.join("target/anneal/units");
        let unit_dir = units_dir.join("demo-01");
        let unit_mir_dir = unit_dir.join("Mir/Demo");
        fs::create_dir_all(&unit_mir_dir).expect("create unit mir dir");

        let src_dir = workspace.join("src");
        fs::create_dir_all(&src_dir).expect("create src dir");
        let rs_bytes = b"pub fn id(x: u32) -> u32 { x }\n";
        fs::write(src_dir.join("lib.rs"), rs_bytes).expect("write src/lib.rs");

        let mir_text = "prelude\nimport Init.Core\nimport Trusted\n\nnamespace Mir.Demo.id\nend Mir.Demo.id\n";
        fs::write(unit_mir_dir.join("id.lean"), mir_text).expect("write id.lean");

        let unit_manifest = UnitCaptureManifest {
            schema: 1,
            crate_name: "demo".to_string(),
            unit_id: "demo-01".to_string(),
            rustc_version: RUSTC_VERSION_STRING.to_string(),
            mir_dialect: MIR_DIALECT_V2026_06_01.to_string(),
            compilation_succeeded: true,
            rust_sources: vec![("src/lib.rs".to_string(), sha256_hex(rs_bytes))],
            unit_targets: vec![UnitTargetRecord {
                target: CapturedTarget {
                    def_id: "demo::id".to_string(),
                    mir_module_path: "Mir/Demo/id.lean".to_string(),
                    mir_module_sha256: sha256_hex(mir_text.as_bytes()),
                },
                lean_module_name: "Mir.Demo.id".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            }],
        };
        fs::write(
            unit_dir.join("UnitCaptureManifest.json"),
            serialize_unit_capture_manifest(&unit_manifest),
        )
        .expect("write UnitCaptureManifest.json");

        let extract_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "extract",
            "--workspace-root",
            workspace.to_str().expect("utf8 path"),
            "--from-units",
        ])
        .expect("parse extract opts");
        execute_cli(&extract_opts).expect("execute extract");
        assert!(units_dir.join("CaptureManifest.json").is_file());

        let scaffold_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "scaffold",
            "--workspace-root",
            workspace.to_str().expect("utf8 path"),
            "--from-units",
        ])
        .expect("parse scaffold opts");
        execute_cli(&scaffold_opts).expect("execute first scaffold");

        let spec_file = workspace.join("anneal/proofs/Specs/Demo/id.lean");
        let proof_file = workspace.join("anneal/proofs/Proof/Demo/id.lean");
        let obligation_file = workspace.join(".anneal/generated/Obligations/Demo/id.lean");

        assert!(!spec_file.exists());
        assert!(!proof_file.exists());
        assert!(obligation_file.is_file());

        fs::create_dir_all(spec_file.parent().unwrap()).expect("create Specs/Demo");
        fs::create_dir_all(proof_file.parent().unwrap()).expect("create Proof/Demo");

        let edited_spec = "-- custom spec\ndef pre (args : List Value) : Prop := True\ndef post (args : List Value) (ret : Value) : Prop := True\n";
        let edited_proof = "-- custom proof\ntheorem verified : VerificationResult Obligations.Demo.id.claim := by sorry\n";
        fs::write(&spec_file, edited_spec).expect("write edited spec");
        fs::write(&proof_file, edited_proof).expect("write edited proof");
        fs::write(&obligation_file, "-- overwritten next run\n").expect("corrupt obligation");

        execute_cli(&scaffold_opts).expect("execute second scaffold");

        assert_eq!(
            fs::read_to_string(&spec_file).expect("read spec"),
            edited_spec
        );
        assert_eq!(
            fs::read_to_string(&proof_file).expect("read proof"),
            edited_proof
        );
        let regenerated_obligation =
            fs::read_to_string(&obligation_file).expect("read obligation");
        assert!(regenerated_obligation.contains("def defaultPre (args : List Value) : Prop :="));

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn cli_generate_external_spec_parses_and_emits_snippet() {
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        let gen_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "generate-external-spec",
            "core::slice::from_raw_parts_mut",
            "--output",
            "/tmp/ext_spec.rs",
        ])
        .expect("parse generate-external-spec");
        assert_eq!(gen_opts.subcommand, CliSubcommand::GenerateExternalSpec);
        assert_eq!(
            gen_opts.extra_cargo_args,
            vec!["core::slice::from_raw_parts_mut".to_string()]
        );
        assert_eq!(gen_opts.out_dir, Some(PathBuf::from("/tmp/ext_spec.rs")));

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let workspace = env::temp_dir().join(format!(
            "cargo-anneal-gen-ext-spec-{}-{}",
            std::process::id(),
            nanos
        ));
        let mir_dir = workspace.join(".anneal/generated/Mir/Core");
        fs::create_dir_all(&mir_dir).expect("create Mir/Core");

        let sample_mir = r#"prelude
import Init.Core
import Trusted

namespace Mir.Core.from_raw_parts_mut
def body : CapturedMir := {
  defPath := "core::slice::from_raw_parts_mut"
  argCount := 2
  localDecls :=
    [ { mutability := .mut, ty := { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 0 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 1 }, debugName := some "data" },
      { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 2 }, debugName := some "len" } ]
  basicBlocks := []
}
end Mir.Core.from_raw_parts_mut
"#;
        fs::write(mir_dir.join("from_raw_parts_mut.lean"), sample_mir)
            .expect("write sample mir");

        let out_file = workspace.join("generated_spec.rs");
        let exec_opts = parse_cli_args([
            "cargo-anneal",
            "anneal",
            "generate-external-spec",
            "core::slice::from_raw_parts_mut",
            "--workspace-root",
            workspace.to_str().expect("utf8 path"),
            "--output",
            out_file.to_str().expect("utf8 path"),
        ])
        .expect("parse exec_opts");
        execute_cli(&exec_opts).expect("execute generate-external-spec");

        let snippet = fs::read_to_string(&out_file).expect("read generated_spec.rs");
        assert!(
            snippet.contains("#[anneal_spec::external_spec(for = core::slice::from_raw_parts_mut)]"),
            "missing external_spec attribute in:\n{snippet}"
        );
        assert!(
            snippet.contains(
                "unsafe fn external_spec_from_raw_parts_mut(data: *mut u8, len: usize) -> &'static mut [u8];"
            ),
            "unexpected signature in:\n{snippet}"
        );

        // Real `anneal-rustc-capture` MIR uses `(List.cons ... List.nil)` list
        // constructor syntax for `.tuple`, `.adt`, and `.fnPtr`.
        let list_cons_mir = r#"prelude
import Init.Core
import Trusted

namespace Mir.Core.tuple_and_adt
def body : CapturedMir := {
  defPath := "my_crate::tuple_and_adt"
  argCount := 2
  localDecls :=
    (List.cons {
      mutability := Mutability.mut
      ty := { kind := (RigidTy.adt "core::option::Option" (List.cons (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u32) (List.cons RigidTy.bool List.nil))) List.nil)), layoutIdx := 0 }
      userTy := Option.none
      debugName := Option.none
    } (List.cons {
      mutability := Mutability.not
      ty := { kind := (RigidTy.fnPtr (List.cons (RigidTy.param 0 "T") List.nil) RigidTy.boolFnSafety.safe Abi.rust), layoutIdx := 1 }
      userTy := Option.none
      debugName := (Option.some "cb")
    } (List.cons {
      mutability := Mutability.not
      ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }
      userTy := Option.none
      debugName := (Option.some "unit_arg")
    } List.nil)))
  basicBlocks := List.nil
}
end Mir.Core.tuple_and_adt
"#
        .replace("RigidTy.boolFnSafety.safe", "RigidTy.bool FnSafety.safe");
        fs::write(mir_dir.join("tuple_and_adt.lean"), list_cons_mir)
            .expect("write tuple_and_adt.lean");
        let tuple_snippet =
            generate_external_spec_snippet(&workspace, None, "my_crate::tuple_and_adt")
                .expect("generate external spec snippet from List.cons MIR");
        assert!(
            tuple_snippet.contains(
                "unsafe fn external_spec_tuple_and_adt<T>(cb: fn(T) -> bool, unit_arg: ()) -> core::option::Option<(u32, bool)>;"
            ),
            "List.cons tuple/adt/fnPtr MIR must reconstruct full Rust types:\n{tuple_snippet}"
        );

        // Both `<[T]>::len` and internal `core::slice::<impl [T]>::len` must
        // emit valid Rust `for = <[T]>::len` and preserve `<T>`.
        for target in ["<[T]>::len", "core::slice::<impl [T]>::len"] {
            let poly_len_snippet = generate_external_spec_snippet(&workspace, None, target)
                .expect("generate external spec snippet for polymorphic slice len");
            assert!(
                poly_len_snippet.contains("#[anneal_spec::external_spec(for = <[T]>::len)]")
                    && poly_len_snippet
                        .contains("unsafe fn external_spec_len<T>(slice: &[T]) -> usize;"),
                "target {target} must emit valid Rust <[T]>::len and preserve <T>:\n{poly_len_snippet}"
            );
        }

        // Concrete `<impl [u32]>::len` must emit `for = <[u32]>::len` and `&[u32]`.
        let u32_len_snippet =
            generate_external_spec_snippet(&workspace, None, "core::slice::<impl [u32]>::len")
                .expect("generate external spec snippet for core::slice::<impl [u32]>::len");
        assert!(
            u32_len_snippet.contains("#[anneal_spec::external_spec(for = <[u32]>::len)]")
                && u32_len_snippet.contains("unsafe fn external_spec_len(slice: &[u32]) -> usize;"),
            "concrete <impl [u32]>::len must emit <[u32]>::len and &[u32]:\n{u32_len_snippet}"
        );

        // `extern "C"` FFI declarations in Rust sources (`unsafe extern "C" { fn ... }`)
        // must preserve `extern "C"` in the generated declaration.
        let src_dir = workspace.join("src");
        fs::create_dir_all(&src_dir).expect("create src dir");
        fs::write(
            src_dir.join("lib.rs"),
            "unsafe extern \"C\" {\n    fn c_crc32(ptr: *const u8, len: usize) -> u32;\n}\n",
        )
        .expect("write src/lib.rs");
        let ffi_snippet = generate_external_spec_snippet(&workspace, None, "c_crc32")
            .expect("generate external spec snippet for extern C fn");
        assert!(
            ffi_snippet.contains(
                "unsafe extern \"C\" fn external_spec_c_crc32(ptr: *const u8, len: usize) -> u32;"
            ),
            "extern C function must preserve `extern \"C\"` in snippet:\n{ffi_snippet}"
        );

        let _ = fs::remove_dir_all(&workspace);
    }

    #[test]
    fn fault_census_scaffold_agent_context_and_fail_closed_reconciliation() {
        use std::collections::BTreeSet;
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let workspace = env::temp_dir().join(format!(
            "cargo-anneal-fault-census-{}-{}",
            std::process::id(),
            nanos
        ));

        let callee_mir = r#"import Trusted

namespace Mir.Demo.leaf
open Trusted.MirAst
def body : CapturedMir :=
  {
    defPath := "demo::leaf"
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.subject
    argCount := 1
    localDecls := []
    basicBlocks :=
      (List.cons {
        statements :=
          (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.div (Operand.copy { local_ := 1, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 4 })) }))), span := "src/lib.rs:1:1" } List.nil)
        terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:1:2" }
        isCleanup := false
      } List.nil)
    fnAbi := { args := [], ret := { layoutIdx := 0, mode := .direct }, conv := .rust, canUnwind := false }
    layouts := []
    allocations := []
  }
end Mir.Demo.leaf
"#;

        let caller_mir = r#"import Trusted

namespace Mir.Demo.caller
open Trusted.MirAst
def body : CapturedMir :=
  {
    defPath := "demo::caller"
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.subject
    argCount := 1
    localDecls := []
    basicBlocks :=
      (List.cons {
        statements :=
          (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:2:1" } List.nil)
        terminator :=
          { kind := (TerminatorKind.call
            (Operand.constant { ty := { kind := (RigidTy.fnDef "demo::leaf" List.nil), layoutIdx := 0 }, val := ConstValue.zeroSized })
            (List.cons (Operand.copy { local_ := 1, projection := List.nil }) List.nil)
            { local_ := 0, projection := List.nil }
            (Option.some 1)
            UnwindAction.continue_), span := "src/lib.rs:2:2" }
        isCleanup := false
      } (List.cons {
        statements :=
          (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:2:3" } List.nil)
        terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:2:4" }
        isCleanup := false
      } List.nil))
    fnAbi := { args := [], ret := { layoutIdx := 0, mode := .direct }, conv := .rust, canUnwind := false }
    layouts := []
    allocations := []
  }
end Mir.Demo.caller
"#;

        let units_dir = workspace.join("target/anneal/units/u0");
        let unit_mir_dir = units_dir.join("Mir/Demo");
        fs::create_dir_all(&unit_mir_dir).expect("create unit Mir/Demo");
        fs::write(unit_mir_dir.join("leaf.lean"), callee_mir).expect("write leaf.lean");
        fs::write(unit_mir_dir.join("caller.lean"), caller_mir).expect("write caller.lean");

        let records = vec![
            UnitTargetRecord {
                target: anneal_rustc_capture::CapturedTarget {
                    def_id: "demo::caller".to_string(),
                    mir_module_path: "Mir/Demo/caller.lean".to_string(),
                    mir_module_sha256: anneal_rustc_capture::sha256_hex(caller_mir.as_bytes()),
                },
                lean_module_name: "Mir.Demo.caller".to_string(),
                item_kind: CapturedItemKind::Subject,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
            UnitTargetRecord {
                target: anneal_rustc_capture::CapturedTarget {
                    def_id: "demo::leaf".to_string(),
                    mir_module_path: "Mir/Demo/leaf.lean".to_string(),
                    mir_module_sha256: anneal_rustc_capture::sha256_hex(callee_mir.as_bytes()),
                },
                lean_module_name: "Mir.Demo.leaf".to_string(),
                item_kind: CapturedItemKind::Callee,
                associated_subject_def_id: None,
                trait_impls: Vec::new(),
            },
        ];

        let scaffold_cfg = ScaffoldConfig::new(&workspace);
        let scaffold_rep =
            scaffold_workspace_with_config(&scaffold_cfg, &records).expect("scaffold workspace");
        assert_eq!(scaffold_rep.generated_fault_census_files.len(), 1);
        let census_json_path = workspace.join(".anneal/generated/FaultCensus/Demo/caller.json");
        assert!(census_json_path.is_file(), "FaultCensus/Demo/caller.json must exist");
        let census_json = fs::read_to_string(&census_json_path).expect("read caller.json");
        assert!(
            census_json.contains("\"reconciliation_verdict\": \"VERIFIED\""),
            "{census_json}"
        );
        assert!(census_json.contains("\"demo::leaf\""), "{census_json}");

        let ob_text = fs::read_to_string(workspace.join(".anneal/generated/Obligations/Demo/caller.lean"))
            .expect("read Obligations/Demo/caller.lean");
        assert!(
            ob_text.contains("Fault-site census coverage summary (compiler-generated metadata):"),
            "{ob_text}"
        );
        assert!(ob_text.contains("verdict: VERIFIED"), "{ob_text}");
        assert!(!ob_text.contains("import Anneal"), "Obligations must never import Anneal");

        let agent_ctx =
            render_agent_context(&workspace, &records, None).expect("render_agent_context");
        assert!(
            agent_ctx.contains("### Fault-Site Census & Coverage Reconciliation"),
            "{agent_ctx}"
        );
        assert!(agent_ctx.contains("verdict: VERIFIED"), "{agent_ctx}");
        assert!(
            agent_ctx.contains("- Property registry: 12/12 MirFaultClass EmittedAndVerified"),
            "{agent_ctx}"
        );
        let mut gap_registry = PropertyRegistry::all_verified();
        gap_registry.set_status(MirFaultClass::DivRemByZero, PropertyStatus::UnemittedGap);
        assert_eq!(
            gap_registry.summary_line(),
            "11/12 MirFaultClass EmittedAndVerified; not verified (fail-closed): \
             div_rem_by_zero=UnemittedGap"
        );

        // `[adv ep1-B1]` `refresh_workspace_assembly` (run by every `verify`) keeps the
        // JSON receipt and the Obligations docstring summary fresh and unique.
        refresh_workspace_assembly(&workspace).expect("refresh_workspace_assembly");
        let refreshed_json = fs::read_to_string(&census_json_path).expect("json after refresh");
        assert!(
            refreshed_json.contains("\"reconciliation_verdict\": \"VERIFIED\""),
            "{refreshed_json}"
        );
        let refreshed_ob =
            fs::read_to_string(workspace.join(".anneal/generated/Obligations/Demo/caller.lean"))
                .expect("read refreshed caller obligations");
        assert_eq!(
            refreshed_ob
                .matches("Fault-site census coverage summary (compiler-generated metadata):")
                .count(),
            1,
            "{refreshed_ob}"
        );
        assert!(refreshed_ob.contains("verdict: VERIFIED"), "{refreshed_ob}");

        // Positive reconciliation on VerificationReport under PropertyRegistry::all_verified()
        let mut report = VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: "Verify.Demo.caller".to_string(),
                status: VerificationStatus::VerifiedUnconditional,
            }],
        };
        apply_fault_site_coverage_reconciliation(
            &workspace,
            &mut report,
            &PropertyRegistry::all_verified(),
            &BTreeSet::new(),
        );
        assert_eq!(
            report.status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        // Negative test 1: Downgrading a required MirFaultClass in callee (`DivRemByZero`)
        // to `UnemittedGap` fails closed with `VerificationStatus::UnknownUnmappedFaultSite`.
        let mut reg_gap = PropertyRegistry::all_verified();
        reg_gap.set_status(MirFaultClass::DivRemByZero, PropertyStatus::UnemittedGap);
        let mut report_gap = VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: "Verify.Demo.caller".to_string(),
                status: VerificationStatus::VerifiedUnconditional,
            }],
        };
        apply_fault_site_coverage_reconciliation(
            &workspace,
            &mut report_gap,
            &reg_gap,
            &BTreeSet::new(),
        );
        let status_gap = report_gap
            .status_for("Verify.Demo.caller")
            .expect("status for caller");
        assert_eq!(status_gap.as_str(), "UNKNOWN(UNMAPPED_FAULT_SITE)");
        let rendered_gap = render_verification_report(&report_gap);
        assert!(
            rendered_gap.contains("Verify.Demo.caller: UNKNOWN(UNMAPPED_FAULT_SITE)"),
            "{rendered_gap}"
        );

        // Negative test 2: Dropping a fault site from `discharged` fails closed with
        // `VerificationStatus::UnknownUnmappedFaultSite`.
        let dropped = BTreeSet::from([FaultSite::new(
            0,
            0,
            MirFaultClass::StorageLiveProtected,
        )]);
        let mut report_dropped = VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: "Verify.Demo.caller".to_string(),
                status: VerificationStatus::VerifiedUnconditional,
            }],
        };
        apply_fault_site_coverage_reconciliation(
            &workspace,
            &mut report_dropped,
            &PropertyRegistry::all_verified(),
            &dropped,
        );
        let status_dropped = report_dropped
            .status_for("Verify.Demo.caller")
            .expect("status for caller");
        assert_eq!(status_dropped.as_str(), "UNKNOWN(UNMAPPED_FAULT_SITE)");

        // Negative test 3: Truncating or deleting a callee's `Mir/<Callee>.lean`
        // fails closed with `VerificationStatus::UnknownUnmappedFaultSite`.
        fs::write(
            workspace.join(".anneal/generated/Mir/Demo/leaf.lean"),
            "import Trusted\nnamespace Mir.Demo.leaf\ndef body : CapturedMir := {\n",
        )
        .expect("truncate leaf.lean");
        let mut report_truncated = VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: "Verify.Demo.caller".to_string(),
                status: VerificationStatus::VerifiedUnconditional,
            }],
        };
        apply_fault_site_coverage_reconciliation(
            &workspace,
            &mut report_truncated,
            &PropertyRegistry::all_verified(),
            &BTreeSet::new(),
        );
        assert_eq!(
            report_truncated
                .status_for("Verify.Demo.caller")
                .expect("status for caller")
                .as_str(),
            "UNKNOWN(UNMAPPED_FAULT_SITE)"
        );

        // `[adv ep1-B1]` additional fail-closed regressions on the restored workspace.
        fs::write(
            workspace.join(".anneal/generated/Mir/Demo/leaf.lean"),
            callee_mir,
        )
        .expect("restore leaf.lean");
        let single = |module: &str, status: VerificationStatus| VerificationReport {
            items: vec![ItemVerificationReport {
                verify_module: module.to_string(),
                status,
            }],
        };
        let reconcile = |mut report: VerificationReport| -> VerificationReport {
            apply_fault_site_coverage_reconciliation(
                &workspace,
                &mut report,
                &PropertyRegistry::all_verified(),
                &BTreeSet::new(),
            );
            report
        };
        let unknown = "UNKNOWN(UNMAPPED_FAULT_SITE)";
        let restored = reconcile(single(
            "Verify.Demo.caller",
            VerificationStatus::VerifiedUnconditional,
        ));
        assert_eq!(
            restored.status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        // Negative test 4: `execute_cli` (`verify` / `agent-verify`) fails closed on
        // any `UnknownUnmappedFaultSite` item and passes a fully reconciled report.
        let cli_err = ensure_fault_site_coverage_reconciled(&report_gap)
            .expect_err("unmapped item must fail the CLI");
        assert!(cli_err.contains("Verify.Demo.caller: UNKNOWN(UNMAPPED_FAULT_SITE)"), "{cli_err}");
        assert!(ensure_fault_site_coverage_reconciled(&restored).is_ok());

        // Negative test 5: a missing subject `Mir/<Item>.lean` fails closed with no
        // escape hatch, while crate-level rollups (`CrateVerify`) are not subjects.
        let missing = reconcile(VerificationReport {
            items: vec![
                ItemVerificationReport {
                    verify_module: "Verify.Demo.ghost".to_string(),
                    status: VerificationStatus::VerifiedUnconditional,
                },
                ItemVerificationReport {
                    verify_module: "CrateVerify".to_string(),
                    status: VerificationStatus::VerifiedUnconditional,
                },
            ],
        });
        assert_eq!(
            missing.status_for("Verify.Demo.ghost").expect("ghost").as_str(),
            unknown
        );
        assert_eq!(missing.items[1].verify_module, "CrateVerify");
        assert_eq!(
            missing.items[1].status,
            VerificationStatus::VerifiedUnconditional
        );

        // Negative test 6: the verify-time scan enforces the strict `Mir/<Item>.lean`
        // grammar. A constructor-shadowing declaration is invisible to the lenient
        // `parse_lean_captured_mir_def` but changes what Lean elaborates.
        let caller_mir_path = workspace.join(".anneal/generated/Mir/Demo/caller.lean");
        let original_caller = fs::read_to_string(&caller_mir_path).expect("read caller.lean");
        let shadowed = original_caller.replacen(
            "def body : CapturedMir :=",
            "def TerminatorKind.return_ : Nat := 0\ndef body : CapturedMir :=",
            1,
        );
        assert_ne!(shadowed, original_caller);
        assert!(parse_lean_captured_mir_def(&shadowed, "body").is_ok());
        assert!(parse_lean_mir_module_body_strict(&shadowed).is_err());
        fs::write(&caller_mir_path, &shadowed).expect("write shadowed caller.lean");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller")
                .expect("caller")
                .as_str(),
            unknown
        );
        fs::write(&caller_mir_path, &original_caller).expect("restore caller.lean");

        // Negative test 7: an unclosed callee fails closed even for modular surfaces
        // and for items that merely depend on some *callee's* trusted contract; only
        // the subject's own `#[spec(trusted)]` contract relaxes callee closure.
        let caller_ob_path = workspace.join(".anneal/generated/Obligations/Demo/caller.lean");
        let original_ob = fs::read_to_string(&caller_ob_path).expect("read caller obligations");
        let unlinked_ob = original_ob.replacen("[Mir.Demo.leaf.body]", ".nil", 1);
        assert_ne!(unlinked_ob, original_ob, "{original_ob}");
        fs::write(&caller_ob_path, &unlinked_ob).expect("unlink defaultCallees");
        let caller_verify_path = workspace.join(".anneal/generated/Verify/Demo/caller.lean");
        let original_verify = fs::read_to_string(&caller_verify_path).unwrap_or_default();
        fs::write(
            &caller_verify_path,
            format!("{original_verify}\n-- ModularVerificationResult modularClaim\n"),
        )
        .expect("mark caller verify module as modular");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller")
                .expect("caller")
                .as_str(),
            unknown
        );
        let callee_trusted = VerificationStatus::VerifiedConditional {
            assumptions: vec!["Assumptions.Demo.leaf.rust_trusted_contract".to_string()],
        };
        assert_eq!(
            reconcile(single("Verify.Demo.caller", callee_trusted))
                .status_for("Verify.Demo.caller")
                .expect("caller")
                .as_str(),
            unknown
        );
        let own_trusted = VerificationStatus::VerifiedConditional {
            assumptions: vec!["Assumptions.Demo.caller.rust_trusted_contract".to_string()],
        };
        assert_eq!(
            reconcile(single("Verify.Demo.caller", own_trusted.clone()))
                .status_for("Verify.Demo.caller"),
            Some(&own_trusted)
        );

        // Negative test 8: a `defaultCallees` table that is not exactly
        // `[Mir.<Callee>.body, ...]` fails closed instead of dropping entries.
        let mangled_ob = original_ob.replacen(
            "[Mir.Demo.leaf.body]",
            "[Mir.Demo.leaf.body, extraCalleeBody]",
            1,
        );
        fs::write(&caller_ob_path, &mangled_ob).expect("mangle defaultCallees");
        let mangled = reconcile(single(
            "Verify.Demo.caller",
            VerificationStatus::VerifiedUnconditional,
        ));
        match mangled.status_for("Verify.Demo.caller") {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("defaultCallees"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }
        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");
        fs::write(&caller_verify_path, &original_verify).expect("restore caller verify");

        // Negative test 9: an Obligations module whose claims never reference the
        // subject's own `Mir.<Item>.body` discharges nothing and fails closed.
        let detached_ob = original_ob.replace("Mir.Demo.caller.body", "Mir.Demo.leaf.body");
        assert_ne!(detached_ob, original_ob);
        fs::write(&caller_ob_path, &detached_ob).expect("detach caller claim");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("never references `Mir.Demo.caller.body`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        // Negative test 10 (`[adv ep1-A1]`): detaching ONLY `def claim`'s `body :=`
        // to `Mir.Demo.leaf.body` while leaving `sigPre` / `defaultCallContract`
        // referencing `Mir.Demo.caller.body` still fails closed.
        let single_claim_detached = original_ob.replacen(
            "{ body := Mir.Demo.caller.body,",
            "{ body := Mir.Demo.leaf.body,",
            1,
        );
        assert_ne!(single_claim_detached, original_ob);
        assert!(single_claim_detached.contains("Mir.Demo.caller.body"));
        fs::write(&caller_ob_path, &single_claim_detached)
            .expect("detach single claim body in caller obligations");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("claim_mir_bodies"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        // Negative test 11 (`[adv ep1-A1]`): overriding `callees := defaultCallees`
        // with `callees := .nil` inside `def claim` while leaving
        // `def defaultCallees : List CapturedMir := [Mir.Demo.leaf.body]` intact
        // fails closed.
        let bypassed_callees_ob = original_ob.replacen(
            "callees := defaultCallees }",
            "callees := .nil }",
            1,
        );
        assert_ne!(bypassed_callees_ob, original_ob);
        assert!(bypassed_callees_ob.contains("[Mir.Demo.leaf.body]"));
        fs::write(&caller_ob_path, &bypassed_callees_ob)
            .expect("bypass defaultCallees in caller claim");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("overrides claim `callees`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        // Negative test 11b (`[adv ep1-A2]`): trailing tokens after `defaultCallees`
        // (`callees := defaultCallees.drop 1`), omitting `callees := defaultCallees` from
        // a claim record, or adding an unused `import Obligations.Demo.leaf` header
        // without `Obligations.Demo.leaf.defaultCallContract` all fail closed.
        let trailing_callees_ob = original_ob.replacen(
            "callees := defaultCallees }",
            "callees := defaultCallees.drop 1 }",
            1,
        );
        assert_ne!(trailing_callees_ob, original_ob);
        fs::write(&caller_ob_path, &trailing_callees_ob).expect("write trailing callees");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("overrides claim `callees`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        let omitted_callees_ob = original_ob.replacen(", callees := defaultCallees }", " }", 1);
        assert_ne!(omitted_callees_ob, original_ob);
        fs::write(&caller_ob_path, &omitted_callees_ob).expect("write omitted callees");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("overrides claim `callees`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        let unused_import_ob = format!("import Obligations.Demo.leaf\n{unlinked_ob}");
        fs::write(&caller_ob_path, &unused_import_ob).expect("write unused import obligations");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(
                    reason.contains("imports `Obligations.Demo.leaf` without referencing"),
                    "{reason}"
                );
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        // Negative test 12 (`[adv ep1-B2]`): an indirect call through a non-constant
        // `func` operand fails closed even though the batch still declares an inline
        // callee (`demo::leaf` stays in `defaultCallees`); only the subject's own
        // trusted contract permits unresolved indirect targets.
        let indirect_caller = original_caller.replacen(
            "(Operand.constant { ty := { kind := (RigidTy.fnDef \"demo::leaf\" List.nil), layoutIdx := 0 }, val := ConstValue.zeroSized })",
            "(Operand.copy { local_ := 1, projection := List.nil })",
            1,
        );
        assert_ne!(indirect_caller, original_caller, "{original_caller}");
        fs::write(&caller_mir_path, &indirect_caller).expect("write indirect caller.lean");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("indirect call"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }
        assert_eq!(
            reconcile(single("Verify.Demo.caller", own_trusted.clone()))
                .status_for("Verify.Demo.caller"),
            Some(&own_trusted)
        );
        fs::write(&caller_mir_path, &original_caller).expect("restore caller.lean");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        // Positive control: `extract_default_callee_suffixes_from_obligations` reads
        // multi-line tables up to the next top-level command and ignores commented-out
        // `def defaultCallees` tables.
        assert_eq!(
            extract_default_callee_suffixes_from_obligations(
                "-- def defaultCallees : List CapturedMir := [Mir.Evil.x.body]\ndef defaultCallees : List CapturedMir :=\n  [Mir.A.x.body,\n   Mir.B.y.body]\n\n/-- next -/\ndef z := 1\n"
            ),
            Ok(vec!["A.x".to_string(), "B.y".to_string()])
        );
        assert_eq!(
            extract_default_callee_suffixes_from_obligations(
                "def defaultCallees : List CapturedMir :=\n  .nil\n\n"
            ),
            Ok(Vec::new())
        );

        // Negative test 13 (`[adv ep1-B3]`): rewriting `def claim` with a positional
        // constructor (`Claim.mk ... .nil`) drops both `body :=` and `callees :=` by 1
        // (leaving global field counts equal across the other 10 claims), yet
        // `validate_obligations_canonical_claims` fails closed.
        let positional_claim_ob = original_ob.replacen(
            "{ body := Mir.Demo.caller.body, pre := spec.pre, post := spec.post, callees := defaultCallees }",
            "Claim.mk Mir.Demo.caller.body spec.pre spec.post List.nil",
            1,
        );
        assert_ne!(positional_claim_ob, original_ob);
        fs::write(&caller_ob_path, &positional_claim_ob).expect("write positional claim");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("canonical `def claim`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        // Negative test 14 (`[adv ep1-B3]`): omitting `, specCallees := defaultCallees`
        // from `equivClaim` (`StatefulEquivClaim.specCallees` defaults to `.nil` in Lean)
        // fails closed.
        let omitted_spec_callees_ob = original_ob.replacen(
            ", implCallees := defaultCallees, specCallees := defaultCallees }",
            ", implCallees := defaultCallees }",
            1,
        );
        assert_ne!(omitted_spec_callees_ob, original_ob);
        fs::write(&caller_ob_path, &omitted_spec_callees_ob)
            .expect("write omitted specCallees obligations");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("overrides claim `callees`"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }

        // Negative test 15 (`[adv ep1-B3]`): tampering with `polyClaim` in
        // `Obligations/Demo/caller.lean` or rewriting `theorem verified` in
        // `Verify/Demo/caller.lean` to prove a non-canonical claim fails closed.
        let tampered_poly_ob = original_ob.replacen(
            "VerificationResult (claimFor typeArgs)",
            "VerificationResult (Claim.mk (Mir.Demo.caller.body.instantiate typeArgs) (fun _ => True) (fun _ _ => True) List.nil)",
            1,
        );
        assert_ne!(tampered_poly_ob, original_ob);
        fs::write(&caller_ob_path, &tampered_poly_ob).expect("write tampered polyClaim");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("polyClaim"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }
        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");

        let tampered_verify = original_verify.replacen(
            "VerificationResult Obligations.Demo.caller.claim",
            "VerificationResult { body := Mir.Demo.leaf.body, pre := fun _ => True, post := fun _ _ => True, callees := .nil }",
            1,
        );
        assert_ne!(tampered_verify, original_verify, "{original_verify}");
        fs::write(&caller_verify_path, &tampered_verify).expect("write tampered Verify");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("non-canonical statement"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }
        fs::write(&caller_verify_path, &original_verify).expect("restore caller Verify");

        // Negative test 16 (`[adv ep1-B3]`): injecting an unused or non-sidecar
        // `externalSpecCallContract "demo::leaf" Mir.Demo.caller.body ...` into
        // `Obligations/Demo/caller.lean` while unlinking `defaultCallees` fails closed.
        let fake_ext_ob = unlinked_ob.replacen(
            "end Obligations.Demo.caller",
            "def fakeExt : MirCallContract := externalSpecCallContract \"demo::leaf\" Mir.Demo.caller.body (fun _ => True) (fun _ _ => True)\nend Obligations.Demo.caller",
            1,
        );
        assert_ne!(fake_ext_ob, unlinked_ob);
        fs::write(&caller_ob_path, &fake_ext_ob).expect("write fake externalSpecCallContract");
        match reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
            .status_for("Verify.Demo.caller")
        {
            Some(VerificationStatus::UnknownUnmappedFaultSite { reason, .. }) => {
                assert!(reason.contains("externalSpecCallContract"), "{reason}");
            }
            other => panic!("expected UNKNOWN(UNMAPPED_FAULT_SITE), got {other:?}"),
        }
        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");

        // Negative test 17 (`[adv ep1-B3]`): recursive self-call in `Mir.Demo.caller`:
        // fails closed when `defaultCallees := .nil`, and succeeds when
        // `defaultCallees := [Mir.Demo.caller.body]` without triggering a false
        // duplicate-`def_path` error.
        let recursive_caller = original_caller.replacen(
            "(RigidTy.fnDef \"demo::leaf\" List.nil)",
            "(RigidTy.fnDef \"demo::caller\" List.nil)",
            1,
        );
        assert_ne!(recursive_caller, original_caller);
        fs::write(&caller_mir_path, &recursive_caller).expect("write recursive caller");
        fs::write(&caller_ob_path, &unlinked_ob).expect("write unlinked recursive obligations");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller")
                .expect("caller")
                .as_str(),
            unknown
        );
        let linked_rec_ob = original_ob.replacen(
            "[Mir.Demo.leaf.body]",
            "[Mir.Demo.caller.body]",
            1,
        );
        fs::write(&caller_ob_path, &linked_rec_ob).expect("write linked recursive obligations");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );
        fs::write(&caller_mir_path, &original_caller).expect("restore caller.lean");
        fs::write(&caller_ob_path, &original_ob).expect("restore caller obligations");
        assert_eq!(
            reconcile(single("Verify.Demo.caller", VerificationStatus::VerifiedUnconditional))
                .status_for("Verify.Demo.caller"),
            Some(&VerificationStatus::VerifiedUnconditional)
        );

        let _ = fs::remove_dir_all(&workspace);
    }
}

