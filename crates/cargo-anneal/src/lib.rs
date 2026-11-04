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
pub use minirust_sync::{
    DeclChangeKind, DeclDiffEntry, ExtractedSpecDecl, LockVerificationReport, LockedSpecFile,
    MiniRustSyncSubcommand, SnapshotDiffReport, SnapshotLockEntry, SpecDeclKind,
    UpstreamMiniRustLock, diff_snapshot_directories, extract_snapshot_declarations,
    load_upstream_lock, parse_minirust_sync_args, parse_upstream_lock,
    render_snapshot_diff_markdown, render_sync_status_report, run_minirust_sync_cli,
    verify_upstream_lock,
};
pub use miri_diff::{
    KnownAnnealBugSpec, MiriDiffConfig, MiriDiffManifest, MiriDiffReport, MiriDiffTestEntry,
    MiriDiffVerdictSpec, load_miri_diff_manifest, parse_miri_diff_manifest,
    render_miri_diff_crate_verify_module, render_miri_diff_report, render_miri_diff_verify_module,
    run_miri_diff_suite, stage_miri_diff_workspace, verify_miri_diff_ub_locations,
};
pub use miri_oracle::{
    ALLOW_MISSING_MIRI_ENV, AnnealOracleConfig, AnnealOutcome, ComparisonVerdict,
    DEFAULT_CAPTURE_RUSTFLAGS, DEFAULT_MIRI_FLAGS, DEFAULT_ORACLE_FUEL, DifftestOracleConfig,
    DifftestOracleReport, DivergenceKind, ItemOracleReport, MiriOracleConfig, MiriOutcome,
    MiriToolchain, NotComparedReason, OracleItemSpec, SourcePos, SourceSpan,
    compare_miri_and_anneal, confirm_anneal_outcomes_in_kernel, discover_zero_arg_pub_fns,
    parse_anneal_probe_output, parse_miri_process_output, render_anneal_confirm_module,
    render_anneal_probe_module, render_miri_driver_source, run_anneal_oracle,
    run_difftest_oracle_pipeline, run_miri_oracle, source_files_match,
};
pub use obligations::{
    AuthoredItemModules, SubjectObligationBundle, derive_item_module_suffix,
    group_subject_obligations, module_suffix_to_rel_path, render_crate_verify_module,
    render_obligations_module, render_obligations_module_with_options, render_proof_template,
    render_proof_template_with_options, render_specs_template, render_verify_module,
    render_verify_module_with_options,
};
pub use scaffold::{
    LEAN_TOOLCHAIN, ScaffoldConfig, ScaffoldReport, detect_authored_item_modules,
    refresh_workspace_assembly, render_lakefile_toml, scaffold_init_proof_templates,
    scaffold_init_spec_templates, scaffold_workspace, scaffold_workspace_with_config,
};
pub use trace_observer::{
    BatchTraceEvalCase, EnvAction, EnvSchedule, FromScheduleBytes, RawByteTraceJson,
    RawCallEventJson, RawOutcomeJson, RawTraceEventJson, RecordedEvent, RecordedOutcome,
    RecordedRawTrace, RecordedShadowAlloc, ScheduleError, ShadowAllocEntryJson,
    TraceCapture, TraceCheckModuleConfig, TraceObserverSpec, TraceRecorder,
    capture_value_bytes, decode_recorded_raw_trace_hex, encode_recorded_raw_trace_hex,
    observe_boundary_call, parse_batch_trace_probe_output, render_batch_trace_eval_lean_module,
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
                if trimmed.is_empty() {
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
            "--out-dir" => {
                i += 1;
                let val = slice
                    .get(i)
                    .ok_or_else(|| "missing value for --out-dir".to_string())?;
                let trimmed = val.trim();
                if trimmed.is_empty() {
                    return Err("missing value for --out-dir".to_string());
                }
                out_dir = Some(PathBuf::from(trimmed));
                i += 1;
            }
            s if s.starts_with("--out-dir=") => {
                let val = s["--out-dir=".len()..].trim();
                if val.is_empty() {
                    return Err("missing value for --out-dir".to_string());
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
                        "unknown subcommand '{other}' (expected 'extract', 'scaffold', 'verify', 'check', 'lock-specs', 'agent-context', 'agent-verify', 'agent-sandbox', 'setup', 'vendor-fuchsia', 'correspondence-bugs', or 'minirust-sync')"
                    ));
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
       minirust-sync       Offline upstream MiniRust lock verifier, snapshot differ, and status reporter\n\n\
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
        }
    }
    let mut totals = format!("{unconditional_count} unconditional, {conditional_count} conditional");
    if ub_exception_count > 0 {
        totals.push_str(&format!(", {ub_exception_count} ub_exception"));
    }
    if provisional_count > 0 {
        totals.push_str(&format!(", {provisional_count} provisional_native"));
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
            let lock_path = lock_workspace_specs_with_options(
                &options.workspace_root,
                &records,
                &mutable_patterns,
                options.lock_file.as_deref(),
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
    }
}

/// Run extraction, optional `.anneal/spec-lock.json` enforcement, deterministic
/// `.anneal/generated/` regeneration, Lake kernel checking, and
/// `TrustedBoundary` auditing according to `options`.
pub fn verify_workspace_with_options(options: &CliOptions) -> Result<VerificationReport, String> {
    let (_manifest, records) = run_extract_phase(options)?;
    let enforce_lock =
        options.locked_specs || options.subcommand == CliSubcommand::AgentVerify;

    let (locked_manifest, has_locked_ub_exceptions) = if enforce_lock {
        let lock = verify_spec_lock_with_options(
            &options.workspace_root,
            &records,
            options.lock_file.as_deref(),
            options.lock_git_ref.as_deref(),
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
/// invoke `lake build`, and run the `TrustedBoundary` anti-cheat audit
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
    run_trusted_boundary_verify_audit_with_options(
        &workspace_root,
        anneal_repo_root.as_deref(),
        config.allow_assumptions,
        config.allow_provisional_native,
        config.item_filter.as_deref(),
        &matched_targets,
    )
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

/// Build the `lake build` command for `dot_anneal_dir`, applying
/// `LAKE_CACHE_ENV_DEFAULTS` for variables the environment leaves unset.
pub fn build_lake_build_command(lake_bin: &Path, dot_anneal_dir: &Path) -> Command {
    let mut cmd = Command::new(lake_bin);
    cmd.arg("build").current_dir(dot_anneal_dir);
    for (key, value) in LAKE_CACHE_ENV_DEFAULTS {
        if env::var_os(key).is_none() {
            cmd.env(key, value);
        }
    }
    cmd
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
        assert_eq!(cmd.get_current_dir(), Some(Path::new("/tmp/ws/.anneal")));
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
            },
            UnitTargetRecord {
                target: manifest.targets[1].clone(),
                lean_module_name: "Mir.Demo.__anodized_fn_requires_id".to_string(),
                item_kind: CapturedItemKind::InlineSpecRequires,
                associated_subject_def_id: Some("demo::id".to_string()),
            },
            UnitTargetRecord {
                target: manifest.targets[2].clone(),
                lean_module_name: "Mir.Demo.__anodized_fn_ensures_id".to_string(),
                item_kind: CapturedItemKind::InlineSpecEnsures,
                associated_subject_def_id: Some("demo::id".to_string()),
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
}
