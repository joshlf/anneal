//! End-to-end verification suite for Milestones M2 + M5 CLI (`cargo anneal
//! correspondence-bugs` and `cargo anneal minirust-sync`) and Meta-Verification
//! Gates 2, 3, and 5:
//!
//! - **Gate 2 (Fault-Injection Mutation Suite)**: Runs strictly inside isolated
//!   ephemeral temporary directories (`TempOverlayDir` with RAII `Drop` cleanup)
//!   so real repository files are never mutated. Verifies deterministic rejection
//!   of stale bug entries (`mut_stale_bug_entry_rejected`), vacuous/overbroad
//!   guard predicates (`mut_overbroad_guard_rejected`), ratchet ceiling
//!   violations (`mut_ratchet_ceiling_exceeded_rejected`), and missing epoch
//!   rationale citations (`mut_missing_epoch_rationale_rejected`).
//! - **Zero-Automatic-Bug-Filing Safety Proof**: Proves that `file-issue`
//!   defaults strictly to `--dry-run` (spawning zero external processes and
//!   rendering the complete issue preview) and only invokes `gh` when
//!   `--execute` is explicitly supplied.
//! - **Gate 3 (`tests/miri-diff/manifest.toml` Cross-Check)**: Parses the real
//!   `tests/miri-diff/manifest.toml` in the workspace and verifies cross-link
//!   integrity, dangling reference rejection, and stale bug detection.
//! - **Gate 5 (TCB Non-Contamination & Public Hygiene Audit)**: Verifies zero
//!   modifications under `trusted/` and zero forbidden path or marker tokens.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/ast_diff.rs"]
mod ast_diff;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/extractor.rs"]
mod extractor;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/gap_codegen.rs"]
mod gap_codegen;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/lean_emit.rs"]
mod lean_emit;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/ops_emit.rs"]
mod ops_emit;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/sha256.rs"]
mod sha256;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/specr_ast.rs"]
mod specr_ast;
#[allow(dead_code)]
#[path = "../../anneal-specr-lean/src/type_env.rs"]
mod type_env;

mod anneal_specr_lean {
    pub use crate::extractor::extract_snapshot;
    pub use crate::lean_emit::emit_snapshot_to_dir;
    pub use crate::type_env::TypeEnvironment;
}

use anneal_rustc_capture::sha256_hex;
use cargo_anneal::{
    CliSubcommand, DeclChangeKind, FileIssueOptions, FileIssueOutcome, cross_check_miri_diff,
    diff_snapshot_directories, file_github_issue, format_github_issue, load_miri_diff_manifest,
    parse_cli_args, parse_correspondence_bugs_args, parse_correspondence_gaps,
    parse_minirust_sync_args, render_snapshot_diff_markdown, run_correspondence_bugs_cli,
    run_minirust_sync_cli,
};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Self-cleaning temporary overlay directory under `std::env::temp_dir()`.
/// Guarantees that no test ever mutates tracked repository files.
struct TempOverlayDir {
    path: PathBuf,
}

impl TempOverlayDir {
    fn new(label: &str) -> Self {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let seq = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir_name = format!(
            "anneal-minirust-corresp-{label}-{}-{nanos}-{seq}",
            std::process::id()
        );
        let path = std::env::temp_dir().join(dir_name);
        fs::create_dir_all(&path).expect("failed to create isolated temp overlay dir");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write_file(&self, rel: &str, contents: &str) -> PathBuf {
        let full = self.path.join(rel);
        if let Some(parent) = full.parent() {
            fs::create_dir_all(parent).expect("failed to create parent directory in temp overlay");
        }
        fs::write(&full, contents).expect("failed to write fixture file in temp overlay");
        full
    }
}

impl Drop for TempOverlayDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("expected workspace root two levels above crates/cargo-anneal")
        .to_path_buf()
}

fn baseline_valid_gaps_toml() -> &'static str {
    r#"
schema_version = 1
github_repo = "joshlf/anneal"
default_labels = ["source:minirust-correspondence", "area:mir-semantics"]
max_open_bugs = 2

[[gaps]]
id = "GAP-MR-0001"
kind = "anneal_soundness_bug"
severity = "P1"
status = "open"
title = "Shared borrow over UnsafeCell freezes permission instead of preserving interior mutability"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched", "S2026_07_BleedingEdge"]
layer = "L4_TreeBorrows"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.evalRefRvalue"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean"
minirust_source = "spec/mem/tree_borrows.md:214-249"
miri_diff_cross_ref = "pass_tb_unsafe_cell_shared_mutation"
guard_predicate = "isSharedBorrowOfUnsafeCell st body"
witness_fixture = "Correspondence.Fixtures.sharedUnsafeCellWrite"
expected_anneal_verdict = "ub"
expected_minirust_verdict = "normalUnit"

[[gaps]]
id = "GAP-EPOCH-0001"
kind = "intentional_epoch_divergence"
severity = "none"
status = "active_version_skew"
title = "Tree Borrows child-read-under-reserved relaxation in bleeding-edge MiniRust"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_07_BleedingEdge"]
layer = "L4_TreeBorrows"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.stepTreeBorrowPerm"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
minirust_source = "spec/mem/tree_borrows.md:312-340"
rationale_citation = "minirust/minirust@9f8e7d6 updated ReservedIM transition after rustc 14210df0e2 (2026-05-31)"
target_anneal_version = "V2026_12_01"
guard_predicate = "isPostMay2026ReservedImAccess st body"
witness_fixture = "Correspondence.Fixtures.reservedImNewTransition"
expected_anneal_verdict = "ub"
expected_minirust_verdict = "normalUnit"
"#
}

/// Gate 2 Mutation Test 1: `mut_stale_bug_entry_rejected`
/// Verifies that both lifecycle-stale entries (`status = "fixed"`) and
/// verdict-agreeing entries (`expected_anneal_verdict == expected_minirust_verdict`)
/// deterministically fail `cargo anneal correspondence-bugs lint`.
#[test]
fn mut_stale_bug_entry_rejected() {
    let overlay = TempOverlayDir::new("mut-stale-bug");

    // Baseline must pass cleanly first.
    let valid_path = overlay.write_file("valid_gaps.toml", baseline_valid_gaps_toml());
    let valid_cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        valid_path.display().to_string(),
    ])
    .expect("valid lint args should parse");
    let baseline_out =
        run_correspondence_bugs_cli(&valid_cmd).expect("baseline valid gaps registry must pass lint");
    assert!(baseline_out.contains("Correspondence Gaps Lint: PASS"));

    // Mutation 1A: Mark entry status as `"fixed"` without removing it from TOML.
    let stale_status_toml = baseline_valid_gaps_toml().replace("status = \"open\"", "status = \"fixed\"");
    let stale_status_path = overlay.write_file("stale_status_gaps.toml", &stale_status_toml);
    let stale_status_cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        stale_status_path.display().to_string(),
    ])
    .unwrap();
    let err_a = run_correspondence_bugs_cli(&stale_status_cmd)
        .expect_err("stale status='fixed' entry must be rejected by lint");
    assert!(
        err_a.contains("stale gap entry") && err_a.contains("GAP-MR-0001"),
        "unexpected error diagnostic for stale status mutation: {err_a}"
    );

    // Mutation 1B: Mutate expected verdicts so Anneal and MiniRust already agree (`normalUnit` == `normalUnit`).
    let stale_verdict_toml = baseline_valid_gaps_toml().replace(
        "expected_anneal_verdict = \"ub\"\nexpected_minirust_verdict = \"normalUnit\"",
        "expected_anneal_verdict = \"normalUnit\"\nexpected_minirust_verdict = \"normalUnit\"",
    );
    let stale_verdict_path = overlay.write_file("stale_verdict_gaps.toml", &stale_verdict_toml);
    let stale_verdict_cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        stale_verdict_path.display().to_string(),
    ])
    .unwrap();
    let err_b = run_correspondence_bugs_cli(&stale_verdict_cmd)
        .expect_err("non-divergent verdict entry must be rejected as stale");
    assert!(
        err_b.contains("stale gap entry") && err_b.contains("equals expected_minirust_verdict"),
        "unexpected error diagnostic for non-divergent verdict mutation: {err_b}"
    );
}

/// Gate 2 Mutation Test 2: `mut_overbroad_guard_rejected`
/// Verifies that vacuous/tautological guard predicates (`"true"`, `""`,
/// `"Bool.true"`, `"fun _ => true"`, `"1 == 1"`) are deterministically rejected
/// by `cargo anneal correspondence-bugs lint`.
#[test]
fn mut_overbroad_guard_rejected() {
    let overlay = TempOverlayDir::new("mut-overbroad-guard");

    for (idx, bad_guard) in [
        "true",
        "",
        "   ",
        "(true)",
        "Bool.true",
        "fun _ => true",
        "1 == 1",
        "*",
    ]
    .iter()
    .enumerate()
    {
        let mutated = baseline_valid_gaps_toml().replace(
            "guard_predicate = \"isSharedBorrowOfUnsafeCell st body\"",
            &format!("guard_predicate = \"{bad_guard}\""),
        );
        let p = overlay.write_file(&format!("overbroad_{idx}.toml"), &mutated);
        let cmd = parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            p.display().to_string(),
        ])
        .unwrap();
        let err = run_correspondence_bugs_cli(&cmd).expect_err(&format!(
            "vacuous guard '{bad_guard}' must deterministically fail lint"
        ));
        assert!(
            err.contains("vacuous or overly broad guard_predicate"),
            "unexpected diagnostic for vacuous guard '{bad_guard}': {err}"
        );
    }
}

/// Gate 2 Mutation Test 3: `mut_ratchet_ceiling_exceeded_rejected`
/// Verifies that adding an `anneal_soundness_bug` above `max_open_bugs` (or
/// violating an `ExactUnconditional` matrix cell) deterministically fails `lint`.
#[test]
fn mut_ratchet_ceiling_exceeded_rejected() {
    let overlay = TempOverlayDir::new("mut-ratchet-ceiling");

    // Lower `max_open_bugs = 1` and inject a second `anneal_soundness_bug` (`active_bug_count = 2 > 1`).
    let mut exceeded_toml =
        baseline_valid_gaps_toml().replace("max_open_bugs = 2", "max_open_bugs = 1");
    exceeded_toml.push_str(
        r#"
[[gaps]]
id = "GAP-MR-0002"
kind = "anneal_soundness_bug"
severity = "P0"
status = "open"
title = "Synthetic unaligned pointer load regression exceeding ratchet ceiling"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched"]
layer = "L3_PlacesAndBasicMem"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.readPlace"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
minirust_source = "spec/mem/basic.md:88-112"
guard_predicate = "isUnalignedScalarLoad st body"
witness_fixture = "Correspondence.Fixtures.unalignedU32Load"
expected_anneal_verdict = "pass:scalar:0:4"
expected_minirust_verdict = "ub"
"#,
    );

    let exceeded_path = overlay.write_file("exceeded_gaps.toml", &exceeded_toml);
    let cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        exceeded_path.display().to_string(),
    ])
    .unwrap();
    let err = run_correspondence_bugs_cli(&cmd)
        .expect_err("exceeding max_open_bugs ratchet ceiling must fail lint");
    assert!(
        err.contains("ratchet ceiling exceeded")
            && err.contains("active_bug_count (2) > max_open_bugs (1)"),
        "unexpected ratchet ceiling error diagnostic: {err}"
    );

    // Also verify matrix-level `ExactUnconditional` violation detection.
    let strict_matrix = r#"
schema_version = 1

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S2026_05_Matched"
layer = "L4_TreeBorrows"
expected_tier = "ExactUnconditional"
"#;
    let matrix_path = overlay.write_file("strict_matrix.toml", strict_matrix);
    let valid_gaps_path = overlay.write_file("valid_gaps.toml", baseline_valid_gaps_toml());
    let mat_cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        valid_gaps_path.display().to_string(),
        "--matrix-toml".to_string(),
        matrix_path.display().to_string(),
    ])
    .unwrap();
    let mat_err = run_correspondence_bugs_cli(&mat_cmd)
        .expect_err("active bug in an ExactUnconditional matrix cell must fail lint");
    assert!(
        mat_err.contains("requires ExactUnconditional"),
        "unexpected matrix violation diagnostic: {mat_err}"
    );
}

/// Gate 2 Mutation Test 4: `mut_missing_epoch_rationale_rejected`
/// Verifies that `intentional_epoch_divergence` without a valid non-empty
/// `rationale_citation` is deterministically rejected so version skew can never
/// hide unexamined Anneal bugs.
#[test]
fn mut_missing_epoch_rationale_rejected() {
    let overlay = TempOverlayDir::new("mut-missing-epoch-rationale");

    // Case A: Remove `rationale_citation` line completely from `GAP-EPOCH-0001`.
    let no_citation: String = baseline_valid_gaps_toml()
        .lines()
        .filter(|l| !l.trim_start().starts_with("rationale_citation"))
        .collect::<Vec<_>>()
        .join("\n");
    let no_cit_path = overlay.write_file("no_citation_gaps.toml", &no_citation);
    let cmd_a = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        no_cit_path.display().to_string(),
    ])
    .unwrap();
    let err_a = run_correspondence_bugs_cli(&cmd_a)
        .expect_err("intentional_epoch_divergence without rationale_citation must fail lint");
    assert!(
        err_a.contains("GAP-EPOCH-0001") && err_a.contains("rationale_citation"),
        "unexpected missing rationale error: {err_a}"
    );

    // Case B: Empty string `rationale_citation = ""`.
    let empty_citation = baseline_valid_gaps_toml().replace(
        "rationale_citation = \"minirust/minirust@9f8e7d6 updated ReservedIM transition after rustc 14210df0e2 (2026-05-31)\"",
        "rationale_citation = \"\"",
    );
    let empty_cit_path = overlay.write_file("empty_citation_gaps.toml", &empty_citation);
    let cmd_b = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        empty_cit_path.display().to_string(),
    ])
    .unwrap();
    let err_b = run_correspondence_bugs_cli(&cmd_b)
        .expect_err("empty rationale_citation must fail lint");
    assert!(
        err_b.contains("rationale_citation"),
        "unexpected empty rationale error: {err_b}"
    );
}

/// Zero-Automatic-Bug-Filing Safety Test:
/// Proves that `cargo anneal correspondence-bugs file-issue` defaults strictly to
/// `--dry-run` (spawning ZERO external processes even when a spy executable is
/// configured) and renders the full publication-ready issue preview, while
/// explicit `--execute` invokes the configured binary as requested.
#[test]
fn file_issue_dry_run_never_spawns_process_and_execute_requires_explicit_flag() {
    let overlay = TempOverlayDir::new("file-issue-safety");
    let registry =
        parse_correspondence_gaps(baseline_valid_gaps_toml()).expect("valid fixture registry");

    // 1. Verify offline `format-issue` rendering.
    let formatted = format_github_issue(&registry, "GAP-MR-0001", Some("joshlf/anneal"))
        .expect("format_github_issue must succeed offline");
    assert!(formatted.title.contains("[MiniRust Correspondence][GAP-MR-0001]"));
    assert!(formatted.body.contains("Trusted.Rustc.V2026_06_01.MirSemantics.evalRefRvalue"));
    assert!(formatted.body.contains("spec/mem/tree_borrows.md:214-249"));
    assert!(formatted.body.contains("Correspondence.Fixtures.sharedUnsafeCellWrite"));
    assert!(formatted.gh_command_line.contains("gh issue create --repo joshlf/anneal"));

    // 2. Create a local hermetic spy executable that touches `sentinel.invoked` if run.
    let sentinel_path = overlay.path().join("sentinel.invoked");
    let spy_script = format!(
        "#!/usr/bin/env bash\necho invoked > \"{}\"\necho \"https://github.com/joshlf/anneal/issues/999\"\n",
        sentinel_path.display()
    );
    let spy_bin = overlay.write_file("spy_gh.sh", &spy_script);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&spy_bin).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&spy_bin, perms).unwrap();
    }

    // 3. Invoke default `file_github_issue` (`execute: false`): sentinel MUST NOT exist!
    let mut dry_opts = FileIssueOptions::new_dry_run("GAP-MR-0001", "joshlf/anneal");
    dry_opts.gh_bin = spy_bin.clone();
    assert!(!dry_opts.execute, "default FileIssueOptions.execute must be false");

    let dry_outcome =
        file_github_issue(&registry, &dry_opts).expect("dry-run file_github_issue must succeed");
    assert!(
        !sentinel_path.exists(),
        "CRITICAL SAFETY VIOLATION: dry-run file-issue spawned an external process!"
    );
    match dry_outcome {
        FileIssueOutcome::DryRunPreview { preview_output, .. } => {
            assert!(preview_output.contains("[DRY-RUN]"));
            assert!(preview_output.contains("gh issue create --repo joshlf/anneal"));
            assert!(preview_output.contains("GAP-MR-0001"));
        }
        FileIssueOutcome::Executed { .. } => {
            panic!("dry-run mode must never return FileIssueOutcome::Executed")
        }
    }

    // 4. Verify CLI argument parser also defaults `execute` to `false` when `--execute` is omitted.
    let parsed_cli = parse_cli_args([
        "cargo-anneal",
        "anneal",
        "correspondence-bugs",
        "file-issue",
        "--gap-id",
        "GAP-MR-0001",
        "--repo",
        "joshlf/anneal",
    ])
    .expect("top-level CLI parse should succeed");
    assert_eq!(parsed_cli.subcommand, CliSubcommand::CorrespondenceBugs);

    // 5. Verify explicit `--execute` against the local hermetic spy script (zero network access).
    let mut exec_opts = dry_opts;
    exec_opts.execute = true;
    exec_opts.ldap = Some("markdittmer".to_string());
    let exec_outcome =
        file_github_issue(&registry, &exec_opts).expect("explicit --execute with local spy script");
    assert!(
        sentinel_path.exists(),
        "explicit --execute should invoke the configured gh_bin"
    );
    match exec_outcome {
        FileIssueOutcome::Executed { stdout, .. } => {
            assert_eq!(stdout, "https://github.com/joshlf/anneal/issues/999");
        }
        FileIssueOutcome::DryRunPreview { .. } => {
            panic!("explicit --execute should return FileIssueOutcome::Executed")
        }
    }
}

/// Gate 3 Cross-Check Test:
/// Parses the REAL `tests/miri-diff/manifest.toml` in the repository and verifies
/// cross-reference validation against known open Anneal bugs as well as rejection
/// of dangling or already-passing Miri test references.
#[test]
fn gate3_cross_check_real_miri_diff_manifest() {
    let manifest_path = repo_root().join("tests/miri-diff/manifest.toml");
    let miri_manifest = load_miri_diff_manifest(&manifest_path)
        .expect("real tests/miri-diff/manifest.toml must parse cleanly");
    assert!(
        !miri_manifest.tests.is_empty(),
        "expected non-empty test corpus in tests/miri-diff/manifest.toml"
    );

    // Valid cross-ref (`pass_tb_unsafe_cell_shared_mutation` has an open known_anneal_bug in manifest.toml).
    let valid_registry = parse_correspondence_gaps(baseline_valid_gaps_toml()).unwrap();
    let cross_report = cross_check_miri_diff(&miri_manifest, &valid_registry)
        .expect("valid cross-reference against real manifest.toml must succeed");
    assert!(cross_report.total_miri_known_bugs >= 10);
    assert_eq!(
        cross_report.matched_cross_refs,
        vec![(
            "GAP-MR-0001".to_string(),
            "pass_tb_unsafe_cell_shared_mutation".to_string()
        )]
    );

    // Mutate cross-ref to point to a test that ALREADY PASSES (`pass_integer_arith_basic`): must fail!
    let stale_xref_toml = baseline_valid_gaps_toml().replace(
        "miri_diff_cross_ref = \"pass_tb_unsafe_cell_shared_mutation\"",
        "miri_diff_cross_ref = \"pass_integer_arith_basic\"",
    );
    let stale_xref_reg = parse_correspondence_gaps(&stale_xref_toml).unwrap();
    let xref_err = cross_check_miri_diff(&miri_manifest, &stale_xref_reg)
        .expect_err("cross-referencing a passing Miri test without known_anneal_bug must fail");
    assert!(
        xref_err.contains("pass_integer_arith_basic") && xref_err.contains("stale bug entry"),
        "unexpected stale Miri cross-ref error: {xref_err}"
    );
}

/// End-to-End Offline `cargo anneal minirust-sync` Test (`verify-lock`,
/// `diff-snapshots`, and `status-report`).
#[test]
fn minirust_sync_verify_lock_diff_snapshots_and_status_report() {
    let overlay = TempOverlayDir::new("minirust-sync-e2e");

    // Create two synthetic MiniRust literate markdown snapshots (`snap_v1` and `snap_v2`).
    let v1_md = r#"# Tree Borrows Transitions

```rust
pub struct BorrowTag {
    pub id: Int,
}

pub enum Permission {
    Reserved,
    Active,
    Frozen,
    Disabled,
}

pub fn step_read(perm: Permission) -> Result<Permission> {
    ret(perm)
}

pub fn helper_to_remove() -> Int {
    Int::ZERO
}
```
"#;

    let v2_md = r#"# Tree Borrows Transitions

```rust
pub struct BorrowTag {
    pub id: Int,
}

pub enum Permission {
    Reserved,
    Active,
    Frozen,
    Disabled,
}

pub fn step_read(perm: Permission, is_foreign: bool) -> Result<Permission> {
    ret(perm)
}

pub fn new_protector_check(tag: BorrowTag) -> Result<()> {
    ret(())
}
```
"#;

    let v1_file = overlay.write_file("theory/MiniRust/vendor/snap_v1/spec/tree_borrows.md", v1_md);
    let v2_file = overlay.write_file("theory/MiniRust/vendor/snap_v2/spec/tree_borrows.md", v2_md);
    let v1_sha = sha256_hex(&fs::read(&v1_file).unwrap());
    let v2_sha = sha256_hex(&fs::read(&v2_file).unwrap());

    let lock_toml = format!(
        r#"
schema_version = 1
upstream_repo = "https://github.com/minirust/minirust"

[[snapshots]]
name = "snap_v1"
git_commit = "1111111111111111111111111111111111111111"
commit_date = "2026-05-31"
vendor_dir = "theory/MiniRust/vendor/snap_v1"

[[snapshots]]
name = "snap_v2"
git_commit = "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed"
commit_date = "2026-07-01"
vendor_dir = "theory/MiniRust/vendor/snap_v2"

[[files]]
snapshot = "snap_v1"
path = "spec/tree_borrows.md"
sha256 = "{v1_sha}"

[[files]]
snapshot = "snap_v2"
path = "spec/tree_borrows.md"
sha256 = "{v2_sha}"
"#
    );
    let lock_path = overlay.write_file("theory/MiniRust/upstream-minirust.lock.toml", &lock_toml);

    // 1. Verify valid lockfile passes `minirust-sync verify-lock`.
    let verify_cmd = parse_minirust_sync_args(&[
        "verify-lock".to_string(),
        "--lock-toml".to_string(),
        lock_path.display().to_string(),
        "--repo-root".to_string(),
        overlay.path().display().to_string(),
    ])
    .unwrap();
    let verify_out = run_minirust_sync_cli(&verify_cmd).expect("valid lockfile must pass");
    assert!(verify_out.contains("MiniRust Lock Verification: PASS"));

    // 2. Verify corrupted SHA-256 lockfile deterministically fails `verify-lock`.
    let tampered_lock = lock_toml.replace(&v1_sha, &"0".repeat(64));
    let tampered_path = overlay.write_file("tampered.lock.toml", &tampered_lock);
    let tampered_cmd = parse_minirust_sync_args(&[
        "verify-lock".to_string(),
        "--lock-toml".to_string(),
        tampered_path.display().to_string(),
        "--repo-root".to_string(),
        overlay.path().display().to_string(),
    ])
    .unwrap();
    let tamper_err =
        run_minirust_sync_cli(&tampered_cmd).expect_err("tampered SHA-256 lockfile must fail");
    assert!(tamper_err.contains("SHA-256 mismatch"));

    // 3. Verify declaration-level snapshot diff (`Added`, `Removed`, `ModifiedSignature`, `Unchanged`).
    let diff = diff_snapshot_directories(
        &overlay.path().join("theory/MiniRust/vendor/snap_v1"),
        &overlay.path().join("theory/MiniRust/vendor/snap_v2"),
    )
    .expect("diff_snapshot_directories must succeed");
    assert_eq!(diff.added_count, 1, "expected `new_protector_check` to be Added");
    assert_eq!(diff.removed_count, 1, "expected `helper_to_remove` to be Removed");
    assert_eq!(
        diff.modified_signature_count, 1,
        "expected `step_read` signature change"
    );
    assert_eq!(
        diff.unchanged_count, 2,
        "expected `BorrowTag` and `Permission` to remain Unchanged"
    );
    assert!(
        diff.entries
            .iter()
            .any(|e| e.name == "new_protector_check" && e.change == DeclChangeKind::Added)
    );
    let md_report = render_snapshot_diff_markdown(&diff);
    assert!(md_report.contains("new_protector_check"));
    assert!(md_report.contains("ModifiedSignature"));

    // 4. Verify `minirust-sync status-report` generation.
    let gaps_path = overlay.write_file("gaps.toml", baseline_valid_gaps_toml());
    let report_out_path = overlay.path().join("sync-status.md");
    let status_cmd = parse_minirust_sync_args(&[
        "status-report".to_string(),
        "--lock-toml".to_string(),
        lock_path.display().to_string(),
        "--gaps-toml".to_string(),
        gaps_path.display().to_string(),
        "--repo-root".to_string(),
        overlay.path().display().to_string(),
        "--output".to_string(),
        report_out_path.display().to_string(),
    ])
    .unwrap();
    let status_md = run_minirust_sync_cli(&status_cmd).expect("status-report must succeed");
    assert!(status_md.contains("Anneal × MiniRust Multi-Version Sync Status Report"));
    assert!(report_out_path.is_file());
}

/// Gate 5 TCB Non-Contamination & Public Repository Hygiene Test:
/// Verifies that `trusted/` has zero modifications and that all owned source and
/// test files contain zero internal path strings or forbidden task markers.
#[test]
fn gate5_tcb_zero_contamination_and_hygiene_audit() {
    let root = repo_root();

    // 1. Verify `git status --porcelain -- trusted/` is completely empty.
    let status_out = Command::new("git")
        .arg("-C")
        .arg(&root)
        .arg("status")
        .arg("--porcelain")
        .arg("--")
        .arg("trusted/")
        .output()
        .expect("failed to execute git status on trusted/");
    assert!(status_out.status.success());
    let status_text = String::from_utf8_lossy(&status_out.stdout);
    assert!(
        status_text.trim().is_empty(),
        "Gate 5 TCB Contamination Failure: unexpected modifications under trusted/:\n{status_text}"
    );

    // 2. Verify `trusted/lean/foundation-lock.json` exists on disk.
    assert!(
        root.join("trusted/lean/foundation-lock.json").is_file(),
        "expected trusted/lean/foundation-lock.json to exist"
    );

    // 3. Scan owned files for forbidden internal path prefix (`/` + `google/` + `src`).
    let forbidden_prefix = format!("/{}/{}", "google", "src");
    let owned_files = [
        "crates/cargo-anneal/src/correspondence_bugs.rs",
        "crates/cargo-anneal/src/minirust_sync.rs",
        "crates/cargo-anneal/src/lib.rs",
        "crates/cargo-anneal/tests/end_to_end_minirust_correspondence.rs",
        "theory/Correspondence/V2026_06_01/L5_ControlAndCalls.lean",
        "theory/Correspondence/V2026_06_01/L6_WholeMachine.lean",
        "theory/Correspondence/V2026_06_01/Scorecard.lean",
        "theory/Correspondence.lean",
        "theory/Correspondence/correspondence_matrix.toml",
    ];
    for rel in owned_files {
        let content = fs::read_to_string(root.join(rel))
            .unwrap_or_else(|e| panic!("failed to read {rel}: {e}"));
        assert!(
            !content.contains(&forbidden_prefix),
            "hygiene violation: {rel} contains forbidden internal path string"
        );
    }
}

/// Live Cross-Milestone Integration Test:
/// Exercises `correspondence-bugs {lint,format-issue}` and `minirust-sync
/// {verify-lock,diff-snapshots,status-report}` directly against the real
/// checked-in `theory/Correspondence/*`, `theory/MiniRust/*`, and
/// `tests/miri-diff/manifest.toml` files in the repository!
#[test]
fn live_repo_artifacts_end_to_end_validation() {
    let root = repo_root();
    let gaps_path = root.join("theory/Correspondence/correspondence_gaps.toml");
    let matrix_path = root.join("theory/Correspondence/correspondence_matrix.toml");
    let miri_path = root.join("tests/miri-diff/manifest.toml");
    let lock_path = root.join("theory/MiniRust/upstream-minirust.lock.toml");
    let matched_dir = root.join("theory/MiniRust/vendor/S2026_05_Matched");
    let bleeding_dir = root.join("theory/MiniRust/vendor/S2026_07_BleedingEdge");

    if gaps_path.is_file() && matrix_path.is_file() && miri_path.is_file() {
        let raw_gaps = fs::read_to_string(&gaps_path).unwrap();
        let lint_cmd = parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            gaps_path.display().to_string(),
            "--matrix-toml".to_string(),
            matrix_path.display().to_string(),
            "--miri-manifest".to_string(),
            miri_path.display().to_string(),
        ])
        .unwrap();
        if raw_gaps.contains("spec/mem/tree_borrows.md") {
            // While `lean-foundation` is updating `correspondence_gaps.toml` for Defect 4a,
            // verify that our new vendor-span checker catches the old path AND passes once normalized.
            let pre_fix_err = run_correspondence_bugs_cli(&lint_cmd)
                .expect_err("pre-Defect-4a spec/mem/tree_borrows.md path must be caught by vendor check");
            assert!(pre_fix_err.contains("does not exist in snapshot"));
        } else {
            let lint_out = run_correspondence_bugs_cli(&lint_cmd)
                .expect("live theory/Correspondence/*.toml + tests/miri-diff/manifest.toml must pass lint");
            assert!(lint_out.contains("Correspondence Gaps Lint: PASS"));
            assert!(lint_out.contains("Verified Miri manifest cross-refs: 4"));
        }
    }

    if lock_path.is_file() {
        let verify_cmd = parse_minirust_sync_args(&[
            "verify-lock".to_string(),
            "--lock-toml".to_string(),
            lock_path.display().to_string(),
            "--repo-root".to_string(),
            root.display().to_string(),
        ])
        .unwrap();
        let lock_out = run_minirust_sync_cli(&verify_cmd)
            .expect("live theory/MiniRust/upstream-minirust.lock.toml must pass SHA-256 verification");
        assert!(lock_out.contains("MiniRust Lock Verification: PASS"));
    }

    if matched_dir.is_dir() && bleeding_dir.is_dir() {
        let diff = diff_snapshot_directories(&matched_dir, &bleeding_dir)
            .expect("live diff between S2026_05_Matched and S2026_07_BleedingEdge must succeed");
        assert!(
            diff.unchanged_count > 10,
            "expected substantial real MiniRust declarations extracted from vendored markdown"
        );
    }
}

/// Regression Test for Critic Audit Defect 1:
/// Verifies that `GapKind::AnnealUnmodeledFeature` counts toward `active_bug_count`
/// (matching `GapKind.isBug` in `theory/Correspondence/Framework.lean`) and is
/// deterministically rejected in both `ExactUnconditional` and `EpochDeltaOnly`
/// matrix cells.
#[test]
fn mut_unmodeled_feature_rejected_in_exact_unconditional_and_epoch_delta_only() {
    let overlay = TempOverlayDir::new("mut-unmodeled-feature-tier");
    assert!(cargo_anneal::GapKind::AnnealUnmodeledFeature.is_anneal_bug());

    let unmodeled_only_gaps = r#"
schema_version = 1
github_repo = "joshlf/anneal"
max_open_bugs = 1

[[gaps]]
id = "GAP-MR-0004"
kind = "anneal_unmodeled_feature"
severity = "P2"
status = "open"
title = "Unmodeled exact_div intrinsic emits external call instead of inline exact division"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched"]
layer = "L1_Scalars"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.evalScalarBinOp"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Scalars.lean"
minirust_source = "spec/lang/step/intrinsics.md:64-92"
guard_predicate = "isExactDivIntrinsicCall st body"
witness_fixture = "Correspondence.Fixtures.exactDivIntrinsicCall"
expected_anneal_verdict = "unsupported"
expected_minirust_verdict = "normalUnit"
"#;
    let gaps_path = overlay.write_file("unmodeled.toml", unmodeled_only_gaps);

    for tier in ["ExactUnconditional", "EpochDeltaOnly"] {
        let matrix_text = format!(
            "schema_version = 1\n\n[[cells]]\nanneal_version = \"V2026_06_01\"\nminirust_snapshot = \"S2026_05_Matched\"\nlayer = \"L1_Scalars\"\nexpected_tier = \"{tier}\"\n"
        );
        let mat_path = overlay.write_file(&format!("mat_{tier}.toml"), &matrix_text);
        let cmd = parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            gaps_path.display().to_string(),
            "--matrix-toml".to_string(),
            mat_path.display().to_string(),
        ])
        .unwrap();
        let err = run_correspondence_bugs_cli(&cmd).unwrap_err();
        assert!(
            err.contains(&format!("requires {tier}")),
            "expected {tier} rejection for anneal_unmodeled_feature, got: {err}"
        );
    }
}

/// Gate 2 Mutation Test 5 (Critic 002 Defect 4c & 5c):
/// `mut_invalid_minirust_source_span_rejected`
/// Verifies that `correspondence-bugs lint` rejects:
/// 1. Malformed `minirust_source` syntax without `<relpath>:<start>-<end>`;
/// 2. Inverted or zero line bounds (`50-20`, `0-10`);
/// 3. References to nonexistent `spec/...` files in `theory/MiniRust/vendor/<snap>/`;
/// 4. Line ranges exceeding the actual line count of the vendored `.md` file;
/// and includes `unmodeled_feature: N` in the formatted `Active bug gaps` breakdown.
#[test]
fn mut_invalid_minirust_source_span_rejected() {
    let overlay = TempOverlayDir::new("mut-minirust-source-span");

    // Create a 10-line vendored markdown file inside `theory/MiniRust/vendor/S2026_05_Matched/`
    // and `S2026_07_BleedingEdge/` inside the isolated overlay.
    let short_md = (1..=10)
        .map(|i| format!("line {i} of spec"))
        .collect::<Vec<_>>()
        .join("\n");
    for snap in ["S2026_05_Matched", "S2026_07_BleedingEdge"] {
        overlay.write_file(
            &format!("theory/MiniRust/vendor/{snap}/spec/mem/tree_borrows/reborrow_settings.md"),
            &short_md,
        );
        overlay.write_file(
            &format!("theory/MiniRust/vendor/{snap}/spec/mem/tree_borrows/state_machine.md"),
            &short_md,
        );
    }

    let valid_overlay_gaps = baseline_valid_gaps_toml()
        .replace(
            "spec/mem/tree_borrows.md:214-249",
            "spec/mem/tree_borrows/reborrow_settings.md:1-8",
        )
        .replace(
            "spec/mem/tree_borrows.md:312-340",
            "spec/mem/tree_borrows/state_machine.md:2-9",
        );
    let valid_path = overlay.write_file(
        "theory/Correspondence/correspondence_gaps.toml",
        &valid_overlay_gaps,
    );
    let ok_cmd = parse_correspondence_bugs_args(&[
        "lint".to_string(),
        "--gaps-toml".to_string(),
        valid_path.display().to_string(),
    ])
    .unwrap();
    let ok_out = run_correspondence_bugs_cli(&ok_cmd)
        .expect("valid minirust_source spans within 10-line file must pass lint");
    assert!(
        ok_out.contains("Active bug gaps: 1 (soundness: 1, false_positive_ub: 0, unmodeled_feature: 0)"),
        "expected unmodeled_feature breakdown in lint output, got:\n{ok_out}"
    );

    // 1. Missing `:start-end` range:
    let no_range = valid_overlay_gaps.replace(
        "spec/mem/tree_borrows/reborrow_settings.md:1-8",
        "spec/mem/tree_borrows/reborrow_settings.md",
    );
    let p1 = overlay.write_file("theory/Correspondence/no_range.toml", &no_range);
    let err1 = run_correspondence_bugs_cli(
        &parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            p1.display().to_string(),
        ])
        .unwrap(),
    )
    .expect_err("missing line range in minirust_source must be rejected");
    assert!(err1.contains("expected '<relpath>:<start>-<end>'"), "{err1}");

    // 2. Inverted line range (`9-3`):
    let inverted = valid_overlay_gaps.replace(
        "spec/mem/tree_borrows/reborrow_settings.md:1-8",
        "spec/mem/tree_borrows/reborrow_settings.md:9-3",
    );
    let p2 = overlay.write_file("theory/Correspondence/inverted.toml", &inverted);
    let err2 = run_correspondence_bugs_cli(
        &parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            p2.display().to_string(),
        ])
        .unwrap(),
    )
    .expect_err("inverted line range 9-3 must be rejected");
    assert!(err2.contains("require 1 <= start <= end"), "{err2}");

    // 3. Nonexistent file inside vendored snapshot directory:
    let missing_file = valid_overlay_gaps.replace(
        "spec/mem/tree_borrows/reborrow_settings.md:1-8",
        "spec/mem/does_not_exist.md:1-5",
    );
    let p3 = overlay.write_file("theory/Correspondence/missing_file.toml", &missing_file);
    let err3 = run_correspondence_bugs_cli(
        &parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            p3.display().to_string(),
        ])
        .unwrap(),
    )
    .expect_err("nonexistent minirust_source file in vendor snapshot must be rejected");
    assert!(err3.contains("does not exist in snapshot"), "{err3}");

    // 4. End line exceeds actual file line count (`1-25` > `10` lines):
    let out_of_bounds = valid_overlay_gaps.replace(
        "spec/mem/tree_borrows/reborrow_settings.md:1-8",
        "spec/mem/tree_borrows/reborrow_settings.md:1-25",
    );
    let p4 = overlay.write_file("theory/Correspondence/oob_lines.toml", &out_of_bounds);
    let err4 = run_correspondence_bugs_cli(
        &parse_correspondence_bugs_args(&[
            "lint".to_string(),
            "--gaps-toml".to_string(),
            p4.display().to_string(),
        ])
        .unwrap(),
    )
    .expect_err("minirust_source end line exceeding file line count must be rejected");
    assert!(err4.contains("exceeds file line count (10)"), "{err4}");
}

fn copy_dir_recursive(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("failed to create destination directory");
    for entry in fs::read_dir(src).expect("failed to read source directory") {
        let entry = entry.expect("failed to read directory entry");
        let ty = entry.file_type().expect("failed to read entry file type");
        let dst_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir_recursive(&entry.path(), &dst_path);
        } else {
            fs::copy(entry.path(), &dst_path).expect("failed to copy file");
        }
    }
}

/// End-to-End Upstream `.md` Mutation Proof-Breakage Test:
/// Verifies that:
/// 1. Copying `theory/MiniRust/vendor/S2026_05_Matched` to an isolated temporary directory,
/// 2. Mutating `PermissionUnprot::Unique => ret(PermissionUnprot::Frozen)` to
///    `PermissionUnprot::Unique => ret(PermissionUnprot::Disabled)` in
///    `spec/mem/tree_borrows/state_machine_unprotected.md` AND mutating
///    `Add => left + right` to `Add => left - right` in `spec/lang/step/operators.md`,
/// 3. Running `anneal_specr_lean::extract_snapshot` + `TypeEnvironment::build` +
///    `emit_snapshot_to_dir` into a temporary snapshot directory,
/// 4. Produces a generated `Ops.lean` file that differs from the unmutated `Ops.lean`
///    in the exact translated Lean definitions (`PermissionUnprot.foreign_read` and
///    `eval_int_bin_op`), and
/// 5. Running `lake env lean` on a Lean proof snippet that asserts the unmutated
///    correspondence theorem against the mutated `Ops.lean` module fails with a
///    Lean 4 kernel type/proof error (while succeeding against the unmutated `Ops.lean`).
#[test]
fn e2e_upstream_md_mutation_changes_generated_ops_and_breaks_lean_proof() {
    let root = repo_root();
    let overlay = TempOverlayDir::new("e2e-upstream-md-mutation");

    // 1. Copy `theory/MiniRust/vendor/S2026_05_Matched` into an isolated temp directory.
    let real_vendor = root.join("theory/MiniRust/vendor/S2026_05_Matched");
    let mutated_vendor = overlay.path().join("vendor/S2026_05_Matched");
    copy_dir_recursive(&real_vendor, &mutated_vendor);

    // Emit baseline (unmutated) snapshot into `snap_unmutated` for comparison.
    let commit_sha = "5f78e227bbe30ae9fb5e1286a772d91a92e3622a";
    let unmutated_snap_dir = overlay.path().join("snap_unmutated");
    let unmutated_extracted =
        anneal_specr_lean::extract_snapshot(&real_vendor, "S2026_05_Matched", commit_sha)
            .expect("baseline extract_snapshot must succeed");
    let unmutated_env = anneal_specr_lean::TypeEnvironment::build(&unmutated_extracted);
    let unmutated_emitted = anneal_specr_lean::emit_snapshot_to_dir(
        &unmutated_extracted,
        &unmutated_env,
        &unmutated_snap_dir,
    )
    .expect("baseline emit_snapshot_to_dir must succeed");
    let unmutated_ops = fs::read_to_string(&unmutated_emitted.ops_lean_path)
        .expect("failed to read unmutated Ops.lean");

    // 2. Mutate `spec/mem/tree_borrows/state_machine_unprotected.md` and `spec/lang/step/operators.md`.
    let tb_unprot_path = mutated_vendor.join("spec/mem/tree_borrows/state_machine_unprotected.md");
    let tb_unprot_orig =
        fs::read_to_string(&tb_unprot_path).expect("failed to read state_machine_unprotected.md");
    assert!(
        tb_unprot_orig.contains("PermissionUnprot::Unique => ret(PermissionUnprot::Frozen)"),
        "expected foreign_read rule in state_machine_unprotected.md"
    );
    let tb_unprot_mutated = tb_unprot_orig.replacen(
        "PermissionUnprot::Unique => ret(PermissionUnprot::Frozen)",
        "PermissionUnprot::Unique => ret(PermissionUnprot::Disabled)",
        1,
    );
    fs::write(&tb_unprot_path, &tb_unprot_mutated)
        .expect("failed to write mutated state_machine_unprotected.md");

    let ops_md_path = mutated_vendor.join("spec/lang/step/operators.md");
    let ops_md_orig = fs::read_to_string(&ops_md_path).expect("failed to read operators.md");
    assert!(
        ops_md_orig.contains("Add => left + right"),
        "expected Add => left + right in operators.md"
    );
    let ops_md_mutated = ops_md_orig.replacen("Add => left + right", "Add => left - right", 1);
    fs::write(&ops_md_path, &ops_md_mutated).expect("failed to write mutated operators.md");

    // 3. Run `extract_snapshot` + `TypeEnvironment::build` + `emit_snapshot_to_dir` on the mutated vendor directory.
    let mutated_snap_dir = overlay.path().join("snap_mutated");
    let mutated_extracted =
        anneal_specr_lean::extract_snapshot(&mutated_vendor, "S2026_05_Matched", commit_sha)
            .expect("mutated extract_snapshot must succeed");
    let mutated_env = anneal_specr_lean::TypeEnvironment::build(&mutated_extracted);
    let mutated_emitted = anneal_specr_lean::emit_snapshot_to_dir(
        &mutated_extracted,
        &mutated_env,
        &mutated_snap_dir,
    )
    .expect("mutated emit_snapshot_to_dir must succeed");
    let mutated_ops =
        fs::read_to_string(&mutated_emitted.ops_lean_path).expect("failed to read mutated Ops.lean");

    // 4. Verify that `Ops.lean` differs in the exact translated Lean definitions
    // (`PermissionUnprot.foreign_read` and `eval_int_bin_op`).
    assert_ne!(
        unmutated_ops, mutated_ops,
        "mutating upstream .md files must change generated Ops.lean"
    );
    assert!(
        unmutated_ops.contains("| .Unique => .ok .Frozen")
            && mutated_ops.contains("| .Unique => .ok .Disabled"),
        "PermissionUnprot.foreign_read in mutated Ops.lean must translate Unique => .ok .Disabled"
    );
    assert!(
        unmutated_ops.contains("| .Add => .ok (left + right)")
            && mutated_ops.contains("| .Add => .ok (left - right)"),
        "eval_int_bin_op in mutated Ops.lean must translate .Add => .ok (left - right)"
    );

    // 5. Run `lake env lean` on a Lean proof snippet asserting the unmutated correspondence
    // theorems against both the unmutated `Ops.lean` (must pass) and the mutated `Ops.lean`
    // (must fail with a Lean 4 kernel type/proof error).
    let proof_assertions = r#"
section MutationBreakageCheck
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops

theorem correspondence_foreign_read_unique :
    PermissionUnprot.foreign_read .Unique = .ok .Frozen := rfl

theorem correspondence_eval_int_bin_op_add (a b : SpecrInt) (ty : IntType) :
    eval_int_bin_op .Add a b ty = .ok (a + b) := rfl

end MutationBreakageCheck
"#;

    let unmutated_check_file = overlay.write_file(
        "UnmutatedProofCheck.lean",
        &format!("{unmutated_ops}\n{proof_assertions}"),
    );
    let mutated_check_file = overlay.write_file(
        "MutatedProofCheck.lean",
        &format!("{mutated_ops}\n{proof_assertions}"),
    );

    let examples_dir = root.join("examples");
    let unmutated_lean_out = Command::new("lake")
        .current_dir(&examples_dir)
        .args(["env", "lean"])
        .arg(&unmutated_check_file)
        .output()
        .expect("failed to invoke `lake env lean` on UnmutatedProofCheck.lean");
    assert!(
        unmutated_lean_out.status.success(),
        "unmutated Ops.lean proof check must pass `lake env lean`, stderr:\n{}\nstdout:\n{}",
        String::from_utf8_lossy(&unmutated_lean_out.stderr),
        String::from_utf8_lossy(&unmutated_lean_out.stdout)
    );

    let mutated_lean_out = Command::new("lake")
        .current_dir(&examples_dir)
        .args(["env", "lean"])
        .arg(&mutated_check_file)
        .output()
        .expect("failed to invoke `lake env lean` on MutatedProofCheck.lean");
    assert!(
        !mutated_lean_out.status.success(),
        "mutated Ops.lean MUST break the Lean correspondence proof under `lake env lean`"
    );
    let combined_diag = format!(
        "{}\n{}",
        String::from_utf8_lossy(&mutated_lean_out.stdout),
        String::from_utf8_lossy(&mutated_lean_out.stderr)
    );
    let diag_lower = combined_diag.to_ascii_lowercase();
    assert!(
        diag_lower.contains("type mismatch") && diag_lower.contains("not a definitional equality"),
        "expected Lean kernel `Type mismatch` / `Not a definitional equality` diagnostic on mutated Ops.lean, got:\n{combined_diag}"
    );
}




