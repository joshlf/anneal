//! Gate 4 Upstream Evolution & Bump Simulation Suite (`upstream_bump_sim.rs`):
//! 1. Verifies the REAL upstream structural diff between vendored `S2026_05_Matched`
//!    (`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`) and `S2026_07_BleedingEdge`
//!    (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`), proving exact classification of
//!    `Added`, `Removed`, `ModifiedSignature`, `ModifiedBody`, `Unchanged`, and
//!    cosmetic span shifts across all 27 real MiniRust chapters.
//! 2. Executes a complete hermetic two-version evolution (`fixture_snap_v1` ->
//!    `fixture_snap_v2`) in an isolated ephemeral temp directory, exercising all 5
//!    `DiffKind` variants, Lean 4 snapshot regeneration, SHA-256 lock verification,
//!    and `GAP-EPOCH` ratchet resolution.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_specr_lean::ast_diff::{DiffKind, diff_snapshots};
use anneal_specr_lean::extractor::extract_snapshot;
use anneal_specr_lean::gap_codegen::{
    parse_gaps_toml, parse_matrix_toml, validate_registry_and_matrix,
};
use anneal_specr_lean::lean_emit::{emit_snapshot_to_dir, verify_snapshot_lock};
use anneal_specr_lean::type_env::TypeEnvironment;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root two levels above crates/anneal-specr-lean")
        .to_path_buf()
}

fn make_ephemeral_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "anneal_specr_lean_gate4_{label}_{}_{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create ephemeral temp dir");
    dir
}

#[test]
fn gate4_real_upstream_diff_s2026_05_matched_to_s2026_07_bleeding_edge() {
    let root = repo_root();
    let matched_dir = root.join("theory/MiniRust/vendor/S2026_05_Matched");
    let bleeding_dir = root.join("theory/MiniRust/vendor/S2026_07_BleedingEdge");

    let snap_matched = extract_snapshot(
        &matched_dir,
        "S2026_05_Matched",
        "5f78e227bbe30ae9fb5e1286a772d91a92e3622a",
    )
    .expect("extract S2026_05_Matched");
    let snap_bleeding = extract_snapshot(
        &bleeding_dir,
        "S2026_07_BleedingEdge",
        "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed",
    )
    .expect("extract S2026_07_BleedingEdge");

    let env_matched = TypeEnvironment::build(&snap_matched);
    let env_bleeding = TypeEnvironment::build(&snap_bleeding);

    let report = diff_snapshots(&env_matched, &env_bleeding);

    // Exact verified counts between real commits 5f78e227... and d821c6e3...:
    assert_eq!(report.added_count, 4, "expected 4 Added declarations in real upstream bump");
    assert_eq!(report.removed_count, 0, "expected 0 Removed declarations in real upstream bump");
    assert_eq!(
        report.modified_signature_count, 11,
        "expected 11 ModifiedSignature declarations in real upstream bump"
    );
    assert_eq!(
        report.modified_body_count, 4,
        "expected 4 ModifiedBody declarations in real upstream bump"
    );
    assert_eq!(
        report.unchanged_count, 393,
        "expected 393 Unchanged declarations (>95% of spec untouched)"
    );
    assert!(
        report.cosmetic_span_shift_count >= 50,
        "expected cosmetic line shifts to be absorbed cleanly without false-positive semantic diffs"
    );

    // Partition identity check: every declaration across the union is accounted for.
    assert_eq!(
        report.added_count
            + report.removed_count
            + report.modified_signature_count
            + report.modified_body_count
            + report.unchanged_count,
        report.entries.len()
    );

    // Pinpoint real upstream semantic changes from PR #290 & PR #295 (Tree Borrows implicit writes):
    assert_eq!(
        report.find("TreeBorrowsParams").map(|e| e.diff_kind),
        Some(DiffKind::Added),
        "TreeBorrowsParams struct added in spec/mem/tree_borrows/memory.md"
    );
    assert_eq!(
        report.find("BasicMemory::Memory::Params").map(|e| e.diff_kind),
        Some(DiffKind::Added),
        "BasicMemory::Memory::Params associated type added in spec/mem/basic.md"
    );
    assert_eq!(
        report.find("Function").map(|e| e.diff_kind),
        Some(DiffKind::ModifiedSignature),
        "Function struct gained implicit_writes: bool in spec/lang/syntax.md"
    );
    assert_eq!(
        report.find("Machine::new").map(|e| e.diff_kind),
        Some(DiffKind::ModifiedSignature),
        "Machine::new gained mem_params: M::Params in spec/lang/machine.md"
    );
    assert_eq!(
        report.find("ConcurrentMemory::retag_ptr").map(|e| e.diff_kind),
        Some(DiffKind::ModifiedSignature),
        "ConcurrentMemory::retag_ptr gained fn_implicit_writes: bool in spec/mem/concurrent.md"
    );
    assert_eq!(
        report.find("PermissionProt::init_access").map(|e| e.diff_kind),
        Some(DiffKind::ModifiedBody),
        "PermissionProt::init_access added PermissionProt::Unique => Some(AccessKind::Write)"
    );

    // Crucial precision check: `Permission::init_access` moved between code blocks in
    // `spec/mem/tree_borrows/state_machine.md` without changing signature or body!
    let perm_init = report
        .find("Permission::init_access")
        .expect("Permission::init_access present in both snapshots");
    assert_eq!(
        perm_init.diff_kind,
        DiffKind::Unchanged,
        "code block relocation without token change must classify as Unchanged"
    );
    assert!(
        perm_init.span_shifted,
        "code block relocation must record span_shifted = true"
    );

    // Verify rendered Markdown & JSON reports are non-empty and deterministic.
    let md_report = report.render_markdown_report();
    assert!(md_report.contains("PermissionProt::init_access"));
    assert!(md_report.contains("TreeBorrowsParams"));
    assert!(md_report.contains("L4_TreeBorrows"));

    let json_report = report.render_json_summary();
    assert!(json_report.contains("\"added_count\": 4"));
    assert!(json_report.contains("\"unchanged_count\": 393"));
}

#[test]
fn gate4_synthetic_two_version_bump_simulation_in_ephemeral_temp_dir() {
    let tmp = make_ephemeral_temp_dir("two_version_sim");
    let v1_vendor = tmp.join("vendor_v1");
    let v2_vendor = tmp.join("vendor_v2");
    let v1_gen = tmp.join("snap_v1");
    let v2_gen = tmp.join("snap_v2");

    fs::create_dir_all(v1_vendor.join("spec/mem/tree_borrows")).expect("mkdir v1");
    fs::create_dir_all(v2_vendor.join("spec/mem/tree_borrows")).expect("mkdir v2");

    // v1 snapshot: 4 declarations (`Perm`, `LegacyHelper`, `step_access`, `unchanged_helper`)
    fs::write(
        v1_vendor.join("spec/mem/tree_borrows/state_machine.md"),
        r#"# Tree Borrows State Machine

```rust
pub enum Perm {
    Reserved,
    Active,
    Frozen,
}

pub struct LegacyHelper {
    pub flag: bool,
}

pub fn step_access(p: Perm) -> Result<Perm> {
    ret(p)
}

pub fn unchanged_helper(x: Int) -> Int {
    x
}
```
"#,
    )
    .expect("write v1 markdown");

    // v2 snapshot:
    // - Adds `Disabled` variant to `Perm` (`ModifiedSignature`)
    // - Removes `LegacyHelper` (`Removed`)
    // - Adds `NewProtectorConfig` (`Added`)
    // - Modifies body of `step_access` while keeping identical signature (`ModifiedBody`)
    // - Leaves `unchanged_helper` untouched except shifted line numbers (`Unchanged` + `span_shifted`)
    fs::write(
        v2_vendor.join("spec/mem/tree_borrows/state_machine.md"),
        r#"# Tree Borrows State Machine

Additional explanatory prose inserted at the top of the chapter in v2
so every subsequent line span shifts downward by 3 lines!

```rust
pub enum Perm {
    Reserved,
    Active,
    Frozen,
    Disabled,
}

pub struct NewProtectorConfig {
    pub strict_mode: bool,
}

pub fn step_access(p: Perm) -> Result<Perm> {
    match p {
        Perm::Disabled => throw_ub!("access to disabled tag"),
        other => ret(other),
    }
}

pub fn unchanged_helper(x: Int) -> Int {
    x
}
```
"#,
    )
    .expect("write v2 markdown");

    let snap_v1 = extract_snapshot(
        &v1_vendor,
        "S_Fixture_V1",
        "1111111111111111111111111111111111111111",
    )
    .expect("extract v1");
    let snap_v2 = extract_snapshot(
        &v2_vendor,
        "S_Fixture_V2",
        "2222222222222222222222222222222222222222",
    )
    .expect("extract v2");

    let env_v1 = TypeEnvironment::build(&snap_v1);
    let env_v2 = TypeEnvironment::build(&snap_v2);

    // Emit both snapshots and verify both lockfiles independently pass SHA-256 verification.
    emit_snapshot_to_dir(&snap_v1, &env_v1, &v1_gen).expect("emit v1");
    emit_snapshot_to_dir(&snap_v2, &env_v2, &v2_gen).expect("emit v2");

    let v1_lock = verify_snapshot_lock(&v1_gen, &v1_vendor).expect("v1 lock valid");
    let v2_lock = verify_snapshot_lock(&v2_gen, &v2_vendor).expect("v2 lock valid");
    assert_eq!(v1_lock.declaration_count, 4);
    assert_eq!(v2_lock.declaration_count, 4);

    // Verify all 5 `DiffKind` classifications in a single end-to-end upgrade!
    let diff = diff_snapshots(&env_v1, &env_v2);
    assert_eq!(diff.added_count, 1);
    assert_eq!(diff.removed_count, 1);
    assert_eq!(diff.modified_signature_count, 1);
    assert_eq!(diff.modified_body_count, 1);
    assert_eq!(diff.unchanged_count, 1);
    assert_eq!(diff.cosmetic_span_shift_count, 1);

    assert_eq!(diff.find("NewProtectorConfig").map(|d| d.diff_kind), Some(DiffKind::Added));
    assert_eq!(diff.find("LegacyHelper").map(|d| d.diff_kind), Some(DiffKind::Removed));
    assert_eq!(diff.find("Perm").map(|d| d.diff_kind), Some(DiffKind::ModifiedSignature));
    assert_eq!(diff.find("step_access").map(|d| d.diff_kind), Some(DiffKind::ModifiedBody));
    let unch = diff.find("unchanged_helper").expect("unchanged_helper in diff");
    assert_eq!(unch.diff_kind, DiffKind::Unchanged);
    assert!(unch.span_shifted);
    assert_eq!(diff.affected_slices(), vec!["L4_TreeBorrows"]);

    // Verify recording the v2 change as an explicit `GAP-EPOCH-SIM-01` entry keeps
    // `S_Fixture_V1` at `ExactUnconditional` (0 gaps) and `S_Fixture_V2` at `EpochDeltaOnly` (0 bugs).
    let gaps_toml = r#"
schema_version = 1
github_repo = "joshlf/anneal"

[[gaps]]
id = "GAP-EPOCH-SIM-01"
kind = "intentional_epoch_divergence"
severity = "none"
status = "active_version_skew"
title = "NewProtectorConfig & Disabled transition in S_Fixture_V2"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S_Fixture_V2"]
layer = "L4_TreeBorrows"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.stepTreeBorrowPerm"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
minirust_source = "spec/mem/tree_borrows/state_machine.md:17-22"
rationale_citation = "minirust/minirust@22222222 introduced strict protector mode after V2026_06_01 freeze"
target_anneal_version = "V2026_12_01"
guard_predicate = "isStrictProtectorMode st body"
witness_fixture = "Correspondence.Fixtures.strictProtectorWitness"
expected_anneal_verdict = "normalUnit"
expected_minirust_verdict = "ub"
"#;

    let matrix_toml = r#"
schema_version = 1

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S_Fixture_V1"
layer = "L4_TreeBorrows"
expected_tier = "ExactUnconditional"
max_open_bugs = 0

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S_Fixture_V2"
layer = "L4_TreeBorrows"
expected_tier = "EpochDeltaOnly"
max_open_bugs = 0
allowed_epoch_gaps = ["GAP-EPOCH-SIM-01"]
"#;

    let reg = parse_gaps_toml(gaps_toml).expect("parse sim gaps");
    let mat = parse_matrix_toml(matrix_toml).expect("parse sim matrix");
    let val = validate_registry_and_matrix(&reg, &mat).expect("sim matrix compliance holds");
    assert_eq!(val.total_gaps, 1);
    assert_eq!(val.epoch_divergence_count, 1);
    assert_eq!(val.soundness_bug_count, 0);

    let _ = fs::remove_dir_all(&tmp);
}
