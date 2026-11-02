//! Gate 1 Integration & Fidelity Suite (`transpiler_fidelity.rs`):
//! Verifies 100% deterministic extraction, AST classification, type environment
//! resolution, Lean 4 `SpecIndex.lean` emission, `@specr-source` 1-based line
//! span accuracy, `upstream-minirust.lock.toml` + `snapshot-lock.json` SHA-256
//! round-trip & tamper detection, and zero forbidden tokens across both real
//! vendored upstream `minirust/minirust` snapshots (`S2026_05_Matched` and
//! `S2026_07_BleedingEdge`).

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_specr_lean::extractor::{
    SpecDomain, extract_snapshot, parse_summary_md_order, parse_upstream_lock_toml,
    verify_upstream_lock,
};
use anneal_specr_lean::gap_codegen::{
    ExpectedTier, GapKind, emit_generated_gaps_lean, parse_gaps_toml, parse_matrix_toml,
    render_github_issue_markdown, validate_registry_and_matrix,
    validate_registry_and_matrix_with_repo_root,
};
use anneal_specr_lean::lean_emit::{
    emit_snapshot_to_dir, render_spec_index_lean, verify_snapshot_lock,
};
use anneal_specr_lean::specr_ast::{EffectLevel, ItemKind};
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
        "anneal_specr_lean_gate1_{label}_{}_{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create ephemeral temp dir");
    dir
}

#[test]
fn gate1_upstream_lock_sha256_integrity_both_real_snapshots() {
    let root = repo_root();
    let lock_path = root.join("theory/MiniRust/upstream-minirust.lock.toml");
    let raw = fs::read_to_string(&lock_path).expect("read upstream-minirust.lock.toml");
    let parsed = parse_upstream_lock_toml(&raw).expect("parse upstream-minirust.lock.toml");

    assert_eq!(parsed.schema_version, 1);
    assert_eq!(parsed.upstream_repo, "https://github.com/minirust/minirust");
    assert_eq!(parsed.snapshots.len(), 2);

    assert_eq!(parsed.snapshots[0].id, "S2026_05_Matched");
    assert_eq!(
        parsed.snapshots[0].git_sha,
        "5f78e227bbe30ae9fb5e1286a772d91a92e3622a"
    );
    assert_eq!(parsed.snapshots[0].file_count, 27);

    assert_eq!(parsed.snapshots[1].id, "S2026_07_BleedingEdge");
    assert_eq!(
        parsed.snapshots[1].git_sha,
        "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed"
    );
    assert_eq!(parsed.snapshots[1].file_count, 27);

    let verified = verify_upstream_lock(&lock_path, &root)
        .expect("all 54 vendored upstream markdown files must pass SHA-256 verification");
    assert_eq!(verified.len(), 2);
    assert_eq!(verified[0].verified_file_count, 27);
    assert_eq!(verified[1].verified_file_count, 27);
    assert!(verified[0].total_verified_bytes > 250_000);
    assert!(verified[1].total_verified_bytes > 250_000);
}

#[test]
fn gate1_deterministic_extraction_and_exact_line_provenance() {
    let root = repo_root();
    let vendor_matched = root.join("theory/MiniRust/vendor/S2026_05_Matched");
    let sha_matched = "5f78e227bbe30ae9fb5e1286a772d91a92e3622a";

    // Run full extraction + AST resolution + Lean rendering twice and verify 100% byte identity.
    let snap_run1 = extract_snapshot(&vendor_matched, "S2026_05_Matched", sha_matched)
        .expect("extract S2026_05_Matched run 1");
    let env_run1 = TypeEnvironment::build(&snap_run1);
    let lean_run1 = render_spec_index_lean(&snap_run1, &env_run1);

    let snap_run2 = extract_snapshot(&vendor_matched, "S2026_05_Matched", sha_matched)
        .expect("extract S2026_05_Matched run 2");
    let env_run2 = TypeEnvironment::build(&snap_run2);
    let lean_run2 = render_spec_index_lean(&snap_run2, &env_run2);

    assert_eq!(snap_run1, snap_run2, "snapshot extraction must be 100% deterministic");
    assert_eq!(env_run1, env_run2, "TypeEnvironment resolution must be 100% deterministic");
    assert_eq!(lean_run1, lean_run2, "emitted Lean 4 module must be byte-for-byte identical");

    // Verify exact chapter count, code block count, and declaration count on real S2026_05_Matched.
    assert_eq!(snap_run1.chapters.len(), 27);
    assert_eq!(snap_run1.total_blocks, 140);
    assert_eq!(env_run1.items.len(), 408);

    // Verify 100% exact 1-based line-range accuracy (`start_line..=end_line`) against raw `.md` files!
    for chapter in &snap_run1.chapters {
        let md_path = vendor_matched.join(&chapter.rel_path);
        let raw_md = fs::read_to_string(&md_path).expect("read raw markdown chapter");
        let md_lines: Vec<&str> = raw_md.lines().collect();

        for block in &chapter.blocks {
            assert!(block.span.start_line >= 1, "line numbers must be 1-based");
            assert!(
                block.span.end_line <= md_lines.len(),
                "end_line {} exceeds chapter {} line count {}",
                block.span.end_line,
                chapter.rel_path,
                md_lines.len()
            );
            if block.line_count > 0 {
                let expected_slice =
                    md_lines[block.span.start_line - 1..block.span.end_line].join("\n");
                assert_eq!(
                    block.source, expected_slice,
                    "extracted block source mismatch at {}",
                    block.span.format_provenance()
                );
            }
        }
    }

    // Verify every single parsed declaration has valid 1-based provenance and appears in `@specr-source`.
    for item in &env_run1.items {
        assert!(item.span.start_line >= 1);
        assert!(item.span.end_line >= item.span.start_line);
        let marker = format!("-- @specr-source: {}", item.span.format_provenance());
        assert!(
            lean_run1.contains(&marker),
            "missing provenance comment `{marker}` for declaration `{}`",
            item.qualified_name
        );
    }
}

#[test]
fn gate1_domain_classification_gc_cow_effects_and_mutual_recursion() {
    let root = repo_root();
    let vendor_bleeding = root.join("theory/MiniRust/vendor/S2026_07_BleedingEdge");
    let sha_bleeding = "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed";

    let snap = extract_snapshot(&vendor_bleeding, "S2026_07_BleedingEdge", sha_bleeding)
        .expect("extract S2026_07_BleedingEdge");
    let env = TypeEnvironment::build(&snap);

    assert_eq!(snap.chapters.len(), 27);
    assert_eq!(snap.total_blocks, 141);
    assert_eq!(env.items.len(), 412);

    // Every major MiniRust semantic chapter domain must be populated with real declarations.
    for required_domain in [
        SpecDomain::Syntax,
        SpecDomain::Values,
        SpecDomain::Types,
        SpecDomain::MemoryInterface,
        SpecDomain::BasicMemory,
        SpecDomain::TreeBorrows,
        SpecDomain::Step,
        SpecDomain::Terminators,
        SpecDomain::Intrinsics,
        SpecDomain::Machine,
    ] {
        let count = env.items_in_domain(required_domain).len();
        assert!(
            count > 0,
            "expected > 0 declarations in domain {:?}, got 0",
            required_domain
        );
    }

    // Verify all major item kinds are extracted and classified.
    assert_eq!(env.stats.struct_count, 37, "exact struct count on S2026_07_BleedingEdge");
    assert!(env.stats.enum_count >= 25, "expected >= 25 enums, got {}", env.stats.enum_count);
    assert!(env.stats.fn_count > 0, "expected free functions in MiniRust spec");
    assert!(
        env.stats.impl_method_count >= 200,
        "expected >= 200 impl methods, got {}",
        env.stats.impl_method_count
    );

    // Verify `GcCow<T>` detection and mutual recursion detection across nominal types (`Type`, `Value`).
    assert!(
        env.stats.gc_cow_item_count > 0,
        "expected GcCow<T> declarations in MiniRust spec"
    );
    assert!(
        env.stats.mutually_recursive_type_count > 0,
        "expected mutually recursive AST/value/type definitions"
    );
    assert!(!env.mutual_recursion_groups.is_empty());

    // Verify explicit effect classification across Pure, Option, FallibleResult, and NondetResult.
    assert!(env.stats.pure_count > 0);
    assert!(env.stats.option_effect_count > 0);
    assert!(env.stats.fallible_result_count > 0);
    assert!(env.stats.nondet_result_count > 0);

    // Spot-check key iconic declarations across MiniRust domains.
    let fn_struct = env.get("Function").expect("Function struct in spec/lang/syntax.md");
    assert_eq!(fn_struct.kind, ItemKind::Struct);
    assert!(fn_struct.fields.iter().any(|f| f.name == "implicit_writes"));

    let machine_new = env.get("Machine::new").expect("Machine::new in spec/lang/machine.md");
    assert_eq!(machine_new.kind, ItemKind::ImplMethod);
    assert_eq!(machine_new.effect, EffectLevel::NondetResult);
}

#[test]
fn gate1_generated_lean_hygiene_and_snapshot_lock_tamper_detection() {
    let root = repo_root();
    let forbidden_task_marker = ["TO", "DO"].concat();
    let forbidden_corp_path = ["/google/", "src"].concat();

    for (snap_id, vendor_rel) in [
        ("S2026_05_Matched", "theory/MiniRust/vendor/S2026_05_Matched"),
        ("S2026_07_BleedingEdge", "theory/MiniRust/vendor/S2026_07_BleedingEdge"),
    ] {
        let gen_dir = root.join(format!("theory/MiniRust/Snapshots/{snap_id}"));
        let vendor_dir = root.join(vendor_rel);

        // 1. Verify on-disk `snapshot-lock.json` round-trips cleanly against every `.md` and `.lean`.
        let lock_check = verify_snapshot_lock(&gen_dir, &vendor_dir)
            .expect("on-disk snapshot-lock.json must pass SHA-256 verification");
        assert_eq!(lock_check.snapshot_id, snap_id);
        assert_eq!(lock_check.verified_input_files, 27);
        assert_eq!(lock_check.verified_output_files, 2);

        // 2. Audit generated `SpecIndex.lean` and `Ops.lean` for strict proof & repository hygiene.
        for rel_lean in ["Generated/SpecIndex.lean", "Generated/Ops.lean"] {
            let lean_path = gen_dir.join(rel_lean);
            let lean_src = fs::read_to_string(&lean_path).expect("read generated Lean module");
            assert!(
                !lean_src.contains("sorry"),
                "{} must contain zero sorry tokens",
                lean_path.display()
            );
            assert!(
                !lean_src.contains("native_decide"),
                "{} must contain zero native_decide tokens",
                lean_path.display()
            );
            assert!(
                !lean_src.contains("axiom "),
                "{} must contain zero custom axioms",
                lean_path.display()
            );
            assert!(
                !lean_src.contains(&forbidden_task_marker),
                "{} must contain zero task marker tokens",
                lean_path.display()
            );
            assert!(
                !lean_src.contains(&forbidden_corp_path),
                "{} must contain zero internal corp paths",
                lean_path.display()
            );
        }
    }

    // 3. Verify tamper detection in an isolated ephemeral temp directory: modifying even 1 byte
    // in a generated `.lean` file or input `.md` file MUST fail `verify_snapshot_lock`.
    let tmp = make_ephemeral_temp_dir("tamper_check");
    let mini_vendor = tmp.join("vendor");
    let mini_out = tmp.join("snap_out");
    fs::create_dir_all(mini_vendor.join("spec/lang")).expect("mkdir mini_vendor");
    fs::write(
        mini_vendor.join("spec/lang/syntax.md"),
        "# Syntax\n\n```rust\npub struct Local(pub u32);\n```\n",
    )
    .expect("write synthetic syntax.md");

    let extracted = extract_snapshot(
        &mini_vendor,
        "S_TamperTest",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    )
    .expect("extract mini_vendor");
    let env = TypeEnvironment::build(&extracted);
    emit_snapshot_to_dir(&extracted, &env, &mini_out).expect("emit mini_out");
    assert!(verify_snapshot_lock(&mini_out, &mini_vendor).is_ok());

    // Tamper with generated SpecIndex.lean by appending a trailing comment line
    let tampered_lean = mini_out.join("Generated/SpecIndex.lean");
    let mut current = fs::read_to_string(&tampered_lean).expect("read SpecIndex.lean");
    current.push_str("\n-- unauthorized manual edit\n");
    fs::write(&tampered_lean, current).expect("write tampered SpecIndex.lean");

    let err = verify_snapshot_lock(&mini_out, &mini_vendor)
        .expect_err("tampered SpecIndex.lean must fail SHA-256 lock verification");
    assert!(
        err.contains("mismatch"),
        "expected mismatch diagnostic, got: {err}"
    );

    let _ = fs::remove_dir_all(&tmp);
}

#[test]
fn gate1_summary_md_order_and_gap_codegen_four_classes_pure_offline() {
    // 1. Verify `SUMMARY.md` chapter order parsing preserves exact link sequence.
    let sample_summary = r#"
# Summary

- [Prelude](spec/prelude/main.md)
- [Memory Interface](spec/mem/interface.md)
  - [Tree Borrows](spec/mem/tree_borrows/state_machine.md)
- [Syntax](spec/lang/syntax.md)
"#;
    let order = parse_summary_md_order(sample_summary, "");
    let paths: Vec<&str> = order.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(
        paths,
        vec![
            "spec/prelude/main.md",
            "spec/mem/interface.md",
            "spec/mem/tree_borrows/state_machine.md",
            "spec/lang/syntax.md",
        ]
    );

    // 2. Verify `gap_codegen` parses, validates, and emits clean Lean 4 + Markdown payloads
    // across all 4 formal non-correspondence classes with zero I/O or network calls.
    let sample_gaps_toml = r#"
schema_version = 1
github_repo = "joshlf/anneal"
default_labels = ["source:minirust-correspondence", "area:mir-semantics"]

[[gaps]]
id = "GAP-MR-0001"
kind = "anneal_soundness_bug"
severity = "P1"
status = "open"
title = "Shared borrow over UnsafeCell freezes permission"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched"]
layer = "L4_TreeBorrows"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.evalRefRvalue"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean"
minirust_source = "spec/mem/tree_borrows/reborrow_settings.md:90-141"
miri_diff_cross_ref = "pass_tb_unsafe_cell_shared_mutation"
guard_predicate = "isSharedBorrowOfUnsafeCell st body"
witness_fixture = "Correspondence.Fixtures.sharedUnsafeCellWrite"
expected_anneal_verdict = "ub"
expected_minirust_verdict = "normalUnit"

[[gaps]]
id = "GAP-MR-0002"
kind = "anneal_false_positive_ub"
severity = "P2"
status = "open"
title = "Conservative alignment check on zero-sized deref projection"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched"]
layer = "L3_PlacesAndBasicMem"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.evalPlace"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
minirust_source = "spec/mem/basic.md:120-150"
guard_predicate = "isZstUnalignedDeref st body"
witness_fixture = "Correspondence.Fixtures.zstUnalignedDeref"
expected_anneal_verdict = "ub"
expected_minirust_verdict = "normalUnit"

[[gaps]]
id = "GAP-MR-0003"
kind = "anneal_unmodeled_feature"
severity = "P3"
status = "open"
title = "Inline exact_div intrinsic not yet modeled in V2026_06_01"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_05_Matched"]
layer = "L5_ControlAndCalls"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.evalIntrinsic"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean"
minirust_source = "spec/lang/step/intrinsics.md:40-75"
guard_predicate = "callsExactDivIntrinsic st body"
witness_fixture = "Correspondence.Fixtures.exactDivCall"
expected_anneal_verdict = "unsupported"
expected_minirust_verdict = "normalVal"

[[gaps]]
id = "GAP-EPOCH-0001"
kind = "intentional_epoch_divergence"
severity = "none"
status = "active_version_skew"
title = "Tree Borrows implicit write on protected Unique reference in S2026_07_BleedingEdge"
anneal_versions = ["V2026_06_01"]
minirust_snapshots = ["S2026_07_BleedingEdge"]
layer = "L4_TreeBorrows"
anneal_decl = "Trusted.Rustc.V2026_06_01.MirSemantics.stepTreeBorrowPerm"
anneal_file = "trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
minirust_source = "spec/mem/tree_borrows/state_machine_protected.md:85-91"
rationale_citation = "minirust/minirust@e60f98bb (PR #295, 2026-07-15) added PermissionProt::Unique => Some(AccessKind::Write)"
target_anneal_version = "V2026_12_01"
guard_predicate = "isProtectedUniqueImplicitWrite st body"
witness_fixture = "Correspondence.Fixtures.protectedUniqueImplicitWrite"
expected_anneal_verdict = "normalUnit"
expected_minirust_verdict = "ub"
"#;

    let sample_matrix_toml = r#"
schema_version = 1

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S2026_05_Matched"
layer = "L4_TreeBorrows"
expected_tier = "GuardedRatchet"
max_open_bugs = 2

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S2026_07_BleedingEdge"
layer = "L4_TreeBorrows"
expected_tier = "EpochDeltaOnly"
max_open_bugs = 0
allowed_epoch_gaps = ["GAP-EPOCH-0001"]
"#;

    let registry = parse_gaps_toml(sample_gaps_toml).expect("parse 4-class gaps TOML");
    let matrix = parse_matrix_toml(sample_matrix_toml).expect("parse matrix TOML");
    assert_eq!(registry.gaps.len(), 4);
    assert_eq!(registry.gaps[0].kind, GapKind::AnnealSoundnessBug);
    assert_eq!(registry.gaps[1].kind, GapKind::AnnealFalsePositiveUb);
    assert_eq!(registry.gaps[2].kind, GapKind::AnnealUnmodeledFeature);
    assert_eq!(registry.gaps[3].kind, GapKind::IntentionalEpochDivergence);
    assert_eq!(matrix.cells[0].expected_tier, ExpectedTier::GuardedRatchet);
    assert_eq!(matrix.cells[1].expected_tier, ExpectedTier::EpochDeltaOnly);

    let summary = validate_registry_and_matrix_with_repo_root(&registry, &matrix, &repo_root())
        .expect("valid 4-class registry + matrix must pass repo-aware validation");
    assert_eq!(summary.total_gaps, 4);
    assert_eq!(summary.soundness_bug_count, 1);
    assert_eq!(summary.false_positive_ub_count, 1);
    assert_eq!(summary.unmodeled_feature_count, 1);
    assert_eq!(summary.epoch_divergence_count, 1);

    let emitted_lean = emit_generated_gaps_lean(&registry, &matrix);
    assert!(emitted_lean.contains("namespace Correspondence"));
    assert!(emitted_lean.contains("GapKind.anneal_soundness_bug"));
    assert!(emitted_lean.contains("GapKind.intentional_epoch_divergence"));
    assert!(emitted_lean.contains("theorem registered_gap_count_exact"));
    assert!(!emitted_lean.contains("sorry"));
    assert!(!emitted_lean.contains("native_decide"));

    // Verify Defect 4b regression check: out-of-bounds line range in `minirust_source`
    // is caught by `validate_registry_and_matrix_with_repo_root`.
    let mut bad_registry = registry.clone();
    bad_registry.gaps[0].minirust_source = "spec/lang/values.md:10-9999".to_string();
    let span_errs = validate_registry_and_matrix_with_repo_root(&bad_registry, &matrix, &repo_root())
        .expect_err("out-of-bounds minirust_source line range must be rejected");
    assert!(span_errs.iter().any(|e| e.contains("exceeds total_lines")));

    let issue = render_github_issue_markdown(&registry.gaps[0], "joshlf/anneal");
    assert!(issue.title.contains("GAP-MR-0001"));
    assert!(issue.markdown_body.contains("Trusted.Rustc.V2026_06_01.MirSemantics.evalRefRvalue"));
    assert_eq!(issue.fingerprint.len(), 64);

    // Verify Defect 1 regression check: `anneal_unmodeled_feature` is counted in `is_bug_gap()`
    // (aligning with `theory/Correspondence/Framework.lean` `GapKind.isBug`) AND is rejected by
    // `ExpectedTier::ExactUnconditional`.
    assert!(GapKind::AnnealUnmodeledFeature.is_bug_gap());
    let strict_matrix = parse_matrix_toml(
        r#"
schema_version = 1

[[cells]]
anneal_version = "V2026_06_01"
minirust_snapshot = "S2026_05_Matched"
layer = "L5_ControlAndCalls"
expected_tier = "ExactUnconditional"
max_open_bugs = 0
"#,
    )
    .expect("parse strict matrix");
    let errs = validate_registry_and_matrix(&registry, &strict_matrix)
        .expect_err("ExactUnconditional must reject anneal_unmodeled_feature gap on L5_ControlAndCalls");
    assert!(errs.iter().any(|e| e.contains("ExactUnconditional")));
}

fn copy_dir_recursive(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("create dst dir");
    for entry in fs::read_dir(src).expect("read src dir") {
        let entry = entry.expect("dir entry");
        let ty = entry.file_type().expect("file type");
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir_recursive(&src_path, &dst_path);
        } else {
            fs::copy(&src_path, &dst_path).expect("copy file");
        }
    }
}

#[test]
fn gate1_upstream_md_mutation_changes_emitted_ops_lean() {
    let root = repo_root();
    let vendor_matched = root.join("theory/MiniRust/vendor/S2026_05_Matched");
    let sha_matched = "5f78e227bbe30ae9fb5e1286a772d91a92e3622a";

    // Baseline emission from unmodified S2026_05_Matched
    let base_snap =
        extract_snapshot(&vendor_matched, "S2026_05_Matched", sha_matched).expect("extract base");
    let base_env = TypeEnvironment::build(&base_snap);
    let tmp = make_ephemeral_temp_dir("md_mutation");
    let base_out = tmp.join("base_out");
    let base_emitted =
        emit_snapshot_to_dir(&base_snap, &base_env, &base_out).expect("emit base snapshot");
    assert!(
        base_emitted
            .ops_lean_content
            .contains("| .Add => .ok (left + right)"),
        "baseline Ops.lean must emit `| .Add => .ok (left + right)`"
    );
    assert!(
        base_emitted
            .ops_lean_content
            .contains("| .Unique => .ok .Frozen"),
        "baseline Ops.lean must emit `| .Unique => .ok .Frozen` in PermissionUnprot.foreign_read"
    );

    // Copy vendor directory and mutate two upstream `.md` files:
    // 1. `Add => left + right` -> `Add => left - right` in `spec/lang/step/operators.md`
    // 2. `PermissionUnprot::Unique => ret(PermissionUnprot::Frozen)` ->
    //    `PermissionUnprot::Unique => ret(PermissionUnprot::Disabled)` in `spec/mem/tree_borrows/state_machine_unprotected.md`
    let mut_vendor = tmp.join("vendor_mut");
    copy_dir_recursive(&vendor_matched, &mut_vendor);

    let ops_md_path = mut_vendor.join("spec/lang/step/operators.md");
    let ops_md_raw = fs::read_to_string(&ops_md_path).expect("read operators.md");
    assert!(
        ops_md_raw.contains("Add => left + right,"),
        "operators.md must contain `Add => left + right,`"
    );
    let ops_md_mut = ops_md_raw.replacen("Add => left + right,", "Add => left - right,", 1);
    fs::write(&ops_md_path, ops_md_mut).expect("write mutated operators.md");

    let unprot_md_path = mut_vendor.join("spec/mem/tree_borrows/state_machine_unprotected.md");
    let unprot_md_raw =
        fs::read_to_string(&unprot_md_path).expect("read state_machine_unprotected.md");
    assert!(
        unprot_md_raw.contains("PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),"),
        "state_machine_unprotected.md must contain Unique => ret(Frozen)"
    );
    let unprot_md_mut = unprot_md_raw.replacen(
        "PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),",
        "PermissionUnprot::Unique => ret(PermissionUnprot::Disabled),",
        1,
    );
    fs::write(&unprot_md_path, unprot_md_mut)
        .expect("write mutated state_machine_unprotected.md");

    let mut_out = tmp.join("mut_out");
    let mut_snap = extract_snapshot(&mut_vendor, "S2026_05_Matched", sha_matched)
        .expect("extract mutated snapshot");
    let mut_env = TypeEnvironment::build(&mut_snap);
    let mut_emitted =
        emit_snapshot_to_dir(&mut_snap, &mut_env, &mut_out).expect("emit mutated snapshot");

    assert_ne!(
        base_emitted.ops_lean_sha256, mut_emitted.ops_lean_sha256,
        "mutating upstream .md code blocks must change Generated/Ops.lean SHA-256"
    );
    assert!(
        mut_emitted
            .ops_lean_content
            .contains("| .Add => .ok (left - right)"),
        "mutated Ops.lean must translate `Add => left - right` into `| .Add => .ok (left - right)`"
    );
    assert!(
        !mut_emitted
            .ops_lean_content
            .contains("| .Add => .ok (left + right)"),
        "mutated Ops.lean must no longer contain `| .Add => .ok (left + right)`"
    );
    assert!(
        mut_emitted
            .ops_lean_content
            .contains("| .Unique => .ok .Disabled"),
        "mutated Ops.lean must translate `PermissionUnprot::Unique => ret(PermissionUnprot::Disabled)`"
    );
    assert!(
        !mut_emitted
            .ops_lean_content
            .contains("| .Unique => .ok .Frozen"),
        "mutated Ops.lean must no longer contain `| .Unique => .ok .Frozen`"
    );

    let _ = fs::remove_dir_all(&tmp);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefPermUnprot {
    Cell,
    Reserved,
    ReservedIm,
    Unique,
    Frozen,
    Disabled,
}

impl RefPermUnprot {
    fn lean(self) -> &'static str {
        match self {
            Self::Cell => ".Cell",
            Self::Reserved => ".Reserved",
            Self::ReservedIm => ".ReservedIm",
            Self::Unique => ".Unique",
            Self::Frozen => ".Frozen",
            Self::Disabled => ".Disabled",
        }
    }

    fn transition(self, access_write: bool, foreign: bool) -> Result<Self, &'static str> {
        match (foreign, access_write) {
            (false, false) => match self {
                Self::Disabled => Err("Tree Borrows: local read of Disabled reference"),
                p => Ok(p),
            },
            (false, true) => match self {
                Self::Frozen => Err("Tree Borrows: local write of Frozen reference"),
                Self::Disabled => Err("Tree Borrows: local write of Disabled reference"),
                Self::Cell => Ok(Self::Cell),
                _ => Ok(Self::Unique),
            },
            (true, false) => match self {
                Self::Reserved => Ok(Self::Reserved),
                Self::Unique => Ok(Self::Frozen),
                p => Ok(p),
            },
            (true, true) => match self {
                Self::Cell => Ok(Self::Cell),
                Self::ReservedIm => Ok(Self::ReservedIm),
                _ => Ok(Self::Disabled),
            },
        }
    }

    fn init_access_read(self) -> bool {
        !matches!(self, Self::Cell)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RefPermProt {
    Cell,
    Reserved(bool, bool),
    Unique,
    Frozen(bool),
    Disabled,
}

impl RefPermProt {
    fn lean(self) -> String {
        match self {
            Self::Cell => ".Cell".to_string(),
            Self::Reserved(l, f) => format!("(.Reserved {l} {f})"),
            Self::Unique => ".Unique".to_string(),
            Self::Frozen(l) => format!("(.Frozen {l})"),
            Self::Disabled => ".Disabled".to_string(),
        }
    }

    fn transition(self, access_write: bool, foreign: bool) -> Result<Self, &'static str> {
        match (foreign, access_write) {
            (false, false) => match self {
                Self::Cell => Ok(Self::Cell),
                Self::Reserved(_, f) => Ok(Self::Reserved(true, f)),
                Self::Unique => Ok(Self::Unique),
                Self::Frozen(_) => Ok(Self::Frozen(true)),
                Self::Disabled => Err("Tree Borrows: local read of protected Disabled reference"),
            },
            (false, true) => match self {
                Self::Cell => Ok(Self::Cell),
                Self::Unique => Ok(Self::Unique),
                Self::Reserved(_, false) => Ok(Self::Unique),
                Self::Reserved(_, true) => Err(
                    "Tree Borrows: local write to protected Reserved reference that had a foreign read",
                ),
                Self::Frozen(_) => Err("Tree Borrows: local write to protected Frozen reference"),
                Self::Disabled => Err("Tree Borrows: local write to protected Disabled reference"),
            },
            (true, false) => match self {
                Self::Cell => Ok(Self::Cell),
                Self::Unique => Err("Tree Borrows: foreign read of protected Unique reference"),
                Self::Reserved(l, _) => Ok(Self::Reserved(l, true)),
                Self::Frozen(l) => Ok(Self::Frozen(l)),
                Self::Disabled => Ok(Self::Disabled),
            },
            (true, true) => match self {
                Self::Cell => Ok(Self::Cell),
                Self::Frozen(true) => Err(
                    "Tree Borrows: foreign write of protected Frozen reference which had a local read",
                ),
                Self::Reserved(true, _) => Err(
                    "Tree Borrows: foreign write of protected Reserved reference which had a local read",
                ),
                Self::Unique => Err("Tree Borrows: foreign read of protected Unique reference"),
                Self::Frozen(false) | Self::Reserved(false, _) | Self::Disabled => {
                    Ok(Self::Disabled)
                }
            },
        }
    }

    fn init_access_lean(self, bleeding_edge: bool) -> &'static str {
        match self {
            Self::Cell => "none",
            Self::Unique if bleeding_edge => "(some .Write)",
            _ => "(some .Read)",
        }
    }

    fn unprotect_lean(self) -> String {
        match self {
            Self::Unique => "(.Unique, some .Write)".to_string(),
            Self::Reserved(true, _) => "(.Reserved, some .Read)".to_string(),
            Self::Reserved(false, _) => "(.Reserved, none)".to_string(),
            Self::Frozen(true) => "(.Frozen, some .Read)".to_string(),
            Self::Frozen(false) => "(.Frozen, none)".to_string(),
            Self::Disabled => "(.Disabled, none)".to_string(),
            Self::Cell => "(.Cell, none)".to_string(),
        }
    }

    fn prevents_deallocation(self) -> bool {
        match self {
            Self::Unique => true,
            Self::Reserved(l, _) | Self::Frozen(l) => l,
            Self::Disabled | Self::Cell => false,
        }
    }
}

fn ref_can_represent(signed: bool, bits: u32, val: i64) -> bool {
    if !signed {
        val >= 0 && val < (1i64 << bits)
    } else {
        let half = 1i64 << (bits - 1);
        val >= -half && val < half
    }
}

fn ref_bring_in_bounds(signed: bool, bits: u32, val: i64) -> i64 {
    let modulus = 1i64 << bits;
    let wrapped = val.rem_euclid(modulus);
    if !signed {
        wrapped
    } else {
        let half = 1i64 << (bits - 1);
        if wrapped < half {
            wrapped
        } else {
            wrapped - modulus
        }
    }
}

fn lean_int(v: i64) -> String {
    if v < 0 {
        format!("({v} : Int)")
    } else {
        format!("({v} : Int)")
    }
}

fn lean_except_int(res: Result<i64, &str>) -> String {
    match res {
        Ok(v) => format!("(.ok {})", lean_int(v)),
        Err(msg) => format!("(.error (.ub \"{msg}\"))"),
    }
}

#[test]
fn gate1_executable_behavioral_equivalence_500_plus_vectors() {
    let root = repo_root();
    let examples_dir = root.join("examples");
    let mut assertions: Vec<String> = Vec::with_capacity(650);

    // =========================================================================
    // 1. L1 Scalar & Arithmetic Vectors (IntType, UnOp, BinOp, Overflow, RelOp, Bit Ops)
    // =========================================================================
    let int_types = [
        (false, 1u32, "{ signed := .Unsigned, size := ⟨1⟩ }"),
        (true, 1u32, "{ signed := .Signed, size := ⟨1⟩ }"),
        (false, 2u32, "{ signed := .Unsigned, size := ⟨2⟩ }"),
        (true, 2u32, "{ signed := .Signed, size := ⟨2⟩ }"),
    ];
    let sample_vals: [i64; 10] = [-300, -129, -128, -1, 0, 1, 127, 128, 255, 256];
    for (signed, size_bytes, lean_ty) in int_types {
        let bits = size_bytes * 8;
        for &v in &sample_vals {
            let can_rep = ref_can_represent(signed, bits, v);
            assertions.push(format!(
                "Ops05.IntType.can_represent {lean_ty} {} = {can_rep}",
                lean_int(v)
            ));
            let bounded = ref_bring_in_bounds(signed, bits, v);
            assertions.push(format!(
                "Ops05.IntType.bring_in_bounds {lean_ty} {} = {}",
                lean_int(v),
                lean_int(bounded)
            ));
        }
    }

    // Unary operators across u8 and i8
    for (signed, size_bytes, lean_ty) in [
        (false, 1u32, "{ signed := .Unsigned, size := ⟨1⟩ }"),
        (true, 1u32, "{ signed := .Signed, size := ⟨1⟩ }"),
    ] {
        let bits = size_bytes * 8;
        for &v in &[-128i64, -1, 0, 1, 42, 127] {
            let neg_res = ref_bring_in_bounds(signed, bits, -v);
            assertions.push(format!(
                "Ops05.eval_int_un_op .Neg {} {lean_ty} = (.ok {})",
                lean_int(v),
                lean_int(neg_res)
            ));
            let not_res = ref_bring_in_bounds(signed, bits, -v - 1);
            assertions.push(format!(
                "Ops05.eval_int_un_op .BitNot {} {lean_ty} = (.ok {})",
                lean_int(v),
                lean_int(not_res)
            ));
            let wrapped_u = v.rem_euclid(1i64 << bits) as u64;
            let ones = i64::from(wrapped_u.count_ones());
            assertions.push(format!(
                "Ops05.eval_int_un_op .CountOnes {} {lean_ty} = (.ok {})",
                lean_int(v),
                lean_int(ones)
            ));
        }
    }

    // Binary operators across i8 and u8
    let bin_pairs: [(i64, i64); 8] = [
        (10, 3),
        (100, 50),
        (-128, -1),
        (-128, 1),
        (42, 0),
        (24, 6),
        (-15, 4),
        (7, 9),
    ];
    for (signed, size_bytes, lean_ty) in [
        (true, 1u32, "{ signed := .Signed, size := ⟨1⟩ }"),
        (false, 1u32, "{ signed := .Unsigned, size := ⟨1⟩ }"),
    ] {
        let bits = size_bytes * 8;
        for &(l, r) in &bin_pairs {
            if !ref_can_represent(signed, bits, l) {
                continue;
            }
            // Add & AddUnchecked
            assertions.push(format!(
                "Ops05.eval_int_bin_op .Add {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(l + r)
            ));
            let add_unch = if ref_can_represent(signed, bits, l + r) {
                Ok(l + r)
            } else {
                Err("overflow in unchecked add")
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .AddUnchecked {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(add_unch)
            ));

            // Sub & SubUnchecked
            assertions.push(format!(
                "Ops05.eval_int_bin_op .Sub {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(l - r)
            ));
            let sub_unch = if ref_can_represent(signed, bits, l - r) {
                Ok(l - r)
            } else {
                Err("overflow in unchecked sub")
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .SubUnchecked {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(sub_unch)
            ));

            // Mul & MulUnchecked
            assertions.push(format!(
                "Ops05.eval_int_bin_op .Mul {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(l * r)
            ));
            let mul_unch = if ref_can_represent(signed, bits, l * r) {
                Ok(l * r)
            } else {
                Err("overflow in unchecked mul")
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .MulUnchecked {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(mul_unch)
            ));

            // Div, DivExact, Rem
            let div_res = if r == 0 {
                Err("division by zero")
            } else {
                let q = l / r;
                if !ref_can_represent(signed, bits, q) {
                    Err("overflow in division")
                } else {
                    Ok(q)
                }
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .Div {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(div_res)
            ));

            let div_exact_res = if r == 0 {
                Err("division by zero")
            } else {
                let q = l / r;
                if !ref_can_represent(signed, bits, q) {
                    Err("overflow in division")
                } else if l % r != 0 {
                    Err("non-zero remainder in exact division")
                } else {
                    Ok(q)
                }
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .DivExact {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(div_exact_res)
            ));

            let rem_res = if r == 0 {
                Err("modulus of remainder is zero")
            } else if !ref_can_represent(signed, bits, l / r) {
                Err("overflow in remainder")
            } else {
                Ok(l % r)
            };
            assertions.push(format!(
                "Ops05.eval_int_bin_op .Rem {} {} {lean_ty} = {}",
                lean_int(l),
                lean_int(r),
                lean_except_int(rem_res)
            ));

            // Shl, Shr, ShlUnchecked, ShrUnchecked (test non-negative right operands)
            if r >= 0 {
                let offset = (r as u32) % bits;
                let shl_val = l * (1i64 << offset);
                assertions.push(format!(
                    "Ops05.eval_int_bin_op .Shl {} {} {lean_ty} = (.ok {})",
                    lean_int(l),
                    lean_int(r),
                    lean_int(shl_val)
                ));
                let shr_val = l.div_euclid(1i64 << offset);
                assertions.push(format!(
                    "Ops05.eval_int_bin_op .Shr {} {} {lean_ty} = (.ok {})",
                    lean_int(l),
                    lean_int(r),
                    lean_int(shr_val)
                ));
                let shl_unch = if r < 0 || r >= i64::from(bits) {
                    Err("overflow in unchecked shift")
                } else {
                    Ok(l * (1i64 << (r as u32)))
                };
                assertions.push(format!(
                    "Ops05.eval_int_bin_op .ShlUnchecked {} {} {lean_ty} = {}",
                    lean_int(l),
                    lean_int(r),
                    lean_except_int(shl_unch)
                ));
            }

            // BitAnd, BitOr, BitXor
            let lu = l.rem_euclid(1i64 << bits) as u64;
            let ru = r.rem_euclid(1i64 << bits) as u64;
            let band = ref_bring_in_bounds(signed, bits, (lu & ru) as i64);
            let bor = ref_bring_in_bounds(signed, bits, (lu | ru) as i64);
            let bxor = ref_bring_in_bounds(signed, bits, (lu ^ ru) as i64);
            assertions.push(format!(
                "Ops05.eval_int_bin_op .BitAnd {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(band)
            ));
            assertions.push(format!(
                "Ops05.eval_int_bin_op .BitOr {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(bor)
            ));
            assertions.push(format!(
                "Ops05.eval_int_bin_op .BitXor {} {} {lean_ty} = (.ok {})",
                lean_int(l),
                lean_int(r),
                lean_int(bxor)
            ));

            // eval_bin_op_int_with_overflow (Add, Sub, Mul)
            for (op_lean, math_res) in [(".Add", l + r), (".Sub", l - r), (".Mul", l * r)] {
                let ovf = !ref_can_represent(signed, bits, math_res);
                let wrapped = ref_bring_in_bounds(signed, bits, math_res);
                assertions.push(format!(
                    "Ops05.eval_bin_op_int_with_overflow {op_lean} {} {} {lean_ty} = ({}, {ovf})",
                    lean_int(l),
                    lean_int(r),
                    lean_int(wrapped)
                ));
            }
        }
    }

    // Relational operators and 3-way compare
    for &(l, r) in &[(-10i64, 5i64), (5, 5), (12, -3), (0, 0), (-100, -99)] {
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Lt {} {} = {}",
            lean_int(l),
            lean_int(r),
            l < r
        ));
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Gt {} {} = {}",
            lean_int(l),
            lean_int(r),
            l > r
        ));
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Le {} {} = {}",
            lean_int(l),
            lean_int(r),
            l <= r
        ));
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Ge {} {} = {}",
            lean_int(l),
            lean_int(r),
            l >= r
        ));
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Eq {} {} = {}",
            lean_int(l),
            lean_int(r),
            l == r
        ));
        assertions.push(format!(
            "Ops05.eval_rel_op_bool .Ne {} {} = {}",
            lean_int(l),
            lean_int(r),
            l != r
        ));
        let cmp_v = if l < r { -1 } else if l == r { 0 } else { 1 };
        assertions.push(format!(
            "Ops05.eval_cmp_int {} {} = {}",
            lean_int(l),
            lean_int(r),
            lean_int(cmp_v)
        ));
    }

    // Unsigned bit-level projections (mrWrapping*, mrChecked*, mrShl, mrShr*)
    for &(a, b) in &[(200u64, 100u64), (15, 20), (128, 2), (255, 1), (42, 0)] {
        let w_add = (a + b) % 256;
        let o_add = a + b >= 256;
        assertions.push(format!("Ops05.mrWrappingAdd {a} {b} 1 = {w_add}"));
        assertions.push(format!("Ops05.mrCheckedAdd {a} {b} 1 = ({w_add}, {o_add})"));
        let w_sub = if b <= a {
            (a - b) % 256
        } else {
            (256 + (a % 256) - (b % 256)) % 256
        };
        let o_sub = b > a;
        assertions.push(format!("Ops05.mrWrappingSub {a} {b} 1 = {w_sub}"));
        assertions.push(format!("Ops05.mrCheckedSub {a} {b} 1 = ({w_sub}, {o_sub})"));
        let w_mul = (a * b) % 256;
        let o_mul = a * b >= 256;
        assertions.push(format!("Ops05.mrWrappingMul {a} {b} 1 = {w_mul}"));
        assertions.push(format!("Ops05.mrCheckedMul {a} {b} 1 = ({w_mul}, {o_mul})"));
    }

    // =========================================================================
    // 2. L2 Bytes & Layout Vectors
    // =========================================================================
    assertions.push("Ops05.MrAbstractByte.data .uninit = none".to_string());
    assertions.push("Ops05.MrAbstractByte.data (.init 42 (some (1, 2))) = some 42".to_string());
    assertions.push("Ops05.MrAbstractByte.provenance .uninit = none".to_string());
    assertions.push(
        "Ops05.MrAbstractByte.provenance (.init 42 (some (1, 2))) = some (1, 2)".to_string(),
    );
    assertions.push("Ops05.MrAbstractByte.le_defined .uninit (.init 99 none) = true".to_string());
    assertions.push(
        "Ops05.MrAbstractByte.le_defined (.init 7 none) (.init 7 (some (1, 0))) = true".to_string(),
    );
    assertions.push(
        "Ops05.MrAbstractByte.le_defined (.init 7 (some (1, 0))) (.init 7 none) = false"
            .to_string(),
    );
    assertions.push("Ops05.decode_bool_bytes [.init 0 none] = some false".to_string());
    assertions.push("Ops05.decode_bool_bytes [.init 1 none] = some true".to_string());
    assertions.push("Ops05.decode_bool_bytes [.init 2 none] = none".to_string());
    assertions.push("Ops05.decode_bool_bytes [.uninit] = none".to_string());
    assertions.push("Ops05.encode_bool_bytes false = [.init 0 none]".to_string());
    assertions.push("Ops05.encode_bool_bytes true = [.init 1 none]".to_string());
    assertions.push(
        "Ops05.decode_int_le (Ops05.encode_int_le 0x1234 2 (some (5, 9))) = some (0x1234, some (5, 9))"
            .to_string(),
    );
    assertions.push(
        "Ops05.decode_int_le (Ops05.encode_int_le 0xABCD 2 none) = some (0xABCD, none)".to_string(),
    );
    assertions.push(
        "Ops05.subslice_with_length [.init 10 none, .init 20 none, .init 30 none] 1 2 = some [.init 20 none, .init 30 none]"
            .to_string(),
    );
    assertions.push("Ops05.subslice_with_length [.init 10 none] 1 2 = none".to_string());
    assertions.push(
        "Ops05.decode_discriminant_tag (Ops05.encode_int_le 3 2 none) 0 2 = some 3".to_string(),
    );

    // =========================================================================
    // 3. L3 Places & BasicMemory Vectors
    // =========================================================================
    let sample_mem =
        "{ allocs := [{ id := 0, align := Align.four, size := 8, live := true, bytes := [1, 2, 3, 4, 5, 6, 7, 8] }], nextAllocId := 1 }";
    assertions.push(format!(
        "Ops05.basicMemLoad {sample_mem} {{ allocId := 0, offset := 0 }} Align.four 4 = .ok [1, 2, 3, 4]"
    ));
    assertions.push(format!(
        "Ops05.basicMemLoad {sample_mem} {{ allocId := 0, offset := 4 }} Align.four 4 = .ok [5, 6, 7, 8]"
    ));
    assertions.push(format!(
        "Ops05.basicMemLoad {sample_mem} {{ allocId := 0, offset := 2 }} Align.four 2 = .error (.ub \"misaligned pointer access\")"
    ));
    assertions.push(format!(
        "Ops05.basicMemLoad {sample_mem} {{ allocId := 9, offset := 0 }} Align.one 1 = .error (.ub \"dangling pointer to nonexistent allocation\")"
    ));
    assertions.push(format!(
        "Ops05.basicMemLoad {sample_mem} {{ allocId := 0, offset := 6 }} Align.two 4 = .error (.ub \"pointer access out of bounds\")"
    ));
    assertions.push(format!(
        "Ops05.basicMemDeallocate {sample_mem} {{ allocId := 0, offset := 1 }} Align.four 8 = .error (.ub \"deallocating with pointer not to the beginning of its allocation\")"
    ));
    assertions.push(format!(
        "Ops05.basicMemDeallocate {sample_mem} {{ allocId := 0, offset := 0 }} Align.four 4 = .error (.ub \"deallocating with incorrect size information\")"
    ));
    assertions.push(format!(
        "Ops05.basicMemDeallocate {sample_mem} {{ allocId := 0, offset := 0 }} Align.two 8 = .error (.ub \"deallocating with incorrect alignment information\")"
    ));
    assertions.push("Ops05.mrProjectFieldOffset 8 [0, 4, 12] 2 = .ok 20".to_string());
    assertions.push(
        "Ops05.mrProjectFieldOffset 8 [0, 4] 5 = .error (.ub \"field projection to invalid field\")"
            .to_string(),
    );
    assertions.push("Ops05.mrProjectIndexOffset 16 4 3 5 = .ok 28".to_string());
    assertions.push(
        "Ops05.mrProjectIndexOffset 16 4 5 5 = .error (.ub \"access to out-of-bounds index\")"
            .to_string(),
    );
    assertions.push("Ops05.mrProjectSubsliceBounds 10 2 7 false = .ok (2, 7)".to_string());
    assertions.push("Ops05.mrProjectSubsliceBounds 10 2 3 true = .ok (2, 7)".to_string());
    assertions.push(
        "Ops05.mrProjectSubsliceBounds 10 8 5 false = .error (.ub \"subslice projection out of bounds\")"
            .to_string(),
    );

    // =========================================================================
    // 4. L4 Tree Borrows Exhaustive State Machine & Reborrow Vectors (Ops05 & Ops07)
    // =========================================================================
    let unprot_states = [
        RefPermUnprot::Cell,
        RefPermUnprot::Reserved,
        RefPermUnprot::ReservedIm,
        RefPermUnprot::Unique,
        RefPermUnprot::Frozen,
        RefPermUnprot::Disabled,
    ];
    for &st in &unprot_states {
        let init_expected = if st.init_access_read() {
            "(some .Read)"
        } else {
            "none"
        };
        assertions.push(format!(
            "Ops05.PermissionUnprot.init_access {} = {init_expected}",
            st.lean()
        ));
        assertions.push(format!(
            "Ops05.PermissionUnprot.prevents_deallocation {} = false",
            st.lean()
        ));
        for &(foreign, rel_lean) in &[(false, ".Local"), (true, ".Foreign")] {
            for &(write, acc_lean) in &[(false, ".Read"), (true, ".Write")] {
                let expected = match st.transition(write, foreign) {
                    Ok(next) => format!("(.ok {})", next.lean()),
                    Err(msg) => format!("(.error (.ub \"{msg}\"))"),
                };
                assertions.push(format!(
                    "Ops05.PermissionUnprot.transition {} {acc_lean} {rel_lean} = {expected}",
                    st.lean()
                ));
            }
        }
    }

    let prot_states = [
        RefPermProt::Cell,
        RefPermProt::Reserved(false, false),
        RefPermProt::Reserved(false, true),
        RefPermProt::Reserved(true, false),
        RefPermProt::Reserved(true, true),
        RefPermProt::Unique,
        RefPermProt::Frozen(false),
        RefPermProt::Frozen(true),
        RefPermProt::Disabled,
    ];
    for &st in &prot_states {
        assertions.push(format!(
            "Ops05.PermissionProt.init_access {} = {}",
            st.lean(),
            st.init_access_lean(false)
        ));
        assertions.push(format!(
            "Ops07.PermissionProt.init_access {} = {}",
            st.lean(),
            st.init_access_lean(true)
        ));
        assertions.push(format!(
            "Ops05.PermissionProt.unprotect {} = {}",
            st.lean(),
            st.unprotect_lean()
        ));
        assertions.push(format!(
            "Ops05.PermissionProt.prevents_deallocation {} = {}",
            st.lean(),
            st.prevents_deallocation()
        ));
        for &(foreign, rel_lean) in &[(false, ".Local"), (true, ".Foreign")] {
            for &(write, acc_lean) in &[(false, ".Read"), (true, ".Write")] {
                let expected = match st.transition(write, foreign) {
                    Ok(next) => format!("(.ok {})", next.lean()),
                    Err(msg) => format!("(.error (.ub \"{msg}\"))"),
                };
                assertions.push(format!(
                    "Ops05.PermissionProt.transition {} {acc_lean} {rel_lean} = {expected}",
                    st.lean()
                ));
            }
        }
    }

    // Exhaustive `reborrow_permission` across all 48 boolean/enum combinations in BOTH snapshots
    for &is_mutable in &[false, true] {
        for &(prot_yes, prot_lean) in &[(true, ".Strong"), (true, ".Weak"), (false, ".No")] {
            for &inside in &[false, true] {
                for &frozen in &[false, true] {
                    for &implicit_writes in &[false, true] {
                        // S2026_05_Matched: no implicit_writes_enabled branch
                        let exp05 = if !is_mutable {
                            if frozen {
                                if prot_yes {
                                    "(.Prot (.Frozen false))"
                                } else {
                                    "(.Unprot .Frozen)"
                                }
                            } else if prot_yes {
                                "(.Prot .Cell)"
                            } else {
                                "(.Unprot .Cell)"
                            }
                        } else if frozen {
                            if prot_yes {
                                "(.Prot (.Reserved false false))"
                            } else {
                                "(.Unprot .Reserved)"
                            }
                        } else if prot_yes {
                            "(.Prot (.Reserved false false))"
                        } else {
                            "(.Unprot .ReservedIm)"
                        };
                        assertions.push(format!(
                            "Ops05.reborrow_permission {is_mutable} {prot_lean} {inside} {frozen} {implicit_writes} = {exp05}"
                        ));

                        // S2026_07_BleedingEdge: implicit_writes_enabled && inside -> .Prot .Unique
                        let exp07 = if is_mutable && prot_yes && implicit_writes && inside {
                            "(.Prot .Unique)"
                        } else {
                            exp05
                        };
                        assertions.push(format!(
                            "Ops07.reborrow_permission {is_mutable} {prot_lean} {inside} {frozen} {implicit_writes} = {exp07}"
                        ));
                    }
                }
            }
        }
    }

    // =========================================================================
    // 5. L5 & L6 Control Flow, Calls, & Machine Step Dispatch Vectors
    // =========================================================================
    for idx in 0..10 {
        assertions.push(format!("Ops05.mrAdvanceStmtPc {idx} = {}", idx + 1));
        assertions.push(format!(
            "Ops05.mrStepDispatchIsTerminator {idx} 5 = {}",
            idx == 5
        ));
    }
    assertions.push(
        "(Ops05.MrStackFrame.jump_to_block { blockIdx := 1, stmtIdx := 4 } 7).blockIdx = 7"
            .to_string(),
    );
    assertions.push(
        "(Ops05.MrStackFrame.jump_to_block { blockIdx := 1, stmtIdx := 4 } 7).stmtIdx = 0"
            .to_string(),
    );
    assertions.push("Ops05.mrLookupSwitchTarget 2 [(1, 10), (2, 20), (3, 30)] 99 = 20".to_string());
    assertions.push("Ops05.mrLookupSwitchTarget 8 [(1, 10), (2, 20), (3, 30)] 99 = 99".to_string());
    assertions.push(
        "Ops05.mrFindCalleeById [(\"f\", 11), (\"g\", 22)] \"g\" = some 22".to_string(),
    );
    assertions.push(
        "Ops05.mrFindCalleeById [(\"f\", 11), (\"g\", 22)] \"h\" = none".to_string(),
    );
    assertions.push("Ops05.mrApplyUnwindAction (some 3) false false = .cleanup 3".to_string());
    assertions.push("Ops05.mrApplyUnwindAction none false false = .panic".to_string());
    assertions.push("Ops05.mrApplyUnwindAction (some 3) true false = .abort".to_string());
    assertions.push("Ops05.mrApplyUnwindAction (some 3) false true = .faultUb".to_string());

    assert!(
        assertions.len() >= 520,
        "expected >= 520 concrete behavioral equivalence vectors, got {}",
        assertions.len()
    );

    // Emit temporary Lean harness and run `lake env lean` to kernel-verify all 520+ vectors
    let tmp = make_ephemeral_temp_dir("behavioral_equiv_500");
    let lean_harness_path = tmp.join("BehavioralEquiv500.lean");
    let mut lean_src = String::with_capacity(64 * 1024);
    lean_src.push_str("import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops\n");
    lean_src.push_str("import MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops\n\n");
    lean_src.push_str("namespace Gate1BehavioralEquiv\n\n");
    lean_src.push_str("open MiniRust.LibSpecr\n\n");
    for (idx, eq_prop) in assertions.iter().enumerate() {
        let expanded = eq_prop
            .replace(
                "Ops05.",
                "MiniRust.Snapshots.S2026_05_Matched.Generated.Ops.",
            )
            .replace(
                "Ops07.",
                "MiniRust.Snapshots.S2026_07_BleedingEdge.Generated.Ops.",
            );
        lean_src.push_str(&format!("theorem vec_{idx:04} : {expanded} := by decide\n"));
    }
    lean_src.push_str("\nend Gate1BehavioralEquiv\n");
    fs::write(&lean_harness_path, &lean_src).expect("write BehavioralEquiv500.lean");

    let home = std::env::var("HOME").unwrap_or_default();
    let current_path = std::env::var("PATH").unwrap_or_default();
    let augmented_path =
        format!("{home}/.cargo/bin:{home}/.elan/bin:{home}/.local/bin:{current_path}");

    let status_build = std::process::Command::new("lake")
        .args(["build", "MiniRust"])
        .current_dir(&examples_dir)
        .env("PATH", &augmented_path)
        .output()
        .expect("spawn `lake build MiniRust`");
    assert!(
        status_build.status.success(),
        "`lake build MiniRust` failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&status_build.stdout),
        String::from_utf8_lossy(&status_build.stderr)
    );

    let output = std::process::Command::new("lake")
        .arg("env")
        .arg("lean")
        .arg(&lean_harness_path)
        .current_dir(&examples_dir)
        .env("PATH", &augmented_path)
        .output()
        .expect("spawn `lake env lean` on 520+ vector harness");

    let _ = fs::remove_dir_all(&tmp);

    assert!(
        output.status.success(),
        "Lean 4 kernel verification of {} concrete vectors failed!\nstdout:\n{}\nstderr:\n{}",
        assertions.len(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
