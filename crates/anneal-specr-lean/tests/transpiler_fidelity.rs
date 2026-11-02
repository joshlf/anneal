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
        assert_eq!(lock_check.verified_output_files, 1);

        // 2. Audit generated `SpecIndex.lean` for strict proof & repository hygiene.
        let lean_path = gen_dir.join("Generated/SpecIndex.lean");
        let lean_src = fs::read_to_string(&lean_path).expect("read generated SpecIndex.lean");
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
