// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! End-to-end integration tests for the Anneal <-> Miri differential testing
//! suite (`tests/miri-diff/corpus` and `tests/miri-diff/manifest.toml`).
//!
//! Exercises:
//! 1. Manifest parsing and validation (`tests/miri-diff/manifest.toml`),
//!    including rejection of stale `known_anneal_bug` entries, missing or
//!    spurious `miri_ub_span` fields, and `ub_location_mismatch` entries whose
//!    `observed_anneal_ub_span` already contains `miri_ub_span`, plus live Miri
//!    oracle verification via `tests/miri-diff/sync_miri_suite.py --eval-miri`.
//! 2. Full 77-test differential execution (`run_miri_diff_suite`):
//!    - Captures MIR from `tests/miri-diff/corpus` with Miri-matching flags
//!      (`-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`).
//!    - Proves `TotalVerificationResult` for all 34 non-bug `pass` tests,
//!      including `pass_direct_fn_call`, whose claim links the captured
//!      `helper_add_ten` body as a callee.
//!    - Proves `StatefulVerificationResult` (`post := False`) and
//!      `¬ TotalClaim.holds` for all 9 non-bug `panic` tests.
//!    - Proves `¬ StatefulClaim.holds ∧ ¬ TotalClaim.holds` via
//!      `refuteMirPointByStrictUB` and verifies Miri UB fault locations via
//!      `MiriOracleProbe.lean` for all 33 non-bug `ub` tests.
//!    - Enforces the `evalMirDiffTagBounded` equality ratchet for the single
//!      open Anneal bug (`panic_explicit_macro`, `[tests.known_anneal_bug]`).
//!    - Runs `trusted/audit/TrustedBoundary.lean` in `verify-audit` mode
//!      (statement-origin isolation, zero `sorryAx`, zero `axiom`, and full
//!      Lean 4 kernel replay at `trustLevel := 0`).
//! 3. Negative ratification checks:
//!    - Verifies that `refuteMirPointByStrictUB` rejects non-UB outcomes
//!      (such as `externalCall` or normal return).
//!    - Verifies that reintroducing any fixed `known_anneal_bug` ratchet
//!      (`pass_uninit_union_write_then_read`, `pass_ref_array_elem_temp_index`,
//!      `tb_child_write_then_parent_read`, `tb_child_write_then_parent_write`,
//!      `safe_reborrow_then_parent_write`, `pass_exact_div_valid`,
//!      `ub_exact_div_non_multiple`,
//!      `pass_copy_nonoverlapping_uninit_bytes_to_uninit`,
//!      `pass_tb_unsafe_cell_shared_mutation`, or `pass_direct_fn_call`) fails
//!      to build in Lake.
//!    - Verifies that reintroducing a stale `ub_location_mismatch` ratchet on
//!      `ub_tb_use_frozen_mut_after_parent_read` (`src/lib.rs:606:23: 606:28`)
//!      fails to build in Lake.
//! 4. Callee-linked certificate shapes: `panic` and `ub` certificates rendered
//!    with a linked (unused) intra-crate callee still build in Lake.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    KnownAnnealBugSpec, MiriDiffConfig, MiriDiffTestEntry, MiriDiffVerdictSpec, MiriToolchain,
    SourcePos, SourceSpan, load_miri_diff_manifest, parse_miri_diff_manifest,
    render_miri_diff_report, render_miri_diff_verify_module,
    render_miri_diff_verify_module_with_callees, run_lake_verify_targets, run_miri_diff_suite,
    verify_miri_diff_ub_locations,
};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-miri-diff-{}-{}-{}",
        label,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temporary directory");
    dir
}

fn anneal_checkout_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("resolve Anneal workspace root from CARGO_MANIFEST_DIR")
        .to_path_buf()
}

fn ensure_rustc_capture_binary(checkout_root: &Path) -> PathBuf {
    let exe_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| checkout_root.join("target"));
    let default_bin = target_dir.join("debug").join(&exe_name);

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let status = Command::new(cargo_bin)
        .current_dir(checkout_root)
        .arg("build")
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .status()
        .expect("build anneal-rustc-capture binary");
    assert!(
        status.success(),
        "cargo build -p anneal-rustc-capture must succeed"
    );
    assert!(
        default_bin.is_file(),
        "expected compiled wrapper binary at {}",
        default_bin.display()
    );
    default_bin
}

#[test]
fn miri_diff_manifest_validation_rejects_stale_bugs_and_bad_paths() {
    let checkout_root = anneal_checkout_root();
    let manifest_path = checkout_root.join("tests/miri-diff/manifest.toml");
    let manifest = load_miri_diff_manifest(&manifest_path).expect("parse checked-in manifest.toml");
    assert_eq!(manifest.schema_version, 1);
    assert_eq!(
        manifest.rustc_commit,
        "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
    );
    assert_eq!(manifest.tests.len(), 77);

    // Every `known_anneal_bug` must have status == "open_bug" and diverge from
    // `miri_verdict` (either by tag or by `ub_location_mismatch`).
    let bug_count = manifest
        .tests
        .iter()
        .filter(|t| t.known_anneal_bug.is_some())
        .count();
    assert_eq!(bug_count, 1);

    // Every `ub` test must have `miri_ub_span` recorded, and no non-`ub` test
    // may have `miri_ub_span`.
    for entry in &manifest.tests {
        if entry.miri_verdict == MiriDiffVerdictSpec::Ub {
            assert!(
                entry.miri_ub_span.is_some(),
                "ub test `{}` must record miri_ub_span",
                entry.name
            );
        } else {
            assert!(
                entry.miri_ub_span.is_none(),
                "non-ub test `{}` must not record miri_ub_span",
                entry.name
            );
        }
    }

    // 1. A stale `known_anneal_bug` whose `observed_anneal_tag` equals
    //    `miri_verdict` must be rejected at parse time.
    let stale_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "sample_fixed_test"
category = "scalar_arithmetic"
upstream_path = "tests/pass/integer-ops.rs"
miri_verdict = "pass:scalar:16:4"
fuel = 128
[tests.known_anneal_bug]
status = "open_bug"
bug_class = "completeness_wrong_return_value"
observed_anneal_tag = "pass:scalar:16:4"
suspected_component = "Trusted.Rustc.V2026_06_01.MirSemantics"
summary = "Already fixed bug must be rejected."
"#;
    let err = parse_miri_diff_manifest(stale_manifest)
        .expect_err("stale known_anneal_bug must be rejected");
    assert!(
        err.contains("observed_anneal_tag equal to miri_verdict"),
        "unexpected error: {err}"
    );

    // 2. Missing `miri_ub_span` on a `ub` test must be rejected.
    let missing_span_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "ub_missing_span"
category = "scalar_arithmetic"
upstream_path = "tests/fail/shift_overflow.rs"
miri_verdict = "ub"
fuel = 128
"#;
    let err = parse_miri_diff_manifest(missing_span_manifest)
        .expect_err("ub test without miri_ub_span must be rejected");
    assert!(
        err.contains("missing 'miri_ub_span' in [[tests]] entry"),
        "unexpected error: {err}"
    );

    // 3. Spurious `miri_ub_span` on a `pass` test must be rejected.
    let spurious_span_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "pass_with_ub_span"
category = "scalar_arithmetic"
upstream_path = "tests/pass/integer-ops.rs"
miri_verdict = "pass:scalar:16:4"
miri_ub_span = "src/lib.rs:10:5"
fuel = 128
"#;
    let err = parse_miri_diff_manifest(spurious_span_manifest)
        .expect_err("pass test with miri_ub_span must be rejected");
    assert!(
        err.contains("has miri_ub_span 'src/lib.rs:10:5' but miri_verdict is"),
        "unexpected error: {err}"
    );

    // 4. A `ub_location_mismatch` entry whose `observed_anneal_ub_span` already
    //    contains `miri_ub_span` must be rejected.
    let matching_ub_loc_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "ub_loc_already_matching"
category = "tree_borrows_and_aliasing"
upstream_path = "tests/fail/tree_borrows/reserved-immut-protected.rs"
miri_verdict = "ub"
miri_ub_span = "src/lib.rs:607:5"
fuel = 128
[tests.known_anneal_bug]
status = "open_bug"
bug_class = "ub_location_mismatch"
observed_anneal_tag = "ub"
observed_anneal_ub_span = "src/lib.rs:607:5: 607:10"
suspected_component = "Trusted.Rustc.V2026_06_01.MirSemantics.Places"
summary = "Span already matches Miri."
"#;
    let err = parse_miri_diff_manifest(matching_ub_loc_manifest)
        .expect_err("ub_location_mismatch with matching span must be rejected");
    assert!(
        err.contains("containing miri_ub_span"),
        "unexpected error: {err}"
    );

    // 5. `observed_anneal_ub_span` on `observed_anneal_tag != "ub"` must be
    //    rejected.
    let non_ub_obs_span_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "non_ub_obs_span"
category = "places_projections_and_pointers"
upstream_path = "tests/pass/ptr_offset.rs"
miri_verdict = "pass:scalar:300:4"
fuel = 128
[tests.known_anneal_bug]
status = "open_bug"
bug_class = "completeness_wrong_return_value"
observed_anneal_tag = "pass:scalar:100:4"
observed_anneal_ub_span = "src/lib.rs:400:5: 400:10"
suspected_component = "Trusted.Rustc.V2026_06_01.MirSemantics.Places"
summary = "Non-UB tag with observed_anneal_ub_span must be rejected."
"#;
    let err = parse_miri_diff_manifest(non_ub_obs_span_manifest)
        .expect_err("observed_anneal_ub_span on non-ub tag must be rejected");
    assert!(
        err.contains("expected 'ub'"),
        "unexpected error: {err}"
    );

    // 6. Unknown/misspelled keys in `[[tests]]` or `[tests.known_anneal_bug]`
    //    must be rejected.
    let unknown_test_key_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "typo_test_key"
category = "scalar_arithmetic"
upstream_path = "tests/pass/integer-ops.rs"
miri_verdict = "pass:scalar:16:4"
miri_ub_spna = "src/lib.rs:10:5"
fuel = 128
"#;
    let err = parse_miri_diff_manifest(unknown_test_key_manifest)
        .expect_err("unknown key in [[tests]] must be rejected");
    assert!(
        err.contains("unknown key 'miri_ub_spna' in [[tests]]"),
        "unexpected error: {err}"
    );

    let unknown_bug_key_manifest = r#"
schema_version = 1
rustc_commit = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
rustc_version = "rustc 1.98.0-nightly (14210df0e 2026-05-31)"
upstream_repo_url = "https://github.com/rust-lang/rust"
upstream_tests_subtree = "src/tools/miri/tests"
miri_flags = ["-Zmiri-tree-borrows"]
capture_rustflags = ["-Zmir-opt-level=0"]

[[tests]]
name = "typo_bug_key"
category = "places_projections_and_pointers"
upstream_path = "tests/pass/ptr_offset.rs"
miri_verdict = "pass:scalar:300:4"
fuel = 128
[tests.known_anneal_bug]
status = "open_bug"
bug_class = "completeness_wrong_return_value"
observed_anneal_tag = "pass:scalar:100:4"
observed_anneal_ub_spna = "src/lib.rs:400:5: 400:10"
suspected_component = "Trusted.Rustc.V2026_06_01.MirSemantics.Places"
summary = "Unknown key in [tests.known_anneal_bug] must be rejected."
"#;
    let err = parse_miri_diff_manifest(unknown_bug_key_manifest)
        .expect_err("unknown key in [tests.known_anneal_bug] must be rejected");
    assert!(
        err.contains("unknown key 'observed_anneal_ub_spna' in [tests.known_anneal_bug]"),
        "unexpected error: {err}"
    );

    // 7. Run `tests/miri-diff/sync_miri_suite.py` (and `--eval-miri` when Miri
    //    is installed) to verify structural and live-Miri alignment.
    let sync_script = checkout_root.join("tests/miri-diff/sync_miri_suite.py");
    let has_miri = match MiriToolchain::resolve(None, None, None) {
        Ok(_) => true,
        Err(err) => {
            if env::var("ANNEAL_ALLOW_MISSING_MIRI").as_deref() == Ok("1") {
                eprintln!(
                    "skipping live --eval-miri check (ANNEAL_ALLOW_MISSING_MIRI=1): {err}"
                );
                false
            } else {
                panic!(
                    "Miri toolchain required for sync_miri_suite.py --eval-miri \
                     (set ANNEAL_ALLOW_MISSING_MIRI=1 to run structural check only): {err}"
                );
            }
        }
    };
    let mut cmd = Command::new("python3");
    cmd.current_dir(&checkout_root).arg(&sync_script);
    if has_miri {
        cmd.arg("--eval-miri");
    }
    let out = cmd.output().expect("spawn sync_miri_suite.py");
    assert!(
        out.status.success(),
        "sync_miri_suite.py failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn end_to_end_miri_differential_suite_and_ratchet() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let checked_in_corpus = checkout_root.join("tests/miri-diff/corpus");
    let manifest_path = checkout_root.join("tests/miri-diff/manifest.toml");

    // Copy the hermetic corpus crate into an isolated temporary directory so
    // the checked-in repository tree remains clean.
    let temp_dir = unique_temp_dir("suite");
    let temp_corpus = temp_dir.join("corpus");
    fs::create_dir_all(temp_corpus.join("src")).expect("create temp corpus src");
    fs::copy(
        checked_in_corpus.join("Cargo.toml"),
        temp_corpus.join("Cargo.toml"),
    )
    .expect("copy Cargo.toml");
    fs::copy(
        checked_in_corpus.join("src/lib.rs"),
        temp_corpus.join("src/lib.rs"),
    )
    .expect("copy src/lib.rs");

    let config = MiriDiffConfig {
        corpus_root: temp_corpus.clone(),
        manifest_path: manifest_path.clone(),
        anneal_repo_root: Some(checkout_root.clone()),
        rustc_wrapper: Some(wrapper_bin.clone()),
    };

    let report = run_miri_diff_suite(&config).expect("77-test Miri differential suite must pass");
    assert_eq!(report.total_tests, 77);
    assert_eq!(report.verified_pass_count, 34);
    assert_eq!(report.verified_panic_count, 9);
    assert_eq!(report.verified_strict_ub_count, 33);
    assert_eq!(report.ratcheted_known_bug_count, 1);
    // 34 pass + 9 panic + 1 helper (`helper_add_ten`) = 44 certificate modules
    assert_eq!(report.audited_certificate_modules.len(), 44);
    assert!(
        report
            .audited_certificate_modules
            .iter()
            .any(|m| m == "Verify.MiriDiffCorpus.pass_direct_fn_call"),
        "pass_direct_fn_call must be an audited certificate module: {:?}",
        report.audited_certificate_modules
    );

    let summary = render_miri_diff_report(&report);
    assert!(summary.contains("Total corpus tests:              77"));
    assert!(summary.contains("TrustedBoundary kernel replay:   PASS"));

    let dot_anneal = temp_corpus.join(".anneal");
    let verify_dir = dot_anneal.join("generated/Verify/MiriDiffCorpus");

    // The retired bug's certificate links only the captured `helper_add_ten`
    // body, through the general bounded combinator rather than the
    // callee-free point combinator.
    let direct_call_verify = fs::read_to_string(verify_dir.join("pass_direct_fn_call.lean"))
        .expect("read pass_direct_fn_call verify module");
    assert_eq!(
        direct_call_verify
            .matches("callees := [Mir.MiriDiffCorpus.helper_add_ten.body]")
            .count(),
        2,
        "unexpected pass_direct_fn_call certificate:\n{direct_call_verify}"
    );
    assert!(direct_call_verify.contains("Lower.verifyTotalMirBounded _ 128"));
    assert!(!direct_call_verify.contains("known_anneal_bug_ratchet"));

    // Negative check 1: `refuteMirPointByStrictUB` must reject an item that
    // stops on `externalCall` (or normal return) rather than `FailureKind.ub`.
    for (non_ub_name, non_ub_cat, non_ub_path) in [
        (
            "pass_direct_fn_call",
            "control_flow_and_calls",
            "tests/pass/calls.rs",
        ),
        (
            "pass_exact_div_valid",
            "scalar_arithmetic",
            "tests/pass/intrinsics/integer.rs",
        ),
    ] {
        let orig_path = verify_dir.join(format!("{non_ub_name}.lean"));
        let orig_content = fs::read_to_string(&orig_path).expect("read original verify module");
        let fake_ub_entry = MiriDiffTestEntry {
            name: non_ub_name.to_string(),
            category: non_ub_cat.to_string(),
            upstream_path: non_ub_path.to_string(),
            miri_verdict: MiriDiffVerdictSpec::Ub,
            miri_ub_span: Some(
                SourcePos::parse_rustc_pos("src/lib.rs:58:14").expect("parse fake miri_ub_span"),
            ),
            fuel: 128,
            known_anneal_bug: None,
        };
        let (fake_ub_lean, _) = render_miri_diff_verify_module(
            "MiriDiffCorpus",
            &format!("miri_diff_corpus::{non_ub_name}"),
            &fake_ub_entry,
        )
        .expect("render fake strict UB module");
        fs::write(&orig_path, fake_ub_lean).expect("write fake strict UB module");
        let strict_ub_res = run_lake_verify_targets(
            &dot_anneal,
            &[format!("Verify.MiriDiffCorpus.{non_ub_name}")],
        );
        fs::write(&orig_path, orig_content).expect("restore original verify module");
        assert!(
            strict_ub_res.is_err(),
            "refuteMirPointByStrictUB must reject non-UB outcome on `{non_ub_name}`"
        );
    }

    // Negative check 2: Reintroducing any fixed `known_anneal_bug` ratchet
    // must fail to compile in Lake.
    for (fixed_name, category, upstream_path, miri_verdict, miri_ub_span, stale_tag) in [
        (
            "pass_uninit_union_write_then_read",
            "uninitialized_memory_and_padding",
            "tests/pass/uninit_byte_read.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 0xAABBCCDDu128,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "pass_ref_array_elem_temp_index",
            "arrays_slices_and_indexing",
            "tests/pass/arrays.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 25,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "tb_child_write_then_parent_read",
            "tree_borrows",
            "tests/pass/tree_borrows/reserved.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 1,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "tb_child_write_then_parent_write",
            "tree_borrows",
            "tests/pass/tree_borrows/reserved.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 3,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "safe_reborrow_then_parent_write",
            "tree_borrows",
            "tests/pass/tree_borrows/reborrow-is-read.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 7,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "pass_exact_div_valid",
            "scalar_arithmetic",
            "tests/pass/intrinsics/integer.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 12,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::ExternalCall("core::intrinsics::exact_div".to_string()),
        ),
        (
            "ub_exact_div_non_multiple",
            "scalar_arithmetic",
            "tests/fail/intrinsics/exact_div1.rs",
            MiriDiffVerdictSpec::Ub,
            Some(SourcePos::parse_rustc_pos("src/lib.rs:248:14").expect("parse miri_ub_span")),
            MiriDiffVerdictSpec::ExternalCall("core::intrinsics::exact_div".to_string()),
        ),
        (
            "pass_copy_nonoverlapping_uninit_bytes_to_uninit",
            "uninit_and_padding",
            "tests/pass/move-uninit-primval.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 5,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "pass_tb_unsafe_cell_shared_mutation",
            "tree_borrows",
            "tests/pass/both_borrows/interior_mutability.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 42,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::Ub,
        ),
        (
            "pass_direct_fn_call",
            "control_flow_and_calls",
            "tests/pass/calls.rs",
            MiriDiffVerdictSpec::PassScalar {
                bits: 42,
                size_bytes: 4,
            },
            None,
            MiriDiffVerdictSpec::ExternalCall("miri_diff_corpus::helper_add_ten".to_string()),
        ),
    ] {
        // Render each ratchet the way `stage_miri_diff_workspace` does, with the
        // test's captured intra-crate callees linked. Without linking,
        // `pass_direct_fn_call` still stops at its `helper_add_ten` call, so its
        // stale `externalCall` ratchet would hold and the check would be vacuous.
        let linked_callees: Vec<String> = match fixed_name {
            "pass_direct_fn_call" => vec!["MiriDiffCorpus.helper_add_ten".to_string()],
            _ => Vec::new(),
        };
        let orig_path = verify_dir.join(format!("{fixed_name}.lean"));
        let orig_content = fs::read_to_string(&orig_path).expect("read original verify module");
        let stale_entry = MiriDiffTestEntry {
            name: fixed_name.to_string(),
            category: category.to_string(),
            upstream_path: upstream_path.to_string(),
            miri_verdict,
            miri_ub_span,
            fuel: 128,
            known_anneal_bug: Some(KnownAnnealBugSpec {
                status: "open_bug".to_string(),
                bug_class: "completeness_false_positive_ub".to_string(),
                observed_anneal_tag: stale_tag,
                observed_anneal_ub_span: None,
                suspected_component: "Trusted.Rustc.V2026_06_01.MirSemantics".to_string(),
                summary: "Reintroduced stale bug ratchet must fail.".to_string(),
            }),
        };
        let (stale_lean, _) = render_miri_diff_verify_module_with_callees(
            "MiriDiffCorpus",
            &format!("miri_diff_corpus::{fixed_name}"),
            &stale_entry,
            &linked_callees,
        )
        .expect("render stale bug ratchet module");
        fs::write(&orig_path, stale_lean).expect("write stale bug ratchet module");
        let stale_res = run_lake_verify_targets(
            &dot_anneal,
            &[format!("Verify.MiriDiffCorpus.{fixed_name}")],
        );
        fs::write(&orig_path, orig_content).expect("restore original verify module");
        assert!(
            stale_res.is_err(),
            "reintroducing fixed known_anneal_bug ratchet for `{fixed_name}` must fail in Lake"
        );
    }

    // Negative check 3: If an open Anneal bug changes behavior (e.g., is fixed
    // to return 300 instead of 100), the `known_anneal_bug_ratchet` theorem
    // must fail to compile, forcing the manifest to be ratcheted down.
    let mismatched_bug_entry = MiriDiffTestEntry {
        name: "pass_ptr_offset_within_array".to_string(),
        category: "places_projections_and_pointers".to_string(),
        upstream_path: "tests/pass/ptr_offset.rs".to_string(),
        miri_verdict: MiriDiffVerdictSpec::PassScalar {
            bits: 300,
            size_bytes: 4,
        },
        miri_ub_span: None,
        fuel: 128,
        known_anneal_bug: Some(KnownAnnealBugSpec {
            status: "open_bug".to_string(),
            bug_class: "completeness_wrong_return_value".to_string(),
            observed_anneal_tag: MiriDiffVerdictSpec::PassScalar {
                bits: 999,
                size_bytes: 4,
            },
            observed_anneal_ub_span: None,
            suspected_component: "Trusted.Rustc.V2026_06_01.MirSemantics.Places".to_string(),
            summary: "Simulated mismatched bug tag".to_string(),
        }),
    };
    let (mismatched_lean, _) = render_miri_diff_verify_module(
        "MiriDiffCorpus",
        "miri_diff_corpus::pass_ptr_offset_within_array",
        &mismatched_bug_entry,
    )
    .expect("render mismatched bug ratchet module");
    fs::write(
        verify_dir.join("pass_ptr_offset_within_array.lean"),
        mismatched_lean,
    )
    .expect("write mismatched bug ratchet module");
    let ratchet_res = run_lake_verify_targets(
        &dot_anneal,
        &["Verify.MiriDiffCorpus.pass_ptr_offset_within_array".to_string()],
    );
    assert!(
        ratchet_res.is_err(),
        "known_anneal_bug_ratchet must fail when Anneal's behavior no longer matches observed_anneal_tag"
    );

    // Negative check 4: Reintroducing the stale `ub_location_mismatch` ratchet on
    // `ub_tb_use_frozen_mut_after_parent_read` (`src/lib.rs:606:23: 606:28`) must
    // fail in Lake now that Anneal faults at Miri's exact span (`src/lib.rs:607:5`).
    let wrong_span_entry = MiriDiffTestEntry {
        name: "ub_tb_use_frozen_mut_after_parent_read".to_string(),
        category: "tree_borrows".to_string(),
        upstream_path: "tests/fail/both_borrows/outdated_local.rs".to_string(),
        miri_verdict: MiriDiffVerdictSpec::Ub,
        miri_ub_span: Some(
            SourcePos::parse_rustc_pos("src/lib.rs:607:5").expect("parse miri_ub_span"),
        ),
        fuel: 128,
        known_anneal_bug: Some(KnownAnnealBugSpec {
            status: "open_bug".to_string(),
            bug_class: "ub_location_mismatch".to_string(),
            observed_anneal_tag: MiriDiffVerdictSpec::Ub,
            observed_anneal_ub_span: Some(
                SourceSpan::parse_anneal_span("src/lib.rs:606:23: 606:28")
                    .expect("parse stale observed_anneal_ub_span"),
            ),
            suspected_component: "Trusted.Rustc.V2026_06_01.MirSemantics.Places".to_string(),
            summary: "Stale observed_anneal_ub_span must fail kernel rfl.".to_string(),
        }),
    };
    let orig_ub_tb_path = verify_dir.join("ub_tb_use_frozen_mut_after_parent_read.lean");
    let orig_ub_tb_content =
        fs::read_to_string(&orig_ub_tb_path).expect("read original ub_tb verify module");
    let (wrong_span_lean, _) = render_miri_diff_verify_module(
        "MiriDiffCorpus",
        "miri_diff_corpus::ub_tb_use_frozen_mut_after_parent_read",
        &wrong_span_entry,
    )
    .expect("render wrong span ratchet module");
    fs::write(&orig_ub_tb_path, wrong_span_lean).expect("write wrong span ratchet module");
    let wrong_span_res = run_lake_verify_targets(
        &dot_anneal,
        &["Verify.MiriDiffCorpus.ub_tb_use_frozen_mut_after_parent_read".to_string()],
    );
    fs::write(&orig_ub_tb_path, orig_ub_tb_content).expect("restore original ub_tb verify module");
    assert!(
        wrong_span_res.is_err(),
        "known_anneal_bug_ratchet must fail when stale observed_anneal_ub_span is reintroduced"
    );

    // Negative check 5: Corrupting `miri_ub_span` on a passing strict UB test
    // (`ub_unchecked_add_overflow_u32`) must fail `verify_miri_diff_ub_locations`.
    let mut corrupted_span_manifest =
        load_miri_diff_manifest(&manifest_path).expect("load checked-in manifest");
    let add_ovf_entry = corrupted_span_manifest
        .tests
        .iter_mut()
        .find(|t| t.name == "ub_unchecked_add_overflow_u32")
        .expect("find ub_unchecked_add_overflow_u32");
    add_ovf_entry.miri_ub_span =
        Some(SourcePos::parse_rustc_pos("src/lib.rs:999:1").expect("parse fake pos"));
    let corrupted_err =
        verify_miri_diff_ub_locations(&dot_anneal, "MiriDiffCorpus", &corrupted_span_manifest)
            .expect_err("corrupted miri_ub_span must fail UB location verification");
    assert!(
        corrupted_err.contains("UB location mismatch on 'ub_unchecked_add_overflow_u32'"),
        "unexpected error: {corrupted_err}"
    );

    // Positive check 6: the callee-linked `panic` and `ub` certificate shapes
    // (which no corpus test currently needs) elaborate and kernel-check. Linking
    // `helper_add_ten` into tests that never call it must not change their
    // outcome.
    let manifest = load_miri_diff_manifest(&manifest_path).expect("load checked-in manifest");
    for linked_name in [
        "panic_checked_add_overflow",
        "ub_unchecked_add_overflow_u32",
    ] {
        let linked_entry = manifest
            .tests
            .iter()
            .find(|t| t.name == linked_name)
            .expect("find callee-linked certificate test");
        let orig_path = verify_dir.join(format!("{linked_name}.lean"));
        let orig_content = fs::read_to_string(&orig_path).expect("read original verify module");
        let (linked_lean, _) = render_miri_diff_verify_module_with_callees(
            "MiriDiffCorpus",
            &format!("miri_diff_corpus::{linked_name}"),
            linked_entry,
            &["MiriDiffCorpus.helper_add_ten".to_string()],
        )
        .expect("render callee-linked certificate");
        assert!(linked_lean.contains("callees := [Mir.MiriDiffCorpus.helper_add_ten.body]"));
        fs::write(&orig_path, linked_lean).expect("write callee-linked certificate");
        let linked_res = run_lake_verify_targets(
            &dot_anneal,
            &[format!("Verify.MiriDiffCorpus.{linked_name}")],
        );
        fs::write(&orig_path, orig_content).expect("restore original verify module");
        assert!(
            linked_res.is_ok(),
            "callee-linked certificate for `{linked_name}` must build: {linked_res:?}"
        );
    }

    let _ = fs::remove_dir_all(&temp_dir);
}
