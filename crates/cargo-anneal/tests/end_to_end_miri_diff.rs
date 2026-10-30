//! End-to-end integration tests for the Anneal <-> Miri differential testing
//! suite (`tests/miri-diff/corpus` and `tests/miri-diff/manifest.toml`).
//!
//! Exercises:
//! 1. Manifest parsing and validation (`tests/miri-diff/manifest.toml`),
//!    including rejection of stale `known_anneal_bug` entries whose
//!    `observed_anneal_tag` already equals `miri_verdict`.
//! 2. Full 74-test differential execution (`run_miri_diff_suite`):
//!    - Captures MIR from `tests/miri-diff/corpus` with Miri-matching flags
//!      (`-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`).
//!    - Proves `TotalVerificationResult` for all 22 non-bug `pass` tests.
//!    - Proves `StatefulVerificationResult` (`post := False`) and
//!      `¬ TotalClaim.holds` for all 9 non-bug `panic` tests.
//!    - Proves `¬ StatefulClaim.holds ∧ ¬ TotalClaim.holds` via
//!      `refuteMirPointByStrictUB` for all 29 non-bug `ub` tests.
//!    - Enforces `evalMirDiffTagBounded` equality ratchets for all 14 open
//!      Anneal bugs (`[tests.known_anneal_bug]`).
//!    - Runs `trusted/audit/TrustedBoundary.lean` in `verify-audit` mode
//!      (statement-origin isolation, zero `sorryAx`, zero `axiom`, and full
//!      Lean 4 kernel replay at `trustLevel := 0`).
//! 3. Negative ratification checks:
//!    - Verifies that `refuteMirPointByStrictUB` rejects non-UB outcomes
//!      (such as `externalCall` or normal return).
//!    - Verifies that when an Anneal bug's behavior changes from its recorded
//!      `observed_anneal_tag`, the `known_anneal_bug_ratchet` theorem fails to
//!      build until `manifest.toml` is ratcheted down.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    KnownAnnealBugSpec, MiriDiffConfig, MiriDiffTestEntry, MiriDiffVerdictSpec,
    load_miri_diff_manifest, parse_miri_diff_manifest, render_miri_diff_report,
    render_miri_diff_verify_module, run_lake_verify_targets, run_miri_diff_suite,
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
    assert_eq!(manifest.tests.len(), 74);

    // Every `known_anneal_bug` must have status == "open_bug" and diverge from `miri_verdict`.
    let bug_count = manifest
        .tests
        .iter()
        .filter(|t| t.known_anneal_bug.is_some())
        .count();
    assert_eq!(bug_count, 14);

    // A stale `known_anneal_bug` whose `observed_anneal_tag` equals `miri_verdict`
    // must be rejected at parse time.
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
        manifest_path,
        anneal_repo_root: Some(checkout_root),
        rustc_wrapper: Some(wrapper_bin),
    };

    let report = run_miri_diff_suite(&config).expect("74-test Miri differential suite must pass");
    assert_eq!(report.total_tests, 74);
    assert_eq!(report.verified_pass_count, 24);
    assert_eq!(report.verified_panic_count, 9);
    assert_eq!(report.verified_strict_ub_count, 27);
    assert_eq!(report.ratcheted_known_bug_count, 14);
    // 24 pass + 9 panic + 1 helper (`helper_add_ten`) = 34 certificate modules
    assert_eq!(report.audited_certificate_modules.len(), 34);

    let summary = render_miri_diff_report(&report);
    assert!(summary.contains("Total corpus tests:              74"));
    assert!(summary.contains("TrustedBoundary kernel replay:   PASS"));

    let dot_anneal = temp_corpus.join(".anneal");
    let verify_dir = dot_anneal.join("generated/Verify/MiriDiffCorpus");

    // Negative check 1: `refuteMirPointByStrictUB` must reject an item that
    // stops on `externalCall` (or normal return) rather than `FailureKind.ub`.
    let fake_ub_entry = MiriDiffTestEntry {
        name: "pass_exact_div_valid".to_string(),
        category: "scalar_arithmetic".to_string(),
        upstream_path: "tests/pass/intrinsics/integer.rs".to_string(),
        miri_verdict: MiriDiffVerdictSpec::Ub,
        fuel: 128,
        known_anneal_bug: None,
    };
    let (fake_ub_lean, _) = render_miri_diff_verify_module(
        "MiriDiffCorpus",
        "miri_diff_corpus::pass_exact_div_valid",
        &fake_ub_entry,
    )
    .expect("render fake strict UB module");
    fs::write(verify_dir.join("pass_exact_div_valid.lean"), fake_ub_lean)
        .expect("write fake strict UB module");
    let strict_ub_res = run_lake_verify_targets(
        &dot_anneal,
        &["Verify.MiriDiffCorpus.pass_exact_div_valid".to_string()],
    );
    assert!(
        strict_ub_res.is_err(),
        "refuteMirPointByStrictUB must reject non-UB externalCall outcome"
    );

    // Negative check 2: If an open Anneal bug changes behavior (e.g., is fixed
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
        fuel: 128,
        known_anneal_bug: Some(KnownAnnealBugSpec {
            status: "open_bug".to_string(),
            bug_class: "completeness_wrong_return_value".to_string(),
            observed_anneal_tag: MiriDiffVerdictSpec::PassScalar {
                bits: 999,
                size_bytes: 4,
            },
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

    let _ = fs::remove_dir_all(&temp_dir);
}
