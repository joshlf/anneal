// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! End-to-end integration tests for `miri-difftest` candidate generation, live
//! Miri + Anneal oracle execution (`evaluate_miri_batches`), `NotCompared`
//! coverage reporting, finding bundle generation, and standalone reproducer
//! round-tripping (`--reproduce`).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_difftest::miri_eval::{evaluate_miri_batches, reproduce_miri_finding};
use anneal_difftest::mutators_miri::{
    GeneratedMiriCandidate, build_standalone_candidate_source, generate_miri_corpus_batch,
};
use cargo_anneal::{
    AnnealOutcome, CaptureDriverConfig, ComparisonVerdict, DivergenceKind, MiriOutcome,
    compare_miri_and_anneal, resolve_rustc_wrapper,
};

struct TempDir(PathBuf);

impl std::ops::Deref for TempDir {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn unique_temp_dir(label: &str) -> TempDir {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!(
        "anneal_miri_oracle_test_{label}_{}_{stamp}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    TempDir(dir)
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repository root")
        .to_path_buf()
}

#[test]
fn miri_identity_batch_reproduces_corpus_divergences_and_coverage() {
    let dir = unique_temp_dir("identity");
    let json_path = dir.join("identity.json");
    let findings_dir = dir.join("findings_id");
    let bin = env!("CARGO_BIN_EXE_miri-difftest");

    let out = Command::new(bin)
        .args(["--identity", "--findings-dir"])
        .arg(&findings_dir)
        .arg("--output-json")
        .arg(&json_path)
        .output()
        .expect("run miri-difftest --identity");
    assert!(
        out.status.success(),
        "miri-difftest --identity failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("# `miri-difftest` Differential Oracle Report"));
    assert!(stdout.contains("- **Oracle comparison**: PERFORMED"));
    assert!(stdout.contains("## `NotCompared` Coverage Table"));
    // Every identity candidate is compared, so the report lists no unmodeled
    // external calls: `helper_add_ten` is linked as a captured callee, and the
    // `core::fmt::Arguments` constructors behind `panic!("...")` are linked as
    // synthetic stubs.
    assert!(!stdout.contains("### Unmodeled External Calls"));
    assert!(!stdout.contains("`core::intrinsics::exact_div`"));
    assert!(!stdout.contains("miri_diff_corpus::helper_add_ten"));
    assert!(!stdout.contains("core::fmt::Arguments"));
    assert!(stdout.contains("- **Reconciled panic-macro sites** (counted in **Agree**): `1`"));
    assert!(stdout.contains("## Reconciled Panic-Macro Sites"));
    assert!(stdout.contains("| `panic_explicit_macro` |"));
    assert!(stdout.contains("| \"explicit panic in corpus\" | `true` |"));

    let verify = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, pathlib, sys, tomllib

json_path = pathlib.Path(sys.argv[1])
findings_dir = pathlib.Path(sys.argv[2])
manifest_path = pathlib.Path(sys.argv[3])
data = json.loads(json_path.read_text())

assert data["harness"] == "miri-difftest"
assert data["oracle_comparison"] == "performed"
assert data["mode"] == "identity"
assert data["total_candidates"] == 77
assert data["compiled_candidates"] == 77
assert data["compile_failed_candidates"] == 0
assert data["compared_candidates"] == 77
assert data["agree_count"] == 77
assert data["diverge_count"] == 0
assert data["kernel_confirmed_divergences"] == 0
assert data["not_compared_count"] == 0
assert isinstance(data.get("obs_path_signatures"), list)
assert len(data["obs_path_signatures"]) > 0
assert all(s.startswith("miri:") for s in data["obs_path_signatures"])
assert "miri:panic_explicit_macro@identity:panic_vs_panic:agree" in data["obs_path_signatures"], (
    f"panic_explicit_macro must compare and agree: {data['obs_path_signatures']}"
)

div_classes = data["divergence_classes"]
assert div_classes == {
    "false_positive_ub": 0,
    "missed_ub": 0,
    "panic_site_mismatch": 0,
    "panic_vs_return": 0,
    "return_vs_panic": 0,
    "ub_location_mismatch": 0,
    "wrong_value": 0,
}, f"unexpected divergence_classes: {div_classes}"

nc = data["not_compared_reasons"]
assert nc == {
    "capture_failed": 0,
    "compile_failed": 0,
    "external_call": 0,
    "miri_oracle_error": 0,
    "out_of_fuel": 0,
    "unsupported": 0,
}, f"unexpected not_compared_reasons: {nc}"

ext = data["unmodeled_external_calls"]
assert ext == {}, f"unexpected ext: {ext}"

expected_findings = {}

manifest = tomllib.loads(manifest_path.read_text())
manifest_bugs = {
    t["name"]
    for t in manifest["tests"]
    if "known_anneal_bug" in t
    and not t["known_anneal_bug"].get("observed_anneal_tag", "").startswith("externalCall:")
}
assert set(expected_findings.keys()) == manifest_bugs, (
    f"expected_findings keys {set(expected_findings)} != manifest bugs {manifest_bugs}"
)
manifest_ext = {
    t["name"]
    for t in manifest["tests"]
    if "known_anneal_bug" in t
    and t["known_anneal_bug"].get("observed_anneal_tag", "").startswith("externalCall:")
}
assert len(manifest_ext) == 1, f"expected 1 externalCall entry in manifest, got {manifest_ext}"
assert manifest_ext == {"panic_explicit_macro"}, f"unexpected externalCall entries: {manifest_ext}"

findings = data["findings"]
assert len(findings) == 0
actual_map = {f["fn_name"]: f["divergence_class"] for f in findings}
assert actual_map == expected_findings, f"mismatch: {actual_map} vs {expected_findings}"

# `panic_explicit_macro` is the only identity candidate whose agreement rests on
# the panic-macro reconciliation, and Anneal's recovered panic message matched
# the message that Miri printed.
assert data["reconciled_panic_sites_count"] == 1, data["reconciled_panic_sites"]
assert data["reconciled_panic_sites"] == [
    {
        "fn_name": "panic_explicit_macro",
        "seed_name": "panic_explicit_macro",
        "batch_miri_pos": data["reconciled_panic_sites"][0]["batch_miri_pos"],
        "anneal_span": data["reconciled_panic_sites"][0]["anneal_span"],
        "anneal_panic_message": "explicit panic in corpus",
        "kernel_confirmed": True,
    }
], data["reconciled_panic_sites"]
site = data["reconciled_panic_sites"][0]
assert site["batch_miri_pos"].startswith("src/lib.rs:"), site
assert "/library/core/src/panic.rs:" in site["anneal_span"], site
"#,
        )
        .arg(&json_path)
        .arg(&findings_dir)
        .arg(repo_root().join("tests/miri-diff/manifest.toml"))
        .output()
        .expect("run python3 verification");
    assert!(
        verify.status.success(),
        "identity verification failed:\n{}",
        String::from_utf8_lossy(&verify.stderr)
    );
}

#[test]
fn miri_seeded_runs_produce_pass_panic_ub_mix_vary_with_seed_and_reproduce_findings() {
    let dir = unique_temp_dir("seeded");
    let bin = env!("CARGO_BIN_EXE_miri-difftest");

    let json1 = dir.join("seed1.json");
    let findings1 = dir.join("findings1");
    let out1 = Command::new(bin)
        .args([
            "--batches",
            "2",
            "--batch-size",
            "6",
            "--seed",
            "0x5EED0001",
            "--findings-dir",
        ])
        .arg(&findings1)
        .arg("--output-json")
        .arg(&json1)
        .output()
        .expect("run miri-difftest seed1");
    assert!(
        out1.status.success(),
        "seed1 failed:\n{}",
        String::from_utf8_lossy(&out1.stderr)
    );

    let json2 = dir.join("seed2.json");
    let findings2 = dir.join("findings2");
    let out2 = Command::new(bin)
        .args([
            "--batches",
            "2",
            "--batch-size",
            "6",
            "--seed",
            "0xCAFEBABE",
            "--findings-dir",
        ])
        .arg(&findings2)
        .arg("--output-json")
        .arg(&json2)
        .output()
        .expect("run miri-difftest seed2");
    assert!(
        out2.status.success(),
        "seed2 failed:\n{}",
        String::from_utf8_lossy(&out2.stderr)
    );

    // Verify both runs produced a mix of pass, panic, and ub verdicts from Miri,
    // that metrics differ across seeds, and that all compared candidates agree.
    let check_out = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, pathlib, sys

d1 = json.loads(pathlib.Path(sys.argv[1]).read_text())
d2 = json.loads(pathlib.Path(sys.argv[2]).read_text())

for label, d in [("seed1", d1), ("seed2", d2)]:
    assert d["oracle_comparison"] == "performed", label
    assert d["mode"] == "seeded", label
    assert d["total_candidates"] == 12, label
    assert d["compiled_candidates"] >= 11, label
    assert d["compared_candidates"] > 0, label
    assert isinstance(d.get("obs_path_signatures"), list) and len(d["obs_path_signatures"]) > 0, label
    mv = d["miri_verdicts"]
    assert mv["pass"] > 0, f"{label} missing Miri pass verdicts: {mv}"
    assert mv["panic"] > 0, f"{label} missing Miri panic verdicts: {mv}"
    assert mv["ub"] > 0, f"{label} missing Miri ub verdicts: {mv}"
    assert mv["error"] == 0, f"{label} unexpected Miri oracle error: {mv}"
    assert d["diverge_count"] == d["kernel_confirmed_divergences"], label
    assert d["diverge_count"] == len(d["findings"]), label
    assert d["agree_count"] == d["compared_candidates"], label
    assert d.get("unmodeled_external_calls", {}).get("miri_diff_corpus::helper_add_ten", 0) == 0, (
        f"{label} unexpected helper_add_ten skip: {d.get('unmodeled_external_calls')}"
    )

# Seed sensitivity: mutator application counts and Miri/Anneal distributions
# must change when the seed changes.
assert (
    d1["miri_verdicts"] != d2["miri_verdicts"]
    or d1["anneal_outcomes"] != d2["anneal_outcomes"]
    or d1["mutator_applications"] != d2["mutator_applications"]
), "metrics did not change across distinct seeds"
assert d1["mutator_applications"] != d2["mutator_applications"], (
    f"mutator_applications identical across seeds: {d1['mutator_applications']}"
)
"#,
        )
        .arg(&json1)
        .arg(&json2)
        .output()
        .expect("run python3 seed comparison");
    assert!(
        check_out.status.success(),
        "seeded check failed:\n{}",
        String::from_utf8_lossy(&check_out.stderr)
    );

    // Negative control: evaluate a candidate that writes a surrogate code point
    // (0xD800) into a `char` local via `*mut u32` and loads it as `u32`,
    // verifying finding bundle generation (`repro.rs`, `finding.json`,
    // `SUMMARY.md`) and standalone `--reproduce` round-tripping.
    let root = repo_root();
    let neg_fn = "\
pub fn neg_ctrl_char_surrogate_via_ptr__b0_c0() -> u32 {
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = 0xD800u32;
    }
    c as u32
}
";
    let neg_cand = GeneratedMiriCandidate {
        id: 0,
        seed_index: 0,
        seed_name: "ub_transmute_invalid_char_surrogate".to_string(),
        fn_name: "neg_ctrl_char_surrogate_via_ptr__b0_c0".to_string(),
        seed_u64: 0xDEAD_BEEF,
        applied_mutators: vec!["BitValidityTransmuteMutator".to_string()],
        tracked_locals: Vec::new(),
        fn_source: neg_fn.to_string(),
        source: build_standalone_candidate_source(neg_fn),
    };
    let neg_findings_dir = dir.join("findings_neg");
    let neg_report = evaluate_miri_batches(
        "seeded",
        0xDEAD_BEEF,
        &[vec![neg_cand]],
        1,
        Some(&neg_findings_dir),
        Some(&root),
    )
    .expect("evaluate negative-control divergence candidate");
    assert_eq!(neg_report.compared_candidates, 1);
    assert_eq!(neg_report.diverge_count, 1);
    assert_eq!(neg_report.kernel_confirmed_divergences, 1);
    assert_eq!(neg_report.findings.len(), 1);
    let f = &neg_report.findings[0];
    assert!(f.kernel_confirmed);
    assert!(
        f.kernel_confirm_theorems
            .contains("def linkedCallees : List CapturedMir :=")
    );
    assert!(f.kernel_confirm_theorems.contains("theorem confirm_tag_"));
    assert!(f.kernel_confirm_theorems.contains("theorem confirm_probe_"));
    assert!(f.kernel_confirm_theorems.contains(":= by\n  rfl"));
    assert!(f.mir_neighborhood.contains("def body : CapturedMir :="));
    let repro_path = f.repro_path.as_ref().expect("repro_path");
    let bundle_dir = repro_path.parent().expect("bundle_dir");
    assert!(bundle_dir.join("finding.json").is_file());
    let summary_md = fs::read_to_string(bundle_dir.join("SUMMARY.md")).expect("read SUMMARY.md");
    assert!(summary_md.contains("## Miri Output Excerpt"));
    assert!(summary_md.contains("## Lean 4 Kernel Confirmation Theorems"));
    assert!(summary_md.contains("## Captured MIR Neighborhood"));
    assert!(summary_md.contains("## Mutant Source"));

    let repro_json = dir.join("repro_neg.json");
    let repro_out = Command::new(bin)
        .arg("--reproduce")
        .arg(repro_path)
        .arg("--output-json")
        .arg(&repro_json)
        .output()
        .expect("run miri-difftest --reproduce");
    assert!(
        repro_out.status.success(),
        "--reproduce failed for {}:\n{}",
        repro_path.display(),
        String::from_utf8_lossy(&repro_out.stderr)
    );
    let verify_repro = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, pathlib, sys
rep = json.loads(pathlib.Path(sys.argv[1]).read_text())
_, _, fn_name, exp_class, exp_miri, exp_anneal, exp_lean = sys.argv
assert rep["fn_name"] == fn_name, f"{rep['fn_name']} != {fn_name}"
assert rep["verdict"] == "diverge", f"expected diverge, got {rep}"
assert rep["divergence_class"] == exp_class, f"{rep['divergence_class']} != {exp_class}"
assert rep["miri_outcome"] == exp_miri, f"{rep['miri_outcome']} != {exp_miri}"
assert rep["anneal_outcome"] == exp_anneal, f"{rep['anneal_outcome']} != {exp_anneal}"
assert rep["anneal_lean_tag"] == exp_lean, f"{rep['anneal_lean_tag']} != {exp_lean}"
assert rep["kernel_confirmed"] is True, f"expected kernel_confirmed=True, got {rep}"
"#,
        )
        .arg(&repro_json)
        .args([
            &f.fn_name,
            &f.divergence_class,
            &f.miri_outcome_tag,
            &f.anneal_outcome_tag,
            &f.anneal_lean_tag,
        ])
        .output()
        .expect("verify reproducer JSON");
    assert!(
        verify_repro.status.success(),
        "reproducer mismatch for {}:\n{}",
        repro_path.display(),
        String::from_utf8_lossy(&verify_repro.stderr)
    );
}

#[test]
fn evaluate_miri_batches_counts_compile_failures_and_rejects_zero_compiled() {
    let root = repo_root();
    let mut batch = generate_miri_corpus_batch(2, 0x1234_5678, 0);
    assert_eq!(batch.len(), 2);

    let broken_fn = "pub fn broken_cand__b0_c2() -> u32 {\n    let x: u32 = \"not_an_int\";\n    x\n}\n";
    batch.push(GeneratedMiriCandidate {
        id: 2,
        seed_index: 0,
        seed_name: "pass_integer_arith_basic".to_string(),
        fn_name: "broken_cand__b0_c2".to_string(),
        seed_u64: 0x9999,
        applied_mutators: vec!["ArithmeticCastMutator".to_string()],
        tracked_locals: Vec::new(),
        fn_source: broken_fn.to_string(),
        source: build_standalone_candidate_source(broken_fn),
    });

    let report = evaluate_miri_batches(
        "seeded",
        0x1234_5678,
        &[batch.clone()],
        3,
        None,
        Some(&root),
    )
    .expect("evaluate_miri_batches with 2 valid + 1 broken candidate");

    assert_eq!(report.total_candidates, 3);
    assert_eq!(report.compiled_candidates, 2);
    assert_eq!(report.compile_failed_candidates, 1);
    assert_eq!(
        report.not_compared_reasons.get("compile_failed").copied(),
        Some(1),
        "compile failures must be recorded in not_compared_reasons['compile_failed']"
    );
    assert_eq!(
        report.compared_candidates + report.not_compared_count,
        report.total_candidates
    );
    assert_eq!(report.item_reports.len(), 2);
    let evaluated_names: BTreeSet<String> =
        report.item_reports.iter().map(|r| r.name.clone()).collect();
    assert!(!evaluated_names.contains("broken_cand__b0_c2"));

    // When 0 candidates compile, `evaluate_miri_batches` must return an error
    // rather than claiming `"oracle_comparison": "performed"`.
    let only_broken = vec![vec![batch.pop().expect("broken candidate")]];
    let err = evaluate_miri_batches("seeded", 0x1234_5678, &only_broken, 1, None, Some(&root))
        .expect_err("0 compiled candidates must fail oracle evaluation");
    assert!(
        err.contains("cannot perform oracle comparison: 0 of 1 candidates compiled"),
        "unexpected error message: {err}"
    );
}

#[test]
fn helper_add_ten_candidates_compare_confirm_and_reproduce_without_external_call_skips() {
    let dir = unique_temp_dir("helper_callees");
    let root = repo_root();
    let bin = env!("CARGO_BIN_EXE_miri-difftest");

    // 1. Both an agreeing mutant and a diverging negative-control mutant calling
    // `helper_add_ten()` must step into `helper_add_ten`, confirm in the Lean 4
    // kernel via `initMachineStateWithMemoryAndCallees`, and round-trip cleanly
    // through `reproduce_miri_finding` and `miri-difftest --reproduce`.
    let agree_fn = "\
pub fn agree_helper_call__b0_c0() -> u32 {
    let base: u32 = helper_add_ten();
    (base * 3u32) + helper_add_ten() + 2u32
}
";
    let agree_cand = GeneratedMiriCandidate {
        id: 0,
        seed_index: 0,
        seed_name: "pass_direct_fn_call".to_string(),
        fn_name: "agree_helper_call__b0_c0".to_string(),
        seed_u64: 0x1111_2222,
        applied_mutators: vec!["ArithmeticCastMutator".to_string()],
        tracked_locals: Vec::new(),
        fn_source: agree_fn.to_string(),
        source: build_standalone_candidate_source(agree_fn),
    };

    let div_fn = "\
pub fn neg_ctrl_helper_call_surrogate__b0_c1() -> u32 {
    let base: u32 = helper_add_ten();
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = 0xD800u32;
    }
    base + (c as u32)
}
";
    let div_cand = GeneratedMiriCandidate {
        id: 1,
        seed_index: 0,
        seed_name: "pass_direct_fn_call".to_string(),
        fn_name: "neg_ctrl_helper_call_surrogate__b0_c1".to_string(),
        seed_u64: 0x3333_4444,
        applied_mutators: vec!["BitValidityTransmuteMutator".to_string()],
        tracked_locals: Vec::new(),
        fn_source: div_fn.to_string(),
        source: build_standalone_candidate_source(div_fn),
    };

    let findings_dir = dir.join("findings_helper");
    let report = evaluate_miri_batches(
        "seeded",
        0xCAFE_0001,
        &[vec![agree_cand, div_cand]],
        2,
        Some(&findings_dir),
        Some(&root),
    )
    .expect("evaluate helper_add_ten batch");

    assert_eq!(report.total_candidates, 2);
    assert_eq!(report.compiled_candidates, 2);
    assert_eq!(report.compared_candidates, 2);
    assert_eq!(report.agree_count, 1);
    assert_eq!(report.diverge_count, 1);
    assert_eq!(report.not_compared_count, 0);
    assert_eq!(report.kernel_confirmed_divergences, 1);
    assert!(
        !report
            .unmodeled_external_calls
            .contains_key("miri_diff_corpus::helper_add_ten"),
        "unexpected helper_add_ten in unmodeled_external_calls: {:?}",
        report.unmodeled_external_calls
    );
    assert_eq!(report.findings.len(), 1);

    let f = &report.findings[0];
    assert_eq!(f.fn_name, "neg_ctrl_helper_call_surrogate__b0_c1");
    assert!(f.kernel_confirmed);
    assert!(
        f.kernel_confirm_theorems
            .contains("def linkedCallees : List CapturedMir :=")
    );
    assert!(f.kernel_confirm_theorems.contains("theorem confirm_tag_"));
    assert!(f.kernel_confirm_theorems.contains("theorem confirm_probe_"));
    assert!(
        f.kernel_confirm_theorems
            .contains("initMachineStateWithMemoryAndCallees")
    );
    assert!(f.kernel_confirm_theorems.contains("linkedCallees"));
    assert!(f.kernel_confirm_theorems.contains(":= by\n  rfl"));

    let repro_path = f.repro_path.as_ref().expect("repro.rs written");
    let direct_repro = reproduce_miri_finding(repro_path, Some(&root))
        .expect("reproduce_miri_finding on helper_add_ten candidate");
    assert_eq!(direct_repro.name, f.fn_name);
    assert!(direct_repro.verdict.is_diverge());
    assert!(direct_repro.kernel_confirmed);

    let repro_json = dir.join("repro_helper.json");
    let cli_repro = Command::new(bin)
        .arg("--reproduce")
        .arg(repro_path)
        .arg("--output-json")
        .arg(&repro_json)
        .output()
        .expect("run miri-difftest --reproduce on helper_add_ten candidate");
    assert!(
        cli_repro.status.success(),
        "--reproduce failed:\n{}",
        String::from_utf8_lossy(&cli_repro.stderr)
    );
    let cli_repro_text = fs::read_to_string(&repro_json).expect("read repro_helper.json");
    assert!(cli_repro_text.contains("\"verdict\": \"diverge\""));
    assert!(cli_repro_text.contains("\"kernel_confirmed\": true"));

    // 2. Seeded batch containing `pass_direct_fn_call` mutants must record 0
    // `miri_diff_corpus::helper_add_ten` skips in `unmodeled_external_calls`.
    let mut seeded_with_helper = Vec::new();
    for b_idx in 0..8usize {
        let batch = generate_miri_corpus_batch(10, 0x5EED_9900 + b_idx as u64, b_idx);
        for cand in batch {
            if cand.seed_name == "pass_direct_fn_call" {
                seeded_with_helper.push(cand);
                if seeded_with_helper.len() >= 4 {
                    break;
                }
            }
        }
        if seeded_with_helper.len() >= 4 {
            break;
        }
    }
    assert!(
        !seeded_with_helper.is_empty(),
        "expected generate_miri_corpus_batch to produce pass_direct_fn_call mutants"
    );
    let batch_len = seeded_with_helper.len();
    let seeded_rep = evaluate_miri_batches(
        "seeded",
        0x5EED_9900,
        &[seeded_with_helper],
        batch_len,
        None,
        Some(&root),
    )
    .expect("evaluate seeded pass_direct_fn_call mutants");
    assert_eq!(seeded_rep.compared_candidates, seeded_rep.compiled_candidates);
    assert_eq!(
        seeded_rep
            .unmodeled_external_calls
            .get("miri_diff_corpus::helper_add_ten")
            .copied()
            .unwrap_or(0),
        0,
        "expected 0 helper_add_ten skips in seeded batch: {:?}",
        seeded_rep.unmodeled_external_calls
    );
}

/// Build a seeded candidate named `fn_name` whose `fn_source` may also define
/// intra-crate helpers.
fn handwritten_candidate(
    id: usize,
    seed_name: &str,
    fn_name: &str,
    applied_mutator: &str,
    fn_source: &str,
) -> GeneratedMiriCandidate {
    GeneratedMiriCandidate {
        id,
        seed_index: 0,
        seed_name: seed_name.to_string(),
        fn_name: fn_name.to_string(),
        seed_u64: 0x00F0_0000 + id as u64,
        applied_mutators: vec![applied_mutator.to_string()],
        tracked_locals: Vec::new(),
        fn_source: fn_source.to_string(),
        source: build_standalone_candidate_source(fn_source),
    }
}

#[test]
fn panic_fmt_candidates_compare_agree_and_preserve_non_macro_panic_site_mismatch() {
    let dir = unique_temp_dir("panic_fmt");
    let root = repo_root();

    // `panic!("...")` and `assert!(cond, "...")` both call
    // `core::fmt::Arguments::<'a>::from_str`, while `unreachable!("...")`
    // inlines its nested `format_args!` and calls
    // `core::fmt::Arguments::<'a>::from_str_nonconst`, before handing the
    // result to `core::panicking::panic_fmt` in `library/core/src/panic.rs`.
    let panic_fn = "\
pub fn panic_fmt_macro__b0_c0() {
    let x: u32 = 3u32;
    if x == 3u32 {
        panic!(\"panic! message from a mutated candidate\");
    }
}
";
    let assert_fn = "\
pub fn assert_fmt_macro__b0_c1() -> u32 {
    let x: u32 = 7u32;
    assert!(x == 8u32, \"x must equal eight\");
    x
}
";
    let unreachable_fn = "\
pub fn unreachable_fmt_macro__b0_c2() -> u32 {
    let x: u32 = 5u32;
    if x == 5u32 {
        unreachable!(\"unreachable! message via from_str_nonconst\");
    }
    x
}
";
    // `todo!()` passes its message to `core::panicking::panic` as a constant,
    // and `assert_eq!` panics through `core::panicking::assert_failed`, which
    // formats its message at run time; both expansions come from
    // `library/core/src/macros/mod.rs`. Both `assert_eq!` operands are locals:
    // a literal operand would be compared through a reference to a promoted
    // constant, which Anneal currently reads incorrectly (a separate
    // `panic_vs_return` divergence that this test does not cover).
    let todo_fn = "\
pub fn todo_macro__b0_c4() -> u32 {
    let x: u32 = 2u32;
    if x == 2u32 {
        todo!();
    }
    x
}
";
    let assert_eq_fn = "\
pub fn assert_eq_macro__b0_c5() -> u32 {
    let x: u32 = 4u32;
    let y: u32 = 5u32;
    assert_eq!(x, y);
    x
}
";
    let assert_ne_custom_fn = "\
pub fn assert_ne_custom_macro__b0_c6() -> u32 {
    let x: u32 = 4u32;
    let y: u32 = 4u32;
    assert_ne!(x, y, \"x and y must differ\");
    x
}
";
    // A genuine non-macro panic-site mismatch: the overflowing `+` panics inside
    // a `#[track_caller]` helper. Miri reports the helper's call site in the
    // candidate; Anneal reports the overflow `assert` terminator inside the
    // helper's own body, a user `src/lib.rs` span that reconciliation must not
    // accept.
    let track_caller_fn = "\
#[track_caller]
#[inline(never)]
pub fn track_caller_overflow_helper(x: u8) -> u8 {
    x + 250u8
}

pub fn neg_ctrl_track_caller_overflow__b0_c3() -> u8 {
    let base: u8 = 10u8;
    track_caller_overflow_helper(base)
}
";
    let candidates = vec![
        handwritten_candidate(
            0,
            "panic_explicit_macro",
            "panic_fmt_macro__b0_c0",
            "ArithmeticCastMutator",
            panic_fn,
        ),
        handwritten_candidate(
            1,
            "panic_explicit_macro",
            "assert_fmt_macro__b0_c1",
            "ArithmeticCastMutator",
            assert_fn,
        ),
        handwritten_candidate(
            2,
            "panic_explicit_macro",
            "unreachable_fmt_macro__b0_c2",
            "ArithmeticCastMutator",
            unreachable_fn,
        ),
        handwritten_candidate(
            3,
            "panic_checked_add_overflow",
            "neg_ctrl_track_caller_overflow__b0_c3",
            "ArithmeticCastMutator",
            track_caller_fn,
        ),
        handwritten_candidate(
            4,
            "panic_explicit_macro",
            "todo_macro__b0_c4",
            "ArithmeticCastMutator",
            todo_fn,
        ),
        handwritten_candidate(
            5,
            "panic_explicit_macro",
            "assert_eq_macro__b0_c5",
            "ArithmeticCastMutator",
            assert_eq_fn,
        ),
        handwritten_candidate(
            6,
            "panic_explicit_macro",
            "assert_ne_custom_macro__b0_c6",
            "ArithmeticCastMutator",
            assert_ne_custom_fn,
        ),
    ];

    let findings_dir = dir.join("findings_panic_fmt");
    let report = evaluate_miri_batches(
        "seeded",
        0x00F0_0001,
        &[candidates],
        7,
        Some(&findings_dir),
        Some(&root),
    )
    .expect("evaluate panic_fmt candidate batch");

    assert_eq!(report.total_candidates, 7);
    assert_eq!(report.compiled_candidates, 7);
    assert_eq!(report.compared_candidates, 7);
    assert_eq!(report.agree_count, 6);
    assert_eq!(report.diverge_count, 1);
    assert_eq!(report.not_compared_count, 0);
    assert_eq!(report.kernel_confirmed_divergences, 1);
    assert_eq!(
        report.not_compared_reasons.get("external_call").copied(),
        Some(0),
        "unexpected external_call skips: {:?}",
        report.not_compared_reasons
    );
    assert!(
        report.unmodeled_external_calls.is_empty(),
        "unexpected unmodeled external calls: {:?}",
        report.unmodeled_external_calls
    );
    assert_eq!(report.miri_verdicts.get("panic").copied(), Some(7));
    assert_eq!(report.anneal_outcomes.get("panic").copied(), Some(7));

    // (a) The macro candidates panic at the macro call site under Miri and inside
    // the macro's standard-library definition under Anneal. The strict
    // comparator reports a panic-site mismatch, and the difftest comparator
    // reconciles it. Where Anneal's run recovers the panic message, it matches
    // Miri's.
    let macro_candidates = [
        (
            "panic_fmt_macro__b0_c0",
            "/library/core/src/panic.rs",
            Some("panic! message from a mutated candidate"),
        ),
        (
            "assert_fmt_macro__b0_c1",
            "/library/core/src/panic.rs",
            Some("x must equal eight"),
        ),
        (
            "unreachable_fmt_macro__b0_c2",
            "/library/core/src/panic.rs",
            Some(
                "internal error: entered unreachable code: \
                 unreachable! message via from_str_nonconst",
            ),
        ),
        (
            "todo_macro__b0_c4",
            "/library/core/src/macros/mod.rs",
            Some("not yet implemented"),
        ),
        (
            "assert_eq_macro__b0_c5",
            "/library/core/src/macros/mod.rs",
            Some("assertion `left == right` failed"),
        ),
        (
            "assert_ne_custom_macro__b0_c6",
            "/library/core/src/macros/mod.rs",
            Some("assertion `left != right` failed: x and y must differ"),
        ),
    ];
    assert_eq!(
        report.reconciled_panic_sites.len(),
        macro_candidates.len(),
        "unexpected reconciled sites: {:?}",
        report.reconciled_panic_sites
    );
    for (name, anneal_file_suffix, anneal_message) in macro_candidates {
        let item = report
            .item_reports
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing item report for {name}"));
        let MiriOutcome::Panic {
            pos: Some(miri_pos),
            message: miri_message,
        } = &item.miri
        else {
            panic!(
                "{name}: expected a Miri panic with a position, got {:?}",
                item.miri
            );
        };
        assert_eq!(miri_pos.file, "src/lib.rs", "{name}: {miri_pos:?}");
        let AnnealOutcome::Panic {
            span: Some(anneal_span),
        } = &item.anneal
        else {
            panic!(
                "{name}: expected an Anneal panic with a span, got {:?}",
                item.anneal
            );
        };
        assert!(
            anneal_span.file.ends_with(anneal_file_suffix),
            "{name}: unexpected Anneal panic span {anneal_span:?}"
        );
        assert!(
            matches!(
                compare_miri_and_anneal(&item.miri, &item.anneal),
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
            ),
            "{name}: strict comparison must report the macro panic-site difference"
        );
        assert_eq!(item.verdict, ComparisonVerdict::Agree, "{name}");
        // The reconciled outcome rests on kernel-checked `by rfl` theorems
        // evaluated with the linked `fmtArgumentsCtorStub` callees.
        assert!(item.kernel_confirmed, "{name}");

        let site = report
            .reconciled_panic_sites
            .iter()
            .find(|s| s.fn_name == name)
            .unwrap_or_else(|| panic!("{name} must be listed as a reconciled site"));
        assert_eq!(site.seed_name, "panic_explicit_macro", "{name}");
        assert!(site.kernel_confirmed, "{name}");
        assert_eq!(
            site.anneal_panic_message.as_deref(),
            anneal_message,
            "{name}: unexpected recovered Anneal panic message"
        );
        if let Some(message) = anneal_message {
            assert_eq!(miri_message, message, "{name}");
        }
        for theorem in ["confirm_tag", "confirm_probe"] {
            assert!(
                site.kernel_confirm_theorems
                    .contains(&format!("theorem {theorem}_{name} :")),
                "{name}: missing {theorem}:\n{}",
                site.kernel_confirm_theorems
            );
        }
        // The recovered message is itself kernel-checked, and the snippet
        // carries the message probe that the theorem evaluates.
        assert_eq!(
            site.kernel_confirm_theorems
                .contains(&format!("theorem confirm_message_{name} :")),
            anneal_message.is_some(),
            "{name}:\n{}",
            site.kernel_confirm_theorems
        );
        assert_eq!(
            site.kernel_confirm_theorems
                .contains("def probePanicMessageBounded"),
            anneal_message.is_some(),
            "{name}"
        );
    }
    assert!(
        report
            .reconciled_panic_sites
            .iter()
            .all(|s| s.fn_name != "neg_ctrl_track_caller_overflow__b0_c3")
    );

    // (b) The non-macro mismatch stays a kernel-confirmed divergence.
    let neg = report
        .item_reports
        .iter()
        .find(|r| r.name == "neg_ctrl_track_caller_overflow__b0_c3")
        .expect("missing item report for the track_caller candidate");
    assert!(
        matches!(
            neg.verdict,
            ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
        ),
        "unexpected verdict: {:?}",
        neg.verdict
    );
    assert!(neg.kernel_confirmed);
    let AnnealOutcome::Panic {
        span: Some(neg_span),
    } = &neg.anneal
    else {
        panic!("expected an Anneal panic with a span, got {:?}", neg.anneal);
    };
    assert_eq!(neg_span.file, "src/lib.rs", "unexpected span {neg_span:?}");
    assert_eq!(
        report
            .divergence_classes
            .get("panic_site_mismatch")
            .copied(),
        Some(1)
    );

    assert_eq!(report.findings.len(), 1);
    let f = &report.findings[0];
    assert_eq!(f.fn_name, "neg_ctrl_track_caller_overflow__b0_c3");
    assert_eq!(f.divergence_class, "panic_site_mismatch");
    assert!(f.kernel_confirmed);
    assert!(
        f.kernel_confirm_theorems
            .contains("theorem confirm_tag_neg_ctrl_track_caller_overflow__b0_c3 :")
    );
    assert!(
        f.kernel_confirm_theorems
            .contains("theorem confirm_probe_neg_ctrl_track_caller_overflow__b0_c3 :")
    );
    assert!(f.kernel_confirm_theorems.contains(":= by\n  rfl"));
    // The snippet is self-contained: `linkedCallees` names the synthetic
    // `core::fmt::Arguments` stub, and `confirm_probe_*` evaluates
    // `probeMirDiffExecBounded`, so their definitions are included. The overflow
    // panic carries no recoverable message, so no message theorem is emitted.
    assert!(
        f.kernel_confirm_theorems
            .contains("def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=")
    );
    assert!(
        f.kernel_confirm_theorems
            .contains("def activeSpan (body : CapturedMir) (st : MirExecState) : String :=")
    );
    assert!(
        f.kernel_confirm_theorems
            .contains("def probeMirDiffExecBounded\n")
    );
    assert!(
        !f.kernel_confirm_theorems
            .contains("theorem confirm_message_neg_ctrl_track_caller_overflow__b0_c3 :")
    );
    assert!(
        f.kernel_confirm_theorems
            .contains("def linkedCallees : List CapturedMir :=")
    );
    assert!(
        f.kernel_confirm_theorems
            .contains("Mir.MiriDiffCorpus.track_caller_overflow_helper.body")
    );
    let repro_path = f.repro_path.as_ref().expect("repro.rs written");
    let bundle_dir = repro_path.parent().expect("bundle dir");
    let summary_md = fs::read_to_string(bundle_dir.join("SUMMARY.md")).expect("read SUMMARY.md");
    assert!(summary_md.contains("def fmtArgumentsCtorStub (defPath : String) : CapturedMir :="));
}

/// Real `lake` binary used behind the logging wrappers below (the pinned
/// toolchain first, then the `elan` proxy).
fn real_lake_binary() -> Option<PathBuf> {
    let home = PathBuf::from(std::env::var_os("HOME")?);
    [
        ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lake",
        ".elan/bin/lake",
    ]
    .into_iter()
    .map(|rel| home.join(rel))
    .find(|p| p.is_file())
}

/// Write an executable `lake` wrapper at `path` that records its subcommand
/// (`build`, `env`, ...) in `log` and then `exec`s `real_lake`.
#[cfg(unix)]
fn write_logging_lake_wrapper(path: &Path, log: &Path, real_lake: &Path) {
    use std::os::unix::fs::PermissionsExt;
    fs::create_dir_all(path.parent().expect("wrapper parent")).expect("create wrapper dir");
    let script = format!(
        "#!/usr/bin/env bash\nprintf '%s\\n' \"${{1:-}}\" >> '{}'\nexec '{}' \"$@\"\n",
        log.display(),
        real_lake.display()
    );
    fs::write(path, script).expect("write lake wrapper");
    let mut perms = fs::metadata(path).expect("wrapper metadata").permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).expect("chmod lake wrapper");
}

fn logged_lake_subcommands(log: &Path) -> BTreeSet<String> {
    fs::read_to_string(log)
        .unwrap_or_default()
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect()
}

/// The `.olean` files that `lake build` produces for `Mir` and `SymbolicEval`
/// are only loadable by the same Lean toolchain, so the helper-linked oracle
/// must run `lake build` and `lake env lean` (probe and confirm modules) with one
/// and the same `lake` binary, whatever the environment selects.
#[cfg(unix)]
#[test]
fn linked_oracle_runs_lake_build_and_lake_env_lean_with_the_same_lake_binary() {
    use std::os::unix::fs::symlink;

    let Some(real_lake) = real_lake_binary() else {
        eprintln!("skipping: no lake toolchain found under $HOME/.elan");
        return;
    };
    let dir = unique_temp_dir("lake_binary");
    let bin = env!("CARGO_BIN_EXE_miri-difftest");
    let cand_fn = "pub fn lake_binary_probe__b0_c0() -> u32 {\n    helper_add_ten() + 1u32\n}\n";
    let repro = dir.join("repro.rs");
    fs::write(&repro, build_standalone_candidate_source(cand_fn)).expect("write repro.rs");

    // Scenario 1: an installed omnibus toolchain (`ANNEAL_TOOLCHAIN_DIR`), whose
    // `lean/bin/lake` is what `run_lake_verify_targets` uses when `LAKE` is unset.
    let toolchain = dir.join("omnibus");
    let omnibus_log = dir.join("omnibus_lake.log");
    write_logging_lake_wrapper(&toolchain.join("lean/bin/lake"), &omnibus_log, &real_lake);
    let real_lean = real_lake.with_file_name("lean");
    if real_lean.is_file() {
        symlink(&real_lean, toolchain.join("lean/bin/lean")).expect("symlink lean");
    } else {
        fs::write(toolchain.join("lean/bin/lean"), "").expect("write lean stub");
    }
    fs::create_dir_all(toolchain.join("bin")).expect("create omnibus bin");
    let capture = resolve_rustc_wrapper(&CaptureDriverConfig::new(dir.to_path_buf()));
    if capture.is_file() {
        symlink(&capture, toolchain.join("bin/anneal-rustc-capture")).expect("symlink capture");
    } else {
        fs::write(toolchain.join("bin/anneal-rustc-capture"), "").expect("write capture stub");
    }
    fs::create_dir_all(toolchain.join("rust/bin")).expect("create omnibus rust/bin");
    fs::write(toolchain.join("rust/bin/rustc"), "").expect("write rustc stub");
    fs::create_dir_all(toolchain.join("share/anneal/trusted/lean")).expect("create share dir");
    fs::write(
        toolchain.join("share/anneal/trusted/lean/foundation-lock.json"),
        "{}\n",
    )
    .expect("write foundation lock stub");

    let out1 = Command::new(bin)
        .arg("--reproduce")
        .arg(&repro)
        .arg("--output-json")
        .arg(dir.join("omnibus.json"))
        .env("ANNEAL_TOOLCHAIN_DIR", &toolchain)
        .env_remove("LAKE")
        .env_remove("ANNEAL_LAKE")
        .output()
        .expect("run miri-difftest --reproduce with an omnibus toolchain");
    let used1 = logged_lake_subcommands(&omnibus_log);
    assert_eq!(
        used1.contains("build"),
        used1.contains("env"),
        "`lake build` and `lake env lean` used different lake binaries with \
         ANNEAL_TOOLCHAIN_DIR set (omnibus lake ran only {used1:?})\nstderr:\n{}",
        String::from_utf8_lossy(&out1.stderr)
    );
    assert!(
        out1.status.success(),
        "--reproduce failed with an omnibus toolchain:\n{}",
        String::from_utf8_lossy(&out1.stderr)
    );

    // Scenario 2: `ANNEAL_LAKE` set while `LAKE` is unset.
    let anneal_lake_log = dir.join("anneal_lake.log");
    let anneal_lake = dir.join("anneal_lake/lake");
    write_logging_lake_wrapper(&anneal_lake, &anneal_lake_log, &real_lake);
    let out2 = Command::new(bin)
        .arg("--reproduce")
        .arg(&repro)
        .arg("--output-json")
        .arg(dir.join("anneal_lake.json"))
        .env("ANNEAL_LAKE", &anneal_lake)
        .env_remove("LAKE")
        .env_remove("ANNEAL_TOOLCHAIN_DIR")
        .output()
        .expect("run miri-difftest --reproduce with ANNEAL_LAKE");
    let used2 = logged_lake_subcommands(&anneal_lake_log);
    assert_eq!(
        used2.contains("build"),
        used2.contains("env"),
        "`lake build` and `lake env lean` used different lake binaries with \
         ANNEAL_LAKE set (ANNEAL_LAKE ran only {used2:?})\nstderr:\n{}",
        String::from_utf8_lossy(&out2.stderr)
    );
    assert!(
        out2.status.success(),
        "--reproduce failed with ANNEAL_LAKE:\n{}",
        String::from_utf8_lossy(&out2.stderr)
    );
}
