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

use anneal_difftest::miri_eval::evaluate_miri_batches;
use anneal_difftest::mutators_miri::{
    GeneratedMiriCandidate, build_standalone_candidate_source, generate_miri_corpus_batch,
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
    assert!(stdout.contains("### Unmodeled External Calls"));
    assert!(stdout.contains("| `core::intrinsics::exact_div` | 2 |"));
    assert!(stdout.contains("| `miri_diff_corpus::helper_add_ten` | 1 |"));

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
assert data["compared_candidates"] == 73
assert data["agree_count"] == 65
assert data["diverge_count"] == 8
assert data["kernel_confirmed_divergences"] == 8
assert data["not_compared_count"] == 4

div_classes = data["divergence_classes"]
assert div_classes == {
    "false_positive_ub": 2,
    "missed_ub": 5,
    "panic_site_mismatch": 0,
    "panic_vs_return": 0,
    "return_vs_panic": 0,
    "ub_location_mismatch": 0,
    "wrong_value": 1,
}, f"unexpected divergence_classes: {div_classes}"

nc = data["not_compared_reasons"]
assert nc == {
    "capture_failed": 0,
    "compile_failed": 0,
    "external_call": 4,
    "miri_oracle_error": 0,
    "out_of_fuel": 0,
    "unsupported": 0,
}, f"unexpected not_compared_reasons: {nc}"

ext = data["unmodeled_external_calls"]
assert ext.get("core::intrinsics::exact_div") == 2, f"unexpected ext: {ext}"
assert ext.get("miri_diff_corpus::helper_add_ten") == 1, f"unexpected ext: {ext}"
assert sum(ext.values()) == 4, f"unexpected ext sum: {ext}"

expected_findings = {
    "ub_transmute_invalid_bool_through_ptr": "missed_ub",
    "pass_copy_nonoverlapping_uninit_bytes_to_uninit": "false_positive_ub",
    "pass_ptr_offset_within_array": "wrong_value",
    "ub_ptr_offset_oob_read": "missed_ub",
    "ub_ptr_offset_oob_write": "missed_ub",
    "ub_ptr_offset_negative_before_start": "missed_ub",
    "ub_unaligned_ptr_read_u32": "missed_ub",
    "pass_tb_unsafe_cell_shared_mutation": "false_positive_ub",
}

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
assert len(manifest_ext) == 4, f"expected 4 externalCall entries in manifest, got {manifest_ext}"

findings = data["findings"]
assert len(findings) == 8
actual_map = {f["fn_name"]: f["divergence_class"] for f in findings}
assert actual_map == expected_findings, f"mismatch: {actual_map} vs {expected_findings}"

for f in findings:
    assert f["kernel_confirmed"] is True
    assert "theorem confirm_tag_" in f["kernel_confirm_theorems"]
    assert "theorem confirm_probe_" in f["kernel_confirm_theorems"]
    assert ":= by\n  rfl" in f["kernel_confirm_theorems"]
    assert "def body : CapturedMir :=" in f["mir_neighborhood"]
    assert f["miri_excerpt"]
    assert f["anneal_lean_tag"].lstrip("(").startswith("MirDiffTag.")
    bundle_dir = findings_dir / f["finding_id"]
    repro_rs = bundle_dir / "repro.rs"
    finding_json = bundle_dir / "finding.json"
    summary_md = bundle_dir / "SUMMARY.md"
    assert repro_rs.is_file(), f"missing {repro_rs}"
    assert finding_json.is_file(), f"missing {finding_json}"
    assert summary_md.is_file(), f"missing {summary_md}"
    assert repro_rs.read_text() == f["mutant_source"]
    md_text = summary_md.read_text()
    assert '## Miri Output Excerpt' in md_text
    assert '## Lean 4 Kernel Confirmation Theorems' in md_text
    assert '## Captured MIR Neighborhood' in md_text
    assert '## Mutant Source' in md_text
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
    // that metrics differ across seeds, and collect all repro.rs paths to re-run.
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
    mv = d["miri_verdicts"]
    assert mv["pass"] > 0, f"{label} missing Miri pass verdicts: {mv}"
    assert mv["panic"] > 0, f"{label} missing Miri panic verdicts: {mv}"
    assert mv["ub"] > 0, f"{label} missing Miri ub verdicts: {mv}"
    assert mv["error"] == 0, f"{label} unexpected Miri oracle error: {mv}"
    assert d["diverge_count"] == d["kernel_confirmed_divergences"], label
    assert d["diverge_count"] == len(d["findings"]), label

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

all_findings = d1["findings"] + d2["findings"]
assert len(all_findings) > 0, "expected at least one divergence finding across seeded runs"
for f in all_findings:
    print(
        f["repro_path"],
        f["fn_name"],
        f["divergence_class"],
        f["miri_outcome"],
        f["anneal_outcome"],
        f["anneal_lean_tag"],
        sep="\t",
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

    let lines: Vec<String> = String::from_utf8_lossy(&check_out.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    assert!(!lines.is_empty(), "must have findings to reproduce");

    for (idx, line) in lines.iter().enumerate() {
        let parts: Vec<&str> = line.split('\t').collect();
        assert_eq!(parts.len(), 6, "unexpected finding line: {line}");
        let (repro_path, fn_name, exp_class, exp_miri, exp_anneal, exp_lean) = (
            parts[0], parts[1], parts[2], parts[3], parts[4], parts[5],
        );
        let repro_json = dir.join(format!("repro_{idx}.json"));
        let repro_out = Command::new(bin)
            .arg("--reproduce")
            .arg(repro_path)
            .arg("--output-json")
            .arg(&repro_json)
            .output()
            .expect("run miri-difftest --reproduce");
        assert!(
            repro_out.status.success(),
            "--reproduce failed for {repro_path}:\n{}",
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
            .args([fn_name, exp_class, exp_miri, exp_anneal, exp_lean])
            .output()
            .expect("verify reproducer JSON");
        assert!(
            verify_repro.status.success(),
            "reproducer mismatch for {repro_path}:\n{}",
            String::from_utf8_lossy(&verify_repro.stderr)
        );
    }
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
