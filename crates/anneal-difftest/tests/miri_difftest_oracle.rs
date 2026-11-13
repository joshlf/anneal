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

use anneal_difftest::miri_eval::{
    MiriEvalOptions, divergence_class_slug, evaluate_miri_batches,
    evaluate_miri_batches_with_options, reproduce_miri_finding,
};
use anneal_difftest::mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, DetRng, GeneratedMiriCandidate,
    MiriAstMutator, MutationMode, PlaceProjectionWrapper, TreeBorrowsRetagInterleaver,
    build_standalone_candidate_source, generate_miri_batch, generate_miri_corpus_batch,
    reconstruct_miri_mutation_steps, replay_miri_mutation_steps,
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

/// Every way to pick `chain` as an ordered subsequence of `names`, as increasing
/// index lists into `names`. A finding records only mutator names, which do not
/// say which pass was kept when a mutator ran more than once.
fn ordered_name_embeddings(names: &[&str], chain: &[String]) -> Vec<Vec<usize>> {
    fn extend(
        names: &[&str],
        chain: &[String],
        from: usize,
        picked: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        let Some(want) = chain.get(picked.len()) else {
            out.push(picked.clone());
            return;
        };
        for (i, name) in names.iter().enumerate().skip(from) {
            if *name == want.as_str() {
                picked.push(i);
                extend(names, chain, i + 1, picked, out);
                picked.pop();
            }
        }
    }
    let mut out = Vec::new();
    extend(names, chain, 0, &mut Vec::new(), &mut out);
    out
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
assert data["total_candidates"] == 106
assert data["compiled_candidates"] == 106
assert data["compile_failed_candidates"] == 0
assert data["compared_candidates"] == 106
assert data["agree_count"] == 106
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
# `panic_explicit_macro` no longer carries an `externalCall` bug: its `Verify`
# module proves a modular safe-panic certificate instead. The oracle below still
# reconciles its panic site through the `fmtArgumentsCtorStub` link.
assert len(manifest_ext) == 0, f"expected 0 externalCall entries in manifest, got {manifest_ext}"
assert manifest_ext == set(), f"unexpected externalCall entries: {manifest_ext}"

findings = data["findings"]
assert len(findings) == 0
actual_map = {f["fn_name"]: f["divergence_class"] for f in findings}
assert actual_map == expected_findings, f"mismatch: {actual_map} vs {expected_findings}"

# `item_outcomes` gives every manifest entry its live per-item outcome (the
# `known_anneal_bug` ratchet audits manifest entries against it), and every
# identity item agrees.
outcomes = data["item_outcomes"]
manifest_names = {t["name"] for t in manifest["tests"]}
assert set(outcomes) == manifest_names, sorted(set(outcomes) ^ manifest_names)
assert len(outcomes) == data["compiled_candidates"], len(outcomes)
for name, outcome in outcomes.items():
    assert set(outcome) == {"verdict", "miri_outcome", "anneal_outcome", "anneal_lean_tag"}, (
        name,
        outcome,
    )
    assert outcome["verdict"] == "agree", (name, outcome)
    assert outcome["anneal_lean_tag"].startswith(("MirDiffTag.", "(MirDiffTag.")), (name, outcome)
macro_outcome = outcomes["panic_explicit_macro"]
assert macro_outcome["miri_outcome"].startswith("panic@"), macro_outcome
assert macro_outcome["anneal_outcome"].startswith("panic@"), macro_outcome
assert macro_outcome["anneal_lean_tag"] == "MirDiffTag.panic", macro_outcome

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
        "anneal_panic_frame": "miri_diff_corpus::panic_explicit_macro",
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
    # Every compiled candidate has a per-item outcome consistent with the
    # aggregate counts and the findings.
    outcomes = d["item_outcomes"]
    assert len(outcomes) == d["compiled_candidates"], (label, len(outcomes))
    verdicts = [o["verdict"] for o in outcomes.values()]
    assert verdicts.count("agree") == d["agree_count"], (label, verdicts)
    assert verdicts.count("diverge") == d["diverge_count"], (label, verdicts)
    assert (
        verdicts.count("not_compared")
        == d["not_compared_count"] - d["compile_failed_candidates"]
    ), (label, verdicts)
    assert {f["fn_name"] for f in d["findings"]} == {
        name for name, o in outcomes.items() if o["verdict"] == "diverge"
    }, label

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
    // The hand-built candidate claims a mutator that no corpus replay reproduces,
    // so shrinking is skipped without any compile check or oracle run.
    assert_eq!(f.shrink_status, "skipped_replay_mismatch");
    assert_eq!(f.original_mutator_chain, vec!["BitValidityTransmuteMutator".to_string()]);
    assert_eq!(f.minimized_mutator_chain, f.original_mutator_chain);
    assert_eq!(f.applied_mutators, f.original_mutator_chain);
    assert_eq!((f.shrink_evaluations, f.executed_oracle_runs), (0, 0));
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
    assert!(summary_md.contains("- **Shrink status**: `skipped_replay_mismatch`"));
    let finding_json =
        fs::read_to_string(bundle_dir.join("finding.json")).expect("read finding.json");
    assert!(finding_json.contains("\"shrink_status\": \"skipped_replay_mismatch\""));
    assert!(finding_json.contains("\"executed_oracle_runs\": 0"));

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

    let broken_fn =
        "pub fn broken_cand__b0_c2() -> u32 {\n    let x: u32 = \"not_an_int\";\n    x\n}\n";
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
    for b_idx in 0..24usize {
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
    assert_eq!(
        seeded_rep.compared_candidates,
        seeded_rep.compiled_candidates
    );
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
    // A panic that unwinds through a cleanup block (here, to drop a local whose
    // type implements `Drop`) ends at a `resume` terminator whose span covers
    // the whole function. Anneal must still attribute the panic to the step
    // that started unwinding, both for the reconciled `panic!` and for the
    // non-macro `#[track_caller]` mismatch, which would otherwise agree
    // because the whole-function span contains Miri's position.
    let cleanup_panic_fn = "\
pub struct CleanupGuardC7(pub u32);

impl Drop for CleanupGuardC7 {
    fn drop(&mut self) {
        self.0 = 0u32;
    }
}

pub fn panic_cleanup_macro__b0_c7() -> u32 {
    let guard = CleanupGuardC7(7u32);
    if guard.0 == 7u32 {
        panic!(\"panic! message unwinding through a cleanup block\");
    }
    guard.0
}
";
    let cleanup_track_caller_fn = "\
pub struct CleanupGuardC8(pub u32);

impl Drop for CleanupGuardC8 {
    fn drop(&mut self) {
        self.0 = 0u32;
    }
}

#[track_caller]
#[inline(never)]
pub fn track_caller_overflow_helper_c8(x: u8) -> u8 {
    x + 250u8
}

pub fn neg_ctrl_cleanup_track_caller__b0_c8() -> u8 {
    let guard = CleanupGuardC8(3u32);
    let base: u8 = 10u8;
    let sum = track_caller_overflow_helper_c8(base);
    if guard.0 == 3u32 { sum } else { 0u8 }
}
";
    // Invocations written through a crate path, rooted, split across lines, or
    // with a comment before `!` still reconcile: Miri reports each
    // invocation's first token, which `StagedLibSource` indexes.
    let qualified_panic_fn = "\
pub fn core_qualified_macro__b0_c9() -> u32 {
    let x: u32 = 6u32;
    if x == 6u32 {
        core::panic!(\"core-qualified panic! message\");
    }
    x
}
";
    let rooted_assert_fn = "\
pub fn rooted_assert_macro__b0_c10() -> u32 {
    let x: u32 = 1u32;
    ::core::assert!(x == 2u32, \"rooted assert! message\");
    x
}
";
    let multiline_panic_fn = "\
pub fn multiline_core_macro__b0_c11() -> u32 {
    let x: u32 = 9u32;
    if x == 9u32 {
        core::
            panic!(\"multi-line core-qualified panic! message\");
    }
    x
}
";
    let commented_assert_fn = "\
pub fn commented_assert_macro__b0_c12() -> u32 {
    let x: u32 = 3u32;
    assert /* why */ !(x == 4u32, \"commented assert! message\");
    x
}
";
    // A panic that Anneal raises in a different function than Miri must not
    // reconcile, even with an identical message. Anneal currently reads `*y`
    // through the promoted `&5u32` as `x` (its stack borrows and the promoted
    // allocation share `allocId`s), so it calls the helper, while Miri panics
    // at the candidate's own `panic!`. Both spans lie in
    // `library/core/src/panic.rs`, and both messages match.
    let masked_frame_fn = "\
#[inline(never)]
pub fn helper_panics_same_message_c13() -> u32 {
    panic!(\"identical panic message\");
}

pub fn masked_promoted_divergence__b0_c13() -> u32 {
    let x: u32 = 4u32;
    let r1: &u32 = &x;
    let r2: &u32 = &x;
    let y: &u32 = &5u32;
    if *y == *r1 {
        helper_panics_same_message_c13()
    } else if *r2 == 0u32 {
        0u32
    } else {
        panic!(\"identical panic message\");
    }
}
";
    // A panic inside a nested `fn` reconciles when both Miri and Anneal panic
    // inside that nested `fn`, and stays a kernel-confirmed divergence when
    // Anneal panics inside the nested `fn` while Miri panics in the outer
    // candidate body (even with an identical message and a `DefPath` whose
    // second segment is the candidate's name).
    let nested_fn_agree = "\
pub fn nested_fn_macro__b0_c14() -> u32 {
    #[inline(never)]
    fn inner_panic() -> u32 {
        panic!(\"nested fn panic! message\");
    }
    inner_panic()
}
";
    let masked_nested_fn = "\
pub fn masked_nested_fn_divergence__b0_c15() -> u32 {
    #[inline(never)]
    fn inner_panics_same_message_c15() -> u32 {
        panic!(\"identical nested panic message\");
    }
    let x: u32 = 4u32;
    let r1: &u32 = &x;
    let r2: &u32 = &x;
    let y: &u32 = &5u32;
    if *y == *r1 {
        inner_panics_same_message_c15()
    } else if *r2 == 0u32 {
        0u32
    } else {
        panic!(\"identical nested panic message\");
    }
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
        handwritten_candidate(
            7,
            "panic_explicit_macro",
            "panic_cleanup_macro__b0_c7",
            "ArithmeticCastMutator",
            cleanup_panic_fn,
        ),
        handwritten_candidate(
            8,
            "panic_checked_add_overflow",
            "neg_ctrl_cleanup_track_caller__b0_c8",
            "ArithmeticCastMutator",
            cleanup_track_caller_fn,
        ),
        handwritten_candidate(
            9,
            "panic_explicit_macro",
            "core_qualified_macro__b0_c9",
            "ArithmeticCastMutator",
            qualified_panic_fn,
        ),
        handwritten_candidate(
            10,
            "panic_explicit_macro",
            "rooted_assert_macro__b0_c10",
            "ArithmeticCastMutator",
            rooted_assert_fn,
        ),
        handwritten_candidate(
            11,
            "panic_explicit_macro",
            "multiline_core_macro__b0_c11",
            "ArithmeticCastMutator",
            multiline_panic_fn,
        ),
        handwritten_candidate(
            12,
            "panic_explicit_macro",
            "commented_assert_macro__b0_c12",
            "ArithmeticCastMutator",
            commented_assert_fn,
        ),
        handwritten_candidate(
            13,
            "panic_explicit_macro",
            "masked_promoted_divergence__b0_c13",
            "ArithmeticCastMutator",
            masked_frame_fn,
        ),
        handwritten_candidate(
            14,
            "panic_explicit_macro",
            "nested_fn_macro__b0_c14",
            "ArithmeticCastMutator",
            nested_fn_agree,
        ),
        handwritten_candidate(
            15,
            "panic_explicit_macro",
            "masked_nested_fn_divergence__b0_c15",
            "ArithmeticCastMutator",
            masked_nested_fn,
        ),
    ];

    let findings_dir = dir.join("findings_panic_fmt");
    let report = evaluate_miri_batches(
        "seeded",
        0x00F0_0001,
        &[candidates],
        16,
        Some(&findings_dir),
        Some(&root),
    )
    .expect("evaluate panic_fmt candidate batch");

    assert_eq!(report.total_candidates, 16);
    assert_eq!(report.compiled_candidates, 16);
    assert_eq!(report.compared_candidates, 16);
    assert_eq!(report.agree_count, 12);
    assert_eq!(report.diverge_count, 4);
    assert_eq!(report.not_compared_count, 0);
    assert_eq!(report.kernel_confirmed_divergences, 4);
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
    assert_eq!(report.miri_verdicts.get("panic").copied(), Some(16));
    assert_eq!(report.anneal_outcomes.get("panic").copied(), Some(16));

    // (a) The macro candidates panic at the macro call site under Miri and inside
    // the macro's standard-library definition under Anneal. The strict
    // comparator reports a panic-site mismatch, and the difftest comparator
    // reconciles it. Where Anneal's run recovers the panic message, it matches
    // Miri's.
    let macro_candidates = [
        (
            "panic_fmt_macro__b0_c0",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::panic_fmt_macro__b0_c0",
            Some("panic! message from a mutated candidate"),
        ),
        (
            "assert_fmt_macro__b0_c1",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::assert_fmt_macro__b0_c1",
            Some("x must equal eight"),
        ),
        (
            "unreachable_fmt_macro__b0_c2",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::unreachable_fmt_macro__b0_c2",
            Some(
                "internal error: entered unreachable code: \
                 unreachable! message via from_str_nonconst",
            ),
        ),
        (
            "todo_macro__b0_c4",
            "/library/core/src/macros/mod.rs",
            "miri_diff_corpus::todo_macro__b0_c4",
            Some("not yet implemented"),
        ),
        (
            "assert_eq_macro__b0_c5",
            "/library/core/src/macros/mod.rs",
            "miri_diff_corpus::assert_eq_macro__b0_c5",
            Some("assertion `left == right` failed"),
        ),
        (
            "assert_ne_custom_macro__b0_c6",
            "/library/core/src/macros/mod.rs",
            "miri_diff_corpus::assert_ne_custom_macro__b0_c6",
            Some("assertion `left != right` failed: x and y must differ"),
        ),
        (
            "panic_cleanup_macro__b0_c7",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::panic_cleanup_macro__b0_c7",
            Some("panic! message unwinding through a cleanup block"),
        ),
        (
            "core_qualified_macro__b0_c9",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::core_qualified_macro__b0_c9",
            Some("core-qualified panic! message"),
        ),
        (
            "rooted_assert_macro__b0_c10",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::rooted_assert_macro__b0_c10",
            Some("rooted assert! message"),
        ),
        (
            "multiline_core_macro__b0_c11",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::multiline_core_macro__b0_c11",
            Some("multi-line core-qualified panic! message"),
        ),
        (
            "commented_assert_macro__b0_c12",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::commented_assert_macro__b0_c12",
            Some("commented assert! message"),
        ),
        (
            "nested_fn_macro__b0_c14",
            "/library/core/src/panic.rs",
            "miri_diff_corpus::nested_fn_macro__b0_c14::inner_panic",
            Some("nested fn panic! message"),
        ),
    ];
    assert_eq!(
        report.reconciled_panic_sites.len(),
        macro_candidates.len(),
        "unexpected reconciled sites: {:?}",
        report.reconciled_panic_sites
    );
    for (name, anneal_file_suffix, expected_frame, anneal_message) in macro_candidates {
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
        // Anneal's panic began in the exact enclosing callable frame, and that
        // frame and the recovered message are themselves kernel-checked; the
        // snippet carries the panic-origin probe that those theorems evaluate.
        assert_eq!(
            site.anneal_panic_frame.as_deref(),
            Some(expected_frame),
            "{name}"
        );
        assert!(
            site.kernel_confirm_theorems
                .contains(&format!("theorem confirm_frame_{name} :")),
            "{name}:\n{}",
            site.kernel_confirm_theorems
        );
        assert!(
            site.kernel_confirm_theorems
                .contains(&format!("some \"{expected_frame}\" := by")),
            "{name}"
        );
        assert_eq!(
            site.kernel_confirm_theorems
                .contains(&format!("theorem confirm_message_{name} :")),
            anneal_message.is_some(),
            "{name}:\n{}",
            site.kernel_confirm_theorems
        );
        assert!(
            site.kernel_confirm_theorems
                .contains("def probePanicOriginBoundedFrom\n"),
            "{name}"
        );
    }
    let negative_controls = [
        "neg_ctrl_track_caller_overflow__b0_c3",
        "neg_ctrl_cleanup_track_caller__b0_c8",
    ];
    let masked_cases = [
        (
            "masked_promoted_divergence__b0_c13",
            "miri_diff_corpus::helper_panics_same_message_c13",
            "identical panic message",
        ),
        (
            "masked_nested_fn_divergence__b0_c15",
            "miri_diff_corpus::masked_nested_fn_divergence__b0_c15::inner_panics_same_message_c15",
            "identical nested panic message",
        ),
    ];
    assert!(report.reconciled_panic_sites.iter().all(|s| {
        !negative_controls.contains(&s.fn_name.as_str())
            && !masked_cases.iter().any(|(m, _, _)| *m == s.fn_name)
    }));

    // (b) The non-macro mismatches stay kernel-confirmed divergences, whether
    // or not the panic unwinds through a cleanup block. Anneal attributes each
    // to the overflowing `x + 250u8` in the helper, a single-line span that
    // does not contain Miri's call-site position.
    for name in negative_controls {
        let neg = report
            .item_reports
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing item report for {name}"));
        assert!(
            matches!(
                neg.verdict,
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
            ),
            "{name}: unexpected verdict: {:?}",
            neg.verdict
        );
        assert!(neg.kernel_confirmed, "{name}");
        let AnnealOutcome::Panic {
            span: Some(neg_span),
        } = &neg.anneal
        else {
            panic!(
                "{name}: expected an Anneal panic with a span, got {:?}",
                neg.anneal
            );
        };
        assert_eq!(
            neg_span.file, "src/lib.rs",
            "{name}: unexpected span {neg_span:?}"
        );
        assert_eq!(
            neg_span.start_line, neg_span.end_line,
            "{name}: Anneal must report the overflow, not a whole-function span: {neg_span:?}"
        );
        let finding = report
            .findings
            .iter()
            .find(|f| f.fn_name == name)
            .unwrap_or_else(|| panic!("{name}: missing finding bundle"));
        assert_eq!(finding.divergence_class, "panic_site_mismatch", "{name}");
        assert!(finding.kernel_confirmed, "{name}");
    }
    // (c) A panic that Anneal raises in another callable body (whether a
    // sibling top-level helper or a nested `fn` inside the candidate) stays a
    // kernel-confirmed divergence even though its span lies in
    // `library/core/src/panic.rs` and its message matches Miri's: the
    // kernel-checked frame names the helper/nested `fn`, not the outer body.
    for (masked, helper_frame, expected_msg) in masked_cases {
        let masked_item = report
            .item_reports
            .iter()
            .find(|r| r.name == masked)
            .unwrap_or_else(|| panic!("missing item report for {masked}"));
        assert!(
            matches!(
                masked_item.verdict,
                ComparisonVerdict::Diverge(DivergenceKind::PanicSiteMismatch { .. })
            ),
            "{masked}: unexpected verdict {:?}; if Anneal now reads promoted \
             constants correctly, the candidate agrees and needs another divergence",
            masked_item.verdict
        );
        assert!(masked_item.kernel_confirmed, "{masked}");
        let MiriOutcome::Panic {
            message: masked_miri_message,
            ..
        } = &masked_item.miri
        else {
            panic!(
                "{masked}: expected a Miri panic, got {:?}",
                masked_item.miri
            );
        };
        assert_eq!(masked_miri_message, expected_msg, "{masked}");
        let AnnealOutcome::Panic {
            span: Some(masked_span),
        } = &masked_item.anneal
        else {
            panic!(
                "{masked}: expected an Anneal panic, got {:?}",
                masked_item.anneal
            );
        };
        assert!(
            masked_span.file.ends_with("/library/core/src/panic.rs"),
            "{masked}: {masked_span:?}"
        );
        let masked_finding = report
            .findings
            .iter()
            .find(|f| f.fn_name == masked)
            .unwrap_or_else(|| panic!("finding for {masked}"));
        assert!(masked_finding.kernel_confirmed, "{masked}");
        assert!(
            masked_finding
                .kernel_confirm_theorems
                .contains(&format!("some \"{helper_frame}\" := by")),
            "{}",
            masked_finding.kernel_confirm_theorems
        );
        assert!(
            masked_finding
                .kernel_confirm_theorems
                .contains(&format!("-- Anneal's panic message: {expected_msg:?}")),
            "{}",
            masked_finding.kernel_confirm_theorems
        );
    }

    assert_eq!(
        report
            .divergence_classes
            .get("panic_site_mismatch")
            .copied(),
        Some(4)
    );

    assert_eq!(report.findings.len(), 4);
    let f = report
        .findings
        .iter()
        .find(|f| f.fn_name == "neg_ctrl_track_caller_overflow__b0_c3")
        .expect("finding for the track_caller candidate");
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
    assert!(f.kernel_confirm_theorems.contains("def unwindOrigin\n"));
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

/// Run `mutator` in `mode` over a closed `u32` seed named after `id`, under
/// the first `DetRng` seed in `0..512` whose output contains `marker`, then
/// run each mutator in `follow_ups` in `Pass` mode, so that their in-place
/// perturbers act on the injected template.
fn template_candidate(
    id: usize,
    mutator: &dyn MiriAstMutator,
    mode: MutationMode,
    marker: &str,
    follow_ups: &[&dyn MiriAstMutator],
) -> GeneratedMiriCandidate {
    let fn_name = format!("ep2_template__b0_c{id}");
    let seed = format!("pub fn {fn_name}() -> u32 {{\n    let base: u32 = 6u32;\n    base\n}}\n");
    for s in 0..512u64 {
        let mut file = syn::parse_file(&seed).expect("parse template seed");
        let mut rng = DetRng::new(0xE2_0000 ^ s);
        let mut locals = Vec::new();
        mutator.mutate_with_mode(&mut file, &mut rng, mode, &mut locals);
        if !prettyplease::unparse(&file).contains(marker) {
            continue;
        }
        let mut applied = vec![mutator.name().to_string()];
        for follow_up in follow_ups {
            follow_up.mutate_with_mode(&mut file, &mut rng, MutationMode::Pass, &mut locals);
            applied.push(follow_up.name().to_string());
        }
        let fn_source = prettyplease::unparse(&file);
        let mut cand = handwritten_candidate(id, "ep2_template", &fn_name, "", &fn_source);
        cand.applied_mutators = applied;
        return cand;
    }
    panic!(
        "{} never emitted `{marker}` in {mode:?} mode",
        mutator.name()
    );
}

#[test]
fn niche_single_c_union_and_raw_retag_templates_compile_and_agree_with_miri() {
    let dir = unique_temp_dir("ep2_templates");
    let root = repo_root();

    // One candidate per Episode 2 template. The `Pass` and `PerturbAst`
    // templates return normally under Miri and the `Ub` templates fault.
    let pass_cases: [(&dyn MiriAstMutator, MutationMode, &str); 16] = [
        (
            &BitValidityTransmuteMutator,
            MutationMode::Pass,
            "transmute::<u32, NonZeroU32>",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::PerturbAst,
            "transmute::<u32, Option<NonZeroU32>>(__niche_zero)",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Pass,
            "__niche_ob: Option<bool>",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::PerturbAst,
            "&raw mut __meters.0",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Pass,
            "transmute::<[u32; 2], SingleC>([0u32,",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::PerturbAst,
            "__overlay: OverlayU32",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Pass,
            "transmute::<u32, NonZeroMeters>",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Pass,
            "__proj_single_ref: &mut SingleC",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::PerturbAst,
            "&raw mut __proj_overlay.bytes",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Pass,
            "__proj_slot: Uninit<[u32; 2]>",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::PerturbAst,
            "&raw const __proj_nzm.0",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Pass,
            "&raw mut (*__rr_p).b",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Pass,
            "&raw const (*__rr_shr).a",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Pass,
            "let __rr_sc_p: *mut u32 = match &mut __rr_sc",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::PerturbAst,
            "&raw mut *__rr_mut",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::PerturbAst,
            "&raw mut (*__rr_fm).b",
        ),
    ];
    let ub_cases: [(&dyn MiriAstMutator, MutationMode, &str); 13] = [
        (
            &BitValidityTransmuteMutator,
            MutationMode::Ub,
            "transmute::<u32, NonZeroU32>(__nz_zero)",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Ub,
            "transmute::<[u32; 2], SingleC>(__bad_single_raw)",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Ub,
            "__part_slot: Uninit<[u8; 4]>",
        ),
        (
            &BitValidityTransmuteMutator,
            MutationMode::Ub,
            "transmute::<u32, NonZeroMeters>(__nzm_zero)",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Ub,
            "&raw const __dead_pair.b",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Ub,
            "__dead_inner as *const u32",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Ub,
            "__proj_half: Uninit<[u32; 2]>",
        ),
        (
            &PlaceProjectionWrapper,
            MutationMode::Ub,
            "&raw const __dead_ov.word",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "&raw mut *__rr_y",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "&raw const *__rr_frozen",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "&raw mut (*__rr_m2).b",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "&raw const (*__rr_s).a",
        ),
        (
            &TreeBorrowsRetagInterleaver,
            MutationMode::Ub,
            "*__rr_sc_m = SingleC::Only",
        ),
    ];
    let mut candidates = Vec::new();
    for (mutator, mode, marker) in pass_cases.into_iter().chain(ub_cases) {
        let id = candidates.len();
        candidates.push(template_candidate(id, mutator, mode, marker, &[]));
    }
    // Templates followed by two `Pass` runs of the perturbing mutators
    // (statement reordering, field/index swaps, transmute-literal and operator
    // rewrites), each of which also appends its own `Pass` template. Like
    // `generate_miri_corpus_batch`, which applies at most three mutator passes,
    // this keeps each candidate within `MIRI_DIFFTEST_CANDIDATE_FUEL` steps.
    let tb: &dyn MiriAstMutator = &TreeBorrowsRetagInterleaver;
    let pp: &dyn MiriAstMutator = &PlaceProjectionWrapper;
    let bv: &dyn MiriAstMutator = &BitValidityTransmuteMutator;
    let arith: &dyn MiriAstMutator = &ArithmeticCastMutator;
    type PerturbedCase<'a> = (
        &'a dyn MiriAstMutator,
        MutationMode,
        &'a str,
        [&'a dyn MiriAstMutator; 2],
    );
    let perturbed_cases: [PerturbedCase<'_>; 7] = [
        (bv, MutationMode::Pass, "__single: SingleC", [tb, pp]),
        (
            bv,
            MutationMode::Ub,
            "__part_slot: Uninit<[u8; 4]>",
            [pp, arith],
        ),
        (
            pp,
            MutationMode::PerturbAst,
            "__proj_single_ref: &mut SingleC",
            [bv, tb],
        ),
        (
            pp,
            MutationMode::Ub,
            "&raw const __dead_pair.b",
            [arith, bv],
        ),
        (tb, MutationMode::Pass, "&raw mut (*__rr_p).b", [pp, arith]),
        (tb, MutationMode::Ub, "&raw mut *__rr_y", [tb, bv]),
        (
            tb,
            MutationMode::Ub,
            "let __tb_act: &mut u32 = unsafe { &mut *__tb_root };",
            [tb, bv],
        ),
    ];
    for (mutator, mode, marker, follow_ups) in perturbed_cases {
        let id = candidates.len();
        candidates.push(template_candidate(id, mutator, mode, marker, &follow_ups));
    }
    // Closed multi-parameter Episode 2 functions exercising parameter seeding
    // (`Option<bool>`, `Option<ColorTag>`, `Option<NonZeroU32>`, `SingleC`,
    // `MetersU32`, `NonZeroMeters`, `OverlayU32`, `[u8; 4]`, `[u32; 2]`,
    // `[u32; 1]`, slice/`str` references `&[u32]` / `&mut [u8]` / `&str` /
    // `&mut str`, and fat raw pointers `*const [u32]` / `*mut [u8]` /
    // `*const str` / `*mut str`), reference-returning signatures
    // (`-> &'a mut u32`), body `'a` annotations, early `return`s,
    // deref-borrowed field projections, and local shadowing through real
    // `rustc` + Miri + Anneal evaluation.
    let param_ep2_seed = "\
pub fn param_ep2_live<'a, 'b>(
    s: SingleC,
    MetersU32(m_inner): MetersU32,
    nm: NonZeroMeters,
    o: OverlayU32,
    r_pair: &'a mut PairU32,
    p_sc: *mut SingleC,
    s_slice: &'a [u32],
    s_mut_bytes: &'b mut [u8],
    p_slice: *const [u32],
    p_mut_bytes: *mut [u8],
    s_str: &'a str,
    s_mut_str: &'b mut str,
    p_str: *const str,
    p_mut_str: *mut str,
    one_elem: [u32; 1],
    (tup_a, tup_b): (u32, u8),
    u_word: Uninit<u32>,
    ob: Option<bool>,
    oc: core::option::Option<ColorTag>,
    onz: core::option::Option<NonZeroU32>,
    bytes: [u8; 4],
    words: [u32; 2],
) -> u32
where
    'a: 'b,
{
    let shadowed: u32 = 1u32;
    let (shadowed, _): (PairU32, u32) = (PairU32 { a: words[0], b: words[1] }, tup_a);
    let rb_ref: &mut u32 = &mut (*r_pair).b;
    let r_pair_a: u32 = r_pair.a;
    *rb_ref = tup_b as u32;
    s_mut_bytes[0] ^= 1u8;
    let _ = (p_slice, p_mut_bytes, s_str, s_mut_str, p_str, p_mut_str);
    let mut borrowed = PairU32 { a: r_pair_a, b: r_pair.b };
    let rb: &mut u32 = &mut (borrowed.b);
    let keep_a: u32 = (borrowed).a;
    *rb = s_mut_bytes[0] as u32;
    let sc_v: u32 = match s {
        SingleC::Only(v) => v,
    };
    let p_sc_v: u32 = unsafe {
        match &*p_sc {
            SingleC::Only(v) => *v,
        }
    };
    let nzm_v: u32 = unsafe { transmute::<NonZeroU32, u32>(nm.0) };
    let ob_v: u32 = match ob {
        Some(true) => 1u32,
        Some(false) => 2u32,
        None => 3u32,
    };
    let oc_v: u32 = match oc {
        Some(ColorTag::Red) => 4u32,
        Some(ColorTag::Green) => 8u32,
        Some(ColorTag::Blue) => 12u32,
        None => 16u32,
    };
    let onz_v: u32 = unsafe { transmute::<Option<NonZeroU32>, u32>(onz) };
    let ov_v: u32 = unsafe { o.word ^ u_word.value };
    m_inner ^ sc_v ^ p_sc_v ^ nzm_v ^ ob_v ^ oc_v ^ onz_v ^ ov_v ^ keep_a ^ s_slice[0] ^ one_elem[0] ^ (bytes[0] as u32) ^ shadowed.a
}
";
    let ref_ret_ep2_seed = "\
pub fn ref_ret_ep2_live<'a>(
    x: &'a mut u32,
    y: &'a mut u32,
    s_static: &'static u32,
    flag: bool,
) -> &'a mut u32 {
    let chosen: &'a mut u32 = if flag {
        *x ^= 3u32 ^ *s_static;
        return x;
    } else {
        *y ^= 5u32;
        y
    };
    chosen
}
";
    // A raw-pointer return sinks into a local (Miri and Anneal cannot compare
    // host addresses), and early `return`s in a scalar-returning function
    // lower to `break '__anneal_ret` while the `&'static [u8]` parameter is
    // backed by a stack array.
    let ptr_ret_ep2_seed = "\
pub fn ptr_ret_ep2_live(p_static: &'static u32, flag: bool) -> *const u32 {
    if flag {
        return p_static as *const u32;
    }
    &raw const *p_static
}
";
    let early_ret_ep2_seed = "\
pub fn early_ret_ep2_live(b_static: &'static [u8], flag: bool) -> u32 {
    if flag {
        return (b_static[0] as u32) ^ 1u32;
    }
    (b_static[1] as u32) ^ 7u32
}
";
    let mut param_batch = generate_miri_batch(&[param_ep2_seed], 2, 0xE2A1_0001);
    assert_eq!(param_batch.len(), 2);
    param_batch.extend(generate_miri_batch(&[ref_ret_ep2_seed], 2, 0xE2A3_0001));
    param_batch.extend(generate_miri_batch(&[ptr_ret_ep2_seed], 2, 0xE2A4_0001));
    param_batch.extend(generate_miri_batch(&[early_ret_ep2_seed], 2, 0xE2A4_0002));
    assert_eq!(param_batch.len(), 8);
    for mut cand in param_batch.drain(..) {
        let id = candidates.len();
        let old_fn_name = cand.fn_name;
        let new_fn_name = format!("param_ep2_live__b0_c{id}");
        cand.id = id;
        cand.fn_source = cand.fn_source.replacen(
            &format!("pub fn {old_fn_name}"),
            &format!("pub fn {new_fn_name}"),
            1,
        );
        cand.fn_name = new_fn_name;
        cand.source = build_standalone_candidate_source(&cand.fn_source);
        candidates.push(cand);
    }
    let template_count = candidates.len();

    // Negative controls: constructs that the templates avoid because Anneal's
    // frozen `trusted/` semantics diverge from Miri on them. Each must stay a
    // kernel-confirmed divergence; once `trusted/` fixes one, this test fails
    // so that the matching template restriction can be lifted.
    let negative_controls: [(&str, &str, &str); 7] = [
        (
            "false_positive_ub",
            "neg_ctrl_option_nonzero_some_transmute",
            "-> u32 {
    let o: Option<NonZeroU32> = unsafe { transmute::<u32, Option<NonZeroU32>>(0x41u32) };
    match o {
        Some(_) => 1u32,
        None => 2u32,
    }
}",
        ),
        (
            "false_positive_ub",
            "neg_ctrl_option_bool_none_transmute",
            "-> u32 {
    let o: Option<bool> = unsafe { transmute::<u8, Option<bool>>(2u8) };
    match o {
        Some(_) => 1u32,
        None => 2u32,
    }
}",
        ),
        (
            "missed_ub",
            "neg_ctrl_single_c_nonzero_payload_transmute_zero",
            "-> u32 {
    #[repr(C)]
    enum SingleCNonZero {
        Only(NonZeroU32),
    }
    let s: SingleCNonZero = unsafe { transmute::<[u32; 2], SingleCNonZero>([0u32, 0u32]) };
    match s {
        SingleCNonZero::Only(v) => unsafe { transmute::<NonZeroU32, u32>(v) },
    }
}",
        ),
        (
            "missed_ub",
            "neg_ctrl_nonzero_ptr_write_zero",
            "-> u32 {
    let mut n: NonZeroU32 = unsafe { transmute::<u32, NonZeroU32>(5u32) };
    let p: *mut u32 = (&raw mut n) as *mut u32;
    unsafe {
        *p = 0u32;
    }
    unsafe { transmute::<NonZeroU32, u32>(n) }
}",
        ),
        (
            "ub_location_mismatch",
            "neg_ctrl_single_c_ptr_write_bad_tag",
            "-> u32 {
    let mut s: SingleC = SingleC::Only(4u32);
    let p: *mut u32 = (&raw mut s) as *mut u32;
    unsafe {
        *p = 2u32;
    }
    let t: SingleC = s;
    match t {
        SingleC::Only(v) => v,
    }
}",
        ),
        (
            "false_positive_ub",
            "neg_ctrl_single_c_ptr_write_payload",
            "-> u32 {
    let mut s: SingleC = SingleC::Only(4u32);
    let p: *mut [u32; 2] = (&raw mut s) as *mut [u32; 2];
    unsafe {
        (*p)[1] = 6u32;
    }
    let t: SingleC = s;
    match t {
        SingleC::Only(v) => v,
    }
}",
        ),
        (
            "false_positive_ub",
            "neg_ctrl_raw_field_ptr_then_sibling_write",
            "-> u32 {
    let mut pair: PairU32 = PairU32 { a: 1u32, b: 2u32 };
    let m: &mut PairU32 = &mut pair;
    let rb: *mut u32 = &raw mut (*m).b;
    let m2: &mut PairU32 = &mut *m;
    m2.b = 7u32;
    unsafe {
        *rb = 9u32;
    }
    pair.b
}",
        ),
    ];
    for (_, name, body) in negative_controls {
        let id = candidates.len();
        let fn_name = format!("{name}__b0_c{id}");
        let fn_source = format!("pub fn {fn_name}() {body}\n");
        candidates.push(handwritten_candidate(
            id,
            "ep2_negative_control",
            &fn_name,
            "BitValidityTransmuteMutator",
            &fn_source,
        ));
    }
    let total = candidates.len();

    let findings_dir = dir.join("findings_ep2");
    let report = evaluate_miri_batches(
        "seeded",
        0xE2_0001,
        &[candidates],
        total,
        Some(&findings_dir),
        Some(&root),
    )
    .expect("evaluate Episode 2 template batch");

    assert_eq!(report.total_candidates, total);
    assert_eq!(report.compiled_candidates, total, "{report:#?}");
    assert_eq!(report.compared_candidates, total, "{report:#?}");
    assert_eq!(
        report.not_compared_count, 0,
        "{:?}",
        report.not_compared_reasons
    );
    assert!(
        report.unmodeled_external_calls.is_empty(),
        "{:?}",
        report.unmodeled_external_calls
    );
    for outcome in ["external_call", "unsupported", "out_of_fuel", "error"] {
        assert_eq!(
            report.anneal_outcomes.get(outcome).copied().unwrap_or(0),
            0,
            "unexpected Anneal `{outcome}` outcomes: {:?}",
            report.anneal_outcomes
        );
    }
    assert_eq!(report.agree_count, template_count, "{:#?}", report.findings);
    assert_eq!(report.diverge_count, negative_controls.len());
    assert_eq!(report.kernel_confirmed_divergences, negative_controls.len());
    // Verify per-item Miri outcomes so a `Pass` template faulting and a `Ub`
    // template losing its UB can never cancel out in aggregate counts:
    // - `0..16`: `pass_cases` (`PassScalar`)
    // - `16..29`: `ub_cases` (`Ub`)
    // - `29..36`: `perturbed_cases` (`[Pass, Ub, Pass, Ub, Pass, Ub, Ub]`)
    let expected_perturbed_ub = [false, true, false, true, false, true, true];
    for id in 0..36usize {
        let fn_name = format!("ep2_template__b0_c{id}");
        let item = report
            .item_reports
            .iter()
            .find(|r| r.name == fn_name)
            .unwrap_or_else(|| panic!("missing item report for `{fn_name}`"));
        let expect_ub = if id < 16 {
            false
        } else if id < 29 {
            true
        } else {
            expected_perturbed_ub[id - 29]
        };
        if expect_ub {
            assert!(
                matches!(item.miri, MiriOutcome::Ub { .. }),
                "expected Miri UB for `{fn_name}`, got {:?}",
                item.miri
            );
        } else {
            assert!(
                matches!(item.miri, MiriOutcome::PassScalar { .. }),
                "expected Miri PassScalar for `{fn_name}`, got {:?}",
                item.miri
            );
        }
    }
    let miri_pass = report.miri_verdicts.get("pass").copied().unwrap_or(0);
    let miri_panic = report.miri_verdicts.get("panic").copied().unwrap_or(0);
    let miri_ub = report.miri_verdicts.get("ub").copied().unwrap_or(0);
    assert!(miri_pass >= 16 + 3 + 4, "{:?}", report.miri_verdicts);
    assert!(miri_ub >= 13 + 4 + 3, "{:?}", report.miri_verdicts);
    assert_eq!(
        miri_pass + miri_panic + miri_ub,
        total,
        "{:?}",
        report.miri_verdicts
    );

    let mut expected_classes = std::collections::BTreeMap::new();
    for (class, name, _) in negative_controls {
        *expected_classes.entry(class.to_string()).or_insert(0usize) += 1;
        let finding = report
            .findings
            .iter()
            .find(|f| f.fn_name.starts_with(name))
            .unwrap_or_else(|| panic!("no finding for negative control `{name}`"));
        assert_eq!(finding.divergence_class, class, "{finding:#?}");
        assert!(finding.kernel_confirmed, "{finding:#?}");
        assert!(
            finding.kernel_confirm_theorems.contains(":= by\n  rfl"),
            "{}",
            finding.kernel_confirm_theorems
        );
    }
    let observed_classes: std::collections::BTreeMap<String, usize> = report
        .divergence_classes
        .iter()
        .filter(|(_, count)| **count > 0)
        .map(|(class, count)| (class.clone(), *count))
        .collect();
    assert_eq!(observed_classes, expected_classes);

    // Verify standalone `repro.rs` round-tripping on an Episode 2 finding
    // bundle exercising `MIRI_CORPUS_MODULE_PREAMBLE` types (`NonZeroU32` /
    // `SingleCNonZero`).
    let repro_finding = report
        .findings
        .iter()
        .find(|f| {
            f.fn_name
                .starts_with("neg_ctrl_single_c_nonzero_payload_transmute_zero")
        })
        .expect("SingleCNonZero negative control finding");
    let repro_path = repro_finding.repro_path.as_ref().expect("repro.rs written");
    let repro_report = reproduce_miri_finding(repro_path, Some(&root))
        .expect("reproduce Episode 2 finding bundle standalone");
    assert!(
        matches!(
            repro_report.verdict,
            ComparisonVerdict::Diverge(DivergenceKind::MissedUb { .. })
        ),
        "{repro_report:#?}"
    );
    assert!(repro_report.kernel_confirmed);
}

/// Seed whose unmutated program the live engine gets wrong: it writes the
/// surrogate code point `0xD800` into a `char` through a `*mut u32` and loads it
/// as `u32`. Miri reports the invalid `char`; Anneal returns `0xD800`
/// (`missed_ub`). When the engine learns `char` validity, this test (like the
/// negative control above) must switch to another divergent seed.
const CHAR_SURROGATE_SEED: &str = "\
pub fn seed_char_surrogate_via_ptr() -> u32 {
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = 0xD800u32;
    }
    c as u32
}
";

/// Seed whose unmutated program (`[]`) writes the valid code point `pair.a`
/// (`0x0061`, `'a'`) and therefore agrees between Miri and Anneal, but diverges
/// (`missed_ub`) when `PlaceProjectionWrapper` flips `pair.a` -> `pair.b`
/// (`0xD800`). A multi-pass candidate containing that flip alongside other
/// `Pass`/`PerturbAst` passes shrinks live from `k >= 2` down to the non-empty
/// 1-minimal chain `["PlaceProjectionWrapper"]`.
const CHAR_SURROGATE_ON_FIELD_FLIP_SEED: &str = "\
pub fn seed_char_surrogate_on_field_flip() -> u32 {
    let pair: PairU32 = PairU32 { a: 0x0061u32, b: 0xD800u32 };
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = pair.a;
    }
    c as u32
}
";

/// Live end-to-end shrinking in `evaluate_miri_batches_with_options`: mutated
/// candidates of a divergent seed (`k -> 0`) and a mutator-triggered divergent
/// seed (`k -> 1`) are evaluated, every finding's chain is shrunk by replaying
/// it against the seed and re-running the live oracle, and each minimized
/// `repro.rs` reproduces exactly the outcome tags recorded in its bundle (so no
/// pre-shrink artifact is left on a minimized finding).
#[test]
fn seeded_divergent_findings_shrink_live_and_minimized_repros_reproduce() {
    let dir = unique_temp_dir("shrink_live");
    let root = repo_root();
    let findings_dir = dir.join("findings_shrink");
    let seeds = [CHAR_SURROGATE_SEED, CHAR_SURROGATE_ON_FIELD_FLIP_SEED];
    let pool = generate_miri_batch(&seeds, 64, 0x5EED_5A1F);
    let seed_fault_cand = pool
        .iter()
        .find(|c| {
            c.seed_index == 0
                && c.applied_mutators.len() >= 2
                && reconstruct_miri_mutation_steps(c, &seeds).is_some_and(|(_, steps)| {
                    steps
                        .iter()
                        .all(|s| matches!(s.mode, MutationMode::Pass | MutationMode::PerturbAst))
                })
        })
        .expect("multi-pass Pass/PerturbAst candidate for CHAR_SURROGATE_SEED")
        .clone();
    let mutator_fault_cand = pool
        .iter()
        .find(|c| {
            c.seed_index == 1
                && c.applied_mutators.len() >= 2
                && c.source.contains("*p = pair.b")
                && reconstruct_miri_mutation_steps(c, &seeds).is_some_and(|(_, steps)| {
                    steps
                        .iter()
                        .all(|s| matches!(s.mode, MutationMode::Pass | MutationMode::PerturbAst))
                })
        })
        .expect("multi-pass candidate where PlaceProjectionWrapper flips pair.a -> pair.b")
        .clone();
    let batch = vec![seed_fault_cand, mutator_fault_cand];
    let options = MiriEvalOptions {
        findings_dir: Some(findings_dir.clone()),
        anneal_repo_root: Some(root.clone()),
        shrink_seeds: Some(seeds.iter().map(|s| (*s).to_string()).collect()),
    };
    let report = evaluate_miri_batches_with_options(
        "seeded",
        0x5EED_5A1F,
        std::slice::from_ref(&batch),
        batch.len(),
        &options,
    )
    .expect("evaluate mutated candidates of divergent seeds");
    assert_eq!(report.findings.len(), report.diverge_count);
    assert_eq!(
        report.findings.len(),
        2,
        "both the seed-fault and mutator-fault candidates must diverge"
    );

    let mut shrunk_to_zero = 0usize;
    let mut shrunk_to_one = 0usize;
    for f in &report.findings {
        eprintln!(
            "{}: {} `{}` ({} -> {} mutators, {} shrink evaluations, {} live runs)",
            f.fn_name,
            f.divergence_class,
            f.shrink_status,
            f.original_mutator_chain.len(),
            f.minimized_mutator_chain.len(),
            f.shrink_evaluations,
            f.executed_oracle_runs
        );
        let cand = batch
            .iter()
            .find(|c| c.fn_name == f.fn_name)
            .expect("finding names a batch candidate");
        assert!(cand.applied_mutators.len() >= 2);
        assert_eq!(f.original_mutator_chain, cand.applied_mutators, "{}", f.fn_name);
        assert_eq!(f.applied_mutators, f.minimized_mutator_chain, "{}", f.fn_name);
        assert_eq!(
            f.shrink_status, "minimized",
            "{}: both multi-pass candidates must shrink live, got `{}`",
            f.fn_name, f.shrink_status
        );
        assert!(f.shrink_evaluations >= 1, "{}: `[]` is always queried", f.fn_name);
        assert!(
            (1..=f.shrink_evaluations).contains(&f.executed_oracle_runs),
            "{}: executed_oracle_runs={} shrink_evaluations={}",
            f.fn_name,
            f.executed_oracle_runs,
            f.shrink_evaluations
        );
        assert!(f.kernel_confirmed, "{}", f.fn_name);
        assert!(f.minimized_mutator_chain.len() < f.original_mutator_chain.len());
        assert_ne!(f.mutant_source, cand.source, "{}", f.fn_name);
        assert!(f.mir_neighborhood.contains("def body : CapturedMir :="), "{}", f.fn_name);
        assert!(
            f.kernel_confirm_theorems
                .contains(&format!("theorem confirm_tag_{} :", f.fn_name)),
            "{}",
            f.fn_name
        );

        let (base, steps) =
            reconstruct_miri_mutation_steps(cand, &seeds).expect("replayable Miri candidate");
        let names: Vec<&str> = steps.iter().map(|s| s.mutator_name.as_str()).collect();
        let embeddings = ordered_name_embeddings(&names, &f.minimized_mutator_chain);
        assert!(!embeddings.is_empty(), "{}: subsequence order", f.fn_name);
        assert!(
            embeddings.iter().any(|kept_idx| {
                let kept: Vec<_> = kept_idx.iter().map(|&i| steps[i].clone()).collect();
                replay_miri_mutation_steps(cand, &base, &kept).source == f.mutant_source
            }),
            "{}: repro.rs must match replayed minimized chain",
            f.fn_name
        );
        if cand.seed_index == 0 {
            assert!(
                f.minimized_mutator_chain.is_empty(),
                "seed-fault candidate must shrink k -> 0, got {:?}",
                f.minimized_mutator_chain
            );
            shrunk_to_zero += 1;
        } else {
            assert_eq!(
                f.minimized_mutator_chain,
                vec!["PlaceProjectionWrapper".to_string()],
                "field-flip candidate must shrink k -> 1"
            );
            shrunk_to_one += 1;
        }

        let repro_path = f.repro_path.as_ref().expect("repro_path");
        assert_eq!(fs::read_to_string(repro_path).expect("read repro.rs"), f.mutant_source);
        let rep = reproduce_miri_finding(repro_path, Some(&root)).expect("reproduce finding");
        let ComparisonVerdict::Diverge(kind) = &rep.verdict else {
            panic!("{}: repro.rs no longer diverges: {:?}", f.fn_name, rep.verdict);
        };
        assert_eq!(divergence_class_slug(kind), f.divergence_class, "{}", f.fn_name);
        assert_eq!(rep.miri.summary_tag(), f.miri_outcome_tag, "{}", f.fn_name);
        assert_eq!(rep.anneal.summary_tag(), f.anneal_outcome_tag, "{}", f.fn_name);
        assert!(rep.kernel_confirmed, "{}", f.fn_name);
        let finding_json = fs::read_to_string(repro_path.with_file_name("finding.json"))
            .expect("read finding.json");
        assert!(finding_json.contains(&format!("\"shrink_status\": \"{}\"", f.shrink_status)));
    }
    assert_eq!(shrunk_to_zero, 1, "expected one k -> 0 live shrink");
    assert_eq!(shrunk_to_one, 1, "expected one k -> 1 live shrink");
}

#[test]
fn ep1_a0_category9_templates_and_witness_polarity_verify_live() {
    let dir = unique_temp_dir("ep1_a0_cat9");
    let findings_dir = dir.join("findings");
    let root = repo_root();

    let candidates: Vec<GeneratedMiriCandidate> = [
        (
            "cat9_move_deinit_pass",
            r#"pub fn cat9_move_deinit_pass() -> u32 {
    let mut x: NonCopyU32 = NonCopyU32(14u32);
    let root: *mut NonCopyU32 = &raw mut x;
    let r: &mut NonCopyU32 = unsafe { &mut *root };
    let moved: NonCopyU32 = x;
    *r = NonCopyU32(moved.0 ^ 7u32);
    ((*r).0) ^ moved.0
}
"#,
        ),
        (
            "cat9_fn_entry_chain_pass",
            r#"pub fn cat9_fn_entry_chain_pass() -> u32 {
    let mut slot: u32 = 20u32;
    let raw: *mut u32 = &raw mut slot;
    let r0: &mut u32 = unsafe { &mut *raw };
    let delta: u32 = helper_reborrow_mid(r0, 5u32);
    *r0 = delta ^ 20u32;
    unsafe {
        *raw = (*r0) ^ 3u32;
        *raw
    }
}
"#,
        ),
        (
            "cat9_scalar_and_mem_intrinsics_pass",
            r#"pub fn cat9_scalar_and_mem_intrinsics_pass() -> u32 {
    let mut pair: PairU32 = PairU32 { a: 0u32, b: 90u32 };
    let mut dst: u32 = 0u32;
    unsafe {
        write_bytes!(&raw mut pair.a, 0x02u8, 1usize);
        copy_nonoverlapping(&raw const pair.a, &raw mut dst, 1usize);
    }
    let nz: u32 = (dst & 0xFFu32) | 1u32;
    let bits: u32 = ctlz(nz) ^ cttz(nz) ^ ctpop(nz) ^ (bswap(nz) & 0xFFu32) ^ (bitreverse(nz) >> 24u32);
    let nz_cnt: u32 = unsafe { ctlz_nonzero(nz) ^ cttz_nonzero(nz) };
    let sat: u8 = saturating_add(saturating_sub(10u8, 20u8), 250u8);
    let wrap: u32 = wrapping_mul(wrapping_add(u32::MAX, 2u32), wrapping_sub(4u32, 1u32));
    let ord = three_way_compare(wrap, 10u32);
    let q: u32 = unsafe { exact_div(36u32, 3u32) };
    let base: *const u32 = &raw const pair.a;
    let back: *const u32 = unsafe { arith_offset(arith_offset(base, 5isize), -4isize) };
    bits ^ nz_cnt ^ (sat as u32) ^ wrap ^ (((ord as i8) + 1i8) as u32) ^ q ^ unsafe { *back }
}
"#,
        ),
        (
            "cat9_fn_entry_protector_ub",
            r#"pub fn cat9_fn_entry_protector_ub() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let delta: u32 = helper_reborrow_mid(unsafe { &mut *raw }, 1u32);
    unsafe {
        *raw = delta;
    }
    helper_violate_fn_entry_protector(unsafe { *raw })
}
"#,
        ),
        (
            "cat9_in_scope_move_raw_read_conservative",
            r#"pub fn cat9_in_scope_move_raw_read_conservative() -> u32 {
    let x = NonCopyU32(15u32);
    let raw: *const u32 = &raw const x.0;
    let moved: NonCopyU32 = x;
    let leaked: u32 = unsafe { *raw };
    moved.0 + leaked
}
"#,
        ),
        (
            "cat9_provenance_overwritten_byte_missed_ub",
            r#"pub fn cat9_provenance_overwritten_byte_missed_ub() -> u32 {
    let x: u32 = 7u32;
    let mut p: *const u32 = &raw const x;
    let byte_ptr: *mut u8 = (&raw mut p) as *mut u8;
    unsafe {
        *byte_ptr = 0u8;
        *p
    }
}
"#,
        ),
    ]
    .into_iter()
    .enumerate()
    .map(|(id, (name, fn_src))| GeneratedMiriCandidate {
        id,
        seed_index: id,
        seed_name: name.to_string(),
        fn_name: name.to_string(),
        seed_u64: id as u64,
        applied_mutators: Vec::new(),
        tracked_locals: Vec::new(),
        fn_source: fn_src.to_string(),
        source: build_standalone_candidate_source(fn_src),
    })
    .collect();

    let options = MiriEvalOptions {
        findings_dir: Some(findings_dir.clone()),
        anneal_repo_root: Some(root),
        shrink_seeds: None,
    };
    let report = evaluate_miri_batches_with_options(
        "seeded",
        0xCA79_0001,
        std::slice::from_ref(&candidates),
        candidates.len(),
        &options,
    )
    .expect("evaluate Category 9 live batch");

    assert_eq!(report.total_candidates, 6);
    assert_eq!(report.compiled_candidates, 6);
    assert_eq!(report.agree_count, 4);
    assert_eq!(report.diverge_count, 2);
    assert_eq!(report.not_compared_count, 0);
    assert_eq!(
        report.witness_polarity_counts.get("unsound_missed_fault"),
        Some(&1)
    );
    assert_eq!(
        report
            .witness_polarity_counts
            .get("sound_conservative_abstraction"),
        Some(&1)
    );
    assert_eq!(
        report.witness_polarity_counts.get("value_mismatch"),
        Some(&0)
    );
    assert_eq!(
        report
            .witness_polarity_counts
            .get("harness_or_extraction_error"),
        Some(&0)
    );
    assert_eq!(report.findings.len(), 2);
    let cons_finding = report
        .findings
        .iter()
        .find(|f| f.fn_name == "cat9_in_scope_move_raw_read_conservative")
        .expect("conservative finding present");
    assert_eq!(cons_finding.divergence_class, "false_positive_ub");
    assert_eq!(
        cons_finding.witness_polarity,
        "sound_conservative_abstraction"
    );
    assert!(cons_finding.kernel_confirmed);

    let unsound_finding = report
        .findings
        .iter()
        .find(|f| f.fn_name == "cat9_provenance_overwritten_byte_missed_ub")
        .expect("unsound missed fault finding present");
    assert_eq!(unsound_finding.divergence_class, "missed_ub");
    assert_eq!(unsound_finding.witness_polarity, "unsound_missed_fault");
    assert!(unsound_finding.kernel_confirmed);
}
