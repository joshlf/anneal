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
    MiriEvalOptions, WitnessPolarity, classify_outcome_tags_polarity,
    classify_verdict_witness_polarity, divergence_class_slug, evaluate_miri_batches,
    evaluate_miri_batches_with_options, reproduce_miri_finding, witness_polarity_accounting_holds,
};
use anneal_difftest::mutators_miri::{
    ArithmeticCastMutator, BitValidityTransmuteMutator, DetRng, GeneratedMiriCandidate,
    MIRI_CORPUS_CRATE_HEADER, MIRI_CORPUS_MODULE_PREAMBLE, MiriAstMutator, MutationMode,
    PlaceProjectionWrapper, RAW_MIRI_DIFF_CORPUS_RS, RawPtrOffsetMutator,
    TreeBorrowsRetagInterleaver, build_standalone_candidate_source, generate_miri_batch,
    generate_miri_corpus_batch, load_miri_diff_corpus_seeds, reconstruct_miri_mutation_steps,
    replay_miri_mutation_steps,
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
assert data["total_candidates"] == 112
assert data["compiled_candidates"] == 112
assert data["compile_failed_candidates"] == 0
assert data["compared_candidates"] == 112
assert data["agree_count"] == 112
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

wp = data["witness_polarity_counts"]
assert wp == {
    "harness_or_extraction_error": 0,
    "sound_conservative_abstraction": 0,
    "unsound_missed_fault": 0,
    "value_mismatch": 0,
}, f"unexpected witness_polarity_counts: {wp}"

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

    // Negative control: evaluate an oracle-separated candidate whose divergence
    // does not depend on any `trusted/` semantic gap, verifying finding bundle
    // generation (`repro.rs`, `finding.json`, `SUMMARY.md`) and standalone
    // `--reproduce` round-tripping. `ANNEAL_CAPTURE_DIR` is set for every
    // `anneal-rustc-capture` compilation (the capture wrapper records nothing
    // without it) and never for the plain `rustc` compilation of the Miri
    // `.rlib` (`run_miri_oracle` removes any ambient value; the `--reproduce`
    // run below passes one), so Anneal returns `2` (kernel-confirmed by `rfl`)
    // while Miri reads an invalid `bool` (`missed_ub`). (The previous control,
    // a surrogate `char` written through `*mut u32`, agrees since
    // `DIV-LM-RAW-OVERWRITE-CHAR-COPY` was fixed; `cfg(miri)` cannot split the
    // oracles because the `.rlib` is compiled without `--cfg miri`.)
    let root = repo_root();
    let neg_fn = r#"pub fn neg_ctrl_capture_split_invalid_bool__b0_c0() -> u32 {
    const ANNEAL_CAPTURE: bool = option_env!("ANNEAL_CAPTURE_DIR").is_some();
    if ANNEAL_CAPTURE {
        2u32
    } else {
        let raw: u8 = 2u8;
        let b: bool = unsafe { *(&raw const raw as *const bool) };
        b as u32
    }
}
"#;
    let neg_cand = GeneratedMiriCandidate {
        id: 0,
        seed_index: 0,
        seed_name: "ub_transmute_invalid_bool_through_ptr".to_string(),
        fn_name: "neg_ctrl_capture_split_invalid_bool__b0_c0".to_string(),
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

    // Pass an ambient `ANNEAL_CAPTURE_DIR` into the `--reproduce` subprocess to
    // verify that `run_miri_oracle` strips `ANNEAL_CAPTURE_DIR` from the Miri
    // `.rlib` and `miri` invocations and preserves the oracle split.
    let repro_json = dir.join("repro_neg.json");
    let repro_out = Command::new(bin)
        .env("ANNEAL_CAPTURE_DIR", dir.join("ambient_capture_dir_leak"))
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
_, _, fn_name, exp_class, exp_polarity, exp_miri, exp_anneal, exp_lean = sys.argv
assert rep["fn_name"] == fn_name, f"{rep['fn_name']} != {fn_name}"
assert rep["verdict"] == "diverge", f"expected diverge, got {rep}"
assert rep["divergence_class"] == exp_class, f"{rep['divergence_class']} != {exp_class}"
assert rep["witness_polarity"] == exp_polarity, f"{rep['witness_polarity']} != {exp_polarity}"
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
            &f.witness_polarity,
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

    // The diverging negative control steps through `helper_add_ten()` in both
    // oracles, then splits them without relying on any `trusted/` semantic gap:
    // `ANNEAL_CAPTURE_DIR` is set for every `anneal-rustc-capture` compilation and
    // never for the plain `rustc` compilation of the Miri `.rlib` (from which
    // `run_miri_oracle` removes any ambient value), so Anneal returns `base`
    // (`10`, kernel-confirmed) while Miri reads an invalid `bool`
    // (`missed_ub`). (A surrogate `char` written through `*mut u32` agrees
    // since `DIV-LM-RAW-OVERWRITE-CHAR-COPY` was fixed.)
    let div_fn = r#"pub fn neg_ctrl_helper_call_capture_split__b0_c1() -> u32 {
    const ANNEAL_CAPTURE: bool = option_env!("ANNEAL_CAPTURE_DIR").is_some();
    let base: u32 = helper_add_ten();
    if ANNEAL_CAPTURE {
        base
    } else {
        let raw: u8 = 2u8;
        let b: bool = unsafe { *(&raw const raw as *const bool) };
        base + (b as u32)
    }
}
"#;
    let div_cand = GeneratedMiriCandidate {
        id: 1,
        seed_index: 0,
        seed_name: "pass_direct_fn_call".to_string(),
        fn_name: "neg_ctrl_helper_call_capture_split__b0_c1".to_string(),
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
    assert_eq!(f.fn_name, "neg_ctrl_helper_call_capture_split__b0_c1");
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

/// `RawPtrOffsetMutator`'s `u8` read of the uninitialized padding byte at offset
/// 1 of a `PaddedU8U32` through `(&raw const s) as *const u8` and
/// `offset(base, 1isize)` (`model-checking/kani#5183`) compiles, faults in Miri on
/// the uninitialized byte, and agrees with Anneal's strict UB at the same read;
/// its `Pass` multi-element `copy_nonoverlapping` template (whole-array pointer
/// casts) compiles and agrees on the returned value. The template's former
/// element sub-place form (`&raw const __cp_src[0]`) stays a negative control: a
/// kernel-confirmed `wrong_value` divergence (Anneal copies only the first
/// element), so this test fails once `trusted/` fixes it and the restriction can
/// be lifted.
#[test]
fn raw_ptr_offset_padding_read_and_whole_array_copy_templates_agree_with_miri() {
    let dir = unique_temp_dir("raw_ptr_pad_templates");
    let root = repo_root();
    let padding = template_candidate(
        0,
        &RawPtrOffsetMutator,
        MutationMode::Ub,
        "let __raw_pad_base: *const u8 = (&raw const __raw_pad_s) as *const u8;",
        &[],
    );
    assert!(
        padding
            .fn_source
            .contains("let __raw_pad_byte: u8 = unsafe { *offset(__raw_pad_base, __raw_pad_step) };")
            && padding.fn_source.contains("let __raw_pad_step: isize = 1isize;")
            && padding.fn_source.contains("PaddedU8U32 {"),
        "{}",
        padding.fn_source
    );
    let copy = template_candidate(
        1,
        &RawPtrOffsetMutator,
        MutationMode::Pass,
        "let __src_p: *const u32 = (&raw const __cp_src) as *const u32;",
        &[],
    );
    assert!(
        copy.fn_source
            .contains("copy_nonoverlapping(__src_p, __dst_p, 2usize);"),
        "{}",
        copy.fn_source
    );
    let neg_name = "neg_ctrl_raw_ptr_elem_subplace_copy__b0_c2";
    let neg_source = format!(
        "pub fn {neg_name}() -> u32 {{
    let __cp_src: [u32; 2] = [22u32, 99u32];
    let mut __cp_dst: [u32; 2] = [0u32, 0u32];
    unsafe {{
        let __src_p: *const u32 = &raw const __cp_src[0];
        let __dst_p: *mut u32 = &raw mut __cp_dst[0];
        copy_nonoverlapping(__src_p, __dst_p, 2usize);
    }}
    __cp_dst[0] ^ __cp_dst[1]
}}
"
    );
    let neg = handwritten_candidate(
        2,
        "raw_ptr_negative_control",
        neg_name,
        "RawPtrOffsetMutator",
        &neg_source,
    );
    let findings_dir = dir.join("findings_raw_ptr_pad");
    let report = evaluate_miri_batches(
        "seeded",
        0xE2_0002,
        &[vec![padding, copy, neg]],
        3,
        Some(&findings_dir),
        Some(&root),
    )
    .expect("evaluate RawPtrOffsetMutator template batch");
    assert_eq!(report.compiled_candidates, 3, "{report:#?}");
    assert_eq!(report.compared_candidates, 3, "{report:#?}");
    let item = |name: &str| {
        report
            .item_reports
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing item report for `{name}`"))
    };

    let pad = item("ep2_template__b0_c0");
    assert!(
        matches!(pad.verdict, ComparisonVerdict::Agree)
            && matches!(&pad.miri, MiriOutcome::Ub { message, .. }
                if message.contains("uninitialized"))
            && matches!(pad.anneal, AnnealOutcome::Ub { span: Some(_) }),
        "the padding read must be UB on the uninitialized byte in Miri and strict UB at \
         the same read in Anneal: verdict={:?} miri={:?} anneal={:?}",
        pad.verdict,
        pad.miri,
        pad.anneal
    );

    let cp = item("ep2_template__b0_c1");
    assert!(
        matches!(cp.verdict, ComparisonVerdict::Agree)
            && matches!(cp.miri, MiriOutcome::PassScalar { size_bytes: 4, .. }),
        "the whole-array copy template must return normally and agree: verdict={:?} \
         miri={:?} anneal={:?}",
        cp.verdict,
        cp.miri,
        cp.anneal
    );

    let gap = item(neg_name);
    assert!(
        matches!(
            gap.verdict,
            ComparisonVerdict::Diverge(DivergenceKind::WrongValue { .. })
        ) && gap.miri
            == MiriOutcome::PassScalar {
                bits: 117,
                size_bytes: 4,
            }
            && gap.anneal
                == AnnealOutcome::PassScalar {
                    bits: 22,
                    size_bytes: 4,
                }
            && gap.kernel_confirmed,
        "the element sub-place copy gap changed (fixed?): verdict={:?} miri={:?} anneal={:?} \
         kernel_confirmed={}; lift the `RawPtrOffsetMutator` copy-template restriction and \
         update `probe_gap_subplace_multi_elem_copy` in `miri_eval.rs`",
        gap.verdict,
        gap.miri,
        gap.anneal,
        gap.kernel_confirmed
    );
    assert_eq!(report.agree_count, 2, "{:#?}", report.findings);
    assert_eq!(report.diverge_count, 1, "{:#?}", report.findings);
    assert_eq!(
        report.findings.iter().map(|f| f.divergence_class.as_str()).collect::<Vec<_>>(),
        vec!["wrong_value"]
    );
}

/// Seed whose unmutated program diverges (`missed_ub`) independently of any
/// `trusted/` semantic gap: it writes the surrogate code point `0xD800` into a
/// `char` through a `*mut u32` and then branches on `ANNEAL_CAPTURE_DIR`, which
/// is set for every `anneal-rustc-capture` compilation (the capture wrapper
/// records nothing without it) and never for the plain `rustc` compilation of
/// the Miri `.rlib`. Miri loads `c` as a `char` and reports the invalid value;
/// Anneal loads the raw `u32` through `p` and returns `0xD800`. (Since
/// `DIV-LM-RAW-OVERWRITE-CHAR-COPY` was fixed, Anneal itself rejects the
/// surrogate `char` load, so an unsplit seed agrees with Miri.)
const CHAR_SURROGATE_SEED: &str = r#"pub fn seed_char_surrogate_via_ptr() -> u32 {
    const ANNEAL_CAPTURE: bool = option_env!("ANNEAL_CAPTURE_DIR").is_some();
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = 0xD800u32;
    }
    if ANNEAL_CAPTURE { unsafe { *p } } else { c as u32 }
}
"#;

/// Seed whose unmutated program (`[]`) writes the valid code point `pair.a`
/// (`0x0061`, `'a'`) and therefore agrees between Miri and Anneal, but diverges
/// (`missed_ub`) when `PlaceProjectionWrapper` flips `pair.a` -> `pair.b`
/// (`0xD800`), with the same `ANNEAL_CAPTURE_DIR` oracle split as
/// `CHAR_SURROGATE_SEED`. A multi-pass candidate containing that flip alongside
/// other `Pass`/`PerturbAst` passes shrinks live from `k >= 2` down to the
/// non-empty 1-minimal chain `["PlaceProjectionWrapper"]`.
const CHAR_SURROGATE_ON_FIELD_FLIP_SEED: &str = r#"pub fn seed_char_surrogate_on_field_flip() -> u32 {
    const ANNEAL_CAPTURE: bool = option_env!("ANNEAL_CAPTURE_DIR").is_some();
    let pair: PairU32 = PairU32 { a: 0x0061u32, b: 0xD800u32 };
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = pair.a;
    }
    if ANNEAL_CAPTURE { unsafe { *p } } else { c as u32 }
}
"#;

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

/// 1-based line of the unique line of `haystack` that contains `needle`.
fn cat9_line_of(haystack: &str, needle: &str) -> u32 {
    let matches: Vec<u32> = haystack
        .lines()
        .enumerate()
        .filter_map(|(i, l)| l.contains(needle).then_some(i as u32 + 1))
        .collect();
    assert_eq!(
        matches.len(),
        1,
        "`{needle}` must match a unique line in staged crate, matched lines: {matches:?}"
    );
    matches[0]
}

/// Category 9 templates must agree with Miri live, and the Category 9 engine
/// gaps that `tests/miri-diff/README.md` documents stay pinned exactly as
/// measured (a ratchet: when Anneal changes on a pin, this test fails and the
/// README and pin must be updated). Every divergence is kernel-confirmed and
/// classified by `WitnessPolarity`, and `witness_polarity_counts` satisfies the
/// accounting identity.
///
/// Frame-relative pointer resolution (fixed by `DIV-MR-CALL-TARGET-LOCAL` and
/// `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL` in `86255c4698`): a borrow entry now
/// records the depth of the frame owning `targetLocal`, so inside a callee a
/// pointer to the caller's local `_k` resolves to the caller's `_k`, not the
/// callee's own `_k`. The former gaps stay pinned as exact agreements:
/// - `cat9_gap_callee_raw_read_wrong_value` (`10`) and
///   `cat9_gap_callee_raw_write_wrong_value` (`11`): the caller's `x` and the
///   callee's `u32` parameter `pad2` are both local `_3`.
/// - `cat9_gap_callee_raw_write_collides_with_ptr_arg` (`9`): the caller's `x`
///   and the callee's pointer argument `alias` are both local `_1`.
/// - `cat9_gap_callee_deref_ref_arg` (`11`): `x` and the reference argument `r`
///   are both local `_1`.
///
/// `cat9_gap_fn_entry_protector_raw_reborrow_missed_ub` (`missed_ub`,
/// `unsound_missed_fault`) still diverges: Miri reports the `FnEntry` protector
/// violation of writing through `raw` while `&*raw` is a protected argument.
/// Anneal's write now reaches `x` (Anneal `11`), but the capture emits no
/// `Retag(FnEntry)`, so no protector exists to forbid it.
///
/// Raw-pointer sibling roots (no call needed): `&raw mut x` mints its own root
/// borrow entry, and creating a later `&x` (a sibling root whose retag reads
/// `x`) freezes it as a foreign read, so any later write through the raw
/// pointer is UB in Anneal; Miri passes, because the raw pointer keeps `x`'s
/// tag and the write only disables `&x`:
/// - `cat9_gap_raw_write_after_unused_shared_borrow` (`false_positive_ub`): the
///   minimal single-frame witness, with `&x` never used.
/// - `cat9_gap_callee_raw_write_with_caller_borrow` (`false_positive_ub`): the
///   frozen raw pointer is written inside a callee.
/// - `cat9_gap_post_return_raw_write_after_ref_arg` (`false_positive_ub`): `&x`
///   is a call argument and the raw write follows the call (it reproduces with
///   a callee whose only locals are `_0` and `_r`).
///
/// User `Drop` impls never run: Anneal's `.drop` terminator only de-initializes
/// the dropped place (the capture's `TerminatorKind::Drop` names no drop impl),
/// while Miri calls `Drop::drop` (Category 9's `UnwindCleanupGuard` has an
/// empty `drop` for this reason):
/// - `cat9_gap_drop_impl_side_effect_skipped` (`wrong_value`,
///   `value_mismatch`): a write through the guard's raw pointer is lost
///   (Anneal `1` vs Miri `7`).
/// - `cat9_gap_drop_impl_panic_missed` (`panic_vs_return`,
///   `unsound_missed_fault`): an overflow panic inside `drop` is missed.
/// - `cat9_gap_drop_impl_ub_missed` (`missed_ub`, `unsound_missed_fault`):
///   `ctlz_nonzero(0)` inside `drop` is missed.
///
/// Other pins:
/// - `cat9_in_scope_move_raw_read_conservative` (`false_positive_ub`): Anneal
///   de-initializes the source of `Operand::Move`; Miri evaluates
///   `Operand::Move` like `Operand::Copy`.
/// - `cat9_provenance_overwritten_byte_missed_ub` (`missed_ub`): overwriting one
///   byte of a pointer strips its provenance in Miri; Anneal keeps it.
#[test]
fn ep1_category9_templates_engine_gap_pins_and_witness_polarity_verify_live() {
    let dir = unique_temp_dir("ep1_cat9");
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
            "cat9_returned_child_pass",
            r#"pub fn cat9_returned_child_pass() -> u32 {
    let mut x: u32 = 5u32;
    let child: &mut u32 = helper_reborrow_return(&mut x);
    *child = *child ^ 6u32;
    x = x + 1u32;
    x
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
            "cat9_frozen_reborrow_write_in_callee_ub",
            r#"pub fn cat9_frozen_reborrow_write_in_callee_ub() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let delta: u32 = helper_reborrow_mid(unsafe { &mut *raw }, 1u32);
    unsafe {
        *raw = delta;
    }
    helper_frozen_reborrow_write_in_callee(unsafe { *raw })
}
"#,
        ),
        (
            "cat9_unwind_cleanup_guard_panic",
            r#"pub fn cat9_unwind_cleanup_guard_panic() -> u32 {
    let start: u32 = u32::MAX;
    helper_unwind_guarded(start, 1u32)
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
        (
            "cat9_gap_fn_entry_protector_raw_reborrow_missed_ub",
            r#"#[inline(never)]
fn cat9_gap_write_alias_during_protected_reborrow(
    _r: &u32,
    alias: *mut u32,
    _slot_pad: u32,
) -> u32 {
    unsafe {
        *alias = 8u32;
    }
    3u32
}

pub fn cat9_gap_fn_entry_protector_raw_reborrow_missed_ub() -> u32 {
    let _pad1: u32 = 1u32;
    let _pad2: u32 = 2u32;
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let v: u32 = cat9_gap_write_alias_during_protected_reborrow(
        unsafe { &*raw },
        raw,
        _pad1 + _pad2,
    );
    v + unsafe { *raw }
}
"#,
        ),
        (
            "cat9_gap_callee_raw_read_wrong_value",
            r#"#[inline(never)]
fn cat9_gap_read_through_raw_arg(alias: *const u32, pad: u32, pad2: u32) -> u32 {
    let seen: u32 = unsafe { *alias };
    seen + (pad & 0u32) + (pad2 & 0u32)
}

pub fn cat9_gap_callee_raw_read_wrong_value() -> u32 {
    let _p1: u32 = 1u32;
    let _p2: u32 = 2u32;
    let x: u32 = 10u32;
    let raw: *const u32 = &raw const x;
    cat9_gap_read_through_raw_arg(raw, 100u32, 200u32)
}
"#,
        ),
        (
            "cat9_gap_callee_raw_write_wrong_value",
            r#"#[inline(never)]
fn cat9_gap_write_through_raw_arg(alias: *mut u32, pad: u32, pad2: u32) -> u32 {
    unsafe {
        *alias = 8u32 + 0u32;
    }
    3u32 + (pad & 0u32) + (pad2 & 0u32)
}

pub fn cat9_gap_callee_raw_write_wrong_value() -> u32 {
    let _p1: u32 = 1u32;
    let _p2: u32 = 2u32;
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let v: u32 = cat9_gap_write_through_raw_arg(raw, 100u32, 200u32);
    v + unsafe { *raw }
}
"#,
        ),
        (
            "cat9_gap_callee_raw_write_collides_with_ptr_arg",
            r#"#[inline(never)]
fn cat9_gap_alias_write_no_caller_borrow(alias: *mut u32) -> u32 {
    unsafe {
        *alias = 6u32;
    }
    3u32
}

pub fn cat9_gap_callee_raw_write_collides_with_ptr_arg() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let v: u32 = cat9_gap_alias_write_no_caller_borrow(raw);
    v + unsafe { *raw }
}
"#,
        ),
        (
            "cat9_gap_callee_deref_ref_arg",
            r#"#[inline(never)]
fn cat9_gap_read_ref_arg(r: &u32, bonus: u32) -> u32 {
    *r + bonus
}

pub fn cat9_gap_callee_deref_ref_arg() -> u32 {
    let x: u32 = 10u32;
    cat9_gap_read_ref_arg(&x, 1u32)
}
"#,
        ),
        (
            "cat9_gap_callee_raw_write_with_caller_borrow",
            r#"#[inline(never)]
fn cat9_gap_alias_write_only(alias: *mut u32) -> u32 {
    unsafe {
        *alias = 7u32;
    }
    3u32
}

pub fn cat9_gap_callee_raw_write_with_caller_borrow() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let _r: &u32 = &x;
    let v: u32 = cat9_gap_alias_write_only(raw);
    v + unsafe { *raw }
}
"#,
        ),
        (
            "cat9_gap_post_return_raw_write_after_ref_arg",
            r#"#[inline(never)]
fn cat9_gap_take_shared_arg(_r: &u32) -> u32 {
    3u32
}

pub fn cat9_gap_post_return_raw_write_after_ref_arg() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let seen: u32 = cat9_gap_take_shared_arg(&x);
    unsafe {
        *raw = 7u32 + seen;
        *raw
    }
}
"#,
        ),
        (
            "cat9_gap_raw_write_after_unused_shared_borrow",
            r#"pub fn cat9_gap_raw_write_after_unused_shared_borrow() -> u32 {
    let mut x: u32 = 10u32;
    let raw: *mut u32 = &raw mut x;
    let _r: &u32 = &x;
    unsafe {
        *raw = 11u32;
        *raw
    }
}
"#,
        ),
        (
            "cat9_gap_drop_impl_side_effect_skipped",
            r#"pub struct Cat9WriteOnDrop(pub *mut u32);

impl Drop for Cat9WriteOnDrop {
    fn drop(&mut self) {
        unsafe {
            *self.0 = 7u32;
        }
    }
}

pub fn cat9_gap_drop_impl_side_effect_skipped() -> u32 {
    let mut x: u32 = 1u32;
    {
        let _guard = Cat9WriteOnDrop(&raw mut x);
    }
    x
}
"#,
        ),
        (
            "cat9_gap_drop_impl_panic_missed",
            r#"pub struct Cat9OverflowOnDrop(pub u32);

impl Drop for Cat9OverflowOnDrop {
    fn drop(&mut self) {
        let _sum: u32 = self.0 + u32::MAX;
    }
}

pub fn cat9_gap_drop_impl_panic_missed() -> u32 {
    let _bomb = Cat9OverflowOnDrop(1u32);
    5u32
}
"#,
        ),
        (
            "cat9_gap_drop_impl_ub_missed",
            r#"pub struct Cat9CtlzOnDrop(pub u32);

impl Drop for Cat9CtlzOnDrop {
    fn drop(&mut self) {
        let _zeros: u32 = unsafe { ctlz_nonzero(self.0 - 1u32) };
    }
}

pub fn cat9_gap_drop_impl_ub_missed() -> u32 {
    let _bomb = Cat9CtlzOnDrop(1u32);
    5u32
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
    // The batch stages every candidate after the shared header and preamble,
    // in order, exactly as `evaluate_miri_batches_with_options` does.
    let mut staged = format!("{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n");
    for cand in &candidates {
        staged.push_str(cand.fn_source.trim());
        staged.push_str("\n\n");
    }

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

    assert_eq!(report.total_candidates, 19);
    assert_eq!(report.compiled_candidates, 19);
    assert_eq!(report.agree_count, 10, "agreements: {:?}", report.item_reports);
    assert_eq!(report.diverge_count, 9, "divergences: {:?}", report.item_reports);
    assert_eq!(report.not_compared_count, 0);
    assert!(witness_polarity_accounting_holds(&report));
    for (slug, expected) in [
        ("unsound_missed_fault", 4usize),
        ("sound_conservative_abstraction", 4),
        ("value_mismatch", 1),
        ("harness_or_extraction_error", 0),
    ] {
        assert_eq!(
            report.witness_polarity_counts.get(slug),
            Some(&expected),
            "witness_polarity_counts[{slug}]: {:?}",
            report.witness_polarity_counts
        );
    }
    assert_eq!(report.findings.len(), 9);
    assert_eq!(report.kernel_confirmed_divergences, 9);
    // With no shrinkable mutator chain, every finding reports its original
    // candidate, so each original item report is itself kernel-confirmed.
    for f in &report.findings {
        assert!(
            report
                .item_reports
                .iter()
                .any(|r| r.name == f.fn_name && r.kernel_confirmed),
            "item report for `{}` must stay kernel-confirmed",
            f.fn_name
        );
        // None of the diverging pins call preamble `helper_*` functions or
        // construct `UnwindCleanupGuard`; `MiriOracleConfirm.lean` must not
        // link helpers or `Drop` impls reachable only from the agreeing
        // candidates in the batch.
        assert!(
            !f.kernel_confirm_theorems.contains("helper_reborrow_")
                && !f.kernel_confirm_theorems.contains("helper_unwind_")
                && !f.kernel_confirm_theorems.contains("UnwindCleanupGuard"),
            "confirm module for `{}` linked unrelated batch helpers:\n{}",
            f.fn_name,
            f.kernel_confirm_theorems
        );
    }
    for f in &report.findings {
        assert!(f.kernel_confirmed, "finding `{}` must be kernel-confirmed", f.fn_name);
        assert_eq!(
            WitnessPolarity::from_str_slug(&f.witness_polarity),
            Some(classify_outcome_tags_polarity(
                &f.miri_outcome_tag,
                &f.anneal_outcome_tag,
                Some(&f.divergence_class),
            ))
            .flatten(),
            "finding `{}` polarity disagrees with its tags",
            f.fn_name
        );
    }

    let item = |name: &str| {
        report
            .item_reports
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing item report `{name}`"))
    };
    for name in [
        "cat9_move_deinit_pass",
        "cat9_fn_entry_chain_pass",
        "cat9_returned_child_pass",
        "cat9_scalar_and_mem_intrinsics_pass",
        "cat9_frozen_reborrow_write_in_callee_ub",
        "cat9_unwind_cleanup_guard_panic",
    ] {
        assert_eq!(item(name).verdict, ComparisonVerdict::Agree, "`{name}` must agree");
    }
    assert!(matches!(item("cat9_frozen_reborrow_write_in_callee_ub").miri, MiriOutcome::Ub { .. }));
    assert!(matches!(item("cat9_unwind_cleanup_guard_panic").miri, MiriOutcome::Panic { .. }));
    assert!(matches!(item("cat9_unwind_cleanup_guard_panic").anneal, AnnealOutcome::Panic { .. }));

    let finding = |name: &str| {
        report
            .findings
            .iter()
            .find(|f| f.fn_name == name)
            .unwrap_or_else(|| panic!("missing finding `{name}`"))
    };
    for name in [
        "cat9_provenance_overwritten_byte_missed_ub",
        "cat9_gap_fn_entry_protector_raw_reborrow_missed_ub",
    ] {
        let unsound = finding(name);
        assert_eq!(unsound.divergence_class, "missed_ub", "`{name}`");
        assert_eq!(unsound.witness_polarity, "unsound_missed_fault", "`{name}`");
        assert!(unsound.kernel_confirmed, "`{name}` must be kernel-confirmed");
    }
    let prot_rep = item("cat9_gap_fn_entry_protector_raw_reborrow_missed_ub");
    let prot_ub_line = cat9_line_of(&staged, "        *alias = 8u32;");
    assert!(
        matches!(
            &prot_rep.miri,
            MiriOutcome::Ub { pos: Some(p), message }
                if p.line == prot_ub_line && message.contains("is forbidden")
        ),
        "expected Miri FnEntry protector UB at line {prot_ub_line}, got {:?}",
        prot_rep.miri
    );
    assert_eq!(
        prot_rep.anneal,
        AnnealOutcome::PassScalar {
            bits: 11,
            size_bytes: 4
        },
        "known Category 9 `FnEntry` protector gap changed (fixed?); update the pin and \
         tests/miri-diff/README.md"
    );

    // Frame-relative pointer resolution agrees with Miri since
    // `DIV-MR-CALL-TARGET-LOCAL` / `DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`: a
    // callee access through a pointer to the caller's `x` reaches `x`, not the
    // callee's local of the same index.
    for (name, bits) in [
        ("cat9_gap_callee_raw_read_wrong_value", 10u128),
        ("cat9_gap_callee_raw_write_wrong_value", 11),
        ("cat9_gap_callee_raw_write_collides_with_ptr_arg", 9),
        ("cat9_gap_callee_deref_ref_arg", 11),
    ] {
        let rep = item(name);
        assert_eq!(rep.verdict, ComparisonVerdict::Agree, "`{name}` must agree");
        assert_eq!(
            (&rep.miri, &rep.anneal),
            (
                &MiriOutcome::PassScalar {
                    bits,
                    size_bytes: 4
                },
                &AnnealOutcome::PassScalar {
                    bits,
                    size_bytes: 4
                }
            ),
            "fixed Category 9 frame-relative pointer case `{name}` regressed; see \
             tests/miri-diff/README.md"
        );
    }

    // Each conservative pin is a Miri pass and an Anneal UB at exactly the
    // documented statement.
    for (name, miri_bits, ub_marker) in [
        ("cat9_in_scope_move_raw_read_conservative", 30u128, "let leaked: u32 = unsafe { *raw };"),
        ("cat9_gap_callee_raw_write_with_caller_borrow", 10, "        *alias = 7u32;"),
        ("cat9_gap_post_return_raw_write_after_ref_arg", 10, "        *raw = 7u32 + seen;"),
        ("cat9_gap_raw_write_after_unused_shared_borrow", 11, "        *raw = 11u32;"),
    ] {
        let f = finding(name);
        assert_eq!(f.divergence_class, "false_positive_ub", "`{name}`");
        assert_eq!(f.witness_polarity, "sound_conservative_abstraction", "`{name}`");
        let rep = item(name);
        assert_eq!(
            rep.miri,
            MiriOutcome::PassScalar {
                bits: miri_bits,
                size_bytes: 4
            },
            "`{name}` Miri outcome changed"
        );
        let expected_line = cat9_line_of(&staged, ub_marker);
        assert!(
            matches!(&rep.anneal, AnnealOutcome::Ub { span: Some(s) } if s.start_line == expected_line),
            "known Category 9 engine gap `{name}` changed (fixed?): expected Anneal UB at \
             staged line {expected_line} (`{}`), got {:?}; update the pin and \
             tests/miri-diff/README.md",
            ub_marker.trim(),
            rep.anneal
        );
    }

    // Anneal never runs a user `Drop` impl: its `.drop` terminator only
    // de-initializes the dropped place, so the side effect, panic, and UB of a
    // `Drop::drop` body are all invisible to it.
    let skipped = item("cat9_gap_drop_impl_side_effect_skipped");
    assert_eq!(
        finding("cat9_gap_drop_impl_side_effect_skipped").divergence_class,
        "wrong_value"
    );
    assert_eq!(
        finding("cat9_gap_drop_impl_side_effect_skipped").witness_polarity,
        "value_mismatch"
    );
    assert_eq!(
        (&skipped.miri, &skipped.anneal),
        (
            &MiriOutcome::PassScalar {
                bits: 7,
                size_bytes: 4
            },
            &AnnealOutcome::PassScalar {
                bits: 1,
                size_bytes: 4
            }
        ),
        "known Category 9 `Drop` gap changed (fixed?); update the pin and tests/miri-diff/README.md"
    );
    for (name, class, fault_marker) in [
        (
            "cat9_gap_drop_impl_panic_missed",
            "panic_vs_return",
            "        let _sum: u32 = self.0 + u32::MAX;",
        ),
        (
            "cat9_gap_drop_impl_ub_missed",
            "missed_ub",
            "        let _zeros: u32 = unsafe { ctlz_nonzero(self.0 - 1u32) };",
        ),
    ] {
        let f = finding(name);
        assert_eq!(f.divergence_class, class, "`{name}`");
        assert_eq!(f.witness_polarity, "unsound_missed_fault", "`{name}`");
        let rep = item(name);
        let fault_line = cat9_line_of(&staged, fault_marker);
        let miri_line = match &rep.miri {
            MiriOutcome::Panic { pos: Some(p), .. } if class == "panic_vs_return" => p.line,
            MiriOutcome::Ub { pos: Some(p), .. } if class == "missed_ub" => p.line,
            other => panic!("`{name}`: unexpected Miri outcome {other:?}"),
        };
        assert_eq!(
            miri_line, fault_line,
            "`{name}`: Miri must fault inside `Drop::drop`"
        );
        assert_eq!(
            rep.anneal,
            AnnealOutcome::PassScalar {
                bits: 5,
                size_bytes: 4
            },
            "known Category 9 `Drop` gap `{name}` changed (fixed?); update the pin and \
             tests/miri-diff/README.md"
        );
    }
}

/// 1-based line of the first line of `staged` that contains `needle` and follows
/// the unique line that contains `header`.
fn c16_line_after(staged: &str, header: &str, needle: &str) -> u32 {
    let start = cat9_line_of(staged, header) as usize;
    staged
        .lines()
        .enumerate()
        .skip(start)
        .find_map(|(i, l)| l.contains(needle).then_some(i as u32 + 1))
        .unwrap_or_else(|| panic!("`{needle}` must follow `{header}` in the staged crate"))
}

/// Source of the corpus function `name` (attributes and doc comments dropped),
/// renamed to `renamed`, so a candidate can run a corpus body in the root frame.
fn c16_corpus_fn_renamed(name: &str, renamed: &str) -> String {
    let file = syn::parse_file(RAW_MIRI_DIFF_CORPUS_RS).expect("corpus parses");
    let mut func = file
        .items
        .into_iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == name => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("tests/miri-diff/corpus/src/lib.rs must define `{name}`"));
    func.attrs.clear();
    func.sig.ident = syn::Ident::new(renamed, func.sig.ident.span());
    prettyplease::unparse(&syn::File {
        shebang: None,
        attrs: Vec::new(),
        items: vec![syn::Item::Fn(func)],
    })
}

/// Campaign #16 same-tag disjoint `copy_nonoverlapping` probes, the static-access
/// probes, and their local twins (Category 11 of `tests/miri-diff/corpus`), run
/// live against Miri.
///
/// Miri's verdict is pinned exactly. Each Anneal gap is pinned to exactly two
/// states (a ratchet: any third state, such as an unsound missed fault, a
/// different value, a fault at a different statement, `NotCompared`, or a
/// compile failure, fails this test):
/// - the documented gap, kernel-confirmed, with Anneal's UB at exactly the
///   documented statement, or
/// - agreement with Miri, once Anneal is fixed.
///
/// Gaps (see "Category 11 engine gaps" in `tests/miri-diff/README.md`):
/// - `pass_copy_nonoverlapping_same_tag_disjoint_{array_halves,struct_fields}`
///   (called as intra-crate callees, and run in the root frame as renamed
///   copies): `false_positive_ub` (`sound_conservative_abstraction`) at the
///   `copy_nonoverlapping`, because `Statements.lean` checks
///   `Nat.beq srcPtr.tag dstPtr.tag` before it compares the copied ranges.
/// - `pass_static_const_raw_ptr_read_and_freeze_retag`: `false_positive_ub` at
///   the first access to the `static` (Anneal reports UB at every access to a
///   `static`, reads included).
/// - `ub_static_unsafe_cell_raw_const_cast_mut_write` and the immutable-static
///   write control: Miri reports UB at the write, and Anneal reports UB earlier,
///   at the first access to the `static` (`ub_location_mismatch`,
///   `value_mismatch`): never a pass.
/// - `c16_gap_unsafe_cell_field_write_through_shared_temp`: a write to the
///   `UnsafeCell` field of a local through a shared reborrow of the containing
///   struct, which Miri allows, is UB in Anneal (`false_positive_ub`). It is the
///   local twin of the `cell` write of the static UB probe, which therefore
///   agrees only once both gaps are fixed.
///
/// Controls that must agree now: a true same-tag overlap (UB at the copy, so the
/// copy pins cannot pass by dropping the overlap check), and the two Category
/// 11 manifest seeds (the local twins of the static probes).
#[test]
fn campaign16_same_tag_disjoint_copy_and_static_retag_probes_verify_live() {
    let dir = unique_temp_dir("campaign16");
    let findings_dir = dir.join("findings");
    let root = repo_root();

    let seed_source = |name: &str| -> String {
        load_miri_diff_corpus_seeds()
            .into_iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("missing Category 11 manifest seed `{name}`"))
            .fn_source
    };
    let named_sources: Vec<(String, String)> = vec![
        (
            "c16_call_array_halves".to_string(),
            "pub fn c16_call_array_halves() -> u32 {\n    \
             pass_copy_nonoverlapping_same_tag_disjoint_array_halves()\n}\n"
                .to_string(),
        ),
        (
            "c16_call_u8_array_halves".to_string(),
            "pub fn c16_call_u8_array_halves() -> u32 {\n    \
             pass_copy_nonoverlapping_same_tag_disjoint_u8_array_halves()\n}\n"
                .to_string(),
        ),
        (
            "c16_call_struct_fields".to_string(),
            "pub fn c16_call_struct_fields() -> u32 {\n    \
             pass_copy_nonoverlapping_same_tag_disjoint_struct_fields()\n}\n"
                .to_string(),
        ),
        (
            "c16_root_array_halves".to_string(),
            c16_corpus_fn_renamed(
                "pass_copy_nonoverlapping_same_tag_disjoint_array_halves",
                "c16_root_array_halves",
            ),
        ),
        (
            "c16_root_u8_array_halves".to_string(),
            c16_corpus_fn_renamed(
                "pass_copy_nonoverlapping_same_tag_disjoint_u8_array_halves",
                "c16_root_u8_array_halves",
            ),
        ),
        (
            "c16_root_struct_fields".to_string(),
            c16_corpus_fn_renamed(
                "pass_copy_nonoverlapping_same_tag_disjoint_struct_fields",
                "c16_root_struct_fields",
            ),
        ),
        (
            "c16_reverse_u8_array_halves".to_string(),
            r#"pub fn c16_reverse_u8_array_halves() -> u32 {
    let mut arr: [u8; 8] = [3u8, 5u8, 9u8, 17u8, 33u8, 65u8, 129u8, 250u8];
    let p: *mut u8 = (&raw mut arr) as *mut u8;
    unsafe {
        let src: *const u8 = offset(p, 4isize) as *const u8;
        copy_nonoverlapping(src, p, 4usize);
    }
    (arr[0] as u32)
        | ((arr[1] as u32) << 8u32)
        | ((arr[2] as u32) << 16u32)
        | ((arr[3] as u32) << 24u32)
}
"#
            .to_string(),
        ),
        (
            "c16_reverse_u32_array_halves".to_string(),
            r#"pub fn c16_reverse_u32_array_halves() -> u32 {
    let mut arr: [u32; 4] = [10u32, 20u32, 30u32, 40u32];
    let p: *mut u32 = &raw mut arr[0];
    unsafe {
        let src: *const u32 = offset(p, 2isize) as *const u32;
        copy_nonoverlapping(src, p, 2usize);
    }
    (arr[0] << 8u32) ^ arr[1]
}
"#
            .to_string(),
        ),
        (
            "c16_whole_struct_cast_fields".to_string(),
            r#"pub fn c16_whole_struct_cast_fields() -> u32 {
    let mut pair: PairU32 = PairU32 { a: 44u32, b: 33u32 };
    let p: *mut u32 = (&raw mut pair) as *mut u32;
    unsafe {
        let dst: *mut u32 = offset(p, 1isize);
        copy_nonoverlapping(p as *const u32, dst, 1usize);
    }
    (pair.a << 8u32) ^ pair.b
}
"#
            .to_string(),
        ),
        (
            "c16_reverse_struct_fields".to_string(),
            r#"pub fn c16_reverse_struct_fields() -> u32 {
    let mut pair: PairU32 = PairU32 { a: 44u32, b: 33u32 };
    let p: *mut u32 = &raw mut pair.a;
    unsafe {
        let src: *const u32 = offset(p, 1isize) as *const u32;
        copy_nonoverlapping(src, p, 1usize);
    }
    (pair.a << 8u32) ^ pair.b
}
"#
            .to_string(),
        ),
        (
            "c16_zero_count_u32_same_tag_copy".to_string(),
            r#"pub fn c16_zero_count_u32_same_tag_copy() -> u32 {
    let mut arr: [u32; 4] = [10u32, 20u32, 30u32, 40u32];
    let p: *mut u32 = &raw mut arr[0];
    unsafe {
        copy_nonoverlapping(p as *const u32, p, 0usize);
    }
    arr[0] + arr[3]
}
"#
            .to_string(),
        ),
        (
            "c16_zero_count_u8_same_tag_copy".to_string(),
            r#"pub fn c16_zero_count_u8_same_tag_copy() -> u32 {
    let mut arr: [u8; 8] = [3u8, 5u8, 9u8, 17u8, 33u8, 65u8, 129u8, 250u8];
    let p: *mut u8 = (&raw mut arr) as *mut u8;
    unsafe {
        copy_nonoverlapping(p as *const u8, p, 0usize);
    }
    (arr[0] as u32) + (arr[3] as u32) + 2u32
}
"#
            .to_string(),
        ),
        (
            "c16_zst_unit_single_direct_same_tag_copy".to_string(),
            r#"pub fn c16_zst_unit_single_direct_same_tag_copy() -> u32 {
    let mut z: () = ();
    let p: *mut () = &raw mut z;
    unsafe {
        copy_nonoverlapping(p as *const (), p, 1usize);
    }
    77u32
}
"#
            .to_string(),
        ),
        (
            "c16_union_same_tag_disjoint_bytes_agree".to_string(),
            r#"pub fn c16_union_same_tag_disjoint_bytes_agree() -> u32 {
    let mut u: OverlayU32 = OverlayU32 {
        bytes: [3u8, 5u8, 9u8, 17u8],
    };
    let p: *mut u8 = (&raw mut u.bytes) as *mut u8;
    unsafe {
        let dst: *mut u8 = offset(p, 2isize);
        copy_nonoverlapping(p as *const u8, dst, 2usize);
        u.word
    }
}
"#
            .to_string(),
        ),
        (
            "c16_same_tag_overlap_control".to_string(),
            r#"pub fn c16_same_tag_overlap_control() -> u32 {
    let mut arr: [u32; 4] = [10u32, 20u32, 30u32, 40u32];
    let p: *mut u32 = &raw mut arr[0];
    unsafe {
        let dst: *mut u32 = offset(p, 1isize);
        copy_nonoverlapping(p as *const u32, dst, 2usize);
    }
    arr[2]
}
"#
            .to_string(),
        ),
        (
            "c16_same_tag_u8_overlap_control".to_string(),
            r#"pub fn c16_same_tag_u8_overlap_control() -> u32 {
    let mut arr: [u8; 8] = [1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8];
    let p: *mut u8 = (&raw mut arr) as *mut u8;
    unsafe {
        let dst: *mut u8 = offset(p, 2isize);
        copy_nonoverlapping(p as *const u8, dst, 4usize);
    }
    arr[2] as u32
}
"#
            .to_string(),
        ),
        (
            "c16_call_static_freeze_read".to_string(),
            "pub fn c16_call_static_freeze_read() -> u32 {\n    \
             pass_static_const_raw_ptr_read_and_freeze_retag()\n}\n"
                .to_string(),
        ),
        (
            "c16_static_unsafe_cell_only_write".to_string(),
            r#"pub fn c16_static_unsafe_cell_only_write() -> u32 {
    let cell: *mut u32 = (&raw const STATIC_FREEZE_AND_CELL.cell) as *const u32 as *mut u32;
    unsafe {
        *cell = 21u32;
        (*cell << 8u32) ^ STATIC_FREEZE_AND_CELL.frozen
    }
}
"#
            .to_string(),
        ),
        (
            "c16_call_static_cell_then_frozen_write".to_string(),
            "pub fn c16_call_static_cell_then_frozen_write() -> u32 {\n    \
             ub_static_unsafe_cell_raw_const_cast_mut_write()\n}\n"
                .to_string(),
        ),
        (
            "c16_static_freeze_and_cell_frozen_only_write".to_string(),
            r#"pub fn c16_static_freeze_and_cell_frozen_only_write() -> u32 {
    let frozen: *mut u32 = (&raw const STATIC_FREEZE_AND_CELL.frozen) as *mut u32;
    unsafe {
        *frozen = 21u32;
        *frozen
    }
}
"#
            .to_string(),
        ),
        (
            "c16_immutable_static_mut_write_control".to_string(),
            r#"pub fn c16_immutable_static_mut_write_control() -> u32 {
    let p: *mut u32 = (&raw const STATIC_FROZEN_PAIR.a) as *mut u32;
    unsafe {
        *p = 9u32;
        *p
    }
}
"#
            .to_string(),
        ),
        (
            "c16_gap_unsafe_cell_field_write_through_shared_temp".to_string(),
            r#"pub fn c16_gap_unsafe_cell_field_write_through_shared_temp() -> u32 {
    let local: FreezeAndCell = FreezeAndCell {
        frozen: 3u32,
        cell: unsafe { transmute::<u32, UnsafeCell<u32>>(12u32) },
    };
    let tmp: &FreezeAndCell = &local;
    let cell: *mut u32 = (&raw const (*tmp).cell) as *const u32 as *mut u32;
    unsafe {
        *cell = 21u32;
    }
    let frozen: *const u32 = &raw const (*tmp).frozen;
    unsafe { (*cell << 8u32) ^ *frozen }
}
"#
            .to_string(),
        ),
        (
            "pass_shared_temp_const_raw_ptr_read_and_freeze_retag".to_string(),
            seed_source("pass_shared_temp_const_raw_ptr_read_and_freeze_retag"),
        ),
        (
            "ub_shared_temp_unsafe_cell_raw_const_cast_mut_write".to_string(),
            seed_source("ub_shared_temp_unsafe_cell_raw_const_cast_mut_write"),
        ),
    ];
    let total_expected = named_sources.len();
    assert_eq!(total_expected, 24);
    let candidates: Vec<GeneratedMiriCandidate> = named_sources
        .iter()
        .enumerate()
        .map(|(id, (name, fn_src))| GeneratedMiriCandidate {
            id,
            seed_index: id,
            seed_name: name.clone(),
            fn_name: name.clone(),
            seed_u64: id as u64,
            applied_mutators: Vec::new(),
            tracked_locals: Vec::new(),
            fn_source: fn_src.clone(),
            source: build_standalone_candidate_source(fn_src),
        })
        .collect();
    // The batch stages every candidate after the shared header and preamble,
    // in order, exactly as `evaluate_miri_batches_with_options` does.
    let mut staged = format!("{MIRI_CORPUS_CRATE_HEADER}\n{MIRI_CORPUS_MODULE_PREAMBLE}\n");
    for cand in &candidates {
        staged.push_str(cand.fn_source.trim());
        staged.push_str("\n\n");
    }

    let options = MiriEvalOptions {
        findings_dir: Some(findings_dir.clone()),
        anneal_repo_root: Some(root.clone()),
        shrink_seeds: None,
    };
    let report = evaluate_miri_batches_with_options(
        "seeded",
        0xC16_0001,
        std::slice::from_ref(&candidates),
        candidates.len(),
        &options,
    )
    .expect("evaluate Campaign #16 / Category 11 live batch");
    assert_eq!(report.total_candidates, total_expected);
    assert_eq!(
        report.compiled_candidates, total_expected,
        "{:?}",
        report.item_reports
    );
    assert_eq!(report.not_compared_count, 0, "{:?}", report.item_reports);
    assert!(witness_polarity_accounting_holds(&report));

    let item = |name: &str| {
        report
            .item_reports
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing item report `{name}`"))
    };
    let polarity = |name: &str| {
        let rep = item(name);
        classify_verdict_witness_polarity(&rep.miri, &rep.anneal, &rep.verdict)
    };
    let mut conservative_gaps = 0usize;
    let mut location_gaps = 0usize;

    // Same-tag disjoint copies across `copyViaBytes` (`&raw mut arr[0]` / `&raw mut
    // pair.a`), `sameContainer` (`(&raw mut arr) as *mut u8` on `[u8; 8]`),
    // whole-struct casts, and both forward (`src < dst`) and backward (`dst < src`)
    // directions: Miri returns the copied value; Anneal reports UB at the
    // `copy_nonoverlapping` or, once fixed, agrees.
    let probe_header = |probe: &str| format!("pub fn {probe}() -> u32 {{");
    for (name, header, bits, copy) in [
        (
            "c16_call_array_halves",
            probe_header("pass_copy_nonoverlapping_same_tag_disjoint_array_halves"),
            30u128,
            "copy_nonoverlapping(p as *const u32, dst, 2usize);",
        ),
        (
            "c16_call_u8_array_halves",
            probe_header("pass_copy_nonoverlapping_same_tag_disjoint_u8_array_halves"),
            285_803_779,
            "copy_nonoverlapping(p as *const u8, dst, 4usize);",
        ),
        (
            "c16_call_struct_fields",
            probe_header("pass_copy_nonoverlapping_same_tag_disjoint_struct_fields"),
            44,
            "copy_nonoverlapping(p as *const u32, dst, 1usize);",
        ),
        (
            "c16_root_array_halves",
            probe_header("c16_root_array_halves"),
            30,
            "copy_nonoverlapping(p as *const u32, dst, 2usize);",
        ),
        (
            "c16_root_u8_array_halves",
            probe_header("c16_root_u8_array_halves"),
            285_803_779,
            "copy_nonoverlapping(p as *const u8, dst, 4usize);",
        ),
        (
            "c16_root_struct_fields",
            probe_header("c16_root_struct_fields"),
            44,
            "copy_nonoverlapping(p as *const u32, dst, 1usize);",
        ),
        (
            "c16_reverse_u8_array_halves",
            probe_header("c16_reverse_u8_array_halves"),
            0xFA81_4121,
            "copy_nonoverlapping(src, p, 4usize);",
        ),
        (
            "c16_reverse_u32_array_halves",
            probe_header("c16_reverse_u32_array_halves"),
            7720,
            "copy_nonoverlapping(src, p, 2usize);",
        ),
        (
            "c16_whole_struct_cast_fields",
            probe_header("c16_whole_struct_cast_fields"),
            11308,
            "copy_nonoverlapping(p as *const u32, dst, 1usize);",
        ),
        (
            "c16_reverse_struct_fields",
            probe_header("c16_reverse_struct_fields"),
            8481,
            "copy_nonoverlapping(src, p, 1usize);",
        ),
        (
            "c16_zero_count_u32_same_tag_copy",
            probe_header("c16_zero_count_u32_same_tag_copy"),
            50,
            "copy_nonoverlapping(p as *const u32, p, 0usize);",
        ),
        (
            "c16_zero_count_u8_same_tag_copy",
            probe_header("c16_zero_count_u8_same_tag_copy"),
            22,
            "copy_nonoverlapping(p as *const u8, p, 0usize);",
        ),
        (
            "c16_zst_unit_single_direct_same_tag_copy",
            probe_header("c16_zst_unit_single_direct_same_tag_copy"),
            77,
            "copy_nonoverlapping(p as *const (), p, 1usize);",
        ),
    ] {
        let rep = item(name);
        assert_eq!(
            rep.miri,
            MiriOutcome::PassScalar {
                bits,
                size_bytes: 4
            },
            "`{name}`: Miri must return the copied value"
        );
        let copy_line = c16_line_after(&staged, &header, copy);
        match (&rep.anneal, polarity(name)) {
            (
                AnnealOutcome::Ub { span: Some(s) },
                Some(WitnessPolarity::SoundConservativeAbstraction),
            ) if s.start_line == copy_line
                && matches!(
                    rep.verdict,
                    ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
                )
                && rep.kernel_confirmed =>
            {
                conservative_gaps += 1;
            }
            (
                AnnealOutcome::PassScalar {
                    bits: b,
                    size_bytes: 4,
                },
                None,
            ) if *b == bits && rep.verdict == ComparisonVerdict::Agree => {}
            (anneal, pol) => panic!(
                "`{name}` left both pinned states: expected Anneal UB at staged line \
                 {copy_line} (`{copy}`, false_positive_ub, kernel-confirmed) or agreement \
                 on `{bits}`, got anneal={anneal:?} verdict={:?} polarity={pol:?} \
                 kernel_confirmed={}; update the pin and tests/miri-diff/README.md",
                rep.verdict, rep.kernel_confirmed
            ),
        }
    }

    // True same-tag overlaps on both `[u32; 4]` (`copyViaBytes`) and `[u8; 8]`
    // (`sameContainer`) must stay UB at the copy in both Miri and Anneal, so the
    // pins above cannot hold because Anneal stopped checking overlap.
    for (ctrl_name, copy_stmt) in [
        (
            "c16_same_tag_overlap_control",
            "copy_nonoverlapping(p as *const u32, dst, 2usize);",
        ),
        (
            "c16_same_tag_u8_overlap_control",
            "copy_nonoverlapping(p as *const u8, dst, 4usize);",
        ),
    ] {
        let overlap = item(ctrl_name);
        let overlap_line = c16_line_after(&staged, &probe_header(ctrl_name), copy_stmt);
        assert_eq!(overlap.verdict, ComparisonVerdict::Agree, "{overlap:?}");
        assert!(
            matches!(&overlap.miri, MiriOutcome::Ub { pos: Some(p), message }
                if p.line == overlap_line && message.contains("overlapping"))
                && matches!(&overlap.anneal, AnnealOutcome::Ub { span: Some(s) }
                    if s.start_line == overlap_line),
            "`{ctrl_name}` must be UB at staged line {overlap_line} in both: \
             miri={:?} anneal={:?}",
            overlap.miri,
            overlap.anneal
        );
    }

    // Union (`OverlayU32`) same-tag disjoint byte copy routes through
    // `Statements.lean`'s `evalCopyUnionBytes` (`rangesDisjoint`) and already
    // agrees live (`[3, 5, 3, 5]` -> `0x0503_0503 = 84_083_971`).
    let union_copy = item("c16_union_same_tag_disjoint_bytes_agree");
    assert_eq!(
        union_copy.verdict,
        ComparisonVerdict::Agree,
        "{union_copy:?}"
    );
    assert_eq!(
        (&union_copy.miri, &union_copy.anneal),
        (
            &MiriOutcome::PassScalar {
                bits: 0x0503_0503,
                size_bytes: 4
            },
            &AnnealOutcome::PassScalar {
                bits: 0x0503_0503,
                size_bytes: 4
            }
        )
    );

    // Static reads, isolated static `UnsafeCell` writes, and the local
    // `UnsafeCell` field write: Miri returns normally; Anneal reports UB at one
    // of the documented conservative gap statements or, once fixed, agrees.
    let static_read_line = c16_line_after(
        &staged,
        &probe_header("pass_static_const_raw_ptr_read_and_freeze_retag"),
        "let raw: *const u32 = &raw const STATIC_FROZEN_PAIR.b;",
    );
    let static_cell_only_access_line = c16_line_after(
        &staged,
        &probe_header("c16_static_unsafe_cell_only_write"),
        "let cell: *mut u32 = (&raw const STATIC_FREEZE_AND_CELL.cell)",
    );
    let static_cell_only_write_line = c16_line_after(
        &staged,
        &probe_header("c16_static_unsafe_cell_only_write"),
        "*cell = 21u32;",
    );
    let local_cell_write_line = c16_line_after(
        &staged,
        &probe_header("c16_gap_unsafe_cell_field_write_through_shared_temp"),
        "*cell = 21u32;",
    );
    for (name, bits, allowed_gap_lines) in [
        (
            "c16_call_static_freeze_read",
            8996u128,
            vec![static_read_line],
        ),
        (
            "c16_static_unsafe_cell_only_write",
            5379,
            vec![static_cell_only_access_line, static_cell_only_write_line],
        ),
        (
            "c16_gap_unsafe_cell_field_write_through_shared_temp",
            5379,
            vec![local_cell_write_line],
        ),
    ] {
        let rep = item(name);
        assert_eq!(
            rep.miri,
            MiriOutcome::PassScalar {
                bits,
                size_bytes: 4
            },
            "`{name}`: Miri outcome changed"
        );
        match (&rep.anneal, polarity(name)) {
            (
                AnnealOutcome::Ub { span: Some(s) },
                Some(WitnessPolarity::SoundConservativeAbstraction),
            ) if allowed_gap_lines.contains(&s.start_line)
                && matches!(
                    rep.verdict,
                    ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
                )
                && rep.kernel_confirmed =>
            {
                conservative_gaps += 1;
            }
            (
                AnnealOutcome::PassScalar {
                    bits: b,
                    size_bytes: 4,
                },
                None,
            ) if *b == bits && rep.verdict == ComparisonVerdict::Agree => {}
            (anneal, pol) => panic!(
                "`{name}` left its pinned states: expected Anneal UB at one of staged \
                 lines {allowed_gap_lines:?} (false_positive_ub, kernel-confirmed) or \
                 agreement on `{bits}`, got anneal={anneal:?} verdict={:?} polarity={pol:?} \
                 kernel_confirmed={}; update the pin and tests/miri-diff/README.md",
                rep.verdict, rep.kernel_confirmed
            ),
        }
    }

    // Static writes: Miri reports UB at the write (frozen bytes of the
    // interior-mutable static, or the read-only immutable static). Anneal must
    // report UB too, never a pass: today at the first access to the `static`
    // (or at `*cell = 21u32;` in the compound probe if static access is fixed
    // before the `UnsafeCell`-field shared-reborrow gap), and once fixed at the
    // write itself.
    let cell_probe = probe_header("ub_static_unsafe_cell_raw_const_cast_mut_write");
    let frozen_only_probe = probe_header("c16_static_freeze_and_cell_frozen_only_write");
    let immutable = probe_header("c16_immutable_static_mut_write_control");
    let cell_probe_cell_write =
        c16_line_after(&staged, cell_probe.as_str(), "*cell = 21u32;");
    for (name, header, first_access, extra_pre_write_gap, write, miri_message) in [
        (
            "c16_call_static_cell_then_frozen_write",
            cell_probe.as_str(),
            "let cell: *mut u32 = (&raw const STATIC_FREEZE_AND_CELL.cell)",
            Some(cell_probe_cell_write),
            "*frozen = *cell;",
            "is forbidden",
        ),
        (
            "c16_static_freeze_and_cell_frozen_only_write",
            frozen_only_probe.as_str(),
            "let frozen: *mut u32 = (&raw const STATIC_FREEZE_AND_CELL.frozen) as *mut u32;",
            None,
            "*frozen = 21u32;",
            "is forbidden",
        ),
        (
            "c16_immutable_static_mut_write_control",
            immutable.as_str(),
            "let p: *mut u32 = (&raw const STATIC_FROZEN_PAIR.a) as *mut u32;",
            None,
            "*p = 9u32;",
            "read-only",
        ),
    ] {
        let rep = item(name);
        let access_line = c16_line_after(&staged, header, first_access);
        let write_line = c16_line_after(&staged, header, write);
        assert!(
            matches!(&rep.miri, MiriOutcome::Ub { pos: Some(p), message }
                if p.line == write_line && message.contains(miri_message)),
            "`{name}`: expected Miri UB (`{miri_message}`) at staged line {write_line}, got {:?}",
            rep.miri
        );
        match (&rep.anneal, polarity(name)) {
            (AnnealOutcome::Ub { span: Some(s) }, Some(WitnessPolarity::ValueMismatch))
                if (s.start_line == access_line
                    || extra_pre_write_gap == Some(s.start_line))
                    && matches!(
                        rep.verdict,
                        ComparisonVerdict::Diverge(DivergenceKind::UbLocationMismatch { .. })
                    )
                    && rep.kernel_confirmed =>
            {
                location_gaps += 1;
            }
            (AnnealOutcome::Ub { span: Some(s) }, None)
                if s.start_line == write_line && rep.verdict == ComparisonVerdict::Agree => {}
            (anneal, pol) => panic!(
                "`{name}` left its pinned states: expected Anneal UB at staged line \
                 {access_line} (or {extra_pre_write_gap:?}, ub_location_mismatch, \
                 kernel-confirmed) or agreement at line {write_line}, got anneal={anneal:?} \
                 verdict={:?} polarity={pol:?} kernel_confirmed={}; update the pin and \
                 tests/miri-diff/README.md",
                rep.verdict, rep.kernel_confirmed
            ),
        }
    }

    // The Category 11 manifest seeds (local twins of the static probes) agree.
    let twin_read = item("pass_shared_temp_const_raw_ptr_read_and_freeze_retag");
    assert_eq!(twin_read.verdict, ComparisonVerdict::Agree, "{twin_read:?}");
    assert_eq!(
        (&twin_read.miri, &twin_read.anneal),
        (
            &MiriOutcome::PassScalar {
                bits: 8996,
                size_bytes: 4
            },
            &AnnealOutcome::PassScalar {
                bits: 8996,
                size_bytes: 4
            }
        )
    );
    let twin_write = item("ub_shared_temp_unsafe_cell_raw_const_cast_mut_write");
    let twin_write_line = c16_line_after(
        &staged,
        &probe_header("ub_shared_temp_unsafe_cell_raw_const_cast_mut_write"),
        "*frozen = 21u32;",
    );
    assert_eq!(
        twin_write.verdict,
        ComparisonVerdict::Agree,
        "{twin_write:?}"
    );
    assert!(
        matches!(&twin_write.miri, MiriOutcome::Ub { pos: Some(p), message }
            if p.line == twin_write_line && message.contains("is forbidden"))
            && matches!(&twin_write.anneal, AnnealOutcome::Ub { span: Some(s) }
                if s.start_line == twin_write_line),
        "the frozen-field write twin must be UB at staged line {twin_write_line} in both: \
         miri={:?} anneal={:?}",
        twin_write.miri,
        twin_write.anneal
    );

    // Batch accounting: exactly the pinned gaps diverge, all kernel-confirmed,
    // and none is an unsound missed fault.
    let gaps = conservative_gaps + location_gaps;
    eprintln!(
        "Campaign #16 / Category 11 pins: {conservative_gaps} sound_conservative_abstraction \
         gaps, {location_gaps} ub_location_mismatch gaps, {} agreements",
        report.agree_count
    );
    assert_eq!(report.diverge_count, gaps, "{:?}", report.item_reports);
    assert_eq!(
        report.agree_count,
        total_expected - gaps,
        "{:?}",
        report.item_reports
    );
    assert_eq!(report.kernel_confirmed_divergences, gaps);
    for (slug, expected) in [
        ("unsound_missed_fault", 0usize),
        ("sound_conservative_abstraction", conservative_gaps),
        ("value_mismatch", location_gaps),
        ("harness_or_extraction_error", 0),
    ] {
        assert_eq!(
            report.witness_polarity_counts.get(slug),
            Some(&expected),
            "witness_polarity_counts[{slug}]: {:?}",
            report.witness_polarity_counts
        );
    }
    assert_eq!(report.findings.len(), gaps);
    for f in &report.findings {
        assert!(
            f.kernel_confirmed,
            "finding `{}` must be kernel-confirmed",
            f.fn_name
        );
        assert_eq!(
            WitnessPolarity::from_str_slug(&f.witness_polarity),
            classify_outcome_tags_polarity(
                &f.miri_outcome_tag,
                &f.anneal_outcome_tag,
                Some(&f.divergence_class),
            ),
            "finding `{}` polarity disagrees with its tags",
            f.fn_name
        );
        let repro = f
            .repro_path
            .as_ref()
            .expect("each finding bundle must record repro_path");
        assert!(repro.is_file(), "missing repro.rs at {}", repro.display());
        assert!(
            repro.with_file_name("finding.json").is_file()
                && repro.with_file_name("SUMMARY.md").is_file(),
            "incomplete finding bundle for `{}`",
            f.fn_name
        );
        // Callee-reachability isolation in chunked `MiriOracleConfirm.lean`:
        // unreached Category 9 helpers/Drop impls are never linked in any chunk,
        // and each callee-wrapper finding links its called Category 11 model
        // probe in its confirm chunk.
        for unrelated in [
            "helper_reborrow_",
            "helper_shared_",
            "helper_frozen_",
            "helper_unwind_",
            "UnwindCleanupGuard",
        ] {
            assert!(
                !f.kernel_confirm_theorems.contains(unrelated),
                "confirm module for `{}` linked unrelated Category 9 helper `{unrelated}`:\n{}",
                f.fn_name,
                f.kernel_confirm_theorems
            );
        }
        let own_probe = match f.fn_name.as_str() {
            "c16_call_array_halves" => {
                Some("pass_copy_nonoverlapping_same_tag_disjoint_array_halves")
            }
            "c16_call_u8_array_halves" => {
                Some("pass_copy_nonoverlapping_same_tag_disjoint_u8_array_halves")
            }
            "c16_call_struct_fields" => {
                Some("pass_copy_nonoverlapping_same_tag_disjoint_struct_fields")
            }
            "c16_call_static_freeze_read" => {
                Some("pass_static_const_raw_ptr_read_and_freeze_retag")
            }
            "c16_call_static_cell_then_frozen_write" => {
                Some("ub_static_unsafe_cell_raw_const_cast_mut_write")
            }
            _ => None,
        };
        if let Some(probe) = own_probe {
            assert!(
                f.kernel_confirm_theorems.contains(probe),
                "confirm chunk for `{}` failed to link its called model probe `{probe}`:\n{}",
                f.fn_name,
                f.kernel_confirm_theorems
            );
        }
    }

    // Round-trip `reproduce_miri_finding` (`--reproduce`) on both:
    // 1. a generated finding bundle whose UB span lies inside a preamble model
    //    probe (`c16_call_u8_array_halves`, when still open), and
    // 2. a standalone minimal reproducer reusing a Category 11 probe name
    //    (`pass_copy_nonoverlapping_same_tag_disjoint_array_halves`) WITHOUT any
    //    `__ANNEAL_MODEL_*` marker.
    if let Some(u8_finding) = report
        .findings
        .iter()
        .find(|f| f.fn_name == "c16_call_u8_array_halves")
    {
        let repro_path = u8_finding.repro_path.as_deref().unwrap();
        let repro_src = fs::read_to_string(repro_path).expect("read finding repro.rs");
        let expected_repro_ub_line = c16_line_after(
            &repro_src,
            &probe_header("pass_copy_nonoverlapping_same_tag_disjoint_u8_array_halves"),
            "copy_nonoverlapping(p as *const u8, dst, 4usize);",
        );
        let repro_rep = reproduce_miri_finding(repro_path, Some(&root))
            .expect("reproduce_miri_finding on preamble-callee finding bundle");
        assert_eq!(repro_rep.name, "c16_call_u8_array_halves");
        assert_eq!(
            repro_rep.miri,
            MiriOutcome::PassScalar {
                bits: 285_803_779,
                size_bytes: 4
            }
        );
        assert!(
            matches!(
                repro_rep.verdict,
                ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
            ),
            "unexpected verdict on finding repro: {repro_rep:?}"
        );
        assert!(
            matches!(
                &repro_rep.anneal,
                AnnealOutcome::Ub { span: Some(s) } if s.start_line == expected_repro_ub_line
            ),
            "expected Anneal UB at repro.rs line {expected_repro_ub_line}, got {:?}",
            repro_rep.anneal
        );
        assert_eq!(
            repro_rep.anneal.summary_tag(),
            u8_finding.anneal_outcome_tag
        );
        assert!(repro_rep.kernel_confirmed);
    }

    let minimal_repro_path = dir.join("minimal_same_tag_probe.rs");
    let minimal_repro_src = format!(
        "{MIRI_CORPUS_CRATE_HEADER}\n\
         use core::intrinsics::{{copy_nonoverlapping, offset}};\n\n{}",
        c16_corpus_fn_renamed(
            "pass_copy_nonoverlapping_same_tag_disjoint_array_halves",
            "pass_copy_nonoverlapping_same_tag_disjoint_array_halves",
        )
    );
    fs::write(&minimal_repro_path, &minimal_repro_src).expect("write minimal repro");
    let minimal_rep = reproduce_miri_finding(&minimal_repro_path, Some(&root))
        .expect("reproduce_miri_finding must accept unmarked standalone Category 11 probe name");
    assert_eq!(
        minimal_rep.name,
        "pass_copy_nonoverlapping_same_tag_disjoint_array_halves"
    );
    assert_eq!(
        minimal_rep.miri,
        MiriOutcome::PassScalar {
            bits: 30,
            size_bytes: 4
        }
    );
    match &minimal_rep.anneal {
        AnnealOutcome::Ub { .. } => {
            assert!(
                matches!(
                    minimal_rep.verdict,
                    ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. })
                ) && minimal_rep.kernel_confirmed,
                "unexpected minimal repro verdict: {minimal_rep:?}"
            );
        }
        AnnealOutcome::PassScalar {
            bits: 30,
            size_bytes: 4,
        } => {
            assert_eq!(minimal_rep.verdict, ComparisonVerdict::Agree);
        }
        other => panic!("unexpected minimal repro Anneal outcome: {other:?}"),
    }

    // Multi-candidate batch combining:
    // (a) 2 mutated candidates from a multi-item seed carrying a local `struct`,
    //     an UNMARKED non-integer-returning helper `fn`, and a trailing
    //     `__ANNEAL_MODEL_*` helper (deduped at crate root without mutating
    //     the unmarked helper),
    // (b) a conflicting agreeing candidate redefining `C16LocalPair` +
    //     `c16_unmarked_step` with incompatible fields/body (isolated into
    //     `stage_ns_0`), and
    // (c) a conflicting divergent candidate redefining `C16LocalPair` +
    //     `c16_unmarked_step` whose UB fault occurs inside `stage_ns_1`'s local
    //     helper (verifying `stage_ns_1` MIR extraction, kernel confirmation
    //     helper linking, zero-drift `repro.rs` span translation, and standalone
    //     `reproduce_miri_finding`).
    let multi_item_seed = "\
#[derive(Copy, Clone)]
pub struct C16LocalPair {
    pub a: u32,
    pub b: u32,
}
fn c16_unmarked_step(pair: C16LocalPair) -> C16LocalPair {
    C16LocalPair {
        a: wrapping_add(pair.a, 1u32),
        b: wrapping_add(pair.b, 2u32),
    }
}
pub fn pass_c16_multi_item_seed() -> u32 {
    let stepped = c16_unmarked_step(C16LocalPair { a: 18u32, b: 21u32 });
    c16_local_model_sum(stepped)
}
pub const __ANNEAL_MODEL_c16_local_model_sum: &str = \"c16_local_model_sum\";
pub fn c16_local_model_sum(pair: C16LocalPair) -> u32 {
    wrapping_add(pair.a, pair.b)
}
";
    let mut multi_batch = generate_miri_batch(&[multi_item_seed], 2, 0xC16_B201);
    let conflict_agree_src = "\
pub struct C16LocalPair {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}
fn c16_unmarked_step(triple: C16LocalPair) -> u32 {
    wrapping_add(wrapping_add(triple.x, triple.y), triple.z)
}
pub fn pass_c16_conflicting_aux_agree() -> u32 {
    c16_unmarked_step(C16LocalPair { x: 10u32, y: 20u32, z: 12u32 })
}
";
    let conflict_div_src = "\
pub struct C16LocalPair {
    pub buf: [u32; 4],
}
fn c16_unmarked_step(mut box_arr: C16LocalPair) -> u32 {
    unsafe {
        let base: *mut u32 = &raw mut box_arr.buf as *mut u32;
        let src: *const u32 = base as *const u32;
        let dst: *mut u32 = offset(base as *const u32, 2isize) as *mut u32;
        copy_nonoverlapping(src, dst, 2usize);
    }
    wrapping_add(box_arr.buf[2], box_arr.buf[3])
}
pub fn pass_c16_conflicting_aux_div() -> u32 {
    c16_unmarked_step(C16LocalPair { buf: [7u32, 8u32, 0u32, 0u32] })
}
";
    multi_batch.push(handwritten_candidate(
        2,
        "pass_c16_conflicting_aux_agree",
        "pass_c16_conflicting_aux_agree",
        "identity",
        conflict_agree_src,
    ));
    let mut conflict_div_cand = handwritten_candidate(
        3,
        "pass_c16_conflicting_aux_div",
        "pass_c16_conflicting_aux_div",
        "identity",
        conflict_div_src,
    );
    conflict_div_cand.applied_mutators.clear();
    multi_batch.push(conflict_div_cand);

    // (d) two candidates implementing conflicting inherent methods on preamble
    //     `PairU32`, where candidate 4 also defines a private helper matching
    //     candidate 5's entry name (`pass_c16_preamble_impl_b`), and candidate 5
    //     defines both `pub struct pass_c16_preamble_impl_b` (`ty:` vs `val:`)
    //     and a scoped `__ANNEAL_MODEL_*` helper inside isolated-preamble `stage_ns`.
    let preamble_impl_a_src = "\
impl PairU32 {
    fn c16_pair_score(&self) -> u32 {
        wrapping_add(self.a, self.b)
    }
}
fn pass_c16_preamble_impl_b() -> u32 {
    1u32
}
pub fn pass_c16_preamble_impl_a() -> u32 {
    let p = PairU32 { a: 20u32, b: 21u32 };
    wrapping_add(p.c16_pair_score(), pass_c16_preamble_impl_b())
}
";
    let preamble_impl_b_src = "\
pub struct pass_c16_preamble_impl_b {
    pub extra: u32,
}
impl PairU32 {
    fn c16_pair_score(&self) -> u32 {
        wrapping_add(wrapping_add(self.a, self.b), 10u32)
    }
}
pub const __ANNEAL_MODEL_c16_scoped_ns_model: &str = \"c16_scoped_ns_model\";
pub fn c16_scoped_ns_model(x: u32) -> u32 {
    wrapping_add(x, 2u32)
}
pub fn pass_c16_preamble_impl_b() -> u32 {
    let local_s = pass_c16_preamble_impl_b { extra: 5u32 };
    let p = PairU32 { a: 10u32, b: 15u32 };
    c16_scoped_ns_model(wrapping_add(p.c16_pair_score(), local_s.extra))
}
";
    multi_batch.push(handwritten_candidate(
        4,
        "pass_c16_preamble_impl_a",
        "pass_c16_preamble_impl_a",
        "identity",
        preamble_impl_a_src,
    ));
    multi_batch.push(handwritten_candidate(
        5,
        "pass_c16_preamble_impl_b",
        "pass_c16_preamble_impl_b",
        "identity",
        preamble_impl_b_src,
    ));

    let multi_findings_dir = dir.join("multi_item_findings");
    let multi_report = evaluate_miri_batches_with_options(
        "c16_multi_item_batch",
        0xC16_B201,
        &[multi_batch],
        6,
        &MiriEvalOptions {
            findings_dir: Some(multi_findings_dir),
            anneal_repo_root: Some(root.clone()),
            shrink_seeds: Some(vec![multi_item_seed.to_string()]),
        },
    )
    .expect("6-candidate unmarked + conflicting multi-item batch must stage without E0428/E0592");
    assert_eq!(multi_report.compiled_candidates, 6);
    assert_eq!(multi_report.compile_failed_candidates, 0);
    assert_eq!(multi_report.compared_candidates, 6);
    assert_eq!(multi_report.not_compared_count, 0);
    assert_eq!(
        multi_report
            .witness_polarity_counts
            .get("unsound_missed_fault"),
        Some(&0)
    );
    for (expected_name, expected_bits) in [
        ("pass_c16_conflicting_aux_agree", 42u128),
        ("pass_c16_preamble_impl_a", 42u128),
        ("pass_c16_preamble_impl_b", 42u128),
    ] {
        let rep = multi_report
            .item_reports
            .iter()
            .find(|r| r.name == expected_name)
            .unwrap_or_else(|| panic!("missing report for {expected_name}"));
        assert_eq!(rep.verdict, ComparisonVerdict::Agree, "{rep:?}");
        assert_eq!(
            rep.miri,
            MiriOutcome::PassScalar {
                bits: expected_bits,
                size_bytes: 4
            }
        );
    }

    if let Some(ns_finding) = multi_report
        .findings
        .iter()
        .find(|f| f.fn_name == "pass_c16_conflicting_aux_div")
    {
        assert_eq!(ns_finding.divergence_class, "false_positive_ub");
        assert!(ns_finding.kernel_confirmed);
        assert!(
            ns_finding
                .mir_neighborhood
                .contains("def body : CapturedMir :="),
            "stage_ns_1 MIR neighborhood must be extracted:\n{}",
            ns_finding.mir_neighborhood
        );
        assert!(
            ns_finding
                .kernel_confirm_theorems
                .contains("Mir.MiriDiffCorpus.stage_ns_1_c16_unmarked_step.body"),
            "stage_ns_1 confirm module must link stage_ns_1 local helper:\n{}",
            ns_finding.kernel_confirm_theorems
        );
        assert!(
            !ns_finding
                .kernel_confirm_theorems
                .contains("Mir.MiriDiffCorpus.c16_unmarked_step.body"),
            "stage_ns_1 confirm module must NOT leak shadowed crate-root helper:\n{}",
            ns_finding.kernel_confirm_theorems
        );
        let ns_repro_path = ns_finding
            .repro_path
            .as_ref()
            .expect("stage_ns_1 finding repro.rs");
        let ns_repro_rep = reproduce_miri_finding(ns_repro_path, Some(&root))
            .expect("reproduce stage_ns_1 finding standalone");
        let ns_repro_anneal_tag = match &ns_repro_rep.anneal {
            AnnealOutcome::Ub { span: Some(s) } => format!("ub@{}", s.display_short()),
            other => other.summary_tag(),
        };
        assert_eq!(
            ns_repro_anneal_tag, ns_finding.anneal_outcome_tag,
            "stage_ns_1 translated UB span must match standalone repro.rs byte-for-byte"
        );
    }
}
