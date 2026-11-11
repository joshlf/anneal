// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! End-to-end integration tests for `scripts/run_diff_test_campaign.py` over
//! live `miri-difftest` oracle results, finding deduplication and quarantine,
//! Miri `PATH` discovery, and red-flag vacuity checks.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn unique_temp_dir(label: &str) -> PathBuf {
    static NEXT_ID: AtomicU64 = AtomicU64::new(1);
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "anneal_campaign_orchestrator_test_{label}_{}_{id}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn write_executable(path: &Path, script: &str) {
    fs::write(path, script).expect("write script");
    let mut perms = fs::metadata(path).expect("stat script").permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).expect("chmod script");
}

fn write_remote_sync_stub(stub: &Path, log: &Path, exit_code: i32) {
    write_executable(
        stub,
        &format!(
            "#!/bin/sh\nprintf '%s\\n' \"$*\" >> '{}'\nexit {exit_code}\n",
            log.display()
        ),
    );
}

const RUNNER_DRIVER: &str = r#"
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("runner", sys.argv[1])
runner = importlib.util.module_from_spec(spec)
sys.modules["runner"] = runner
spec.loader.exec_module(runner)
runner.REMOTE_SYNC_BIN = sys.argv[2]
args = sys.argv[3:]
miri_override = None
itree_override = None
while args and "=" in args[0] and not args[0].startswith("--"):
    key, value = args.pop(0).split("=", 1)
    if key == "miri_summary":
        miri_override = json.loads(value)
    elif key == "itree_summary":
        itree_override = json.loads(value)
    else:
        raise SystemExit(f"unknown driver override {key}")
if miri_override is not None or itree_override is not None:
    orig_run = runner.run_harness
    def stub_run(repo_root, bin_name, harness_args, json_path):
        if bin_name == "miri-difftest" and miri_override is not None:
            return dict(miri_override)
        if bin_name == "itree-difftest" and itree_override is not None:
            return dict(itree_override)
        return orig_run(repo_root, bin_name, harness_args, json_path)
    runner.run_harness = stub_run
sys.argv = ["run_diff_test_campaign.py", *args]
sys.exit(runner.main())
"#;

fn run_campaign_driver(
    remote_sync_stub: &Path,
    env_vars: &[(&str, &Path)],
    removed_env_vars: &[&str],
    overrides: &[String],
    runner_args: &[&str],
    state_dir: &Path,
) -> Output {
    let root = repo_root();
    let mut cmd = Command::new("python3");
    cmd.arg("-c")
        .arg(RUNNER_DRIVER)
        .arg(root.join("scripts/run_diff_test_campaign.py"))
        .arg(remote_sync_stub)
        .args(overrides)
        .args(runner_args)
        .arg("--state-dir")
        .arg(state_dir)
        .current_dir(&root)
        .env("PYTHONDONTWRITEBYTECODE", "1");
    for k in removed_env_vars {
        cmd.env_remove(k);
    }
    for (key, value) in env_vars {
        cmd.env(key, value);
    }
    cmd.output().expect("run campaign runner driver")
}

#[test]
fn live_smoke_campaign_separates_outcomes_reproduces_findings_and_quarantines() {
    let dir = unique_temp_dir("live_smoke");
    let state_dir = dir.join("state_dir");
    let junit = dir.join("diff_test_report.xml");
    let junit_arg = junit.to_string_lossy().into_owned();
    let remote_sync_log = dir.join("remote-sync.log");
    let remote_sync = dir.join("remote_sync_stub.sh");
    write_remote_sync_stub(&remote_sync, &remote_sync_log, 0);

    // 1. Live smoke run with default seed `0x5eed0001` and no quarantine file:
    // must run real Miri + Anneal and real ITree + Lean `TraceCheck`, separate
    // compared/agreed/diverged/not-compared, materialize `coverage_ratchet.json`,
    // and exit 0 (`PASS (0 divergences)`) now that all 4 previously open corpus
    // bugs (`DIFF-AB`, `DIFF-C`, `DIFF-D`, `DIFF-E`) are fixed in `MirSemantics`.
    let out1 = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[],
        &[
            "--profile",
            "smoke",
            "--remote-uri",
            "",
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir,
    );
    let stdout1 = String::from_utf8_lossy(&out1.stdout);
    let stderr1 = String::from_utf8_lossy(&out1.stderr);
    assert_eq!(
        out1.status.code(),
        Some(0),
        "live smoke campaign on 0x5eed0001 must exit 0:\nstdout:\n{stdout1}\nstderr:\n{stderr1}"
    );
    assert!(
        !remote_sync_log.exists(),
        "campaign without --remote-uri must not invoke remote-sync"
    );

    let report1 =
        fs::read_to_string(state_dir.join("reports/LATEST_REPORT.md")).expect("read LATEST_REPORT");
    assert_eq!(report1.trim(), stdout1.trim());
    assert!(
        report1.contains("Status: PASS (0 divergences)."),
        "report must announce PASS (0 divergences):\n{report1}"
    );
    assert!(
        report1.contains("| Oracle comparison | **performed** | **performed** |"),
        "report must show performed for both miri-difftest and itree-difftest:\n{report1}"
    );
    assert!(
        report1.contains("| Compared | 16 | 16 ("),
        "report must show 16 compared candidates for both miri-difftest and itree-difftest:\n{report1}"
    );
    assert!(
        report1.contains("| Agreed | 16 | 16 ("),
        "report must show 16 agreed Miri candidates and 16 agreed ITree candidates:\n{report1}"
    );
    assert!(
        report1.contains(
            "| Diverged (raw / distinct) | 0 (0 distinct: 0 unquarantined, 0 quarantined) | 0 (0 distinct: 0 unquarantined, 0 quarantined) |"
        ),
        "report must show raw and deduplicated divergence counts:\n{report1}"
    );
    assert!(
        report1.contains("| Kernel-confirmed divergences (`by rfl`) | 0 | 0 ("),
        "report must show 0 kernel-confirmed Miri and ITree divergences:\n{report1}"
    );
    assert!(
        report1.contains("| Not compared | 0 | 0 |"),
        "report must show not-compared counts:\n{report1}"
    );
    assert!(
        report1.contains("## Not-Compared Breakdown by Reason (`miri-difftest`)"),
        "report must include not-compared breakdown table:\n{report1}"
    );
    assert!(
        report1.contains("## ITree Native vs. Lean `TraceCheck` Breakdown (`itree-difftest`)"),
        "report must include ITree TraceCheck breakdown table:\n{report1}"
    );
    for check in [
        "oracle_invoked",
        "non_zero_compared",
        "plausible_wall_clock",
        "seed_sensitivity",
        "oracle_error_threshold",
        "itree_oracle_invoked",
        "itree_non_zero_compared",
        "itree_plausible_wall_clock",
        "itree_seed_sensitivity",
        "itree_oracle_error_threshold",
    ] {
        assert!(
            report1.contains(&format!("| `{check}` | PASS |")),
            "red-flag check `{check}` must PASS in live smoke report:\n{report1}"
        );
    }
    let ratchet_json = fs::read_to_string(state_dir.join("state/coverage_ratchet.json"))
        .expect("read coverage_ratchet.json");
    assert!(
        ratchet_json.contains("\"cumulative_distinct_obs_paths\":")
            && !ratchet_json.contains("\"cumulative_distinct_obs_paths\": 0"),
        "coverage_ratchet.json must record non-zero cumulative_distinct_obs_paths:\n{ratchet_json}"
    );

    // 2. Live kernel-confirmed Miri vs. Anneal divergence bundle + `--reproduce` +
    // unquarantined / partial-quarantine / full-quarantine verification:
    // Evaluate a batch with 3 corpus candidates plus a negative-control
    // candidate (`char` surrogate written through `*mut u32`) through live
    // `evaluate_miri_batches` to produce a real `repro.rs` bundle on disk.
    let root = repo_root();
    let mut div_batch =
        anneal_difftest::mutators_miri::generate_miri_corpus_batch(3, 0x5eed_0001, 0);
    let neg_fn = "\
pub fn neg_ctrl_char_surrogate_via_ptr__b0_c3() -> u32 {
    let mut c: char = 'a';
    let p: *mut u32 = (&raw mut c) as *mut u32;
    unsafe {
        *p = 0xD800u32;
    }
    c as u32
}
";
    div_batch.push(anneal_difftest::mutators_miri::GeneratedMiriCandidate {
        id: 3,
        seed_index: 0,
        seed_name: "ub_transmute_invalid_char_surrogate".to_string(),
        fn_name: "neg_ctrl_char_surrogate_via_ptr__b0_c3".to_string(),
        seed_u64: 0xDEAD_BEEF,
        applied_mutators: vec!["BitValidityTransmuteMutator".to_string()],
        tracked_locals: Vec::new(),
        fn_source: neg_fn.to_string(),
        source: anneal_difftest::mutators_miri::build_standalone_candidate_source(neg_fn),
    });
    let live_findings_dir = dir.join("live_findings");
    let live_div_eval = anneal_difftest::miri_eval::evaluate_miri_batches(
        "seeded",
        0x5eed_0001,
        &[div_batch],
        4,
        Some(&live_findings_dir),
        Some(&root),
    )
    .expect("evaluate live divergence batch");
    let live_div_payload = anneal_difftest::miri_eval::render_eval_report_json(&live_div_eval);

    let state_dir_div = dir.join("state_dir_div");
    let out_div = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[format!("miri_summary={live_div_payload}")],
        &[
            "--profile",
            "smoke",
            "--miri-only",
            "--remote-uri",
            "",
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir_div,
    );
    let stdout_div = String::from_utf8_lossy(&out_div.stdout);
    let stderr_div = String::from_utf8_lossy(&out_div.stderr);
    assert_eq!(
        out_div.status.code(),
        Some(4),
        "campaign with unquarantined divergence must exit 4:\nstdout:\n{stdout_div}\nstderr:\n{stderr_div}"
    );
    let report_div = fs::read_to_string(state_dir_div.join("reports/LATEST_REPORT.md"))
        .expect("read LATEST_REPORT for div run");
    assert!(
        report_div.contains("Status: DIVERGENCE DETECTED (1 unquarantined distinct, 1 raw)."),
        "report must announce 1 unquarantined distinct / 1 raw divergence:\n{report_div}"
    );
    assert!(
        report_div.contains(
            "| `BitValidityTransmuteMutator:missed_ub:MirDiffTag.normalScalar` | `missed_ub` | 1 |"
        ),
        "report must list deduplicated BitValidityTransmuteMutator missed_ub fingerprint:\n{report_div}"
    );

    let junit1 = fs::read_to_string(&junit).expect("read JUnit XML");
    assert!(
        junit1.contains("failures=\"1\""),
        "JUnit XML must record 1 failure for unquarantined divergences:\n{junit1}"
    );
    assert!(
        junit1.contains("unquarantined divergences detected (1 distinct, 1 total)"),
        "JUnit XML must describe the unquarantined divergences:\n{junit1}"
    );

    // Verify `LATEST_CAMPAIGN_SUMMARY.json` and reproduce each distinct finding's
    // `primary_repro_path` via `miri-difftest --reproduce`.
    let summary_json =
        fs::read_to_string(state_dir_div.join("reports/LATEST_CAMPAIGN_SUMMARY.json"))
            .expect("read LATEST_CAMPAIGN_SUMMARY.json");
    assert!(summary_json.contains(
        "\"fingerprint\": \"BitValidityTransmuteMutator:missed_ub:MirDiffTag.normalScalar\""
    ));

    // Extract primary_repro_path values from the summary JSON and run `--reproduce` on each.
    let repro_paths: Vec<PathBuf> = summary_json
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let rest = trimmed.strip_prefix("\"primary_repro_path\": \"")?;
            let path_str = rest.strip_suffix("\",")?;
            Some(PathBuf::from(path_str))
        })
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    assert_eq!(
        repro_paths.len(),
        1,
        "expected 1 distinct primary_repro_path entry, got {repro_paths:?}"
    );
    for repro_path in &repro_paths {
        assert!(
            repro_path.is_file(),
            "repro_path must exist: {}",
            repro_path.display()
        );
        let repro_out = Command::new(env!("CARGO_BIN_EXE_miri-difftest"))
            .arg("--reproduce")
            .arg(repro_path)
            .output()
            .expect("run miri-difftest --reproduce");
        let repro_stdout = String::from_utf8_lossy(&repro_out.stdout);
        assert!(
            repro_out.status.success(),
            "miri-difftest --reproduce failed on {}:\n{}",
            repro_path.display(),
            String::from_utf8_lossy(&repro_out.stderr)
        );
        assert!(
            repro_stdout.contains("\"verdict\": \"diverge\"")
                && repro_stdout.contains("\"kernel_confirmed\": true"),
            "reproducer output must confirm divergence:\n{repro_stdout}"
        );
    }

    // 3. Partial quarantine (seeding a known divergence that is NOT quarantined):
    // Quarantining only an unrelated fingerprint leaves `BitValidityTransmuteMutator`
    // unquarantined, which must still fail with exit 4.
    let partial_quarantine = dir.join("partial_quarantine.json");
    fs::write(
        &partial_quarantine,
        r#"{"quarantined": ["pass_tb_unsafe_cell_shared_mutation:false_positive_ub:MirDiffTag.ub"]}"#,
    )
    .expect("write partial quarantine");
    let state_dir_partial = dir.join("state_dir_partial");
    let out_partial = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[format!("miri_summary={live_div_payload}")],
        &[
            "--profile",
            "smoke",
            "--miri-only",
            "--miri-seed",
            "0x5eed0001",
            "--quarantine-file",
            &partial_quarantine.to_string_lossy(),
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir_partial,
    );
    assert_eq!(
        out_partial.status.code(),
        Some(4),
        "leaving a known divergence unquarantined must fail the campaign with exit 4"
    );
    let report_partial = fs::read_to_string(state_dir_partial.join("reports/LATEST_REPORT.md"))
        .expect("read partial report");
    assert!(
        report_partial.contains("Status: DIVERGENCE DETECTED (1 unquarantined distinct, 1 raw)."),
        "partial quarantine must leave 1 unquarantined distinct divergence:\n{report_partial}"
    );

    // 4. Full quarantine of the known fingerprint: when all encountered
    // divergences are quarantined, the campaign must exit 0 (`EXIT_SUCCESS`)
    // and emit 0 JUnit failures.
    let full_quarantine = dir.join("full_quarantine.json");
    fs::write(
        &full_quarantine,
        r#"{
            "quarantined": [
                "BitValidityTransmuteMutator:missed_ub:MirDiffTag.normalScalar"
            ]
        }"#,
    )
    .expect("write full quarantine");
    let state_dir_clean = dir.join("state_dir_clean");
    let out_clean = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[format!("miri_summary={live_div_payload}")],
        &[
            "--profile",
            "smoke",
            "--miri-only",
            "--miri-seed",
            "0x5eed0001",
            "--quarantine-file",
            &full_quarantine.to_string_lossy(),
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir_clean,
    );
    let stdout_clean = String::from_utf8_lossy(&out_clean.stdout);
    let stderr_clean = String::from_utf8_lossy(&out_clean.stderr);
    assert_eq!(
        out_clean.status.code(),
        Some(0),
        "campaign with all divergences quarantined must exit 0:\nstdout:\n{stdout_clean}\nstderr:\n{stderr_clean}"
    );
    let junit_clean = fs::read_to_string(&junit).expect("read clean JUnit XML");
    assert!(
        junit_clean.contains("failures=\"0\""),
        "clean quarantined campaign must have 0 JUnit failures:\n{junit_clean}"
    );
    assert!(
        stdout_clean.contains(
            "Status: PASS (1 quarantined known bug fingerprints)."
        ),
        "report must show quarantined fingerprint count in status banner:\n{stdout_clean}"
    );
    assert!(
        stdout_clean.contains("### Unquarantined Divergences (0 distinct)")
            && stdout_clean.contains("### Quarantined Divergences (1 distinct)"),
        "report must show 0 unquarantined and 1 quarantined divergences:\n{stdout_clean}"
    );
}

#[test]
fn campaign_orchestrator_fails_when_miri_removed_from_path() {
    let dir = unique_temp_dir("no_miri_path");
    let state_dir = dir.join("state_dir");
    let junit = dir.join("diff_test_report.xml");
    let junit_arg = junit.to_string_lossy().into_owned();
    let remote_sync_log = dir.join("remote-sync.log");
    let remote_sync = dir.join("remote_sync_stub.sh");
    write_remote_sync_stub(&remote_sync, &remote_sync_log, 1);

    fs::create_dir_all(state_dir.join("state")).expect("create state dir");
    let initial_ledger =
        r#"{"next_miri_seed": "0x5eed0001", "next_itree_seed": "0x5eed0002", "total_campaigns_run": 2}"#;
    fs::write(state_dir.join("state/campaign_ledger.json"), initial_ledger).expect("write ledger");

    // Build a restricted PATH directory that contains every tool EXCEPT `miri`
    // and `cargo-miri`.
    let no_miri_bin = dir.join("no_miri_bin");
    fs::create_dir_all(&no_miri_bin).expect("create no_miri_bin");
    let orig_path = std::env::var("PATH").unwrap_or_default();
    for dir_entry in orig_path.split(':') {
        let p = Path::new(dir_entry);
        let Ok(entries) = fs::read_dir(p) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name_str = name.to_string_lossy();
            if name_str == "miri" || name_str == "cargo-miri" {
                continue;
            }
            let dst = no_miri_bin.join(&name);
            if !dst.exists() {
                let _ = std::os::unix::fs::symlink(entry.path(), &dst);
            }
        }
    }

    let out = run_campaign_driver(
        &remote_sync,
        &[("PATH", &no_miri_bin)],
        &["ANNEAL_MIRI_BIN"],
        &[],
        &[
            "--profile",
            "smoke",
            "--miri-only",
            "--remote-uri",
            "",
            "--junit-xml",
            &junit_arg,
        ],
        &state_dir,
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        out.status.code(),
        Some(2),
        "campaign with Miri removed from PATH must fail with exit 2:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("could not locate 'miri' or 'cargo-miri' on PATH"),
        "stderr must explain that Miri is missing from PATH:\n{stderr}"
    );
    assert!(
        stdout.contains("Status: HARNESS FAILED."),
        "report must announce HARNESS FAILED when Miri is missing:\n{stdout}"
    );
    let junit_xml = fs::read_to_string(&junit).expect("read JUnit XML");
    assert!(
        junit_xml.contains("<failure message=\"harness failed\">"),
        "JUnit XML must record harness failure:\n{junit_xml}"
    );
    assert_eq!(
        fs::read_to_string(state_dir.join("state/campaign_ledger.json")).expect("read ledger"),
        initial_ledger,
        "ledger must remain untouched when Miri is missing from PATH"
    );
}

#[test]
fn campaign_orchestrator_red_flag_checks_reject_vacuous_and_faulty_runs() {
    let dir = unique_temp_dir("red_flags");
    let remote_sync_log = dir.join("remote-sync.log");
    let remote_sync = dir.join("remote_sync_stub.sh");
    write_remote_sync_stub(&remote_sync, &remote_sync_log, 1);

    let initial_ledger = r#"{
  "last_miri_seed": "0x00000011",
  "last_miri_signature": {
    "anneal_outcomes": {"error": 0, "external_call": 0, "out_of_fuel": 0, "panic": 2, "pass": 4, "ub": 2, "unsupported": 0},
    "miri_verdicts": {"error": 0, "panic": 2, "pass": 4, "ub": 2},
    "mutator_applications": {"ArithmeticCastMutator": 4, "BitValidityTransmuteMutator": 2, "PlaceProjectionWrapper": 2, "RawPtrOffsetMutator": 2, "TreeBorrowsRetagInterleaver": 2}
  },
  "next_itree_seed": "0x00000022",
  "next_miri_seed": "0x00000022",
  "total_campaigns_run": 3
}"#;

    // 1. `zero_compared_items`: all 8 candidates are `external_call` (`compared_candidates == 0`).
    let zero_compared = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000022",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 0,
        "agree_count": 0,
        "diverge_count": 0,
        "not_compared_count": 8,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 8, "panic": 0, "ub": 0, "error": 0},
        "anneal_outcomes": {"pass": 0, "panic": 0, "ub": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 8, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 8},
        "unmodeled_external_calls": {"foo::bar": 8},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;

    // 2. `impossible_wall_clock`: `elapsed_ms` is 1.5 ms (< 50.0 ms).
    let impossible_clock = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000022",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 8,
        "diverge_count": 0,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 5, "panic": 2, "ub": 1, "error": 0},
        "anneal_outcomes": {"pass": 5, "panic": 2, "ub": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 0},
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 1.5
    }"#;

    // 3. `identical_metrics_across_seeds`: matches `last_miri_signature` from seed `0x00000011` on seed `0x00000022`.
    let identical_seed_sig = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000022",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 8,
        "diverge_count": 0,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 4, "panic": 2, "ub": 2, "error": 0},
        "anneal_outcomes": {"pass": 4, "panic": 2, "ub": 2, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 0},
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 4, "BitValidityTransmuteMutator": 2, "PlaceProjectionWrapper": 2, "RawPtrOffsetMutator": 2, "TreeBorrowsRetagInterleaver": 2},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;

    // 4. `oracle_not_invoked`: `miri_verdicts` are all 0 despite `compiled_candidates == 8`.
    let oracle_not_invoked = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000022",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 8,
        "diverge_count": 0,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 0, "panic": 0, "ub": 0, "error": 0},
        "anneal_outcomes": {"pass": 5, "panic": 2, "ub": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 0},
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;

    // 5. `oracle_errors_exceeded`: 1 `miri_oracle_error` when `--max-oracle-errors` is 0.
    let oracle_error_exceeded = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000022",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 7,
        "agree_count": 7,
        "diverge_count": 0,
        "not_compared_count": 1,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 5, "panic": 1, "ub": 1, "error": 1},
        "anneal_outcomes": {"pass": 6, "panic": 1, "ub": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0},
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;

    for (label, check_col, reason_token, payload) in [
        (
            "zero_compared",
            "non_zero_compared",
            "zero_compared_items",
            zero_compared,
        ),
        (
            "impossible_clock",
            "plausible_wall_clock",
            "impossible_wall_clock",
            impossible_clock,
        ),
        (
            "identical_seeds",
            "seed_sensitivity",
            "identical_metrics_across_seeds",
            identical_seed_sig,
        ),
        (
            "oracle_not_invoked",
            "oracle_invoked",
            "oracle_not_invoked",
            oracle_not_invoked,
        ),
        (
            "oracle_errors",
            "oracle_error_threshold",
            "oracle_errors_exceeded",
            oracle_error_exceeded,
        ),
    ] {
        let case_dir = dir.join(label);
        let junit = case_dir.join("diff_test_report.xml");
        let junit_arg = junit.to_string_lossy().into_owned();
        fs::create_dir_all(case_dir.join("state")).expect("create state dir");
        fs::write(case_dir.join("state/campaign_ledger.json"), initial_ledger)
            .expect("write ledger");

        let out = run_campaign_driver(
            &remote_sync,
            &[],
            &[],
            &[format!("miri_summary={payload}")],
            &[
                "--profile",
                "smoke",
                "--miri-only",
                "--remote-uri",
                "",
                "--junit-xml",
                &junit_arg,
            ],
            &case_dir,
        );
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(
            out.status.code(),
            Some(2),
            "red-flag case `{label}` must fail with exit 2:\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.contains("Status: RED FLAG / HARNESS FAILED."),
            "red-flag case `{label}` must report RED FLAG / HARNESS FAILED:\n{stdout}"
        );
        assert!(
            stdout.contains(&format!("| `{check_col}` | **FAIL** |")),
            "red-flag case `{label}` must mark `{check_col}` as **FAIL**:\n{stdout}"
        );
        assert!(
            stdout.contains(reason_token) && stderr.contains(reason_token),
            "red-flag case `{label}` must cite `{reason_token}` in stdout and stderr"
        );
        let junit_xml = fs::read_to_string(&junit).expect("read JUnit XML");
        assert!(
            junit_xml.contains("<failure message=\"red-flag vacuity check failed\">")
                && junit_xml.contains(reason_token),
            "JUnit XML for `{label}` must record red-flag failure `{reason_token}`:\n{junit_xml}"
        );
        assert_eq!(
            fs::read_to_string(case_dir.join("state/campaign_ledger.json")).expect("read ledger"),
            initial_ledger,
            "ledger must not advance when red-flag check `{label}` fails"
        );
    }

    // 6. Fingerprint-collision quarantine resistance and earliest-fault-line
    // cause attribution:
    // - Finding 0 (`pass_array_index_and_mutation__b0_c6`) is quarantined by
    //   `fn_name`, while Finding 1 (`pass_unchecked_arith_in_bounds__b0_c7`)
    //   shares fingerprint `RawPtrOffsetMutator:missed_ub:MirDiffTag.normalScalar`
    //   and is NOT quarantined -> the fingerprint MUST remain unquarantined and
    //   point to Finding 1's reproducer.
    // - Finding 2 (`pass_ptr_offset_within_array__b0_c6`) faults in Anneal
    //   at line 2 (seed body `*p1`) and later panics in Miri at line 4
    //   (appended `__miri_valid_52335` tail) -> earliest-line attribution must
    //   assign cause `pass_ptr_offset_within_array`, not
    //   `BitValidityTransmuteMutator`.
    let repro_dir = dir.join("collision_repros");
    fs::create_dir_all(&repro_dir).expect("create collision_repros");
    let repro0 = repro_dir.join("repro0.rs");
    let repro1 = repro_dir.join("repro1.rs");
    let repro2 = repro_dir.join("repro2.rs");
    for r in [&repro0, &repro1, &repro2] {
        fs::write(r, "pub fn stub() {}\n").expect("write stub repro");
    }
    let collision_payload = format!(
        r#"{{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000033",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 5,
        "diverge_count": 3,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": 3,
        "miri_verdicts": {{"pass": 5, "panic": 1, "ub": 2, "error": 0}},
        "anneal_outcomes": {{"pass": 7, "panic": 0, "ub": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0}},
        "divergence_classes": {{"wrong_value": 0, "false_positive_ub": 1, "missed_ub": 2, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0}},
        "not_compared_reasons": {{"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 0}},
        "unmodeled_external_calls": {{}},
        "mutator_applications": {{"RawPtrOffsetMutator": 2, "BitValidityTransmuteMutator": 1}},
        "findings": [
            {{
                "finding_id": "f0",
                "fn_name": "pass_array_index_and_mutation__b0_c6",
                "seed_name": "pass_array_index_and_mutation",
                "applied_mutators": ["RawPtrOffsetMutator"],
                "divergence_class": "missed_ub",
                "miri_outcome": "ub@src/lib.rs:2:5",
                "miri_excerpt": "UB",
                "miri_pos": "src/lib.rs:2:5",
                "anneal_outcome": "pass:scalar:1:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 1 4)",
                "anneal_span": null,
                "mutant_source": "pub fn f0() -> u32 {{\n    let __miri_ptr_1: u32 = unsafe {{ *offset(__oob_base, 2isize) }};\n    __miri_ptr_1\n}}\n",
                "kernel_confirmed": true,
                "repro_path": "{}"
            }},
            {{
                "finding_id": "f1",
                "fn_name": "pass_unchecked_arith_in_bounds__b0_c7",
                "seed_name": "pass_unchecked_arith_in_bounds",
                "applied_mutators": ["RawPtrOffsetMutator"],
                "divergence_class": "missed_ub",
                "miri_outcome": "ub@src/lib.rs:2:5",
                "miri_excerpt": "UB",
                "miri_pos": "src/lib.rs:2:5",
                "anneal_outcome": "pass:scalar:2:4",
                "anneal_lean_tag": "(MirDiffTag.normalScalar 2 4)",
                "anneal_span": null,
                "mutant_source": "pub fn f1() -> u32 {{\n    let __miri_ptr_2: u32 = unsafe {{ *offset(__neg_base, -1isize) }};\n    __miri_ptr_2\n}}\n",
                "kernel_confirmed": true,
                "repro_path": "{}"
            }},
            {{
                "finding_id": "f2",
                "fn_name": "pass_ptr_offset_within_array__b0_c6",
                "seed_name": "pass_ptr_offset_within_array",
                "applied_mutators": ["BitValidityTransmuteMutator"],
                "divergence_class": "false_positive_ub",
                "miri_outcome": "panic@src/lib.rs:4:5",
                "miri_excerpt": "panicked",
                "miri_pos": "src/lib.rs:4:5",
                "anneal_outcome": "ub@src/lib.rs:2:5",
                "anneal_lean_tag": "MirDiffTag.ub",
                "anneal_span": "src/lib.rs:2:5",
                "mutant_source": "pub fn f2() -> u32 {{\n    *p1;\n    let __tail: u32 = 0;\n    let __miri_valid_52335: u32 = __panic_arr[__panic_idx];\n    __tail ^ __miri_valid_52335\n}}\n",
                "kernel_confirmed": true,
                "repro_path": "{}"
            }}
        ],
        "elapsed_ms": 500.0
    }}"#,
        repro0.display(),
        repro1.display(),
        repro2.display()
    );

    let collision_quarantine = dir.join("collision_quarantine.json");
    fs::write(
        &collision_quarantine,
        r#"{"quarantined": ["pass_array_index_and_mutation__b0_c6"]}"#,
    )
    .expect("write collision quarantine");
    let collision_state = dir.join("collision_state");
    let out_coll = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[format!("miri_summary={collision_payload}")],
        &[
            "--profile",
            "smoke",
            "--miri-only",
            "--quarantine-file",
            &collision_quarantine.to_string_lossy(),
            "--remote-uri",
            "",
        ],
        &collision_state,
    );
    let stdout_coll = String::from_utf8_lossy(&out_coll.stdout);
    assert_eq!(
        out_coll.status.code(),
        Some(4),
        "unquarantined finding colliding with a fn_name-quarantined finding must NOT be swallowed:\n{stdout_coll}"
    );
    assert!(
        stdout_coll.contains("Status: DIVERGENCE DETECTED (2 unquarantined distinct, 3 raw)."),
        "both RawPtrOffsetMutator (via f1) and pass_ptr_offset_within_array (via f2) must be unquarantined:\n{stdout_coll}"
    );
    assert!(
        stdout_coll.contains(
            "| `pass_ptr_offset_within_array:false_positive_ub:MirDiffTag.ub` | `false_positive_ub` | 1 |"
        ),
        "f2 must be attributed to pass_ptr_offset_within_array, not BitValidityTransmuteMutator:\n{stdout_coll}"
    );
    assert!(
        stdout_coll.contains(&format!("`{}`", repro1.display())),
        "RawPtrOffsetMutator row must point to the unquarantined repro1.rs:\n{stdout_coll}"
    );

    // 7. ITree red-flag failure (`itree_oracle_invoked` fail) and ITree divergence
    // deduplication + quarantine:
    let clean_miri_payload = r#"{
        "harness": "miri-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000044",
        "batches": 1,
        "batch_size": 8,
        "total_candidates": 8,
        "compiled_candidates": 8,
        "compile_failed_candidates": 0,
        "compared_candidates": 8,
        "agree_count": 8,
        "diverge_count": 0,
        "not_compared_count": 0,
        "kernel_confirmed_divergences": 0,
        "miri_verdicts": {"pass": 6, "panic": 1, "ub": 1, "error": 0},
        "anneal_outcomes": {"pass": 6, "panic": 1, "ub": 1, "unsupported": 0, "out_of_fuel": 0, "external_call": 0, "error": 0},
        "divergence_classes": {"wrong_value": 0, "false_positive_ub": 0, "missed_ub": 0, "ub_location_mismatch": 0, "panic_vs_return": 0, "return_vs_panic": 0, "panic_site_mismatch": 0},
        "not_compared_reasons": {"compile_failed": 0, "capture_failed": 0, "miri_oracle_error": 0, "unsupported": 0, "out_of_fuel": 0, "external_call": 0},
        "unmodeled_external_calls": {},
        "mutator_applications": {"ArithmeticCastMutator": 8},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;

    // 7a. `itree_oracle_not_invoked`: `kernel_confirmed_traces` (0) != `distinct_traces_checked` (8).
    let bad_itree_payload = r#"{
        "harness": "itree-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000055",
        "batches": 1,
        "batch_size": 8,
        "trials_per_candidate": 12,
        "total_candidates": 8,
        "unsafe_token_violations": 0,
        "opt_level_0_compiled": 8,
        "opt_level_2_compiled": 8,
        "opt_level_0_and_2_compiled": 8,
        "instrumented_compiled": 8,
        "compared_candidates": 8,
        "agree_candidates": 8,
        "diverge_candidates": 0,
        "not_compared_candidates": 0,
        "total_traces_executed": 96,
        "distinct_traces_checked": 8,
        "agree_traces": 8,
        "diverge_traces": 0,
        "kernel_confirmed_traces": 0,
        "kernel_confirmed_divergences": 0,
        "distinct_obs_paths": 8,
        "diag_tag_counts": {"ok": 8, "outcome_mismatch": 0, "unexpected_ext_call": 0, "call_arg_mismatch": 0, "branch_tag_mismatch": 0, "unconsumed_events": 0, "step_faulted": 0, "decode_arg_failed": 0, "decode_event_failed": 0, "decode_outcome_failed": 0, "out_of_fuel": 0},
        "per_candidate_distinct_traces": {"b0_c0__kernel_step": 1},
        "mutator_applications": {"BranchLoopWeaver": 8},
        "findings": [],
        "elapsed_ms": 500.0
    }"#;
    let itree_rf_dir = dir.join("itree_red_flag");
    let out_itree_rf = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[
            format!("miri_summary={clean_miri_payload}"),
            format!("itree_summary={bad_itree_payload}"),
        ],
        &["--profile", "smoke", "--remote-uri", ""],
        &itree_rf_dir,
    );
    let stdout_itree_rf = String::from_utf8_lossy(&out_itree_rf.stdout);
    assert_eq!(
        out_itree_rf.status.code(),
        Some(2),
        "bad itree summary must fail red-flag check with exit 2:\n{stdout_itree_rf}"
    );
    assert!(
        stdout_itree_rf.contains("| `itree_oracle_invoked` | **FAIL** |")
            && stdout_itree_rf.contains("itree_oracle_not_invoked"),
        "report must flag `itree_oracle_invoked` as FAIL:\n{stdout_itree_rf}"
    );

    // 7b. ITree divergence deduplication and quarantine (`BranchLoopWeaver:itree_branch_tag_mismatch:TraceReplayDiag.branch_tag_mismatch`).
    let itree_repro_dir = dir.join("itree_repros");
    fs::create_dir_all(&itree_repro_dir).expect("create itree_repros");
    let itree_repro0 = itree_repro_dir.join("repro.rs");
    fs::write(&itree_repro0, "pub fn kernel_step() {}\n").expect("write itree stub repro");
    let div_itree_payload = format!(
        r#"{{
        "harness": "itree-difftest",
        "oracle_comparison": "performed",
        "mode": "seeded",
        "seed": "0x00000055",
        "batches": 1,
        "batch_size": 8,
        "trials_per_candidate": 12,
        "total_candidates": 8,
        "unsafe_token_violations": 0,
        "opt_level_0_compiled": 8,
        "opt_level_2_compiled": 8,
        "opt_level_0_and_2_compiled": 8,
        "instrumented_compiled": 8,
        "compared_candidates": 8,
        "agree_candidates": 7,
        "diverge_candidates": 1,
        "not_compared_candidates": 0,
        "total_traces_executed": 96,
        "distinct_traces_checked": 8,
        "agree_traces": 7,
        "diverge_traces": 1,
        "kernel_confirmed_traces": 8,
        "kernel_confirmed_divergences": 1,
        "distinct_obs_paths": 8,
        "diag_tag_counts": {{"ok": 7, "outcome_mismatch": 0, "unexpected_ext_call": 0, "call_arg_mismatch": 0, "branch_tag_mismatch": 1, "unconsumed_events": 0, "step_faulted": 0, "decode_arg_failed": 0, "decode_event_failed": 0, "decode_outcome_failed": 0, "out_of_fuel": 0}},
        "per_candidate_distinct_traces": {{"b0_c0__kernel_step": 1}},
        "mutator_applications": {{"BranchLoopWeaver": 8}},
        "findings": [
            {{
                "finding_id": "finding_0000_case_b0_c0__kernel_step_t0",
                "fn_name": "b0_c0__kernel_step",
                "case_ident": "case_b0_c0__kernel_step_t0",
                "seed_index": 0,
                "applied_mutators": ["BranchLoopWeaver"],
                "diag_tag": "branch_tag_mismatch",
                "diag_repr": "TraceReplayDiag.branch_tag_mismatch 0 1 2",
                "trace_hex": "deadbeef",
                "checked_mir_module": "Mir.ItreeDiffStaged.b0_c0__kernel_step",
                "kernel_confirmed": true,
                "repro_path": "{}"
            }}
        ],
        "elapsed_ms": 500.0
    }}"#,
        itree_repro0.display()
    );

    let itree_div_dir = dir.join("itree_div_unquarantined");
    let out_itree_div = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[
            format!("miri_summary={clean_miri_payload}"),
            format!("itree_summary={div_itree_payload}"),
        ],
        &["--profile", "smoke", "--remote-uri", ""],
        &itree_div_dir,
    );
    let stdout_itree_div = String::from_utf8_lossy(&out_itree_div.stdout);
    assert_eq!(
        out_itree_div.status.code(),
        Some(4),
        "unquarantined ITree divergence must exit 4:\n{stdout_itree_div}"
    );
    assert!(
        stdout_itree_div.contains(
            "| `BranchLoopWeaver:itree_branch_tag_mismatch:TraceReplayDiag.branch_tag_mismatch` | `itree_branch_tag_mismatch` | 1 |"
        ),
        "report must list ITree divergence fingerprint:\n{stdout_itree_div}"
    );

    let itree_quarantine = dir.join("itree_quarantine.json");
    fs::write(
        &itree_quarantine,
        r#"{"quarantined": ["BranchLoopWeaver:itree_branch_tag_mismatch:TraceReplayDiag.branch_tag_mismatch"]}"#,
    )
    .expect("write itree quarantine");
    let itree_quar_dir = dir.join("itree_div_quarantined");
    let out_itree_quar = run_campaign_driver(
        &remote_sync,
        &[],
        &[],
        &[
            format!("miri_summary={clean_miri_payload}"),
            format!("itree_summary={div_itree_payload}"),
        ],
        &[
            "--profile",
            "smoke",
            "--quarantine-file",
            &itree_quarantine.to_string_lossy(),
            "--remote-uri",
            "",
        ],
        &itree_quar_dir,
    );
    assert_eq!(
        out_itree_quar.status.code(),
        Some(0),
        "quarantined ITree divergence must exit 0"
    );
}
