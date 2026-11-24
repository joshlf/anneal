//! False-proof mutation probes and end-to-end negative fault-site coverage
//! integration tests (`Episode 2`).
//!
//! Exercises:
//! 1. The 4 deterministic false-proof mutation probes
//!    (`CallArgBlindProbe`, `SwitchBreakStripProbe`, `LoopUpdateOverflowProbe`,
//!    and `DerefAliasProbe`) over both `IrCapturedMir` and emitted
//!    `Mir/<Item>.lean` modules.
//! 2. Fail-closed rejection of forged waivers, blank justifications,
//!    non-waivable `UnsupportedFallback` sites, and `UnemittedGap` dispositions
//!    in the 12-class `PropertyRegistry`.
//! 3. End-to-end real `rustc` MIR capture (`anneal-rustc-capture`), unit-level
//!    `audit_captured_units_fault_census`, workspace scaffolding, and negative
//!    tampering rejection via `reconcile_workspace_fault_coverage`.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_rustc_capture::lean_emit::{
    IrPlace, IrRvalue, IrStatement, IrStatementKind, emit_mir_lean_module,
};
use cargo_anneal::{
    CaptureDriverConfig, ExplicitSiteWaiver, FalseProofMutationProbe, FaultSite, FaultSiteCensus,
    FaultSiteCoverageReconciler, MutationProbeScenario, PropertyClass, PropertyDisposition,
    PropertyRegistry, ScaffoldConfig, UncoveredReason, WaiverKind,
    audit_captured_units_fault_census, reconcile_workspace_fault_coverage, run_cargo_capture,
    scaffold_workspace_with_config,
};

struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(label: &str) -> Self {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = env::temp_dir().join(format!(
            "cargo-anneal-fault-probes-{label}-{}-{nanos}-{seq}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("create temporary test directory");
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
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
    if default_bin.is_file() {
        return default_bin;
    }

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let status = Command::new(cargo_bin)
        .current_dir(checkout_root)
        .args(["build", "-p", "anneal-rustc-capture", "--bin", "anneal-rustc-capture"])
        .status()
        .expect("invoke cargo build -p anneal-rustc-capture");
    assert!(status.success(), "cargo build -p anneal-rustc-capture must succeed");
    assert!(
        default_bin.is_file(),
        "expected compiled wrapper binary at {}",
        default_bin.display()
    );
    default_bin
}

fn assert_probe_roundtrips_and_catches_omission(probe: FalseProofMutationProbe) {
    let scenario = MutationProbeScenario::build(probe);
    let reconciler = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());

    // 1. Emitted `.lean` MIR module must parse strictly to the identical census.
    let mod_name = format!("Mir.Probes.{}", probe.as_str());
    let lean_src = emit_mir_lean_module(&mod_name, &scenario.mir);
    let lean_census =
        FaultSiteCensus::from_lean_mir_module(&lean_src).expect("strict parse emitted Mir module");
    assert_eq!(
        lean_census, scenario.census,
        "{probe}: IR census and Lean MIR census diverged"
    );

    // 2. Unmutated baseline obligations pass fail-closed reconciliation.
    let (baseline_report, mutant_report) = scenario.execute(&reconciler);
    assert!(
        baseline_report.is_covered(),
        "{probe} baseline unexpectedly failed:\n{}",
        baseline_report.render_diagnostic_report()
    );
    assert!(baseline_report.clone().into_result().is_ok());

    // 3. Mutated obligations fail closed on the exact stripped fault sites.
    assert!(
        !mutant_report.is_covered(),
        "{probe} mutant must be rejected fail-closed"
    );
    let err = mutant_report
        .clone()
        .into_result()
        .expect_err("mutant must return CoverageReconciliationError");
    let diag_text = err.to_string();
    assert!(diag_text.contains("FAULT_COVERAGE_FAILED"), "{diag_text}");

    let actual_uncovered: BTreeSet<FaultSite> = mutant_report
        .uncovered_diagnostics
        .iter()
        .map(|d| {
            assert_eq!(
                d.reason,
                UncoveredReason::OmittedObligation,
                "{probe}: unexpected uncovered reason on {d}"
            );
            d.site
        })
        .collect();
    assert_eq!(
        actual_uncovered, scenario.expected_uncovered_sites,
        "{probe}: uncovered site set mismatch"
    );
}

#[test]
fn call_arg_blind_probe_catches_omitted_argument_deref_obligation() {
    assert_probe_roundtrips_and_catches_omission(FalseProofMutationProbe::CallArgBlindProbe);

    let scenario = MutationProbeScenario::build(FalseProofMutationProbe::CallArgBlindProbe);
    assert_eq!(
        scenario.expected_uncovered_sites,
        BTreeSet::from([FaultSite::terminator(
            0,
            0,
            PropertyClass::PointerDereference
        )])
    );
    assert!(
        scenario
            .census
            .sites
            .contains(&FaultSite::terminator(0, 0, PropertyClass::CallContract))
    );
}

#[test]
fn switch_break_strip_probe_catches_omitted_otherwise_branch_div_ub() {
    assert_probe_roundtrips_and_catches_omission(FalseProofMutationProbe::SwitchBreakStripProbe);

    let scenario = MutationProbeScenario::build(FalseProofMutationProbe::SwitchBreakStripProbe);
    assert_eq!(
        scenario.expected_uncovered_sites,
        BTreeSet::from([
            FaultSite::statement(2, 0, PropertyClass::DivRemUb),
            FaultSite::statement(2, 0, PropertyClass::UninitRead),
            FaultSite::terminator(2, 1, PropertyClass::UninitRead),
        ])
    );
    assert!(scenario.census.sites.contains(&FaultSite::terminator(
        0,
        0,
        PropertyClass::SwitchExhaustiveness
    )));
}

#[test]
fn loop_update_overflow_probe_catches_omitted_latch_overflow_and_total_termination() {
    assert_probe_roundtrips_and_catches_omission(FalseProofMutationProbe::LoopUpdateOverflowProbe);

    let scenario = MutationProbeScenario::build(FalseProofMutationProbe::LoopUpdateOverflowProbe);
    assert_eq!(
        scenario.expected_uncovered_sites,
        BTreeSet::from([FaultSite::statement(
            2,
            0,
            PropertyClass::ArithmeticOverflow
        )])
    );
    assert_eq!(scenario.census.loop_back_edges, vec![(2, 1)]);

    // Also verify that stripping `LoopTermination` at `(bb2, term[1])` without a
    // partial-correctness waiver is rejected under `PropertyRegistry::strict()`.
    let loop_term_site = FaultSite::terminator(2, 1, PropertyClass::LoopTermination);
    let mut missing_term = scenario.baseline_coverage.discharged_sites.clone();
    assert!(missing_term.remove(&loop_term_site));
    let strict_rec = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());
    let rep = strict_rec.reconcile(&scenario.census, missing_term, []);
    assert!(!rep.is_covered());
    assert_eq!(rep.uncovered_diagnostics.len(), 1);
    assert_eq!(rep.uncovered_diagnostics[0].site, loop_term_site);
}

#[test]
fn deref_alias_probe_catches_omitted_pointer_dereference_and_borrows_check() {
    assert_probe_roundtrips_and_catches_omission(FalseProofMutationProbe::DerefAliasProbe);

    let scenario = MutationProbeScenario::build(FalseProofMutationProbe::DerefAliasProbe);
    assert_eq!(
        scenario.expected_uncovered_sites,
        BTreeSet::from([FaultSite::statement(
            0,
            0,
            PropertyClass::PointerDereference
        )])
    );
}

#[test]
fn all_four_probes_reject_forged_waivers_and_unemitted_registry_gaps() {
    let strict_rec = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());

    for probe in FalseProofMutationProbe::ALL {
        let scenario = MutationProbeScenario::build(probe);

        // 1. Attempting to paper over the missing obligation site(s) using a
        //    `PartialCorrectnessDivergence` waiver (valid only on `LoopTermination`)
        //    or an empty justification string MUST fail closed.
        let bad_kind_waivers: Vec<ExplicitSiteWaiver> = scenario
            .expected_uncovered_sites
            .iter()
            .map(|&site| {
                ExplicitSiteWaiver::new(
                    site,
                    WaiverKind::PartialCorrectnessDivergence,
                    "forged partial-correctness waiver on safety site",
                )
            })
            .collect();
        let bad_kind_rep = strict_rec.reconcile_with_call_context(
            &scenario.census,
            scenario.mutated_coverage.discharged_sites.iter().copied(),
            bad_kind_waivers,
            &scenario.mutated_coverage.call_context,
        );
        assert!(
            !bad_kind_rep.is_covered(),
            "{probe}: forged PartialCorrectnessDivergence waiver on non-loop site must fail closed"
        );
        assert!(bad_kind_rep
            .uncovered_diagnostics
            .iter()
            .all(|d| matches!(d.reason, UncoveredReason::InvalidWaiver { .. })));

        let blank_reason_waivers: Vec<ExplicitSiteWaiver> = scenario
            .expected_uncovered_sites
            .iter()
            .map(|&site| ExplicitSiteWaiver::new(site, WaiverKind::ScopedUbException, "  "))
            .collect();
        let blank_rep = strict_rec.reconcile_with_call_context(
            &scenario.census,
            scenario.mutated_coverage.discharged_sites.iter().copied(),
            blank_reason_waivers,
            &scenario.mutated_coverage.call_context,
        );
        assert!(
            !blank_rep.is_covered(),
            "{probe}: blank waiver reason must fail closed"
        );

        // 2. Marking any required class as `UnemittedGap` in `PropertyRegistry`
        //    rejects even the unmutated baseline!
        let target_class = scenario
            .expected_uncovered_sites
            .iter()
            .next()
            .expect("non-empty uncovered set")
            .class;
        let gap_reg = PropertyRegistry::strict()
            .try_with_disposition(target_class, PropertyDisposition::UnemittedGap)
            .expect("set UnemittedGap");
        let gap_rec = FaultSiteCoverageReconciler::new(gap_reg);
        let (gap_baseline, _) = scenario.execute(&gap_rec);
        assert!(
            !gap_baseline.is_covered(),
            "{probe}: UnemittedGap on `{target_class}` must reject baseline"
        );
        assert!(gap_baseline.uncovered_diagnostics.iter().any(|d| {
            d.site.class == target_class && d.reason == UncoveredReason::RegistryUnemittedGap
        }));

        // 3. Injecting an `UnsupportedFallback` construct (`ThreadLocalRef`) into
        //    the probe body cannot be waived even with `TrustedAssumptionBoundary`.
        let mut unsupported_mir = scenario.mir.clone();
        unsupported_mir.basic_blocks[0].statements.push(IrStatement {
            kind: IrStatementKind::Assign(
                IrPlace {
                    local_: 0,
                    projection: Vec::new(),
                },
                IrRvalue::ThreadLocalRef(String::from("probes::TLS_SLOT")),
            ),
            span: String::from("probes.rs:99:5"),
            comment: None,
        });
        let unsupported_census = FaultSiteCensus::from_ir_captured_mir(&unsupported_mir);
        let tls_site = unsupported_census
            .sites
            .iter()
            .copied()
            .find(|s| s.class == PropertyClass::UnsupportedFallback)
            .expect("census must record UnsupportedFallback site");
        let forged_waiver = ExplicitSiteWaiver::new(
            tls_site,
            WaiverKind::TrustedAssumptionBoundary,
            "attempt to waive UnsupportedFallback",
        );
        let tls_rep = strict_rec.reconcile(
            &unsupported_census,
            unsupported_census.sites.iter().copied(),
            [forged_waiver],
        );
        assert!(!tls_rep.is_covered());
        assert!(tls_rep.uncovered_diagnostics.iter().any(|d| {
            d.site == tls_site && matches!(d.reason, UncoveredReason::UnsupportedConstruct { .. })
        }));
    }
}

#[test]
fn end_to_end_rustc_captured_workspace_reconciles_and_rejects_negative_tampering() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);
    let tmp = TempDirGuard::new("e2e-negative-coverage");
    let ws = tmp.path();
    fs::create_dir_all(ws.join("src")).expect("create src/");

    let anneal_spec_dir = checkout_root.join("crates/anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "fault_probe_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(ws.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    let lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[inline(never)]
pub fn helper_leaf(v: u32) -> u32 {
    v.wrapping_add(1)
}

#[inline(never)]
pub fn helper_inc(v: u32) -> u32 {
    helper_leaf(v)
}

#[anneal_spec::spec(requires: d != 0 && shift < 8)]
pub fn rich_subject(arr: &[u32; 4], idx: usize, d: u32, shift: u32) -> u32 {
    let base = if idx < 4 { arr[idx] } else { arr[0] };
    let mut acc = (base / d) << shift;
    let mut i = 0u32;
    while i < 3 {
        acc = helper_inc(acc);
        i += 1;
    }
    acc
}
"#;
    fs::write(ws.join("src/lib.rs"), lib_rs).expect("write src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(ws);
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (manifest, records) = run_cargo_capture(&driver_cfg).expect("capture crate MIR");
    assert!(manifest.compilation_succeeded);

    // 1. Unit-level strict MIR fault-site census over real `rustc` output must succeed.
    let unit_censuses = audit_captured_units_fault_census(&driver_cfg.units_dir, &records)
        .expect("all rustc-captured MIR modules must parse strictly");
    let subj_census = unit_censuses
        .get("fault_probe_pkg::rich_subject")
        .expect("find rich_subject census");
    let classes_seen: BTreeSet<PropertyClass> =
        subj_census.sites.iter().map(|s| s.class).collect();
    for expected_class in [
        PropertyClass::ArithmeticOverflow,
        PropertyClass::ShiftBounds,
        PropertyClass::DivRemUb,
        PropertyClass::PointerDereference,
        PropertyClass::SliceArrayBounds,
        PropertyClass::CallContract,
        PropertyClass::LoopTermination,
        PropertyClass::SwitchExhaustiveness,
        PropertyClass::UninitRead,
    ] {
        assert!(
            classes_seen.contains(&expected_class),
            "expected `{expected_class}` in rich_subject census, got {classes_seen:?}"
        );
    }
    assert!(
        !classes_seen.contains(&PropertyClass::UnsupportedFallback),
        "supported Rust code must not trigger UnsupportedFallback: {:?}",
        subj_census.unscannable_reasons
    );

    // 2. Scaffold workspace and verify clean reconciliation across subject & transitive callees.
    let mut scaffold_cfg = ScaffoldConfig::new(ws);
    scaffold_cfg.units_dir = Some(driver_cfg.units_dir.clone());
    scaffold_cfg.anneal_repo_root = Some(checkout_root);
    scaffold_workspace_with_config(&scaffold_cfg, &records).expect("scaffold workspace");

    let clean_reports = reconcile_workspace_fault_coverage(ws, &records)
        .expect("clean scaffolded workspace must pass fault-site reconciliation");
    assert!(clean_reports.iter().all(|r| r.is_covered()));

    let ob_path = ws.join(".anneal/generated/Obligations/FaultProbePkg/rich_subject.lean");
    let ver_path = ws.join(".anneal/generated/Verify/FaultProbePkg/rich_subject.lean");
    let mir_path = ws.join(".anneal/generated/Mir/FaultProbePkg/rich_subject.lean");
    let orig_ob = fs::read_to_string(&ob_path).expect("read Obligations");
    let orig_ver = fs::read_to_string(&ver_path).expect("read Verify");
    let orig_mir = fs::read_to_string(&mir_path).expect("read Mir");

    // Negative Attack A: Strip direct callee `helper_inc` from `defaultCallees` in `Obligations`.
    let stripped_direct_ob = orig_ob
        .replace("Mir.FaultProbePkg.helper_inc.body, ", "")
        .replace(", Mir.FaultProbePkg.helper_inc.body", "")
        .replace("Mir.FaultProbePkg.helper_inc.body", "")
        .replace("[]", ".nil");
    fs::write(&ob_path, &stripped_direct_ob).expect("write tampered Obligations");
    let err_a = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("stripping direct callee from defaultCallees must fail closed");
    assert!(err_a.contains("fault_probe_pkg::helper_inc"), "{err_a}");
    fs::write(&ob_path, &orig_ob).expect("restore Obligations");

    // Negative Attack B: Strip grand-callee `helper_leaf` from `defaultCallees` while leaving `helper_inc`.
    let stripped_grand_ob = orig_ob
        .replace("Mir.FaultProbePkg.helper_leaf.body, ", "")
        .replace(", Mir.FaultProbePkg.helper_leaf.body", "")
        .replace("Mir.FaultProbePkg.helper_leaf.body", "")
        .replace("[]", ".nil");
    fs::write(&ob_path, &stripped_grand_ob).expect("write grand-callee-stripped Obligations");
    let err_b = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("stripping grand-callee from defaultCallees must fail closed");
    assert!(err_b.contains("fault_probe_pkg::helper_leaf"), "{err_b}");
    fs::write(&ob_path, &orig_ob).expect("restore Obligations");

    // Negative Attack C: Unpin `claim` body while planting a decoy string literal containing the expected tokens.
    let decoy_unpinned_ob = format!(
        "{}\ndef decoyString : String := \"def claim : Claim := {{ body := Mir.FaultProbePkg.rich_subject.body, callees := defaultCallees }}\"\n",
        orig_ob.replace(
            "body := Mir.FaultProbePkg.rich_subject.body",
            "body := Mir.FaultProbePkg.helper_inc.body",
        )
    );
    let decoy_unpinned_ob = decoy_unpinned_ob.replace(
        "end Obligations.FaultProbePkg.rich_subject",
        "def decoyAfter : Nat := 0\nend Obligations.FaultProbePkg.rich_subject",
    );
    fs::write(&ob_path, &decoy_unpinned_ob).expect("write decoy Obligations");
    let err_c = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("decoy string literal in Obligations must not bypass claim pin check");
    assert!(
        err_c.contains("FAULT_COVERAGE_FAILED `fault_probe_pkg::rich_subject`"),
        "{err_c}"
    );
    fs::write(&ob_path, &orig_ob).expect("restore Obligations");

    // Negative Attack D: Tamper `Verify` certificate to prove `True` (even with decoy comment/string).
    fs::write(
        &ver_path,
        "import Trusted\nnamespace Verify.FaultProbePkg.rich_subject\n-- theorem verified : VerificationResult Obligations.FaultProbePkg.rich_subject.claim :=\ndef decoy : String := \"VerificationResult Obligations.FaultProbePkg.rich_subject.claim\"\ntheorem verified : True := trivial\nend Verify.FaultProbePkg.rich_subject\n",
    )
    .expect("write rogue Verify");
    let err_d = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("rogue Verify certificate must fail closed");
    assert!(
        err_d.contains("FAULT_COVERAGE_FAILED `fault_probe_pkg::rich_subject`"),
        "{err_d}"
    );
    fs::write(&ver_path, &orig_ver).expect("restore Verify");

    // Negative Attack E: Deleting generated `Obligations` or `Verify` file on disk must fail closed.
    fs::remove_file(&ob_path).expect("delete Obligations");
    let err_del_ob = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("missing Obligations module on disk must fail closed");
    assert!(
        err_del_ob.contains("missing or unreadable generated Obligations module"),
        "{err_del_ob}"
    );
    fs::write(&ob_path, &orig_ob).expect("restore Obligations");

    fs::remove_file(&ver_path).expect("delete Verify");
    let err_del_ver = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("missing Verify module on disk must fail closed");
    assert!(
        err_del_ver.contains("missing or unreadable generated Verify module"),
        "{err_del_ver}"
    );
    fs::write(&ver_path, &orig_ver).expect("restore Verify");

    // Negative Attack F: Tampering on-disk `.anneal/generated/Mir/FaultProbePkg/rich_subject.lean`
    // MUST fail closed directly on SHA-256 mismatch (never silently falling back to `target/anneal/units`),
    // AND even with an unpinned SHA, non-inline helper syntax fails closed in the strict MIR parser.
    fs::write(
        &mir_path,
        "import Trusted\nnamespace Mir.FaultProbePkg.rich_subject\ndef sneakyHelper : Nat := 0\ndef body : CapturedMir := { defPath := \"fault_probe_pkg::rich_subject\", basicBlocks := [] }\nend Mir.FaultProbePkg.rich_subject\n",
    )
    .expect("write tampered Mir");
    let err_f_sha = reconcile_workspace_fault_coverage(ws, &records)
        .expect_err("on-disk Mir tampering must fail closed on SHA mismatch without fallback");
    assert!(err_f_sha.contains("MIR SHA-256 mismatch"), "{err_f_sha}");

    let mut unpinned_records = records.clone();
    for rec in &mut unpinned_records {
        if rec.target.def_id == "fault_probe_pkg::rich_subject" {
            rec.target.mir_module_sha256.clear();
        }
    }
    let err_f_parse = reconcile_workspace_fault_coverage(ws, &unpinned_records)
        .expect_err("non-inline helper declaration in Mir module must fail closed");
    assert!(err_f_parse.contains("unsupported_fallback"), "{err_f_parse}");
    fs::write(&mir_path, &orig_mir).expect("restore Mir");

    // Confirm full restoration passes again.
    let restored =
        reconcile_workspace_fault_coverage(ws, &records).expect("restored workspace must pass");
    assert!(restored.iter().all(|r| r.is_covered()));
}

#[test]
fn external_spec_subject_rejects_stateless_verify_surface_tampering() {
    use anneal_rustc_capture::{CapturedItemKind, CapturedTarget, UnitTargetRecord};
    use cargo_anneal::obligations::{
        AuthoredItemModules, ExternalSpecContractRef, SubjectObligationBundle,
        reconcile_subject_bundle_coverage, render_obligations_module_with_options,
        render_verify_module_with_options,
    };

    let scenario = MutationProbeScenario::build(FalseProofMutationProbe::CallArgBlindProbe);
    let mir_lean = emit_mir_lean_module("Mir.Probes.call_arg_blind", &scenario.mir);
    let subject = UnitTargetRecord {
        target: CapturedTarget {
            def_id: String::from("probes::call_arg_blind"),
            mir_module_path: String::from("Mir/Probes/call_arg_blind.lean"),
            mir_module_sha256: String::new(),
        },
        lean_module_name: String::from("Mir.Probes.call_arg_blind"),
        item_kind: CapturedItemKind::Subject,
        associated_subject_def_id: None,
        trait_impls: Vec::new(),
    };
    let bundle = SubjectObligationBundle {
        subject,
        item_module_suffix: String::from("Probes.call_arg_blind"),
        item_rel_path: PathBuf::from("Probes/call_arg_blind.lean"),
        inline_requires: Vec::new(),
        inline_ensures: Vec::new(),
        inline_qualifiers: Vec::new(),
        external_specs: Vec::new(),
        called_callees: Vec::new(),
        transitive_callees: Vec::new(),
        external_spec_callees: vec![ExternalSpecContractRef {
            target_def_id: String::from("probes::callee_u32"),
            sidecar_module_suffix: String::from("Probes.__ext_callee_u32"),
            req_module_suffix: None,
            ens_module_suffix: None,
        }],
        spec_callees: Vec::new(),
        spec_companions_with_calls: BTreeSet::new(),
    };

    let authored = AuthoredItemModules::default();
    let ob_src = render_obligations_module_with_options(&bundle, authored);
    let valid_ver_src = render_verify_module_with_options(&bundle, authored);

    // Valid rendered ModularVerificationResult passes reconciliation cleanly.
    let ok_rep = reconcile_subject_bundle_coverage(
        &bundle,
        authored,
        &mir_lean,
        Some(&ob_src),
        Some(&valid_ver_src),
    );
    assert!(
        ok_rep.is_covered(),
        "valid modular Verify should pass:\n{}",
        ok_rep.render_diagnostic_report()
    );

    // Tampering `Verify` to prove stateless `VerificationResult ...claim` instead of
    // `ModularVerificationResult ...modularClaim` (which drops `envAssumed` call contracts)
    // MUST fail closed!
    let downgraded_ver_src = valid_ver_src
        .replace("ModularVerificationResult", "VerificationResult")
        .replace(
            "Obligations.Probes.call_arg_blind.modularClaim",
            "Obligations.Probes.call_arg_blind.claim",
        );
    let bad_rep = reconcile_subject_bundle_coverage(
        &bundle,
        authored,
        &mir_lean,
        Some(&ob_src),
        Some(&downgraded_ver_src),
    );
    assert!(
        !bad_rep.is_covered(),
        "downgrading ModularVerificationResult to stateless VerificationResult must fail closed"
    );
    assert!(bad_rep.uncovered_diagnostics.iter().any(|d| {
        matches!(d.reason, UncoveredReason::UnsupportedConstruct { .. })
    }));
}
