//! End-to-end integration test for the Rust-to-Lean verification pipeline.
//!
//! Exercises the complete workflow from a real Rust crate through
//! `anneal-rustc-capture` (`RUSTC_WORKSPACE_WRAPPER`), `cargo-anneal` manifest
//! aggregation, pure generated-assembly workspace scaffolding (typeclass
//! defaults without generate-then-edit stamping), Lean 4 kernel checking of
//! `VerificationResult` theorems under Lake, anti-cheat `TrustedBoundary`
//! rejection of `sorry` and rogue `axiom` declarations, and scoped conditional
//! verification via `Assumptions.<Item>`.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_rustc_capture::{CapturedItemKind, sha256_hex};
use cargo_anneal::{
    CaptureDriverConfig, CliSubcommand, ScaffoldConfig, SPEC_LOCK_REL_PATH, VerificationStatus,
    VerifyConfig, check_specs_non_vacuous, execute_cli, group_subject_obligations,
    parse_capture_manifest, parse_cli_args, render_agent_context, render_extract_report,
    render_lock_specs_report, render_scaffold_report, render_verification_report,
    run_cargo_capture, scaffold_workspace_with_config, verify_spec_lock, verify_workspace,
    verify_workspace_with_config, verify_workspace_with_options,
};

fn unique_temp_dir(label: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let dir = env::temp_dir().join(format!(
        "cargo-anneal-e2e-{}-{}-{}",
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
fn end_to_end_rustc_capture_scaffold_and_lean_kernel_verify() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_crate = unique_temp_dir("pipeline");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create temporary crate src/");

    let anneal_spec_dir = checkout_root.join("crates").join("anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "canary_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    // Populate the temporary crate with:
    // 1. `identity_u32` annotated with inline `#[anneal_spec::spec]`
    // 2. `external_id_u32` accompanied by an `#[anneal_spec::external_spec]`
    //    sidecar contract
    // 3. `const_forty_two` whose specification will be overridden purely in
    //    Lean via an authored `Specs/CanaryPkg/const_forty_two.lean` `ItemSpec`
    //    instance
    // 4. `is_small_u32` annotated with `#[anneal_spec::model]`
    let lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[anneal_spec::spec(requires: x == 7, ensures: |ref ret| *ret == 7)]
pub fn identity_u32(x: u32) -> u32 {
    x
}

pub fn external_id_u32(x: u32) -> u32 {
    x
}

#[anneal_spec::external_spec(
    for = external_id_u32,
    requires: x == 9,
    ensures: |ret: u32| ret == 9,
)]
fn external_id_u32_spec(x: u32) -> u32;

pub const fn const_forty_two() -> u32 {
    42
}

#[anneal_spec::model]
pub const fn is_small_u32(x: u32) -> bool {
    x < 1000
}
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write src/lib.rs");

    // 1. Run `cargo_anneal::run_cargo_capture` using the compiled
    //    `anneal-rustc-capture` workspace wrapper.
    let mut driver_cfg = CaptureDriverConfig::new(&temp_crate);
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (manifest, records) =
        run_cargo_capture(&driver_cfg).expect("run_cargo_capture must succeed");

    assert!(manifest.compilation_succeeded);
    assert!(!manifest.rust_sources.is_empty());
    assert!(!manifest.targets.is_empty());

    let root_manifest_path = driver_cfg.units_dir.join("CaptureManifest.json");
    assert!(root_manifest_path.is_file());
    let parsed_root = parse_capture_manifest(
        &fs::read_to_string(&root_manifest_path).expect("read CaptureManifest.json"),
    )
    .expect("parse root CaptureManifest.json");
    assert_eq!(parsed_root, manifest);

    // 2. Verify contract role classification and obligation grouping.
    let model_record = records
        .iter()
        .find(|r| r.target.def_id == "canary_pkg::is_small_u32")
        .expect("find model item canary_pkg::is_small_u32");
    assert_eq!(model_record.item_kind, CapturedItemKind::Model);

    let bundles = group_subject_obligations(&records);
    let id_bundle = bundles
        .iter()
        .find(|b| b.subject.target.def_id == "canary_pkg::identity_u32")
        .expect("find subject bundle for canary_pkg::identity_u32");
    assert_eq!(id_bundle.item_module_suffix, "CanaryPkg.identity_u32");
    assert_eq!(id_bundle.inline_requires.len(), 1);
    assert_eq!(id_bundle.inline_ensures.len(), 1);
    assert_eq!(id_bundle.inline_qualifiers.len(), 1);

    let ext_id_bundle = bundles
        .iter()
        .find(|b| b.subject.target.def_id == "canary_pkg::external_id_u32")
        .expect("find subject bundle for canary_pkg::external_id_u32");
    assert_eq!(ext_id_bundle.item_module_suffix, "CanaryPkg.external_id_u32");
    assert_eq!(ext_id_bundle.inline_requires.len(), 1);
    assert_eq!(ext_id_bundle.inline_ensures.len(), 1);
    assert!(!ext_id_bundle.external_specs.is_empty());

    let forty_two_bundle = bundles
        .iter()
        .find(|b| b.subject.target.def_id == "canary_pkg::const_forty_two")
        .expect("find subject bundle for canary_pkg::const_forty_two");
    assert_eq!(
        forty_two_bundle.item_module_suffix,
        "CanaryPkg.const_forty_two"
    );

    // 3. Scaffold the `.anneal/` Lake workspace using pure generated assembly
    //    (default `init_proof_templates == false`). Verify that zero
    //    generate-then-edit files are stamped into `anneal/proofs/`.
    let extract_summary = render_extract_report(&manifest, &records);
    assert!(extract_summary.contains("Subject items: 3"));
    assert!(extract_summary.contains("canary_pkg::identity_u32 -> Mir.CanaryPkg.identity_u32"));

    let scaffold_cfg = ScaffoldConfig {
        workspace_root: temp_crate.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    let report = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("scaffold_workspace_with_config must succeed");
    let scaffold_summary = render_scaffold_report(&report);
    assert!(scaffold_summary.contains("Obligations: 3, Verify: 3"));
    assert!(scaffold_summary.contains("created Specs: 0, preserved Specs: 0"));
    assert!(report.created_spec_files.is_empty());
    assert!(report.created_proof_files.is_empty());
    assert!(!temp_crate.join("anneal/proofs/Specs/CanaryPkg/identity_u32.lean").exists());
    assert!(!temp_crate.join("anneal/proofs/Specs/CanaryPkg/external_id_u32.lean").exists());

    // Verify that the emitted Mir/<Crate>/<Item>.lean files match the manifest
    // SHA-256 digests and contain `layouts`, `body`, and `defaultClaim`.
    for subject_def_id in [
        "canary_pkg::identity_u32",
        "canary_pkg::external_id_u32",
        "canary_pkg::const_forty_two",
    ] {
        let rec = records
            .iter()
            .find(|r| r.target.def_id == subject_def_id)
            .expect("find subject target record");
        let placed_mir = temp_crate
            .join(".anneal/generated")
            .join(&rec.target.mir_module_path);
        let mir_text = fs::read_to_string(&placed_mir).expect("read placed Mir module");
        assert_eq!(
            sha256_hex(mir_text.as_bytes()),
            rec.target.mir_module_sha256
        );
        assert!(mir_text.contains("def layouts : LayoutTable :="));
        assert!(mir_text.contains("def body : CapturedMir :="));
        assert!(mir_text.contains("def defaultClaim : Claim :="));
    }

    // Verify that `Obligations.CanaryPkg.identity_u32` imports only `Trusted`
    // and `Mir.*` (never `Anneal`), defines `defaultPre` and `defaultPost` via
    // `MirBoolPredicateHolds`, and registers `defaultSpec : ItemSpec`.
    let obligations_id_path =
        temp_crate.join(".anneal/generated/Obligations/CanaryPkg/identity_u32.lean");
    let obligations_id_text = fs::read_to_string(&obligations_id_path)
        .expect("read Obligations/CanaryPkg/identity_u32.lean");
    assert!(!obligations_id_text.contains("import Anneal"));
    assert!(
        obligations_id_text
            .contains("import Mir.CanaryPkg.__anodized_fn_requires_identity_u32")
    );
    assert!(
        obligations_id_text
            .contains("import Mir.CanaryPkg.__anodized_fn_ensures_identity_u32")
    );
    assert!(obligations_id_text.contains(
        "def defaultPre (args : List Value) : Prop :=\n  And (Trusted.Sequence.length args = Mir.CanaryPkg.identity_u32.body.argCount) (MirBoolPredicateHolds Mir.CanaryPkg.__anodized_fn_requires_identity_u32.body args)"
    ));
    assert!(obligations_id_text.contains(
        "def defaultPost (args : List Value) (ret : Value) : Prop :=\n  MirBoolPredicateHolds Mir.CanaryPkg.__anodized_fn_ensures_identity_u32.body (List.append args (List.cons ret List.nil))"
    ));
    assert!(obligations_id_text.contains(
        "instance (priority := low) defaultSpec : ItemSpec \"canary_pkg::identity_u32\" where"
    ));
    assert!(obligations_id_text.contains(
        "def refineSpec\n    (extraPre : List Value → Prop)\n    (extraPost : List Value → Value → Prop) :\n    ItemSpec \"canary_pkg::identity_u32\" where"
    ));
    assert!(obligations_id_text.contains(
        "def refineStatefulSpec\n    (extraPre : List Value → Memory → Prop)\n    (extraPost : List Value → Memory → Value → Memory → Prop) :\n    StatefulItemSpec \"canary_pkg::identity_u32\" where"
    ));
    assert!(obligations_id_text.contains(
        "def refineSafeSpec\n    (safetyDomain : List Value → Prop)\n    (extraPre : List Value → Prop)\n    (extraPost : List Value → Value → Prop) :\n    ItemSpec \"canary_pkg::identity_u32\" where"
    ));
    assert!(obligations_id_text.contains(
        "def refineSafeStatefulSpec\n    (safetyDomain : List Value → Memory → Prop)\n    (extraPre : List Value → Memory → Prop)\n    (extraPost : List Value → Memory → Value → Memory → Prop) :\n    StatefulItemSpec \"canary_pkg::identity_u32\" where"
    ));
    assert!(obligations_id_text.contains(
        "def claim [spec : ItemSpec \"canary_pkg::identity_u32\"] : Claim :="
    ));

    // 4. Author `verifyByWP` proofs:
    //    - `identity_u32` and `external_id_u32` have NO `Specs/<Item>.lean`
    //      files on disk at all! They are proved directly against the
    //      generated `Obligations.<Item>.defaultSpec` instance.
    //    - `const_forty_two` overrides its contract purely in Lean by authoring
    //      `anneal/proofs/Specs/CanaryPkg/const_forty_two.lean` with a
    //      normal-priority `instance : ItemSpec "canary_pkg::const_forty_two"`.
    let proof_id_path =
        temp_crate.join("anneal/proofs/Proof/CanaryPkg/identity_u32.lean");
    let proof_ext_path =
        temp_crate.join("anneal/proofs/Proof/CanaryPkg/external_id_u32.lean");
    let specs_42_path =
        temp_crate.join("anneal/proofs/Specs/CanaryPkg/const_forty_two.lean");
    let proof_42_path =
        temp_crate.join("anneal/proofs/Proof/CanaryPkg/const_forty_two.lean");

    fs::create_dir_all(proof_id_path.parent().unwrap()).expect("create Proof/CanaryPkg");
    fs::create_dir_all(specs_42_path.parent().unwrap()).expect("create Specs/CanaryPkg");

    let proof_id_lean = r#"import Trusted
import Anneal
import Mir.CanaryPkg.identity_u32
import Obligations.CanaryPkg.identity_u32

namespace Proof.CanaryPkg.identity_u32

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 2000000 in
theorem verified : VerificationResult Obligations.CanaryPkg.identity_u32.claim :=
  dischargeRustEqU32
    Obligations.CanaryPkg.identity_u32.claim
    4
    64
    Mir.CanaryPkg.__anodized_fn_requires_identity_u32.body
    Mir.CanaryPkg.__anodized_fn_ensures_identity_u32.body
    7

end Proof.CanaryPkg.identity_u32
"#;

    let proof_ext_lean = r#"import Trusted
import Anneal
import Mir.CanaryPkg.external_id_u32
import Obligations.CanaryPkg.external_id_u32

namespace Proof.CanaryPkg.external_id_u32

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 2000000 in
theorem verified : VerificationResult Obligations.CanaryPkg.external_id_u32.claim :=
  dischargeRustEqU32
    Obligations.CanaryPkg.external_id_u32.claim
    4
    64
    Mir.CanaryPkg.__anodized_fn_requires_external_id_u32_spec.body
    Mir.CanaryPkg.__anodized_fn_ensures_external_id_u32_spec.body
    9

end Proof.CanaryPkg.external_id_u32
"#;

    let specs_42_lean = r#"import Trusted
import Obligations.CanaryPkg.const_forty_two

namespace Specs.CanaryPkg.const_forty_two

open Trusted.MirSemantics
open Trusted.VerificationResult

instance : ItemSpec "canary_pkg::const_forty_two" where
  pre args := args = List.nil
  post args ret :=
    And (args = List.nil) (ret = .scalar { bits := 42, sizeBytes := 4 })

end Specs.CanaryPkg.const_forty_two
"#;

    let proof_42_lean = r#"import Trusted
import Anneal
import Mir.CanaryPkg.const_forty_two
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two

namespace Proof.CanaryPkg.const_forty_two

open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : VerificationResult Obligations.CanaryPkg.const_forty_two.claim :=
  verifyByWP Obligations.CanaryPkg.const_forty_two.claim 4 (by
    intro args h_pre
    subst h_pre
    exact ⟨rfl, rfl⟩)

end Proof.CanaryPkg.const_forty_two
"#;

    fs::write(&proof_id_path, proof_id_lean).expect("write identity_u32 proof");
    fs::write(&proof_ext_path, proof_ext_lean).expect("write external_id_u32 proof");
    fs::write(&specs_42_path, specs_42_lean).expect("write const_forty_two spec override");
    fs::write(&proof_42_path, proof_42_lean).expect("write const_forty_two proof");

    // Re-run `scaffold_workspace_with_config` to confirm that regenerating
    // `.anneal/generated/` preserves the authored files and still does not
    // stamp out `Specs` files for `identity_u32` or `external_id_u32`.
    let report_rerun = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("re-run scaffold_workspace_with_config");
    assert_eq!(report_rerun.created_spec_files.len(), 0);
    assert_eq!(report_rerun.preserved_spec_files, vec![specs_42_path.clone()]);
    assert_eq!(report_rerun.created_proof_files.len(), 0);
    assert_eq!(report_rerun.preserved_proof_files.len(), 3);

    // 5. Invoke `verify_workspace` (`lake build` + `TrustedBoundary` verify-audit)
    //    and confirm all 3 items are `VerifiedUnconditional` and pass
    //    `checkStatementOrigins`.
    let verify_report =
        verify_workspace(&temp_crate).expect("verify_workspace must succeed unconditionally");
    assert_eq!(
        verify_report.status_for("Verify.CanaryPkg.identity_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        verify_report.status_for("Verify.CanaryPkg.external_id_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        verify_report.status_for("Verify.CanaryPkg.const_forty_two"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );

    let olean_id = temp_crate
        .join(".anneal/.lake/build/lib/lean/Verify/CanaryPkg/identity_u32.olean");
    let olean_ext = temp_crate
        .join(".anneal/.lake/build/lib/lean/Verify/CanaryPkg/external_id_u32.olean");
    let olean_42 = temp_crate
        .join(".anneal/.lake/build/lib/lean/Verify/CanaryPkg/const_forty_two.olean");
    assert!(olean_id.is_file());
    assert!(olean_ext.is_file());
    assert!(olean_42.is_file());
    assert!(temp_crate.join(".anneal/generated/CrateVerify.lean").is_file());
    assert!(temp_crate.join(".anneal/.lake/build/lib/lean/CrateVerify.olean").is_file());

    let single_item_report = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate).with_item_filter(Some("identity_u32".to_string())),
    )
    .expect("single-item verify --item identity_u32 must succeed");
    assert_eq!(single_item_report.items.len(), 1);
    assert_eq!(
        single_item_report.status_for("Verify.CanaryPkg.identity_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );

    // 5b. Exercise `lock-specs`, `agent-context`, and `agent-verify` along with
    //     anti-cheating negative tests for the agent harness workflow.
    let lock_cli_opts = parse_cli_args([
        "cargo-anneal",
        "anneal",
        "lock-specs",
        "--workspace-root",
        temp_crate.to_str().expect("utf8 path"),
        "--anneal-root",
        checkout_root.to_str().expect("utf8 path"),
        "--from-units",
    ])
    .expect("parse lock-specs CLI options");
    assert_eq!(lock_cli_opts.subcommand, CliSubcommand::LockSpecs);
    execute_cli(&lock_cli_opts).expect("execute lock-specs must succeed");

    let spec_lock_path = temp_crate.join(SPEC_LOCK_REL_PATH);
    assert!(spec_lock_path.is_file());
    let lock_summary = render_lock_specs_report(&temp_crate, &spec_lock_path)
        .expect("render_lock_specs_report must succeed");
    assert!(lock_summary.contains("Locked Specs files: 1"));
    assert!(lock_summary.contains("Non-vacuity check: PASS"));

    let verify_summary = render_verification_report(&verify_report);
    assert!(verify_summary.contains("Verify.CanaryPkg.identity_u32: UNCONDITIONAL"));
    assert!(verify_summary.contains("Totals: 3 unconditional, 0 conditional"));
    assert!(verify_summary.contains("TrustedBoundary kernel replay: PASS"));

    let locked_manifest =
        verify_spec_lock(&temp_crate, &records).expect("verify_spec_lock must succeed");
    assert_eq!(locked_manifest.locked_specs_files.len(), 1);
    assert_eq!(
        locked_manifest.locked_specs_files[0].rel_path,
        "anneal/proofs/Specs/CanaryPkg/const_forty_two.lean"
    );
    assert!(locked_manifest.locked_assumptions_files.is_empty());

    let full_agent_ctx =
        render_agent_context(&temp_crate, &records, None).expect("render full agent context");
    assert!(full_agent_ctx.contains("- **Total Subject Items**: 3"));
    assert!(full_agent_ctx.contains("- **Proof Status**: 3 Present, 0 Missing"));
    assert!(full_agent_ctx.contains("- **Spec Lock (`.anneal/spec-lock.json`)**: Active (Locked)"));
    assert!(full_agent_ctx.contains("## Item `canary_pkg::identity_u32` (`CanaryPkg.identity_u32`)"));
    assert!(full_agent_ctx.contains("## Item `canary_pkg::const_forty_two` (`CanaryPkg.const_forty_two`)"));

    let filtered_agent_ctx = render_agent_context(&temp_crate, &records, Some("identity_u32"))
        .expect("render filtered agent context");
    assert!(filtered_agent_ctx.contains("- **Total Subject Items**: 1"));
    assert!(filtered_agent_ctx.contains("CanaryPkg.identity_u32"));
    assert!(!filtered_agent_ctx.contains("CanaryPkg.const_forty_two"));

    let agent_verify_opts = parse_cli_args([
        "cargo-anneal",
        "anneal",
        "agent-verify",
        "--workspace-root",
        temp_crate.to_str().expect("utf8 path"),
        "--anneal-root",
        checkout_root.to_str().expect("utf8 path"),
        "--from-units",
    ])
    .expect("parse agent-verify CLI options");
    assert_eq!(agent_verify_opts.subcommand, CliSubcommand::AgentVerify);
    assert!(agent_verify_opts.locked_specs);

    let agent_verify_report = verify_workspace_with_options(&agent_verify_opts)
        .expect("agent-verify must succeed when specs and proofs are intact");
    assert_eq!(
        agent_verify_report.status_for("Verify.CanaryPkg.identity_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );

    // Negative check 1: Adding an unlocked `Specs/<Item>.lean` (Spec-Override
    // loophole where an agent creates `Specs/CanaryPkg/identity_u32.lean` to
    // override `defaultSpec` with a vacuous or trivial contract).
    let unlocked_spec_id_path =
        temp_crate.join("anneal/proofs/Specs/CanaryPkg/identity_u32.lean");
    fs::write(
        &unlocked_spec_id_path,
        "prelude\nimport Trusted\nnamespace Specs.CanaryPkg.identity_u32\nopen Trusted.VerificationResult\ninstance : ItemSpec \"canary_pkg::identity_u32\" where\n  pre := fun _ => False\n  post := fun _ _ => True\nend Specs.CanaryPkg.identity_u32\n",
    )
    .expect("write unlocked Specs override");
    let unlocked_spec_err = verify_workspace_with_options(&agent_verify_opts)
        .expect_err("agent-verify must reject adding an unlocked Specs/<Item>.lean file");
    assert!(
        unlocked_spec_err.contains(
            "unlocked Specs file 'anneal/proofs/Specs/CanaryPkg/identity_u32.lean' was added"
        ),
        "expected unlocked Specs rejection, got: {unlocked_spec_err}"
    );
    fs::remove_file(&unlocked_spec_id_path).expect("remove unlocked Specs override");

    // Negative check 2: Modifying a locked `Specs/<Item>.lean`.
    let weakened_specs_42 = specs_42_lean.replace(
        "And (args = List.nil) (ret = .scalar { bits := 42, sizeBytes := 4 })",
        "True",
    );
    fs::write(&specs_42_path, &weakened_specs_42).expect("write modified locked Specs file");
    let modified_spec_err = verify_workspace_with_options(&agent_verify_opts)
        .expect_err("agent-verify must reject modifying a locked Specs/<Item>.lean file");
    assert!(
        modified_spec_err.contains(
            "locked Specs file 'anneal/proofs/Specs/CanaryPkg/const_forty_two.lean' was modified"
        ),
        "expected modified Specs rejection, got: {modified_spec_err}"
    );
    fs::write(&specs_42_path, specs_42_lean).expect("restore locked Specs file");

    // Negative check 3: Adding an unlocked `Assumptions/<Item>.lean`.
    let unlocked_assumptions_id_path =
        temp_crate.join("anneal/proofs/Assumptions/CanaryPkg/identity_u32.lean");
    fs::create_dir_all(unlocked_assumptions_id_path.parent().unwrap())
        .expect("create Assumptions/CanaryPkg");
    fs::write(
        &unlocked_assumptions_id_path,
        "prelude\nimport Trusted\nimport Obligations.CanaryPkg.identity_u32\nnamespace Assumptions.CanaryPkg.identity_u32\naxiom fake : Trusted.VerificationResult.VerificationResult Obligations.CanaryPkg.identity_u32.claim\nend Assumptions.CanaryPkg.identity_u32\n",
    )
    .expect("write unlocked Assumptions file");
    let unlocked_assump_err = verify_workspace_with_options(&agent_verify_opts)
        .expect_err("agent-verify must reject adding an unlocked Assumptions/<Item>.lean file");
    assert!(
        unlocked_assump_err.contains(
            "unlocked Assumptions file 'anneal/proofs/Assumptions/CanaryPkg/identity_u32.lean' was added"
        ),
        "expected unlocked Assumptions rejection, got: {unlocked_assump_err}"
    );
    fs::remove_file(&unlocked_assumptions_id_path).expect("remove unlocked Assumptions file");

    // Negative check 4: Tampering with
    // `.anneal/generated/Obligations/<Item>.lean` is deterministically
    // overwritten and restored before Lake runs.
    fs::write(
        &obligations_id_path,
        "-- tampered generated obligation file\n",
    )
    .expect("tamper with generated Obligations file");
    verify_workspace_with_options(&agent_verify_opts)
        .expect("agent-verify must deterministically regenerate tampered .anneal/generated/Obligations/<Item>.lean");
    let restored_obligations_id =
        fs::read_to_string(&obligations_id_path).expect("read restored Obligations file");
    assert_eq!(
        restored_obligations_id, obligations_id_text,
        "tampered .anneal/generated/Obligations/<Item>.lean must be restored byte-for-byte"
    );

    // Negative check 5 (Check 4): Authoring `Specs/CanaryPkg/identity_u32.lean`
    // that drops the Rust `#[spec]` `ensures` clause (without `refineSpec` or
    // `rustEnsures`) is rejected by `check_specs_non_vacuous`.
    fs::write(
        &unlocked_spec_id_path,
        "prelude\nimport Trusted\nimport Obligations.CanaryPkg.identity_u32\nnamespace Specs.CanaryPkg.identity_u32\nopen Trusted.VerificationResult\ninstance : ItemSpec \"canary_pkg::identity_u32\" where\n  pre args := Obligations.CanaryPkg.identity_u32.rustRequires args\n  post _ _ := True\nend Specs.CanaryPkg.identity_u32\n",
    )
    .expect("write Specs override dropping rustEnsures");
    let drop_ensures_err = check_specs_non_vacuous(&temp_crate)
        .expect_err("check_specs_non_vacuous must reject dropping Rust #[spec] ensures");
    assert!(
        drop_ensures_err.contains("drops the Rust #[spec] `ensures` clause"),
        "expected dropped ensures rejection, got: {drop_ensures_err}"
    );
    fs::remove_file(&unlocked_spec_id_path).expect("remove Specs override dropping rustEnsures");

    // Negative check 6 (Check 5): Removing `import Specs.CanaryPkg.const_forty_two`
    // from `Proof/CanaryPkg/const_forty_two.lean` while
    // `Specs/CanaryPkg/const_forty_two.lean` exists on disk is rejected by
    // `check_specs_non_vacuous`.
    let proof_42_missing_spec_import =
        proof_42_lean.replace("import Specs.CanaryPkg.const_forty_two\n", "");
    fs::write(&proof_42_path, &proof_42_missing_spec_import)
        .expect("write Proof/CanaryPkg/const_forty_two.lean without import Specs");
    let missing_import_err = check_specs_non_vacuous(&temp_crate).expect_err(
        "check_specs_non_vacuous must reject Proof missing import Specs.CanaryPkg.const_forty_two",
    );
    assert!(
        missing_import_err.contains("missing `import Specs.CanaryPkg.const_forty_two`"),
        "expected missing import Specs rejection, got: {missing_import_err}"
    );
    fs::write(&proof_42_path, proof_42_lean).expect("restore Proof/CanaryPkg/const_forty_two.lean");

    // 6. Anti-cheat rejection: `sorry` in `Proof/<Item>.lean` must fail
    //    `verify_workspace`.
    let sorry_proof_42 = r#"import Trusted
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two

namespace Proof.CanaryPkg.const_forty_two

open Trusted.VerificationResult

theorem verified : VerificationResult Obligations.CanaryPkg.const_forty_two.claim := by
  sorry

end Proof.CanaryPkg.const_forty_two
"#;
    fs::write(&proof_42_path, sorry_proof_42).expect("write sorry proof");
    let sorry_err = verify_workspace(&temp_crate)
        .expect_err("verify_workspace must reject sorryAx in Proof.<Item>");
    assert!(
        sorry_err.contains("sorryAx"),
        "expected sorryAx rejection message, got: {sorry_err}"
    );

    // 7. Anti-cheat rejection: rogue `axiom` in `Proof/<Item>.lean` must fail
    //    `verify_workspace`.
    let rogue_axiom_proof_42 = r#"import Trusted
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two

namespace Proof.CanaryPkg.const_forty_two

open Trusted.VerificationResult

axiom cheated : VerificationResult Obligations.CanaryPkg.const_forty_two.claim

theorem verified : VerificationResult Obligations.CanaryPkg.const_forty_two.claim :=
  cheated

end Proof.CanaryPkg.const_forty_two
"#;
    fs::write(&proof_42_path, rogue_axiom_proof_42).expect("write rogue axiom proof");
    let axiom_err = verify_workspace(&temp_crate)
        .expect_err("verify_workspace must reject axiom in Proof.<Item>");
    assert!(
        axiom_err.contains("axiom"),
        "expected axiom rejection message, got: {axiom_err}"
    );

    // 8. Scoped conditional verification via `Assumptions.<Item>`:
    //    - Author `anneal/proofs/Assumptions/CanaryPkg/const_forty_two.lean`
    //      with a scoped `axiom`.
    //    - Verify that strict `verify_workspace(&temp_crate)` rejects it by
    //      default (`allow_assumptions == false`).
    //    - Verify that `verify_workspace_with_config` with
    //      `allow_assumptions == true` succeeds and classifies
    //      `Verify.CanaryPkg.const_forty_two` as `VerifiedConditional`.
    let assumptions_42_path =
        temp_crate.join("anneal/proofs/Assumptions/CanaryPkg/const_forty_two.lean");
    fs::create_dir_all(assumptions_42_path.parent().unwrap())
        .expect("create Assumptions/CanaryPkg");
    let assumptions_42_lean = r#"import Trusted
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two

namespace Assumptions.CanaryPkg.const_forty_two

open Trusted.VerificationResult

axiom assumed_forty_two_contract :
  VerificationResult Obligations.CanaryPkg.const_forty_two.claim

end Assumptions.CanaryPkg.const_forty_two
"#;
    let conditional_proof_42 = r#"import Trusted
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two
import Assumptions.CanaryPkg.const_forty_two

namespace Proof.CanaryPkg.const_forty_two

open Trusted.VerificationResult

theorem verified : VerificationResult Obligations.CanaryPkg.const_forty_two.claim :=
  Assumptions.CanaryPkg.const_forty_two.assumed_forty_two_contract

end Proof.CanaryPkg.const_forty_two
"#;
    fs::write(&assumptions_42_path, assumptions_42_lean).expect("write Assumptions module");
    fs::write(&proof_42_path, conditional_proof_42).expect("write conditional proof");

    let strict_err = verify_workspace(&temp_crate)
        .expect_err("strict verify_workspace must reject conditional assumptions without --allow-assumptions");
    assert!(
        strict_err.contains("Assumptions.CanaryPkg.const_forty_two.assumed_forty_two_contract"),
        "expected conditional assumption name in strict rejection error, got: {strict_err}"
    );

    let conditional_report = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate).with_allow_assumptions(true),
    )
    .expect("verify_workspace_with_config(allow_assumptions = true) must succeed");

    assert_eq!(
        conditional_report.status_for("Verify.CanaryPkg.identity_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        conditional_report.status_for("Verify.CanaryPkg.external_id_u32"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        conditional_report.status_for("Verify.CanaryPkg.const_forty_two"),
        Some(&VerificationStatus::VerifiedConditional {
            assumptions: vec![
                "Assumptions.CanaryPkg.const_forty_two.assumed_forty_two_contract".to_string()
            ],
        })
    );

    let _ = fs::remove_dir_all(&temp_crate);
}
