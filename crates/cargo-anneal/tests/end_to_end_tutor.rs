//! End-to-end integration test for the `examples/tutor` (`frame_tutor`)
//! companion crate and the six-chapter Anneal Tutor progression.
//!
//! Copies `examples/tutor/` into an isolated temporary workspace and drives it
//! through the stages taught in `docs/tutor/`:
//!
//! 1. **Chapters 1 & 2 (`extract` and `scaffold`)**: Captures `PostCleanup` MIR
//!    and companion `#[spec]`, `#[model]`, and `#[invariant]` items for
//!    `frame_tutor`, verifies `render_extract_report` and
//!    `render_scaffold_report`, and confirms that `magic_version` requires no
//!    authored `Specs` or `Proof` files and `pin_magic` requires no authored
//!    `Specs` override.
//! 2. **Chapter 3 (Progressive adoption via `Assumptions.*`)**: Temporarily
//!    introduces `Assumptions/FrameTutor/pin_magic.lean` and routes
//!    `Proof/FrameTutor/pin_magic.lean` through `assumed_pin_magic`, verifying
//!    that strict verification (`allow_assumptions: false`) rejects the axiom
//!    by name while `--allow-assumptions` (`allow_assumptions: true`) succeeds
//!    and `render_verification_report` records `Verify.FrameTutor.pin_magic` as
//!    `CONDITIONAL [Assumptions.FrameTutor.pin_magic.assumed_pin_magic]` alongside
//!    `Verify.FrameTutor.magic_version: UNCONDITIONAL`.
//! 3. **Chapters 4, 5 & 6 (Manual proofs, `Partial` safe-vs.-unsafe separation,
//!    stateful `unsafe` verification, and locked-spec agent workflow)**:
//!    Restores the unconditional `dischargeRustEqU32` proof for `pin_magic`,
//!    verifies that `Specs/FrameTutor/advance_offset.lean` uses
//!    `refineSafeSpec` and `Proof/FrameTutor/advance_offset.lean` uses
//!    `verifyByWPSafe` and `MirContractHoldsWithSafety`, locks specifications
//!    via `lock_workspace_specs`, checks `render_lock_specs_report` and
//!    `render_agent_context`, verifies that tampering with
//!    `Specs/FrameTutor/read_version_ref.lean` fails `verify_spec_lock`, and
//!    runs locked-spec verification (`allow_assumptions: false`,
//!    `locked_specs: true`) to confirm that all four subject items
//!    (`magic_version`, `pin_magic`, `advance_offset`, `read_version_ref`)
//!    verify as `VerifiedUnconditional`.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    CliOptions, CliSubcommand, ScaffoldConfig, VerificationStatus, lock_workspace_specs,
    parse_cli_args, render_agent_context, render_extract_report, render_lock_specs_report,
    render_scaffold_report, render_verification_report, scaffold_workspace_with_config,
    verify_spec_lock, verify_workspace_with_options,
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

fn ensure_tutor_binaries(checkout_root: &Path) -> (PathBuf, PathBuf) {
    let wrapper_name = format!("anneal-rustc-capture{}", env::consts::EXE_SUFFIX);
    let cli_name = format!("cargo-anneal{}", env::consts::EXE_SUFFIX);
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| checkout_root.join("target"));
    let wrapper_bin = target_dir.join("debug").join(&wrapper_name);
    let cli_bin = target_dir.join("debug").join(&cli_name);

    let cargo_bin = env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let status = Command::new(cargo_bin)
        .current_dir(checkout_root)
        .arg("build")
        .arg("-p")
        .arg("anneal-rustc-capture")
        .arg("--bin")
        .arg("anneal-rustc-capture")
        .arg("-p")
        .arg("cargo-anneal")
        .arg("--bin")
        .arg("cargo-anneal")
        .status()
        .expect("build anneal-rustc-capture and cargo-anneal binaries");
    assert!(
        status.success(),
        "cargo build -p anneal-rustc-capture -p cargo-anneal must succeed"
    );
    assert!(
        wrapper_bin.is_file(),
        "expected compiled wrapper binary at {}",
        wrapper_bin.display()
    );
    assert!(
        cli_bin.is_file(),
        "expected compiled cargo-anneal binary at {}",
        cli_bin.display()
    );
    (wrapper_bin, cli_bin)
}

fn copy_dir_recursive(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("create destination directory");
    for entry in fs::read_dir(src).expect("read source directory") {
        let entry = entry.expect("read directory entry");
        let file_type = entry.file_type().expect("read entry file type");
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_recursive(&src_path, &dst_path);
        } else {
            fs::copy(&src_path, &dst_path).expect("copy file");
        }
    }
}

#[test]
fn end_to_end_tutor_progression_chapters_1_to_6() {
    let checkout_root = anneal_checkout_root();
    let (wrapper_bin, cli_bin) = ensure_tutor_binaries(&checkout_root);
    let anneal_spec_dir = checkout_root.join("crates/anneal-spec");
    let tutor_example_dir = checkout_root.join("examples/tutor");

    assert!(
        tutor_example_dir.join("Cargo.toml").is_file(),
        "examples/tutor/Cargo.toml must exist"
    );
    assert!(
        tutor_example_dir.join("README.md").is_file(),
        "examples/tutor/README.md must exist"
    );
    assert!(
        tutor_example_dir.join("src/lib.rs").is_file(),
        "examples/tutor/src/lib.rs must exist"
    );

    // Place the temporary crate at `<temp_root>/examples/tutor` so we can
    // exercise both Tutor CLI flavours:
    // - Flavour A: running from `<temp_root>` with a relative
    //   `--manifest-path examples/tutor/Cargo.toml`, and
    // - Flavour B: running `cargo anneal <subcommand>` directly inside
    //   `<temp_root>/examples/tutor` with `cargo-anneal` and
    //   `anneal-rustc-capture` on `PATH`.
    let temp_root = unique_temp_dir("tutor");
    let temp_crate = temp_root.join("examples/tutor");
    copy_dir_recursive(&tutor_example_dir.join("src"), &temp_crate.join("src"));
    copy_dir_recursive(
        &tutor_example_dir.join("anneal"),
        &temp_crate.join("anneal"),
    );

    let cargo_toml_raw = fs::read_to_string(tutor_example_dir.join("Cargo.toml"))
        .expect("read examples/tutor/Cargo.toml");
    let patched_cargo_toml = cargo_toml_raw.replace(
        "../../crates/anneal-spec",
        &anneal_spec_dir.display().to_string(),
    );
    fs::write(temp_crate.join("Cargo.toml"), patched_cargo_toml)
        .expect("write patched Cargo.toml in temporary workspace");

    let specs_dir = temp_crate.join("anneal/proofs/Specs/FrameTutor");
    let proof_dir = temp_crate.join("anneal/proofs/Proof/FrameTutor");
    let assumptions_dir = temp_crate.join("anneal/proofs/Assumptions/FrameTutor");

    // Verify the initial durable file layout from `examples/tutor/`:
    // - `magic_version` has neither `Specs` nor `Proof`.
    // - `pin_magic`, `total_frame_len`, and `__anneal_unsafe_impl_WireHeader_for_FrameLen`
    //   have `Proof` but no `Specs` override.
    // - `advance_offset`, `read_version_ref`, and `write_version_mut` have both
    //   `Specs` and `Proof`.
    assert!(!specs_dir.join("magic_version.lean").exists());
    assert!(!proof_dir.join("magic_version.lean").exists());
    assert!(!specs_dir.join("pin_magic.lean").exists());
    assert!(proof_dir.join("pin_magic.lean").is_file());
    assert!(!specs_dir.join("total_frame_len.lean").exists());
    assert!(proof_dir.join("total_frame_len.lean").is_file());
    assert!(specs_dir.join("advance_offset.lean").is_file());
    assert!(proof_dir.join("advance_offset.lean").is_file());
    assert!(specs_dir.join("read_version_ref.lean").is_file());
    assert!(proof_dir.join("read_version_ref.lean").is_file());
    assert!(specs_dir.join("write_version_mut.lean").is_file());
    assert!(proof_dir.join("write_version_mut.lean").is_file());
    assert!(!specs_dir.join("__anneal_unsafe_impl_WireHeader_for_FrameLen.lean").exists());
    assert!(proof_dir.join("__anneal_unsafe_impl_WireHeader_for_FrameLen.lean").is_file());

    let advance_offset_spec = fs::read_to_string(specs_dir.join("advance_offset.lean"))
        .expect("read Specs/FrameTutor/advance_offset.lean");
    assert!(
        advance_offset_spec.contains("Obligations.FrameTutor.advance_offset.refineSafeSpec"),
        "Specs/FrameTutor/advance_offset.lean must use refineSafeSpec:\n{advance_offset_spec}"
    );
    let advance_offset_proof = fs::read_to_string(proof_dir.join("advance_offset.lean"))
        .expect("read Proof/FrameTutor/advance_offset.lean");
    assert!(
        advance_offset_proof.contains("verifyByWPSafe")
            && advance_offset_proof.contains("MirContractHoldsWithSafety"),
        "Proof/FrameTutor/advance_offset.lean must use verifyByWPSafe and MirContractHoldsWithSafety:\n{advance_offset_proof}"
    );

    // =========================================================================
    // Stage 1: Chapters 1 & 2 (`extract` and `scaffold` + CLI reports)
    //          Also exercises Flavour A (relative `--manifest-path examples/tutor/Cargo.toml`
    //          from `temp_root`) and Flavour B (`cargo anneal scaffold` from inside
    //          `temp_crate` with `PATH` containing the compiled binaries).
    // =========================================================================
    let bin_dir = cli_bin.parent().expect("cli_bin parent dir");
    let path_env = match env::var_os("PATH") {
        Some(existing) => {
            let mut paths = vec![bin_dir.to_path_buf()];
            paths.extend(env::split_paths(&existing));
            env::join_paths(paths).expect("join PATH")
        }
        None => bin_dir.as_os_str().to_os_string(),
    };

    // Flavour A: invoke `cargo-anneal extract --manifest-path examples/tutor/Cargo.toml`
    // from `<temp_root>` using a relative `--manifest-path`.
    let cli_extract_out = Command::new(&cli_bin)
        .current_dir(&temp_root)
        .env("PATH", &path_env)
        .arg("extract")
        .arg("--manifest-path")
        .arg("examples/tutor/Cargo.toml")
        .output()
        .expect("execute Flavour A relative --manifest-path extract");
    assert!(
        cli_extract_out.status.success(),
        "Flavour A relative --manifest-path extract must succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&cli_extract_out.stdout),
        String::from_utf8_lossy(&cli_extract_out.stderr),
    );
    let cli_extract_stdout = String::from_utf8_lossy(&cli_extract_out.stdout);
    assert!(
        cli_extract_stdout.contains("Anneal Extract Summary:"),
        "expected Flavour A extract stdout to contain summary:\n{cli_extract_stdout}"
    );

    // Flavour B: invoke `cargo-anneal anneal scaffold --from-units` directly inside
    // `<temp_root>/examples/tutor` without `--manifest-path`.
    let cli_scaffold_out = Command::new(&cli_bin)
        .current_dir(&temp_crate)
        .env("PATH", &path_env)
        .arg("anneal")
        .arg("scaffold")
        .arg("--from-units")
        .output()
        .expect("execute Flavour B in-crate cargo anneal scaffold");
    assert!(
        cli_scaffold_out.status.success(),
        "Flavour B in-crate scaffold must succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&cli_scaffold_out.stdout),
        String::from_utf8_lossy(&cli_scaffold_out.stderr),
    );
    let cli_scaffold_stdout = String::from_utf8_lossy(&cli_scaffold_out.stdout);
    assert!(
        cli_scaffold_stdout.contains("Anneal Scaffold Summary:"),
        "expected Flavour B scaffold stdout to contain summary:\n{cli_scaffold_stdout}"
    );

    let units_dir = temp_crate.join("target/anneal/units");
    let (manifest, records) = cargo_anneal::aggregate_unit_manifests(&units_dir)
        .expect("aggregate captured unit manifests from Flavour A extract");

    let extract_report = render_extract_report(&manifest, &records);
    assert_eq!(cli_extract_stdout.as_ref(), extract_report);
    for expected_item in [
        "frame_tutor::magic_version",
        "frame_tutor::pin_magic",
        "frame_tutor::total_frame_len",
        "frame_tutor::advance_offset",
        "frame_tutor::read_version_ref",
        "frame_tutor::write_version_mut",
        "frame_tutor::__anneal_unsafe_impl_WireHeader_for_FrameLen",
    ] {
        assert!(
            extract_report.contains(expected_item),
            "extract report must list {expected_item}:\n{extract_report}"
        );
    }
    assert!(
        extract_report.contains("Total MIR targets: 19")
            && extract_report.contains("Subject items: 6")
            && extract_report.contains("model: 2")
            && extract_report.contains("invariant: 1")
            && extract_report.contains("unsafe_trait_impl: 1"),
        "extract report must record 19 MIR targets, 6 subjects, and #[model]/#[invariant]/#[unsafe_impl] companions:\n{extract_report}"
    );

    let mut scaffold_cfg = ScaffoldConfig::new(&temp_crate);
    scaffold_cfg.units_dir = Some(units_dir.clone());
    scaffold_cfg.anneal_repo_root = Some(checkout_root.clone());

    let scaffold_report = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("scaffold_workspace_with_config must succeed");
    let rendered_scaffold = render_scaffold_report(&scaffold_report);
    assert_eq!(cli_scaffold_stdout.as_ref(), rendered_scaffold);
    assert_eq!(scaffold_report.generated_obligation_files.len(), 7);
    assert_eq!(scaffold_report.generated_verify_files.len(), 7);
    assert_eq!(scaffold_report.created_spec_files.len(), 0);
    assert_eq!(scaffold_report.preserved_spec_files.len(), 3);
    assert_eq!(scaffold_report.created_proof_files.len(), 0);
    assert_eq!(scaffold_report.preserved_proof_files.len(), 6);

    // =========================================================================
    // Stage 2: Chapter 3 (Progressive adoption with `Assumptions.*`)
    // =========================================================================
    let original_pin_magic_proof =
        fs::read_to_string(proof_dir.join("pin_magic.lean")).expect("read pin_magic.lean");

    fs::create_dir_all(&assumptions_dir).expect("create Assumptions/FrameTutor directory");
    fs::write(
        assumptions_dir.join("pin_magic.lean"),
        r#"import Trusted
import Obligations.FrameTutor.pin_magic

namespace Assumptions.FrameTutor.pin_magic

open Trusted.VerificationResult

axiom assumed_pin_magic :
  VerificationResult Obligations.FrameTutor.pin_magic.claim

end Assumptions.FrameTutor.pin_magic
"#,
    )
    .expect("write temporary Assumptions/FrameTutor/pin_magic.lean");

    fs::write(
        proof_dir.join("pin_magic.lean"),
        r#"import Trusted
import Obligations.FrameTutor.pin_magic
import Assumptions.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.VerificationResult

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  Assumptions.FrameTutor.pin_magic.assumed_pin_magic

end Proof.FrameTutor.pin_magic
"#,
    )
    .expect("route Proof/FrameTutor/pin_magic.lean through assumed_pin_magic");

    scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("re-scaffold with Assumptions/FrameTutor/pin_magic.lean must succeed");

    let base_verify_options = CliOptions {
        subcommand: CliSubcommand::Verify,
        workspace_root: temp_crate.clone(),
        manifest_path: None,
        units_dir: units_dir.clone(),
        rustc_wrapper: Some(wrapper_bin.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        from_existing_units: true,
        init_specs: false,
        init_proofs: false,
        allow_assumptions: false,
        locked_specs: false,
        item_filter: None,
        allow_impl_edit: None,
        filter: None,
        extra_cargo_args: Vec::new(),
    };

    let strict_err = verify_workspace_with_options(&base_verify_options)
        .expect_err("strict verification without --allow-assumptions must reject assumed_pin_magic");
    assert!(
        strict_err.contains("Assumptions.FrameTutor.pin_magic.assumed_pin_magic"),
        "expected strict verification error to name assumed_pin_magic, got:\n{strict_err}"
    );

    let mut conditional_options = base_verify_options.clone();
    conditional_options.allow_assumptions = true;
    let conditional_report = verify_workspace_with_options(&conditional_options)
        .expect("verification with allow_assumptions: true must succeed");

    assert_eq!(
        conditional_report.status_for("Verify.FrameTutor.magic_version"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        conditional_report.status_for("Verify.FrameTutor.pin_magic"),
        Some(&VerificationStatus::VerifiedConditional {
            assumptions: vec![
                "Assumptions.FrameTutor.pin_magic.assumed_pin_magic".to_string()
            ],
        })
    );

    let rendered_conditional = render_verification_report(&conditional_report);
    assert!(
        rendered_conditional.contains("Verify.FrameTutor.magic_version: UNCONDITIONAL"),
        "expected magic_version to be marked UNCONDITIONAL:\n{rendered_conditional}"
    );
    assert!(
        rendered_conditional.contains(
            "Verify.FrameTutor.pin_magic: CONDITIONAL [Assumptions.FrameTutor.pin_magic.assumed_pin_magic]"
        ),
        "expected pin_magic to be marked CONDITIONAL with assumed_pin_magic:\n{rendered_conditional}"
    );

    // =========================================================================
    // Stage 3: Chapters 4, 5 & 6 (Manual proof, stateful `unsafe` proof, and
    //          locked-spec agent workflow)
    // =========================================================================
    fs::remove_dir_all(&temp_crate.join("anneal/proofs/Assumptions"))
        .expect("remove temporary Assumptions directory");
    fs::write(proof_dir.join("pin_magic.lean"), &original_pin_magic_proof)
        .expect("restore unconditional Proof/FrameTutor/pin_magic.lean");

    scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("re-scaffold after restoring unconditional pin_magic proof must succeed");

    let lock_path =
        lock_workspace_specs(&temp_crate, &records).expect("lock_workspace_specs must succeed");
    let lock_report = render_lock_specs_report(&temp_crate, &lock_path)
        .expect("render_lock_specs_report must succeed");
    assert!(
        lock_report.contains("Anneal Spec-Lock")
            && lock_report.contains("Locked MIR targets: 19")
            && lock_report.contains("Locked Specs files: 3"),
        "unexpected spec-lock report:\n{lock_report}"
    );
    assert!(
        lock_report.contains("Non-vacuity check: PASS"),
        "spec-lock report must confirm non-vacuity check passed:\n{lock_report}"
    );

    let agent_ctx = render_agent_context(&temp_crate, &records, Some("read_version_ref"))
        .expect("render_agent_context for read_version_ref must succeed");
    assert!(
        agent_ctx.contains("frame_tutor::read_version_ref"),
        "agent-context must include frame_tutor::read_version_ref:\n{agent_ctx}"
    );
    assert!(
        agent_ctx.contains("StatefulItemSpec \"frame_tutor::read_version_ref\""),
        "agent-context must include locked StatefulItemSpec:\n{agent_ctx}"
    );
    assert!(
        agent_ctx.contains("def body : CapturedMir :="),
        "agent-context must include captured MIR body for read_version_ref:\n{agent_ctx}"
    );

    // Negative anti-cheat check: tampering with a locked `Specs` file must be
    // rejected by `verify_spec_lock` and `agent-verify` (`locked_specs: true`).
    let read_version_spec_path = specs_dir.join("read_version_ref.lean");
    let original_read_version_spec =
        fs::read_to_string(&read_version_spec_path).expect("read read_version_ref.lean spec");
    fs::write(
        &read_version_spec_path,
        format!("{original_read_version_spec}\n-- unauthorized spec mutation\n"),
    )
    .expect("tamper with Specs/FrameTutor/read_version_ref.lean");
    let tamper_err = verify_spec_lock(&temp_crate, &records)
        .expect_err("verify_spec_lock must reject tampered Specs/FrameTutor/read_version_ref.lean");
    assert!(
        tamper_err.contains("spec-lock violation")
            && tamper_err.contains("read_version_ref.lean"),
        "expected spec-lock violation naming read_version_ref.lean, got:\n{tamper_err}"
    );

    fs::write(&read_version_spec_path, &original_read_version_spec)
        .expect("restore Specs/FrameTutor/read_version_ref.lean");
    verify_spec_lock(&temp_crate, &records)
        .expect("verify_spec_lock must succeed after restoring read_version_ref.lean");

    let mut agent_verify_options = base_verify_options;
    agent_verify_options.subcommand = CliSubcommand::AgentVerify;
    agent_verify_options.allow_assumptions = false;
    agent_verify_options.locked_specs = true;

    let final_report = verify_workspace_with_options(&agent_verify_options)
        .expect("locked-spec agent-verify must succeed unconditionally for all 7 items");

    for verify_mod in [
        "Verify.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen",
        "Verify.FrameTutor.advance_offset",
        "Verify.FrameTutor.magic_version",
        "Verify.FrameTutor.pin_magic",
        "Verify.FrameTutor.read_version_ref",
        "Verify.FrameTutor.total_frame_len",
        "Verify.FrameTutor.write_version_mut",
    ] {
        assert_eq!(
            final_report.status_for(verify_mod),
            Some(&VerificationStatus::VerifiedUnconditional),
            "expected {verify_mod} to verify as VerifiedUnconditional"
        );
    }

    let rendered_final = render_verification_report(&final_report);
    assert!(
        rendered_final.contains("Totals: 7 unconditional, 0 conditional"),
        "expected 7 unconditional and 0 conditional items:\n{rendered_final}"
    );
    assert!(
        rendered_final.contains("TrustedBoundary kernel replay: PASS"),
        "expected TrustedBoundary kernel replay: PASS:\n{rendered_final}"
    );

    let _ = fs::remove_dir_all(&temp_root);
}

/// Path of the tutor workflow driver relative to the checkout root.
const TUTOR_WORKFLOW_SCRIPT: &str = "docs/tutor/workflow/tutor_workflow.py";

fn run_tutor_workflow(checkout_root: &Path, args: &[&str]) -> std::process::Output {
    Command::new("python3")
        .arg("-B")
        .arg(TUTOR_WORKFLOW_SCRIPT)
        .args(args)
        .current_dir(checkout_root)
        .output()
        .unwrap_or_else(|err| panic!("execute python3 {TUTOR_WORKFLOW_SCRIPT}: {err}"))
}

/// Every command, report, and error block in `docs/tutor/0*-*.md` must be
/// generated by a `<!-- tutor: ... -->` directive that names a step of
/// `docs/tutor/workflow/tutor.toml`. This parses both without executing
/// anything, so it runs on every `cargo test`.
#[test]
fn tutor_workflow_directives_and_coverage_are_well_formed() {
    let checkout_root = anneal_checkout_root();
    let output = run_tutor_workflow(&checkout_root, &["lint"]);
    assert!(
        output.status.success(),
        "`{TUTOR_WORKFLOW_SCRIPT} lint` failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Drive `examples/tutor/` through `docs/tutor/workflow/tutor.toml` with the
/// freshly built `cargo-anneal`, then require every managed block in the
/// chapters to equal what that run produced. When this fails after an
/// intentional CLI or tutorial change, run
/// `python3 docs/tutor/workflow/tutor_workflow.py render` and review the diff.
#[test]
fn tutor_chapters_match_the_tutor_workflow() {
    let checkout_root = anneal_checkout_root();
    let (_wrapper_bin, cli_bin) = ensure_tutor_binaries(&checkout_root);
    let bin_dir = cli_bin.parent().expect("cli_bin parent dir");
    let bin_dir_arg = bin_dir.to_str().expect("utf8 bin dir");
    let output = run_tutor_workflow(
        &checkout_root,
        &["check", "--no-build", "--bin-dir", bin_dir_arg],
    );
    assert!(
        output.status.success(),
        "`{TUTOR_WORKFLOW_SCRIPT} check` failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// Strip `/-! ... -/` module doc comments and collapse consecutive blank lines
/// so Lean code blocks in documentation can be compared against on-disk files.
fn strip_lean_module_doc_comments(text: &str) -> String {
    let mut cleaned = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("/-!") {
        cleaned.push_str(&rest[..start]);
        if let Some(end) = rest[start + 3..].find("-/") {
            rest = &rest[start + 3 + end + 2..];
        } else {
            rest = "";
            break;
        }
    }
    cleaned.push_str(rest);
    cleaned
        .lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Extract fenced code blocks (` ```<info>\n...\n``` `) from Markdown text.
fn extract_fenced_blocks(markdown: &str) -> Vec<(String, String)> {
    let mut blocks = Vec::new();
    let mut in_block = false;
    let mut current_lang = String::new();
    let mut current_body = String::new();

    for line in markdown.lines() {
        let trimmed = line.trim_start();
        if !in_block {
            if let Some(rest) = trimmed.strip_prefix("```") {
                in_block = true;
                current_lang = rest.trim().to_string();
                current_body.clear();
            }
        } else if trimmed.starts_with("```") {
            in_block = false;
            blocks.push((current_lang.clone(), current_body.clone()));
        } else {
            current_body.push_str(line);
            current_body.push('\n');
        }
    }
    blocks
}

/// Extract local relative Markdown link targets `[label](target)` outside
/// fenced code blocks.
fn extract_markdown_links(markdown: &str) -> Vec<String> {
    let mut links = Vec::new();
    let mut in_block = false;
    for line in markdown.lines() {
        if line.trim_start().starts_with("```") {
            in_block = !in_block;
            continue;
        }
        if in_block {
            continue;
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        let mut in_inline_code = false;
        while i < bytes.len() {
            if bytes[i] == b'`' {
                in_inline_code = !in_inline_code;
                i += 1;
                continue;
            }
            if !in_inline_code && i + 3 < bytes.len() && bytes[i] == b']' && bytes[i + 1] == b'(' {
                if let Some(rel_end) = line[i + 2..].find(')') {
                    let raw_target = line[i + 2..i + 2 + rel_end].trim();
                    let target = raw_target
                        .split_whitespace()
                        .next()
                        .unwrap_or("")
                        .split('#')
                        .next()
                        .unwrap_or("");
                    if !target.is_empty()
                        && !target.starts_with("http://")
                        && !target.starts_with("https://")
                        && !target.starts_with("mailto:")
                    {
                        links.push(target.to_string());
                    }
                    i += 2 + rel_end + 1;
                    continue;
                }
            }
            i += 1;
        }
    }
    links
}

#[test]
fn tutor_and_repo_docs_links_cli_flavours_and_reports_stay_in_sync() {
    let checkout_root = anneal_checkout_root();
    let cwd = env::current_dir().expect("read current_dir");

    let doc_files = [
        "README.md",
        "AGENTS.md",
        "agent_docs/development.md",
        "agent_docs/trusted-rust.md",
        "agent_docs/writing.md",
        "crates/README.md",
        "docs/agent-proof-workflow.md",
        "docs/mir-coverage-and-composition.md",
        "docs/tutor/README.md",
        "docs/tutor/01-basic-usage-and-outputs.md",
        "docs/tutor/02-rust-specifications.md",
        "docs/tutor/03-assumptions-and-incremental-adoption.md",
        "docs/tutor/04-manual-proof-workflow.md",
        "docs/tutor/05-verifying-unsafe-rust.md",
        "docs/tutor/06-agentic-proof-workflow.md",
        "docs/tutor/workflow/README.md",
        "examples/README.md",
        "examples/tutor-ch1/README.md",
        "examples/tutor-ch2/README.md",
        "examples/tutor-ch3/README.md",
        "examples/tutor-ch4/README.md",
        "examples/tutor/README.md",
        "skills/anneal-doc-audit/SKILL.md",
        "skills/anneal-prove/SKILL.md",
        "tests/README.md",
        "theory/README.md",
        "trusted/README.md",
        "trusted/audit/README.md",
        "trusted/lean/README.md",
        "trusted/rustc-capture/README.md",
    ];

    // 1. Verify that every documented relative Markdown link resolves to an
    //    existing file or directory on disk.
    for rel_doc in doc_files {
        let doc_path = checkout_root.join(rel_doc);
        assert!(
            doc_path.is_file(),
            "expected documentation file {} to exist",
            doc_path.display()
        );
        let text = fs::read_to_string(&doc_path).expect("read doc file");
        let doc_dir = doc_path.parent().expect("doc parent dir");
        for link in extract_markdown_links(&text) {
            let resolved = doc_dir.join(&link);
            assert!(
                resolved.exists(),
                "broken relative Markdown link '{link}' in {} (resolved to {})",
                rel_doc,
                resolved.display()
            );
        }
    }

    // 2. Verify that every `cargo anneal` and `cargo run -p cargo-anneal --`
    //    command in the Tutor chapters and READMEs parses cleanly through
    //    `parse_cli_args`, resolves relative `--manifest-path` to an absolute
    //    path, and that Tutor chapter command blocks include both Flavour A
    //    (`cargo run -p cargo-anneal --`) and Flavour B (`cargo anneal`).
    let tutor_chapter_docs = [
        "docs/tutor/01-basic-usage-and-outputs.md",
        "docs/tutor/02-rust-specifications.md",
        "docs/tutor/03-assumptions-and-incremental-adoption.md",
        "docs/tutor/04-manual-proof-workflow.md",
        "docs/tutor/05-verifying-unsafe-rust.md",
        "docs/tutor/06-agentic-proof-workflow.md",
    ];

    let mut total_parsed_cli_commands = 0usize;
    for rel_doc in doc_files {
        let doc_path = checkout_root.join(rel_doc);
        let text = fs::read_to_string(&doc_path).expect("read doc file");
        let is_tutor_chapter = tutor_chapter_docs.contains(&rel_doc);

        for (lang, body) in extract_fenced_blocks(&text) {
            if matches!(lang.as_str(), "bash" | "sh") {
                let mut has_flavour_a = false;
                let mut has_flavour_b = false;

                for raw_line in body.lines() {
                    let line = raw_line.trim();
                    if line.is_empty() || line.starts_with('#') {
                        continue;
                    }
                    // Skip placeholder templates like `<SUBCOMMAND>` or `<Crate>`.
                    if line.contains('<') && line.contains('>') {
                        continue;
                    }
                    if let Some(rest) = line.strip_prefix("cargo run -p cargo-anneal -- ") {
                        has_flavour_a = true;
                        let mut argv = vec!["cargo-anneal"];
                        argv.extend(rest.split_whitespace());
                        let opts = parse_cli_args(&argv).unwrap_or_else(|err| {
                            panic!(
                                "invalid Flavour A CLI command `{line}` in {rel_doc}: {err}"
                            )
                        });
                        assert_ne!(opts.subcommand, CliSubcommand::Help);
                        assert!(
                            opts.workspace_root.is_absolute(),
                            "workspace_root must be absolute for `{line}` in {rel_doc}"
                        );
                        if let Some(ref mp) = opts.manifest_path {
                            assert!(
                                mp.is_absolute(),
                                "manifest_path must be normalized to an absolute path for `{line}` in {rel_doc}"
                            );
                            if rest.contains("--manifest-path examples/tutor/Cargo.toml") {
                                assert_eq!(
                                    mp,
                                    &cwd.join("examples/tutor/Cargo.toml"),
                                    "unexpected resolved manifest_path for `{line}`"
                                );
                                assert_eq!(
                                    opts.workspace_root,
                                    cwd.join("examples/tutor"),
                                    "unexpected resolved workspace_root for `{line}`"
                                );
                            }
                        }
                        total_parsed_cli_commands += 1;
                    } else if let Some(rest) = line.strip_prefix("cargo anneal ") {
                        has_flavour_b = true;
                        let mut argv = vec!["cargo-anneal", "anneal"];
                        argv.extend(rest.split_whitespace());
                        let opts = parse_cli_args(&argv).unwrap_or_else(|err| {
                            panic!(
                                "invalid Flavour B CLI command `{line}` in {rel_doc}: {err}"
                            )
                        });
                        assert_ne!(opts.subcommand, CliSubcommand::Help);
                        assert!(
                            opts.workspace_root.is_absolute(),
                            "workspace_root must be absolute for `{line}` in {rel_doc}"
                        );
                        total_parsed_cli_commands += 1;
                    }
                }

                if is_tutor_chapter && (has_flavour_a || has_flavour_b) {
                    assert!(
                        has_flavour_a && has_flavour_b,
                        "CLI block in tutor chapter {rel_doc} must provide both Flavour A (`cargo run -p cargo-anneal -- ...`) and Flavour B (`cargo anneal ...`):\n{body}"
                    );
                }
            }

            // 3. Verify that CLI report snippets in Tutor docs match the exact
            //    format emitted by `render_*_report` in `cargo-anneal`.
            if lang == "text"
                && (body.contains("Anneal Extract Summary:")
                    || body.contains("Anneal Scaffold Summary:")
                    || body.contains("Anneal Spec-Lock Summary:")
                    || body.contains("Anneal Verification Summary:"))
            {
                assert!(
                    !body.contains("=== Anneal "),
                    "stale `=== Anneal ... ===` banner in {rel_doc}:\n{body}"
                );
                assert!(
                    !body.contains("UNCONDITIONAL [UNCONDITIONAL]"),
                    "stale duplicate `[UNCONDITIONAL]` tag in {rel_doc}:\n{body}"
                );
                assert!(
                    !body.contains("    - frame_tutor::"),
                    "stale `- ` bullet prefix in Subject mappings in {rel_doc}:\n{body}"
                );
            }
        }
    }
    assert!(
        total_parsed_cli_commands >= 20,
        "expected at least 20 parsed CLI commands across documentation, found {total_parsed_cli_commands}"
    );

    // 4. Verify that durable Lean proof and specification modules in
    //    `examples/tutor/anneal/proofs/` match the full-module listings in
    //    Chapters 4 and 5, and that Chapter 6's final Spec-Lock and
    //    Verification reports match `examples/tutor/`.
    let ch4_text = fs::read_to_string(checkout_root.join("docs/tutor/04-manual-proof-workflow.md"))
        .expect("read Chapter 4");
    let ch5_text = fs::read_to_string(checkout_root.join("docs/tutor/05-verifying-unsafe-rust.md"))
        .expect("read Chapter 5");
    let ch6_text = fs::read_to_string(checkout_root.join("docs/tutor/06-agentic-proof-workflow.md"))
        .expect("read Chapter 6");

    for (rel_lean, chapter_text, chapter_name) in [
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/pin_magic.lean",
            &ch4_text,
            "docs/tutor/04-manual-proof-workflow.md",
        ),
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/total_frame_len.lean",
            &ch4_text,
            "docs/tutor/04-manual-proof-workflow.md",
        ),
        (
            "examples/tutor/anneal/proofs/Specs/FrameTutor/advance_offset.lean",
            &ch4_text,
            "docs/tutor/04-manual-proof-workflow.md",
        ),
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/advance_offset.lean",
            &ch4_text,
            "docs/tutor/04-manual-proof-workflow.md",
        ),
        (
            "examples/tutor/anneal/proofs/Specs/FrameTutor/read_version_ref.lean",
            &ch5_text,
            "docs/tutor/05-verifying-unsafe-rust.md",
        ),
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/read_version_ref.lean",
            &ch5_text,
            "docs/tutor/05-verifying-unsafe-rust.md",
        ),
        (
            "examples/tutor/anneal/proofs/Specs/FrameTutor/write_version_mut.lean",
            &ch5_text,
            "docs/tutor/05-verifying-unsafe-rust.md",
        ),
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/write_version_mut.lean",
            &ch5_text,
            "docs/tutor/05-verifying-unsafe-rust.md",
        ),
        (
            "examples/tutor/anneal/proofs/Proof/FrameTutor/__anneal_unsafe_impl_WireHeader_for_FrameLen.lean",
            &ch5_text,
            "docs/tutor/05-verifying-unsafe-rust.md",
        ),
    ] {
        let lean_disk = strip_lean_module_doc_comments(
            &fs::read_to_string(checkout_root.join(rel_lean)).expect("read durable Lean file"),
        );
        let normalized_chapter = strip_lean_module_doc_comments(chapter_text);
        assert!(
            normalized_chapter.contains(&lean_disk),
            "{chapter_name} is out of sync with on-disk {rel_lean}:\nexpected block:\n{lean_disk}"
        );
    }

    assert!(
        ch6_text.contains(
            "Anneal Spec-Lock Summary:\n  \
               Lock file: .anneal/spec-lock.json\n  \
               Locked MIR targets: 19\n  \
               Locked Specs files: 3\n  \
               Locked Assumptions files: 0\n  \
               Non-vacuity check: PASS"
        ),
        "Chapter 6 Spec-Lock Summary block does not match examples/tutor output"
    );
    assert!(
        ch6_text.contains(
            "Anneal Verification Summary:\n  \
               Verify.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen: UNCONDITIONAL\n  \
               Verify.FrameTutor.advance_offset: UNCONDITIONAL\n  \
               Verify.FrameTutor.magic_version: UNCONDITIONAL\n  \
               Verify.FrameTutor.pin_magic: UNCONDITIONAL\n  \
               Verify.FrameTutor.read_version_ref: UNCONDITIONAL\n  \
               Verify.FrameTutor.total_frame_len: UNCONDITIONAL\n  \
               Verify.FrameTutor.write_version_mut: UNCONDITIONAL\n  \
               Totals: 7 unconditional, 0 conditional\n  \
               TrustedBoundary kernel replay: PASS"
        ),
        "Chapter 6 Verification Summary block does not match examples/tutor output"
    );
}
