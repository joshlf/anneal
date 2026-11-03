//! End-to-end integration test for the Rust-Only Incremental Adoption Lifecycle.
//!
//! Verifies that everyday Rust developers can adopt Anneal incrementally using
//! only Rust attributes (`.rs` files) with zero authored `.lean` files under
//! `anneal/proofs/`:
//! 1. Stage 1: Bracket out an unproved `unsafe` / FFI leaf helper with
//!    `#[anneal_spec::spec(trusted, requires: ..., ensures: ...)]` while
//!    verifying callers and sibling functions around it via generated
//!    `defaultProof` / `defaultModularProof` / `defaultTotalProof` instances.
//!    Running `cargo anneal verify --allow-assumptions` succeeds with 0 files in
//!    `anneal/proofs/`, reporting the leaf as `VerifiedConditional`
//!    (`Assumptions.<Leaf>.rust_trusted_contract`) and callers/siblings as
//!    `VerifiedUnconditional`.
//! 2. Stage 2: Running `cargo anneal verify` without `--allow-assumptions`
//!    fails closed (`TrustedBoundary` rejects `Assumptions.<Leaf>.rust_trusted_contract`).
//! 3. Stage 3: Replacing the leaf's `trusted` qualifier with a real verified
//!    implementation causes `cargo anneal verify` (without `--allow-assumptions`)
//!    to prune the stale generated `Assumptions` module and pass 100%
//!    `VerifiedUnconditional`, still with zero authored `.lean` files in
//!    `anneal/proofs/`.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use cargo_anneal::{
    CaptureDriverConfig, ScaffoldConfig, VerificationStatus, VerifyConfig,
    render_verification_report, run_cargo_capture, scaffold_workspace_with_config,
    vendor_fuchsia_crates, verify_workspace_with_config,
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

fn count_lean_files(dir: &Path) -> usize {
    if !dir.is_dir() {
        return 0;
    }
    let mut count = 0;
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                count += count_lean_files(&path);
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                count += 1;
            }
        }
    }
    count
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
fn end_to_end_rust_only_incremental_adoption_lifecycle() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_crate = unique_temp_dir("rust-only-adoption");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create temporary crate src/");

    let anneal_spec_dir = checkout_root.join("crates").join("anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "rust_only_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    // =========================================================================
    // Stage 1: Bracket out an unproved leaf helper (`ffi_read_reg`) with
    // `#[anneal_spec::spec(trusted, ...)]` and verify callers/siblings around
    // it with ZERO authored `.lean` files under `anneal/proofs/`.
    // =========================================================================
    let stage1_lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[anneal_spec::spec(
    trusted,
    requires: port == 10,
    ensures: |ret: u32| ret == 42,
)]
pub unsafe fn ffi_read_reg(port: u32) -> u32 {
    // Unproved placeholder body that does NOT compute 42, demonstrating that
    // Stage 1 relies on the explicit conditional axiom generated from `trusted`.
    port.wrapping_add(999)
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 50,
)]
pub fn read_and_offset(port: u32) -> u32 {
    let v = unsafe { ffi_read_reg(port) };
    v + 8
}

#[anneal_spec::spec(
    requires: x < 1000,
    ensures: |ret: u32| ret <= 1000,
)]
pub fn clamp_add_one(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    safe_total,
    requires: x == 7,
    ensures: |ret: u32| ret == 8,
)]
pub fn safe_inc_bounded(x: u32) -> u32 {
    x + 1
}
"#;
    fs::write(src_dir.join("lib.rs"), stage1_lib_rs).expect("write stage 1 src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(&temp_crate);
    driver_cfg.rustc_wrapper = Some(wrapper_bin.clone());
    let (manifest1, records1) =
        run_cargo_capture(&driver_cfg).expect("Stage 1 run_cargo_capture must succeed");
    assert!(manifest1.compilation_succeeded);

    let scaffold_cfg = ScaffoldConfig {
        workspace_root: temp_crate.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    let scaffold1 = scaffold_workspace_with_config(&scaffold_cfg, &records1)
        .expect("Stage 1 scaffold_workspace_with_config must succeed");

    // Confirm zero authored `.lean` files exist under `anneal/proofs/` and
    // `.anneal/generated/Assumptions/RustOnlyPkg/ffi_read_reg.lean` was generated.
    assert_eq!(count_lean_files(&temp_crate.join("anneal/proofs")), 0);
    assert_eq!(scaffold1.generated_assumption_files.len(), 1);
    let gen_assumption_path =
        temp_crate.join(".anneal/generated/Assumptions/RustOnlyPkg/ffi_read_reg.lean");
    assert!(gen_assumption_path.is_file());

    // Stage 1: Verify with `--allow-assumptions` (`allow_assumptions: true`).
    let stage1_report = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate)
            .with_anneal_repo_root(&checkout_root)
            .with_allow_assumptions(true),
    )
    .expect("Stage 1 verify_workspace_with_config(allow_assumptions = true) must succeed");

    assert_eq!(
        stage1_report.status_for("Verify.RustOnlyPkg.ffi_read_reg"),
        Some(&VerificationStatus::VerifiedConditional {
            assumptions: vec![
                "Assumptions.RustOnlyPkg.ffi_read_reg.rust_trusted_contract".to_string()
            ],
        })
    );
    assert_eq!(
        stage1_report.status_for("Verify.RustOnlyPkg.read_and_offset"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        stage1_report.status_for("Verify.RustOnlyPkg.clamp_add_one"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    assert_eq!(
        stage1_report.status_for("Verify.RustOnlyPkg.safe_inc_bounded"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );

    let stage1_summary = render_verification_report(&stage1_report);
    assert!(stage1_summary.contains(
        "Verify.RustOnlyPkg.ffi_read_reg: CONDITIONAL [Assumptions.RustOnlyPkg.ffi_read_reg.rust_trusted_contract]"
    ));
    assert!(stage1_summary.contains("Verify.RustOnlyPkg.read_and_offset: UNCONDITIONAL"));
    assert!(stage1_summary.contains("Verify.RustOnlyPkg.clamp_add_one: UNCONDITIONAL"));
    assert!(stage1_summary.contains("Verify.RustOnlyPkg.safe_inc_bounded: UNCONDITIONAL"));
    assert!(stage1_summary.contains("Totals: 3 unconditional, 1 conditional"));

    // =========================================================================
    // Stage 2: Running `cargo anneal verify` without `--allow-assumptions` must
    // fail closed and reject `Assumptions.RustOnlyPkg.ffi_read_reg.rust_trusted_contract`.
    // =========================================================================
    let stage2_err = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate).with_anneal_repo_root(&checkout_root),
    )
    .expect_err(
        "Stage 2 strict verify_workspace without --allow-assumptions must reject conditional axiom",
    );
    assert!(
        stage2_err.contains("Assumptions.RustOnlyPkg.ffi_read_reg.rust_trusted_contract"),
        "expected conditional axiom rejection in Stage 2, got: {stage2_err}"
    );

    // =========================================================================
    // Stage 3: Replace `trusted` on `ffi_read_reg` with a real verified
    // implementation; `cargo anneal verify` (without `--allow-assumptions`) now
    // passes 100% UNCONDITIONAL, still with ZERO files in `anneal/proofs/`.
    // =========================================================================
    let stage3_lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 42,
)]
pub unsafe fn ffi_read_reg(port: u32) -> u32 {
    port + 32
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 50,
)]
pub fn read_and_offset(port: u32) -> u32 {
    let v = unsafe { ffi_read_reg(port) };
    v + 8
}

#[anneal_spec::spec(
    requires: x < 1000,
    ensures: |ret: u32| ret <= 1000,
)]
pub fn clamp_add_one(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    safe_total,
    requires: x == 7,
    ensures: |ret: u32| ret == 8,
)]
pub fn safe_inc_bounded(x: u32) -> u32 {
    x + 1
}
"#;
    fs::write(src_dir.join("lib.rs"), stage3_lib_rs).expect("write stage 3 src/lib.rs");

    let (manifest3, records3) =
        run_cargo_capture(&driver_cfg).expect("Stage 3 run_cargo_capture must succeed");
    assert!(manifest3.compilation_succeeded);

    let scaffold3 = scaffold_workspace_with_config(&scaffold_cfg, &records3)
        .expect("Stage 3 scaffold_workspace_with_config must succeed");
    assert!(scaffold3.generated_assumption_files.is_empty());
    assert!(
        !gen_assumption_path.exists(),
        "stale .anneal/generated/Assumptions/RustOnlyPkg/ffi_read_reg.lean must be pruned"
    );
    assert_eq!(count_lean_files(&temp_crate.join("anneal/proofs")), 0);

    let stage3_report = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate).with_anneal_repo_root(&checkout_root),
    )
    .expect("Stage 3 strict verify_workspace without --allow-assumptions must succeed");

    for module in [
        "Verify.RustOnlyPkg.ffi_read_reg",
        "Verify.RustOnlyPkg.read_and_offset",
        "Verify.RustOnlyPkg.clamp_add_one",
        "Verify.RustOnlyPkg.safe_inc_bounded",
    ] {
        assert_eq!(
            stage3_report.status_for(module),
            Some(&VerificationStatus::VerifiedUnconditional),
            "expected {module} to be VerifiedUnconditional in Stage 3"
        );
    }

    let stage3_summary = render_verification_report(&stage3_report);
    assert!(stage3_summary.contains("Totals: 4 unconditional, 0 conditional"));
    assert!(stage3_summary.contains("TrustedBoundary kernel replay: PASS"));

    // =========================================================================
    // Stage 4: Cargo-free GN/Bazel `--units-dir` verification mode in a
    // standalone target directory WITHOUT `Cargo.toml`, consuming pre-captured
    // `UnitCaptureManifest` records directly from `driver_cfg.units_dir`.
    // =========================================================================
    let gn_target_dir = unique_temp_dir("gn-units-dir-only");
    assert!(!gn_target_dir.join("Cargo.toml").exists());
    let gn_report = verify_workspace_with_config(
        &VerifyConfig::new(&gn_target_dir)
            .with_units_dir(&driver_cfg.units_dir)
            .with_anneal_repo_root(&checkout_root),
    )
    .expect("Stage 4 Cargo-free --units-dir verify_workspace_with_config must succeed");
    assert_eq!(
        gn_report.status_for("Verify.RustOnlyPkg.clamp_add_one"),
        Some(&VerificationStatus::VerifiedUnconditional)
    );
    let gn_summary = render_verification_report(&gn_report);
    assert!(gn_summary.contains("Totals: 4 unconditional, 0 conditional"));

    let _ = fs::remove_dir_all(&gn_target_dir);
    let _ = fs::remove_dir_all(&temp_crate);
}

#[test]
fn vendor_fuchsia_crates_stages_self_contained_bundle() {
    let checkout_root = anneal_checkout_root();
    let vendor_dir = unique_temp_dir("vendor-fuchsia");

    let vendored = vendor_fuchsia_crates(&checkout_root, &vendor_dir)
        .expect("vendor_fuchsia_crates must succeed");
    assert_eq!(vendored.len(), 4);

    for crate_name in [
        "anneal-spec-macros-0.1.0-alpha.1",
        "anneal-spec-0.1.0-alpha.1",
        "anneal-rustc-capture-0.1.0-alpha.1",
        "cargo-anneal-0.1.0-alpha.1",
    ] {
        let crate_dir = vendor_dir.join(crate_name);
        assert!(crate_dir.join("Cargo.toml").is_file(), "missing Cargo.toml in {crate_name}");
        assert!(crate_dir.join("LICENSE-BSD").is_file(), "missing LICENSE-BSD in {crate_name}");
        assert!(
            crate_dir.join("LICENSE-APACHE").is_file(),
            "missing LICENSE-APACHE in {crate_name}"
        );
        assert!(crate_dir.join("LICENSE-MIT").is_file(), "missing LICENSE-MIT in {crate_name}");
        let checksum_json = fs::read_to_string(crate_dir.join(".cargo-checksum.json"))
            .expect("read .cargo-checksum.json");
        assert!(checksum_json.contains("\"package\":null"));
        assert!(checksum_json.contains("\"Cargo.toml\":"));
    }

    let lean_root = vendor_dir.join("cargo-anneal-0.1.0-alpha.1/lean-root");
    assert!(lean_root.join("trusted/lean").is_dir());
    assert!(lean_root.join("trusted/audit/check_trusted.py").is_file());
    assert!(lean_root.join("theory/Anneal").is_dir());
    assert!(lean_root.join("examples/lakefile.toml").is_file());
    assert!(lean_root.join("lean-toolchain").is_file());

    let _ = fs::remove_dir_all(&vendor_dir);
}
