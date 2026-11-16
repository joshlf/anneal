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
//!
//! `end_to_end_rust_only_closure_deref_edge_shapes` additionally pins the
//! closure-captured companion shapes the four lifecycle items do not cover
//! (reversed and two-parameter pins, `<=` bounds, `u8` / `u64` widths,
//! `|ref ret|`, and a modular caller of a `trusted` leaf) on real captured MIR.
//! `end_to_end_rust_only_closure_deref_rejects_false_contracts` checks that the
//! same shapes reject implementations that violate their `#[spec]`.

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
    static PREREQS: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    PREREQS
        .get_or_init(|| {
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

            // Pre-warm `Trusted` and `Anneal` once into Lake's content-addressed
            // artifact cache (`LAKE_ARTIFACT_CACHE=true`) before the parallel
            // e2e tests spawn concurrent `lake build` processes in independent
            // `.anneal/` workspaces, avoiding 3x redundant cold rebuilds of
            // `SymReflect` and cgroup memory spikes.
            let lake_dir = checkout_root.join(".lake");
            fs::create_dir_all(&lake_dir).expect("create `.lake` dir for cache-warm lock");
            let lock_file = fs::OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(false)
                .open(lake_dir.join(".anneal-e2e-cache-warm.lock"))
                .expect("open `.anneal-e2e-cache-warm.lock`");
            lock_file
                .lock()
                .expect("acquire exclusive lock for `lake build Anneal` cache warm");
            let lake_bin = env::var_os("HOME")
                .map(|h| PathBuf::from(h).join(".elan/bin/lake"))
                .filter(|p| p.is_file())
                .unwrap_or_else(|| PathBuf::from("lake"));
            let mut lake_cmd = cargo_anneal::build_lake_build_command(&lake_bin, checkout_root);
            lake_cmd.arg("Anneal");
            let lake_status = lake_cmd.status().expect("spawn `lake build Anneal`");
            let _ = lock_file.unlock();
            assert!(
                lake_status.success(),
                "`lake build Anneal` pre-warm in checkout root must succeed"
            );

            default_bin
        })
        .clone()
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

/// Real `rustc`-captured `V2026_06_01` `anodized` closure-captured companion
/// shapes beyond the four lifecycle items above, all discharged by the generated
/// default proofs with zero authored `.lean` files:
/// - a reversed constant-on-LHS pin (`requires: 10 == port`),
/// - a two-parameter short-circuit `&&` pin with a reversed second operand,
/// - a `<=` upper bound (`checkSymUpperBound1Loop`),
/// - `u8` / `u64` pin widths and a `|ref ret|` `ensures` binder,
/// - callers that inline pinned safe and `unsafe` siblings, and
/// - a modular caller (`dischargeRustModularContractAuto`) of a `trusted`
///   `unsafe` sibling whose `requires` and `ensures` are both reversed.
///
/// A regression in the closure-deref auto-discharge
/// (`checkOptMirRequiresPinsScalarsForSubject`, `checkSymUpperBound1Loop`,
/// `checkCalleeEnsuresPinsRet`) therefore fails here on real captured MIR, not
/// only on the hand-built bodies in `tests/mir/SymbolicEvalTests.lean`.
#[test]
fn end_to_end_rust_only_closure_deref_edge_shapes() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_crate = unique_temp_dir("rust-only-closure-deref-edges");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create temporary crate src/");

    let anneal_spec_dir = checkout_root.join("crates").join("anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "edge_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    let lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[anneal_spec::spec(
    requires: 10 == port,
    ensures: |ret: u32| ret == 42,
)]
pub fn rev_pin(port: u32) -> u32 {
    port + 32
}

#[anneal_spec::spec(
    requires: a == 10 && 20 == b,
    ensures: |ret: u32| 30 == ret,
)]
pub fn add_two(a: u32, b: u32) -> u32 {
    a + b
}

#[anneal_spec::spec(
    requires: x <= 100,
    ensures: |ret: u32| ret <= 101,
)]
pub fn le_bound(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    requires: x == 5,
    ensures: |ret: u64| ret == 6,
)]
pub fn u64_pin(x: u64) -> u64 {
    x + 1
}

#[anneal_spec::spec(
    requires: x == 200,
    ensures: |ret: u8| ret == 201,
)]
pub fn u8_pin(x: u8) -> u8 {
    x + 1
}

#[anneal_spec::spec(
    requires: x == 7,
    ensures: |ref ret| *ret == 8,
)]
pub fn ref_ens(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 50,
)]
pub fn call_rev(port: u32) -> u32 {
    let v = rev_pin(port);
    v + 8
}

#[anneal_spec::spec(
    requires: 10 == port,
    ensures: |ret: u32| 42 == ret,
)]
pub unsafe fn ffi_rev(port: u32) -> u32 {
    port + 32
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 50,
)]
pub fn call_ffi_rev(port: u32) -> u32 {
    let v = unsafe { ffi_rev(port) };
    v + 8
}

#[anneal_spec::spec(
    trusted,
    requires: 10 == port,
    ensures: |ret: u32| 42 == ret,
)]
pub unsafe fn ffi_trusted_rev(port: u32) -> u32 {
    port.wrapping_add(999)
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 50,
)]
pub fn call_trusted_rev(port: u32) -> u32 {
    let v = unsafe { ffi_trusted_rev(port) };
    v + 8
}

#[anneal_spec::spec(
    requires: idx == 3,
    ensures: |ret: usize| ret == 4,
)]
pub fn usize_pin(idx: usize) -> usize {
    idx + 1
}

#[anneal_spec::spec(
    requires: x < 8,
    ensures: |ret: u32| ret == le_bound(x),
)]
pub fn bound_with_spec_callee(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    safe_total,
    requires: 42 == x,
    ensures: |ret: u32| x.wrapping_add(5) == ret,
)]
pub fn total_pin_with_spec_callee(x: u32) -> u32 {
    x + 5
}
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(&temp_crate);
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (manifest, records) =
        run_cargo_capture(&driver_cfg).expect("edge-shape run_cargo_capture must succeed");
    assert!(manifest.compilation_succeeded);

    let scaffold_cfg = ScaffoldConfig {
        workspace_root: temp_crate.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    let scaffold = scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("edge-shape scaffold_workspace_with_config must succeed");
    assert_eq!(scaffold.generated_assumption_files.len(), 1);
    assert_eq!(count_lean_files(&temp_crate.join("anneal/proofs")), 0);

    // The caller of the `trusted` leaf must take the modular route, so the
    // reversed callee `requires` / `ensures` exercise `checkCalleeEnsuresPinsRet`.
    let modular_verify = fs::read_to_string(
        temp_crate.join(".anneal/generated/Verify/EdgePkg/call_trusted_rev.lean"),
    )
    .expect("read generated Verify/EdgePkg/call_trusted_rev.lean");
    assert!(
        modular_verify.contains("ModularItemProof")
            && modular_verify.contains("dischargeRustModularContractAuto"),
        "call_trusted_rev must be discharged through the modular route:\n{modular_verify}"
    );

    // Call-containing `ensures` companions must emit the `*WithSpecCalleesAuto`
    // auto-discharge combinators across both `ItemProof` and `TotalItemProof`.
    let spec_callee_bound_verify = fs::read_to_string(
        temp_crate.join(".anneal/generated/Verify/EdgePkg/bound_with_spec_callee.lean"),
    )
    .expect("read generated Verify/EdgePkg/bound_with_spec_callee.lean");
    assert!(
        spec_callee_bound_verify.contains("dischargeRustBoundedRange1WithSpecCalleesAuto"),
        "bound_with_spec_callee must emit dischargeRustBoundedRange1WithSpecCalleesAuto:\n{spec_callee_bound_verify}"
    );
    let spec_callee_total_verify = fs::read_to_string(
        temp_crate.join(".anneal/generated/Verify/EdgePkg/total_pin_with_spec_callee.lean"),
    )
    .expect("read generated Verify/EdgePkg/total_pin_with_spec_callee.lean");
    assert!(
        spec_callee_total_verify.contains("TotalItemProof")
            && spec_callee_total_verify.contains("dischargeRustTotalPinnedContractWithSpecCalleesAuto"),
        "total_pin_with_spec_callee must emit TotalItemProof + dischargeRustTotalPinnedContractWithSpecCalleesAuto:\n{spec_callee_total_verify}"
    );

    let report = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate)
            .with_anneal_repo_root(&checkout_root)
            .with_allow_assumptions(true),
    )
    .expect("edge-shape verify_workspace_with_config(allow_assumptions = true) must succeed");

    for module in [
        "Verify.EdgePkg.rev_pin",
        "Verify.EdgePkg.add_two",
        "Verify.EdgePkg.le_bound",
        "Verify.EdgePkg.u64_pin",
        "Verify.EdgePkg.u8_pin",
        "Verify.EdgePkg.ref_ens",
        "Verify.EdgePkg.call_rev",
        "Verify.EdgePkg.ffi_rev",
        "Verify.EdgePkg.call_ffi_rev",
        "Verify.EdgePkg.call_trusted_rev",
        "Verify.EdgePkg.usize_pin",
        "Verify.EdgePkg.bound_with_spec_callee",
        "Verify.EdgePkg.total_pin_with_spec_callee",
    ] {
        assert_eq!(
            report.status_for(module),
            Some(&VerificationStatus::VerifiedUnconditional),
            "expected {module} to be VerifiedUnconditional"
        );
    }
    assert_eq!(
        report.status_for("Verify.EdgePkg.ffi_trusted_rev"),
        Some(&VerificationStatus::VerifiedConditional {
            assumptions: vec![
                "Assumptions.EdgePkg.ffi_trusted_rev.rust_trusted_contract".to_string()
            ],
        })
    );

    let summary = render_verification_report(&report);
    assert!(
        summary.contains("Totals: 13 unconditional, 1 conditional"),
        "unexpected edge-shape summary:\n{summary}"
    );
    assert!(summary.contains("TrustedBoundary kernel replay: PASS"));

    let _ = fs::remove_dir_all(&temp_crate);
}

/// Soundness canary for the closure-captured companion auto-discharge on real
/// captured MIR: implementations that violate their `#[spec]` must be rejected
/// by the generated default proofs even though their companions use the
/// reversed, `<=`, and modular-`trusted` shapes that
/// `end_to_end_rust_only_closure_deref_edge_shapes` accepts. `ok_pin` keeps a
/// correct sibling in the crate so the failure is attributed per item.
#[test]
fn end_to_end_rust_only_closure_deref_rejects_false_contracts() {
    let checkout_root = anneal_checkout_root();
    let wrapper_bin = ensure_rustc_capture_binary(&checkout_root);

    let temp_crate = unique_temp_dir("rust-only-closure-deref-negative");
    let src_dir = temp_crate.join("src");
    fs::create_dir_all(&src_dir).expect("create temporary crate src/");

    let anneal_spec_dir = checkout_root.join("crates").join("anneal-spec");
    let cargo_toml = format!(
        r#"[package]
name = "edge_neg_pkg"
version = "0.1.0"
edition = "2024"
publish = false

[dependencies]
anneal-spec = {{ path = "{}" }}
"#,
        anneal_spec_dir.display()
    );
    fs::write(temp_crate.join("Cargo.toml"), cargo_toml).expect("write Cargo.toml");

    // `rev_pin` returns 42, `le_bound` returns 101 at `x = 100`, and
    // `call_trusted_rev` returns 50 under the trusted callee contract.
    let lib_rs = r#"#![allow(dead_code)]

use anneal_spec::*;

#[anneal_spec::spec(
    requires: 10 == port,
    ensures: |ret: u32| ret == 43,
)]
pub fn rev_pin(port: u32) -> u32 {
    port + 32
}

#[anneal_spec::spec(
    requires: x <= 100,
    ensures: |ret: u32| ret <= 100,
)]
pub fn le_bound(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    trusted,
    requires: 10 == port,
    ensures: |ret: u32| 42 == ret,
)]
pub unsafe fn ffi_trusted_rev(port: u32) -> u32 {
    port.wrapping_add(999)
}

#[anneal_spec::spec(
    requires: port == 10,
    ensures: |ret: u32| ret == 51,
)]
pub fn call_trusted_rev(port: u32) -> u32 {
    let v = unsafe { ffi_trusted_rev(port) };
    v + 8
}

#[anneal_spec::spec(
    requires: x == 7,
    ensures: |ret: u32| ret == 8,
)]
pub fn ok_pin(x: u32) -> u32 {
    x + 1
}

#[anneal_spec::spec(
    requires: x < 8,
    ensures: |ret: u32| ret == ok_pin(x),
)]
pub fn bad_spec_callee_bound(x: u32) -> u32 {
    x + 2
}

#[anneal_spec::spec(
    safe_total,
    requires: 42 == x,
    ensures: |ret: u32| x.wrapping_add(5) == ret,
)]
pub fn bad_total_spec_callee(x: u32) -> u32 {
    x + 6
}
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write src/lib.rs");

    let mut driver_cfg = CaptureDriverConfig::new(&temp_crate);
    driver_cfg.rustc_wrapper = Some(wrapper_bin);
    let (manifest, records) =
        run_cargo_capture(&driver_cfg).expect("negative run_cargo_capture must succeed");
    assert!(manifest.compilation_succeeded);
    let scaffold_cfg = ScaffoldConfig {
        workspace_root: temp_crate.clone(),
        units_dir: Some(driver_cfg.units_dir.clone()),
        anneal_repo_root: Some(checkout_root.clone()),
        init_spec_templates: false,
        init_proof_templates: false,
    };
    scaffold_workspace_with_config(&scaffold_cfg, &records)
        .expect("negative scaffold_workspace_with_config must succeed");
    assert_eq!(count_lean_files(&temp_crate.join("anneal/proofs")), 0);

    let err = verify_workspace_with_config(
        &VerifyConfig::new(&temp_crate)
            .with_anneal_repo_root(&checkout_root)
            .with_allow_assumptions(true),
    )
    .expect_err("false closure-deref contracts must not verify");
    for module_file in [
        "Verify/EdgeNegPkg/rev_pin.lean",
        "Verify/EdgeNegPkg/le_bound.lean",
        "Verify/EdgeNegPkg/call_trusted_rev.lean",
        "Verify/EdgeNegPkg/bad_spec_callee_bound.lean",
        "Verify/EdgeNegPkg/bad_total_spec_callee.lean",
    ] {
        assert!(
            err.contains(module_file),
            "expected a kernel rejection in {module_file}, got:\n{err}"
        );
    }
    assert!(
        !err.contains("Verify/EdgeNegPkg/ok_pin.lean"),
        "the correct sibling ok_pin must still verify, got:\n{err}"
    );

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
