// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for `cargo-anneal verify` on the `#109`
//! vertical slice (`pub fn id(x: usize) -> usize { x }`).

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use cargo_anneal::audit::ReleaseChannel;
use cargo_anneal::{
    CaptureError, VerifyError, VerifyOptions, capture_crate,
    capture_crate_with_options, run_trusted_audit, verify_crate,
};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

struct TempCrateDir {
    path: PathBuf,
}

impl TempCrateDir {
    fn new(label: &str, lib_rs_source: &str) -> Self {
        Self::new_with_cargo_toml(
            label,
            lib_rs_source,
            Some(
                "[package]\n\
                 name = \"sample\"\n\
                 version = \"0.1.0\"\n\
                 edition = \"2024\"\n\n\
                 [package.metadata.anneal.trust-policy]\n\
                 allow-candidate-features = [\"*\"]\n",
            ),
        )
    }

    fn new_without_policy(label: &str, lib_rs_source: &str) -> Self {
        Self::new_with_cargo_toml(
            label,
            lib_rs_source,
            Some(
                "[package]\n\
                 name = \"sample\"\n\
                 version = \"0.1.0\"\n\
                 edition = \"2024\"\n",
            ),
        )
    }

    fn new_with_cargo_toml(
        label: &str,
        lib_rs_source: &str,
        cargo_toml: Option<&str>,
    ) -> Self {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = env::temp_dir().join(format!(
            "anneal-verify-id-{}-{}-{}",
            std::process::id(),
            label,
            id
        ));
        let src_dir = path.join("src");
        fs::create_dir_all(&src_dir).expect("create temp crate src dir");
        if let Some(toml) = cargo_toml {
            fs::write(path.join("Cargo.toml"), toml.as_bytes())
                .expect("write temp Cargo.toml");
        }
        fs::write(src_dir.join("lib.rs"), lib_rs_source.as_bytes())
            .expect("write temp src/lib.rs");
        Self { path }
    }
}

impl Drop for TempCrateDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn verifies_annotated_pub_fn_id_via_cli() {
    let crate_dir = TempCrateDir::new(
        "annotated-id",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let bin = env!("CARGO_BIN_EXE_cargo-anneal");
    let output = Command::new(bin)
        .arg("anneal")
        .arg("verify")
        .arg(&crate_dir.path)
        .output()
        .expect("invoke cargo-anneal binary");

    assert!(
        output.status.success(),
        "expected `cargo-anneal anneal verify` to succeed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let mir_lean =
        fs::read_to_string(crate_dir.path.join(".anneal/Mir.lean")).unwrap();
    assert!(mir_lean.contains("Trusted.EnsuresEqArg 1"));
    assert!(crate_dir.path.join(".anneal/CaptureManifest.json").is_file());
    assert!(crate_dir.path.join(".anneal/Proof.lean").is_file());
}

#[test]
fn verifies_unannotated_pub_fn_id_well_formedness() {
    let crate_dir = TempCrateDir::new(
        "unannotated-id",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "id");

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("specs := []"));
}

#[test]
fn rejects_incorrect_id_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-id",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(_x: usize) -> usize {\n    \
             0\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for false spec, got: {err}"
    );
}

#[test]
fn rejects_unsupported_mir_construct_fail_closed() {
    let crate_dir = TempCrateDir::new(
        "unsupported-add",
        "pub fn add(x: u32, y: u32) -> u32 {\n    \
             x + y\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(
            err,
            VerifyError::Capture(CaptureError::UnsupportedMir(_))
        ),
        "expected fail-closed UnsupportedMir error, got: {err}"
    );
}

#[test]
fn rejects_tampered_mir_lean_after_capture() {
    let crate_dir = TempCrateDir::new(
        "tampered-mir",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let output = capture_crate_with_options(
        &crate_dir.path,
        true,
        &VerifyOptions::default(),
    )
    .unwrap();

    let mut mir_src = fs::read_to_string(&output.mir_lean_path).unwrap();
    mir_src.push_str("\n-- post-capture tampering\n");
    fs::write(&output.mir_lean_path, mir_src.as_bytes()).unwrap();

    let err =
        run_trusted_audit(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    match err {
        VerifyError::AuditRejected { stderr, .. } => {
            assert!(
                stderr.contains("Mir module digest mismatch for .anneal/Mir.lean"),
                "expected SHA-256 mismatch error, got: {stderr}"
            );
        }
        other => panic!("expected AuditRejected, got: {other}"),
    }
}

#[test]
fn rejects_spoofed_theorem_type_in_proof_lean() {
    let crate_dir = TempCrateDir::new(
        "spoofed-proof",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let _ = capture_crate(&crate_dir.path).unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Proof.lean"),
        b"prelude\nimport Trusted\nimport Mir\nnamespace Proof\ntheorem verify_crate : True := trivial\nend Proof\n",
    )
    .unwrap();

    let options = VerifyOptions {
        keep_proof: true,
        ..VerifyOptions::default()
    };
    let err = verify_crate(&crate_dir.path, &options).unwrap_err();
    match err {
        VerifyError::AuditRejected { stderr, .. } => {
            assert!(
                stderr.contains(
                    "Proof.verify_crate has type True, expected Trusted.CrateTheorem Mir.crate"
                ),
                "expected exact kernel type rejection, got: {stderr}"
            );
        }
        other => panic!("expected AuditRejected, got: {other}"),
    }
}

#[test]
fn rejects_candidate_features_by_default_without_opt_in() {
    let crate_dir = TempCrateDir::new_without_policy(
        "default-vetted-only",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    match err {
        VerifyError::Capture(CaptureError::CandidateFeatureNotEnabled {
            feature,
            ..
        }) => {
            assert_eq!(feature, "rustc_capture");
        }
        other => panic!(
            "expected pre-execution CandidateFeatureNotEnabled for rustc_capture, got: {other}"
        ),
    }
    assert!(
        !crate_dir.path.join(".anneal/Mir.lean").exists(),
        "rustc should not execute when candidate capture feature is not enabled"
    );
}

#[test]
fn rejects_candidate_features_on_stable_release_channel() {
    let crate_dir = TempCrateDir::new(
        "stable-channel-rejects-candidates",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let options = VerifyOptions {
        release_channel: Some(ReleaseChannel::Stable),
        ..VerifyOptions::default()
    };
    let err = verify_crate(&crate_dir.path, &options).unwrap_err();
    match err {
        VerifyError::Capture(CaptureError::CandidateFeatureNotEnabled {
            feature,
            reason,
        }) => {
            assert_eq!(feature, "rustc_capture");
            assert!(reason.contains("stable release channel"));
        }
        other => panic!(
            "expected CandidateFeatureNotEnabled on stable channel, got: {other}"
        ),
    }
}

#[test]
fn verifies_via_cli_flag_and_emits_candidate_tcb_audit_section() {
    let crate_dir = TempCrateDir::new_without_policy(
        "cli-allow-candidates",
        "// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );

    let bin = env!("CARGO_BIN_EXE_cargo-anneal");
    let output = Command::new(bin)
        .arg("anneal")
        .arg("verify")
        .arg("--allow-candidate-features")
        .arg("*")
        .arg(&crate_dir.path)
        .output()
        .expect("invoke cargo-anneal binary");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected `cargo-anneal anneal verify --allow-candidate-features '*'` to succeed:\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("Candidate-Trusted TCB (Unvetted / Alpha):"),
        "expected Candidate-Trusted TCB audit section in stdout, got: {stdout}"
    );
    assert!(stdout.contains("rustc_capture"));
    assert!(stdout.contains("mir_semantics"));
}

#[test]
fn verifies_annotated_pub_fn_load_relaxed() {
    let crate_dir = TempCrateDir::new(
        "annotated-load-relaxed",
        "use core::sync::atomic::{AtomicUsize, Ordering};\n\n\
         // anneal:spec ensures(atomic_load(a))\n\
         pub fn load_relaxed(a: &AtomicUsize) -> usize {\n    \
             a.load(Ordering::Relaxed)\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "load_relaxed");

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("Trusted.EnsuresAtomicLoad 1"));
    assert!(mir_lean.contains("Trusted.Terminator.callAtomicLoad"));
}

#[test]
fn verifies_unannotated_pub_fn_load_relaxed_well_formedness() {
    let crate_dir = TempCrateDir::new(
        "unannotated-load-relaxed",
        "use core::sync::atomic::{AtomicUsize, Ordering};\n\n\
         pub fn load_relaxed(a: &AtomicUsize) -> usize {\n    \
             a.load(Ordering::Relaxed)\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "load_relaxed");
}

#[test]
fn rejects_incorrect_load_relaxed_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-load-relaxed",
        "use core::sync::atomic::AtomicUsize;\n\n\
         // anneal:spec ensures(atomic_load(a))\n\
         pub fn load_relaxed(_a: &AtomicUsize) -> usize {\n    \
             0\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for false atomic load spec, got: {err}"
    );
}

#[test]
fn verifies_annotated_pub_fn_max_assign() {
    let crate_dir = TempCrateDir::new(
        "annotated-max-assign",
        "// anneal:spec ensures(max_assign(x, y))\n\
         pub fn max_assign(x: &mut usize, y: usize) -> usize {\n    \
             if *x < y {\n        \
                 *x = y;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "max_assign");

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("Trusted.EnsuresMaxAssign"));
    assert!(mir_lean.contains("Trusted.Terminator.switchInt"));
}

#[test]
fn verifies_unannotated_pub_fn_max_assign_well_formedness() {
    let crate_dir = TempCrateDir::new(
        "unannotated-max-assign",
        "pub fn max_assign(x: &mut usize, y: usize) -> usize {\n    \
             if *x < y {\n        \
                 *x = y;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "max_assign");
}

#[test]
fn rejects_incorrect_max_assign_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-max-assign",
        "// anneal:spec ensures(max_assign(x, y))\n\
         pub fn max_assign(x: &mut usize, y: usize) -> usize {\n    \
             if *x <= y {\n        \
                 *x = y;\n    \
             }\n    \
             y\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong max_assign body, got: {err}"
    );
}

#[test]
fn verifies_annotated_pub_fn_update_min() {
    let crate_dir = TempCrateDir::new(
        "annotated-update-min",
        "// anneal:spec ensures(update_min(x, y, v))\n\
         pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize {\n    \
             let r = if *x <= *y { &mut *x } else { &mut *y };\n    \
             *r = v;\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "update_min");

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("Trusted.EnsuresUpdateMin"));
    assert!(mir_lean.contains("Trusted.Terminator.switchInt"));
}

#[test]
fn verifies_unannotated_pub_fn_update_min_well_formedness() {
    let crate_dir = TempCrateDir::new(
        "unannotated-update-min",
        "pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize {\n    \
             let r = if *x <= *y { &mut *x } else { &mut *y };\n    \
             *r = v;\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "update_min");
}

#[test]
fn rejects_incorrect_update_min_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-update-min",
        "// anneal:spec ensures(update_min(x, y, v))\n\
         pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize {\n    \
             let r = if *x < *y { &mut *x } else { &mut *y };\n    \
             *r = v;\n    \
             *x\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong update_min body, got: {err}"
    );
}

#[test]
fn verifies_clamp_assign_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-clamp-assign",
        "// anneal:spec ensures(clamp_assign(x, lo, hi))\n\
         pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize {\n    \
             if *x < lo {\n        \
                 *x = lo;\n    \
             } else if *x > hi {\n        \
                 *x = hi;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "clamp_assign");
}

#[test]
fn rejects_incorrect_clamp_assign_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-clamp-assign",
        "// anneal:spec ensures(clamp_assign(x, lo, hi))\n\
         pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize {\n    \
             if *x <= lo {\n        \
                 *x = lo;\n    \
             } else if *x > hi {\n        \
                 *x = hi;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong clamp_assign body, got: {err}"
    );
}

#[test]
fn verifies_is_aligned_mask_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-is-aligned-mask",
        "// anneal:spec ensures(is_aligned_mask(addr, mask))\n\
         pub fn is_aligned_mask(addr: usize, mask: usize) -> bool {\n    \
             (addr & mask) == 0\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "is_aligned_mask");
}

#[test]
fn rejects_incorrect_is_aligned_mask_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-is-aligned-mask",
        "// anneal:spec ensures(is_aligned_mask(addr, mask))\n\
         pub fn is_aligned_mask(addr: usize, mask: usize) -> bool {\n    \
             (addr | mask) == 0\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong is_aligned_mask body, got: {err}"
    );
}

#[test]
fn verifies_shared_max_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-shared-max",
        "// anneal:spec ensures(shared_max(x, y))\n\
         pub fn shared_max(x: &usize, y: &usize) -> usize {\n    \
             let r = if *x < *y { y } else { x };\n    \
             *r\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "shared_max");
}

#[test]
fn rejects_incorrect_shared_max_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-shared-max",
        "// anneal:spec ensures(shared_max(x, y))\n\
         pub fn shared_max(x: &usize, y: &usize) -> usize {\n    \
             let r = if *x <= *y { x } else { y };\n    \
             *r\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong shared_max body, got: {err}"
    );
}

#[test]
fn verifies_max_assign_shared_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-max-assign-shared",
        "// anneal:spec ensures(max_assign_shared(dst, src))\n\
         pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize {\n    \
             if *dst < *src {\n        \
                 *dst = *src;\n    \
             }\n    \
             *dst\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "max_assign_shared");
}

#[test]
fn rejects_incorrect_max_assign_shared_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-max-assign-shared",
        "// anneal:spec ensures(max_assign_shared(dst, src))\n\
         pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize {\n    \
             if *dst > *src {\n        \
                 *dst = *src;\n    \
             }\n    \
             *dst\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong max_assign_shared body, got: {err}"
    );
}

#[test]
fn verifies_sort_pair_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-sort-pair",
        "// anneal:spec ensures(sort_pair(x, y))\n\
         pub fn sort_pair(x: &mut usize, y: &mut usize) -> usize {\n    \
             if *x > *y {\n        \
                 let tmp = *x;\n        \
                 *x = *y;\n        \
                 *y = tmp;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "sort_pair");
}

#[test]
fn rejects_incorrect_sort_pair_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-sort-pair",
        "// anneal:spec ensures(sort_pair(x, y))\n\
         pub fn sort_pair(x: &mut usize, y: &mut usize) -> usize {\n    \
             if *x < *y {\n        \
                 let tmp = *x;\n        \
                 *x = *y;\n        \
                 *y = tmp;\n    \
             }\n    \
             *x\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong sort_pair body, got: {err}"
    );
}

#[test]
fn verifies_two_phase_reborrow_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-two-phase-reborrow",
        "// anneal:spec ensures(two_phase_reborrow(x, y, a, b))\n\
         pub fn two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize) -> usize {\n    \
             let r1 = if *x <= *y { &mut *x } else { &mut *y };\n    \
             *r1 = a;\n    \
             let r2 = if *x <= *y { &mut *y } else { &mut *x };\n    \
             *r2 = b;\n    \
             *x\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "two_phase_reborrow");
}

#[test]
fn rejects_incorrect_two_phase_reborrow_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-two-phase-reborrow",
        "// anneal:spec ensures(two_phase_reborrow(x, y, a, b))\n\
         pub fn two_phase_reborrow(x: &mut usize, y: &mut usize, a: usize, b: usize) -> usize {\n    \
             let r1 = if *x <= *y { &mut *x } else { &mut *y };\n    \
             *r1 = a;\n    \
             let r2 = if *x <= *y { &mut *x } else { &mut *y };\n    \
             *r2 = b;\n    \
             *x\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong two_phase_reborrow body, got: {err}"
    );
}

#[test]
fn verifies_add_bounded_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-add-bounded",
        "// anneal:spec ensures(add_bounded(x, y))\n\
         pub fn add_bounded(x: usize, y: usize) -> usize {\n    \
             if x <= 1000 && y <= 1000 {\n        \
                 x + y\n    \
             } else {\n        \
                 0\n    \
             }\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "add_bounded");
}

#[test]
fn rejects_unguarded_add_bounded_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-add-bounded",
        "// anneal:spec ensures(add_bounded(x, y))\n\
         pub fn add_bounded(x: usize, y: usize) -> usize {\n    \
             x + y\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for unguarded add_bounded body, got: {err}"
    );
}

#[test]
fn verifies_abs_diff_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-abs-diff",
        "// anneal:spec ensures(abs_diff(x, y))\n\
         pub fn abs_diff(x: usize, y: usize) -> usize {\n    \
             if x >= y {\n        \
                 x - y\n    \
             } else {\n        \
                 y - x\n    \
             }\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "abs_diff");
}

#[test]
fn rejects_incorrect_abs_diff_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-abs-diff",
        "// anneal:spec ensures(abs_diff(x, y))\n\
         pub fn abs_diff(x: usize, y: usize) -> usize {\n    \
             if x <= y {\n        \
                 x - y\n    \
             } else {\n        \
                 y - x\n    \
             }\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong abs_diff body, got: {err}"
    );
}

#[test]
fn verifies_choose_mut_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-choose-mut",
        "// anneal:spec ensures(choose_mut(b, x, y))\n\
         pub fn choose_mut<'a>(b: bool, x: &'a mut usize, y: &'a mut usize) -> &'a mut usize {\n    \
             if b { x } else { y }\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "choose_mut");
}

#[test]
fn rejects_incorrect_choose_mut_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-choose-mut",
        "// anneal:spec ensures(choose_mut(b, x, y))\n\
         pub fn choose_mut<'a>(b: bool, x: &'a mut usize, y: &'a mut usize) -> &'a mut usize {\n    \
             if !b { x } else { y }\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong choose_mut body, got: {err}"
    );
}

#[test]
fn verifies_count_up_end_to_end() {
    let crate_dir = TempCrateDir::new(
        "valid-count-up",
        "// anneal:spec ensures(count_up(n))\n\
         pub fn count_up(n: usize) -> usize {\n    \
             let mut i = 0;\n    \
             while i < n && i < 1000 {\n        \
                 i += 1;\n    \
             }\n    \
             i\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "count_up");
}

#[test]
fn rejects_incorrect_count_up_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-count-up",
        "// anneal:spec ensures(count_up(n))\n\
         pub fn count_up(n: usize) -> usize {\n    \
             let mut i = 0;\n    \
             while i < n && i < 999 {\n        \
                 i += 1;\n    \
             }\n    \
             i\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean audit rejection for wrong count_up body, got: {err}"
    );
}
