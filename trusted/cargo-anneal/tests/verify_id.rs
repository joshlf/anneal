// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for `cargo-anneal verify`.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use cargo_anneal::{
    CaptureError, ReleaseChannel, VerifyError, VerifyOptions, capture_crate,
    capture_crate_with_options, run_trusted_audit, verify_crate,
};

struct TempCrateDir {
    _dir: tempfile::TempDir,
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
        let dir = tempfile::Builder::new()
            .prefix(&format!("anneal-verify-id-{label}-"))
            .tempdir()
            .expect("create temp crate dir");
        let path = dir.path().to_path_buf();
        let src_dir = path.join("src");
        fs::create_dir_all(&src_dir).expect("create temp crate src dir");
        if let Some(toml) = cargo_toml {
            fs::write(path.join("Cargo.toml"), toml.as_bytes())
                .expect("write temp Cargo.toml");
        }
        fs::write(src_dir.join("lib.rs"), lib_rs_source.as_bytes())
            .expect("write temp src/lib.rs");
        Self { _dir: dir, path }
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

    fs::write(
        &output.mir_lean_path,
        b"prelude\nimport Trusted\nnamespace Mir\ntheorem crate : True := trivial\nend Mir\n",
    )
    .unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Proof.lean"),
        b"prelude\nimport Trusted\nimport Mir\nnamespace Proof\ntheorem verify_crate : True := Mir.crate\nend Proof\n",
    )
    .unwrap();

    let err =
        run_trusted_audit(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    match err {
        VerifyError::AuditRejected { stderr, .. } => {
            assert!(
                stderr.contains("Mir.crate must be a definition, found theorem"),
                "expected Mir.crate definition check rejection, got: {stderr}"
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
