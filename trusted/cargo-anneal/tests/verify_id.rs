// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for `cargo-anneal verify`.

use std::fs;
use std::os::unix::fs::symlink;
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

#[test]
fn verifies_library_crate_with_assoc_const_pme_and_wrapper() {
    let crate_dir = TempCrateDir::new(
        "assoc-const-pme-lib",
        "pub trait SizeEq<Src, Dst> {\n    \
             const ASSERT: ();\n\
         }\n\
         impl<Src, Dst> SizeEq<Src, Dst> for () {\n    \
             const ASSERT: () = assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());\n\
         }\n\
         pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             let () = <() as SizeEq<Src, Dst>>::ASSERT;\n    \
             unsafe { core::mem::transmute_copy(&x) }\n\
         }\n\
         pub fn outer_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             transmute_checked::<Src, Dst>(x)\n\
         }\n",
    );

    let bin = env!("CARGO_BIN_EXE_cargo-anneal");
    let output = Command::new(bin)
        .arg("anneal")
        .arg("verify")
        .arg(&crate_dir.path)
        .output()
        .expect("invoke cargo-anneal binary");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected PME library crate verification to succeed:\nstdout: {stdout}\nstderr: {stderr}"
    );

    let mir_lean =
        fs::read_to_string(crate_dir.path.join(".anneal/Mir.lean")).unwrap();
    assert!(mir_lean.contains("def pme_assert_const_body : Trusted.MirBody"));
    assert!(mir_lean.contains(
        "requiredConsts := [(pme_assert_const_body, \
         [Trusted.MirTy.param 0, Trusted.MirTy.param 1])]"
    ));
    assert!(
        mir_lean.contains("Trusted.Terminator.call1 ⟨0⟩ transmute_checked_body")
    );
}

#[test]
fn verifies_library_crate_with_inline_const_pme() {
    let crate_dir = TempCrateDir::new(
        "inline-const-pme-lib",
        "pub fn inline_const_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             let () = const { assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>()) };\n    \
             unsafe { core::mem::transmute_copy(&x) }\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "inline_const_transmute");
    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains(
        "requiredConsts := [(pme_assert_const_body, \
         [Trusted.MirTy.param 0, Trusted.MirTy.param 1])]"
    ));
}

#[test]
fn rejects_transmute_without_pme_assertion() {
    let crate_dir = TempCrateDir::new(
        "transmute-without-pme",
        "pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             unsafe { core::mem::transmute_copy(&x) }\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean kernel rejection when PME size assertion is omitted, got: {err}"
    );
}

#[test]
fn verifies_nonzero_library_crate_with_safe_and_unsafe_apis() {
    let crate_dir = TempCrateDir::new(
        "nonzero-lib",
        "#[repr(transparent)]\n\
         pub struct NonZeroUsize {\n    \
             val: usize,\n\
         }\n\
         pub fn make_nonzero(x: usize) -> NonZeroUsize {\n    \
             if x == 0 {\n        \
                 NonZeroUsize { val: 1 }\n    \
             } else {\n        \
                 NonZeroUsize { val: x }\n    \
             }\n\
         }\n\
         pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {\n    \
             NonZeroUsize { val: x }\n\
         }\n\
         pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize {\n    \
             if x.val == 0 {\n        \
                 unsafe { core::hint::unreachable_unchecked() }\n    \
             } else {\n        \
                 x.val\n    \
             }\n\
         }\n",
    );

    let output =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap();
    assert_eq!(output.functions.len(), 3);

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("access := Trusted.FieldAccess.priv"));
    assert!(mir_lean.contains("adtInv := nonZeroAdtInv"));
    assert!(mir_lean.contains(
        "kind := Trusted.FnKind.pubUnsafe True newUncheckedSafetyPre"
    ));
}

#[test]
fn rejects_nonzero_library_when_safe_fn_violates_invariant() {
    let crate_dir = TempCrateDir::new(
        "nonzero-buggy-zero",
        "#[repr(transparent)]\n\
         pub struct NonZeroUsize {\n    \
             val: usize,\n\
         }\n\
         pub fn make_nonzero(_x: usize) -> NonZeroUsize {\n    \
             NonZeroUsize { val: 0 }\n\
         }\n\
         pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {\n    \
             NonZeroUsize { val: x }\n\
         }\n\
         pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize {\n    \
             if x.val == 0 {\n        \
                 unsafe { core::hint::unreachable_unchecked() }\n    \
             } else {\n        \
                 x.val\n    \
             }\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean kernel rejection when safe constructor returns 0, got: {err}"
    );
}

#[test]
fn rejects_nonzero_library_when_field_is_pub_safe() {
    let crate_dir = TempCrateDir::new(
        "nonzero-pub-field",
        "#[repr(transparent)]\n\
         pub struct NonZeroUsize {\n    \
             pub val: usize,\n\
         }\n\
         pub fn make_nonzero(x: usize) -> NonZeroUsize {\n    \
             if x == 0 {\n        \
                 NonZeroUsize { val: 1 }\n    \
             } else {\n        \
                 NonZeroUsize { val: x }\n    \
             }\n\
         }\n\
         pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {\n    \
             NonZeroUsize { val: x }\n\
         }\n\
         pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize {\n    \
             if x.val == 0 {\n        \
                 unsafe { core::hint::unreachable_unchecked() }\n    \
             } else {\n        \
                 x.val\n    \
             }\n\
         }\n",
    );

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err, VerifyError::AuditRejected { .. }),
        "expected Lean kernel rejection when NonZeroUsize field is pubSafe, got: {err}"
    );
}

#[test]
fn rejects_symlinked_manifest_and_lib_rs_and_extra_targets() {
    let crate_dir = TempCrateDir::new(
        "symlink-lib",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );
    let real_lib = crate_dir.path.join("src/real_lib.rs");
    fs::rename(crate_dir.path.join("src/lib.rs"), &real_lib).unwrap();
    symlink(&real_lib, crate_dir.path.join("src/lib.rs")).unwrap();

    let err =
        verify_crate(&crate_dir.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(
            err,
            VerifyError::Capture(
                CaptureError::Io(_) | CaptureError::UnsupportedMir(_)
            )
        ),
        "expected symlinked src/lib.rs rejection, got: {err}"
    );

    let symlink_toml_crate = TempCrateDir::new(
        "symlink-toml",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );
    let real_toml = symlink_toml_crate.path.join("real_Cargo.toml");
    fs::rename(symlink_toml_crate.path.join("Cargo.toml"), &real_toml).unwrap();
    symlink(&real_toml, symlink_toml_crate.path.join("Cargo.toml")).unwrap();
    let err_toml =
        verify_crate(&symlink_toml_crate.path, &VerifyOptions::default())
            .unwrap_err();
    assert!(
        matches!(
            err_toml,
            VerifyError::Capture(
                CaptureError::Io(_) | CaptureError::UnsupportedMir(_)
            )
        ),
        "expected symlinked Cargo.toml rejection, got: {err_toml}"
    );

    let build_rs_crate = TempCrateDir::new(
        "extra-build-rs",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );
    fs::write(build_rs_crate.path.join("build.rs"), b"fn main() {}\n").unwrap();
    let err2 = verify_crate(&build_rs_crate.path, &VerifyOptions::default())
        .unwrap_err();
    assert!(
        matches!(
            err2,
            VerifyError::Capture(
                CaptureError::Io(_) | CaptureError::UnsupportedMir(_)
            )
        ),
        "expected build.rs rejection, got: {err2}"
    );

    let bin_crate = TempCrateDir::new_with_cargo_toml(
        "extra-bin-target",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
        Some(
            "[package]\n\
             name = \"sample\"\n\
             version = \"0.1.0\"\n\
             edition = \"2024\"\n\n\
             [package.metadata.anneal.trust-policy]\n\
             allow-candidate-features = [\"*\"]\n\n\
             [[bin]]\n\
             name = \"helper\"\n\
             path = \"src/main.rs\"\n",
        ),
    );
    fs::write(bin_crate.path.join("src/main.rs"), b"fn main() {}\n").unwrap();
    let err_bin =
        verify_crate(&bin_crate.path, &VerifyOptions::default()).unwrap_err();
    assert!(
        matches!(err_bin, VerifyError::Capture(CaptureError::UnsupportedMir(_))),
        "expected extra [[bin]] target rejection, got: {err_bin}"
    );

    let proof_lean_crate = TempCrateDir::new(
        "existing-src-proof-lean",
        "pub fn id(x: usize) -> usize {\n    \
             x\n\
         }\n",
    );
    fs::write(proof_lean_crate.path.join("src/proof.lean"), b"-- proof\n")
        .unwrap();
    let err_proof =
        verify_crate(&proof_lean_crate.path, &VerifyOptions::default())
            .unwrap_err();
    assert!(
        matches!(
            err_proof,
            VerifyError::Capture(CaptureError::UnsupportedMir(_))
        ),
        "expected existing src/proof.lean rejection, got: {err_proof}"
    );
}

#[test]
fn captures_alloc_passthrough_with_doc_spec_and_emits_artifact() {
    let crate_dir = TempCrateDir::new(
        "alloc-passthrough",
        "/// anneal:spec ensures(ret == x)\n\
         pub fn alloc_passthrough(x: usize) -> usize {\n    \
             let a = x;\n    \
             let b = a;\n    \
             b\n\
         }\n",
    );

    let output = capture_crate_with_options(
        &crate_dir.path,
        true,
        &VerifyOptions::default(),
    )
    .unwrap();
    assert_eq!(output.functions.len(), 1);
    assert_eq!(output.functions[0].name, "alloc_passthrough");

    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains("artifacts := [{ path := \"src/lib.rs\""));
    assert!(mir_lean.contains("Trusted.EnsuresEqArg 1"));
}

#[test]
fn captures_pme_and_nonzero_with_renamed_generics_and_pub_crate() {
    let pme_crate = TempCrateDir::new(
        "renamed-generics-pme",
        "const DECOY: () = ();\n\
         pub trait SizeEq<A, B> {\n    \
             const ASSERT: ();\n\
         }\n\
         impl<A, B> SizeEq<A, B> for () {\n    \
             const ASSERT: () = assert!(core::mem::size_of::<A>() == core::mem::size_of::<B>());\n\
         }\n\
         pub fn transmute_checked<First: Copy, Second: Copy>(x: First) -> Second {\n    \
             let () = <() as SizeEq<First, Second>>::ASSERT;\n    \
             unsafe { core::mem::transmute_copy(&x) }\n\
         }\n\
         pub fn swapped_outer<U: Copy, V: Copy>(x: V) -> U {\n    \
             transmute_checked::<V, U>(x)\n\
         }\n",
    );

    let output = capture_crate_with_options(
        &pme_crate.path,
        true,
        &VerifyOptions::default(),
    )
    .unwrap();
    assert_eq!(output.functions.len(), 2);
    let mir_lean = fs::read_to_string(&output.mir_lean_path).unwrap();
    assert!(mir_lean.contains(
        "requiredConsts := [(pme_assert_const_body, \
         [Trusted.MirTy.param 0, Trusted.MirTy.param 1])]"
    ));
    assert!(mir_lean.contains(
        "(Trusted.Terminator.call1 ⟨0⟩ transmute_checked_body \
         (Trusted.Operand.move ⟨2⟩) ⟨1⟩ \
         [Trusted.MirTy.param 1, Trusted.MirTy.param 0])"
    ));

    let nz_crate = TempCrateDir::new(
        "pub-crate-nonzero",
        "#[repr(transparent)]\n\
         pub struct NonZeroUsize {\n    \
             #[allow(dead_code)]\n    \
             pub(crate) val: usize,\n\
         }\n\
         pub fn make_nonzero(x: usize) -> NonZeroUsize {\n    \
             if x == 0 {\n        \
                 NonZeroUsize { val: 1 }\n    \
             } else {\n        \
                 NonZeroUsize { val: x }\n    \
             }\n\
         }\n\
         pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {\n    \
             NonZeroUsize { val: x }\n\
         }\n\
         pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize {\n    \
             if x.val == 0 {\n        \
                 unsafe { core::hint::unreachable_unchecked() }\n    \
             } else {\n        \
                 x.val\n    \
             }\n\
         }\n",
    );
    let nz_out = capture_crate_with_options(
        &nz_crate.path,
        true,
        &VerifyOptions::default(),
    )
    .unwrap();
    let nz_mir = fs::read_to_string(&nz_out.mir_lean_path).unwrap();
    assert!(nz_mir.contains("access := Trusted.FieldAccess.priv"));
}

#[test]
fn rejects_unsupported_items_and_module_qualified_calls() {
    for (label, src) in [
        ("enum-item", "pub enum E { A }\npub fn id(x: usize) -> usize { x }\n"),
        (
            "tuple-struct",
            "pub struct NonZeroUsize(usize);\npub fn id(x: usize) -> usize { x }\n",
        ),
        (
            "unsafe-trait",
            "pub unsafe trait Bad {}\npub fn id(x: usize) -> usize { x }\n",
        ),
        (
            "impl-method",
            "pub struct NonZeroUsize { val: usize }\n\
             impl NonZeroUsize { pub fn f(self) -> usize { self.val } }\n",
        ),
        (
            "private-unsafe-fn",
            "unsafe fn bad(x: usize) -> usize { x }\n",
        ),
    ] {
        let crate_dir = TempCrateDir::new(label, src);
        let err = capture_crate_with_options(
            &crate_dir.path,
            false,
            &VerifyOptions::default(),
        )
        .unwrap_err();
        assert!(
            matches!(err, CaptureError::UnsupportedMir(_)),
            "expected UnsupportedMir for {label}, got: {err}"
        );
    }
}
