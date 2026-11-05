// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end integration tests for `cargo-anneal verify`: the `rustc_driver`
//! capture built from `trusted/rustc-capture`, the first-order `Trusted.Crate`
//! emission, the verified `Anneal.proveCrate` decision procedure, and the host
//! validation rules around them.

use std::env;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::PathBuf;
use std::process::Command;

use cargo_anneal::{
    ReleaseChannel, VerifyConfig, capture, setup, verify_crate,
    verify_crate_with_report,
};

fn toolchain_dir() -> PathBuf {
    if let Some(tc) = env::var_os("ANNEAL_TOOLCHAIN") {
        return PathBuf::from(tc);
    }
    setup::resolve_installed()
        .expect("set ANNEAL_TOOLCHAIN or install an Anneal toolchain")
}

fn anneal_root() -> PathBuf {
    fs::canonicalize(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."))
        .expect("canonicalize anneal workspace root")
}

fn cfg_for(crate_dir: &PathBuf) -> VerifyConfig {
    VerifyConfig {
        crate_dir: crate_dir.clone(),
        toolchain_dir: toolchain_dir(),
        anneal_root: anneal_root(),
        allow_candidate_features: Vec::new(),
        release_channel: ReleaseChannel::Alpha,
    }
}

fn cli() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-anneal"));
    cmd.arg("anneal")
        .arg("verify")
        .arg("--toolchain")
        .arg(toolchain_dir())
        .arg("--anneal-root")
        .arg(anneal_root());
    cmd
}

const POLICY: &str = "[package.metadata.anneal.trust-policy]\n\
                      allow-candidate-features = [\"*\"]\n";

const ID_SPEC: &str = "/// anneal:spec ensures(ret == x)\n\
                       pub fn id(x: usize) -> usize {\n    x\n}\n";
const ID_PLAIN: &str = "pub fn id(x: usize) -> usize {\n    x\n}\n";

struct TempCrateDir {
    _dir: tempfile::TempDir,
    path: PathBuf,
}

impl TempCrateDir {
    fn with(label: &str, source: &str, policy: bool) -> Self {
        let dir = tempfile::Builder::new()
            .prefix(&format!("anneal-verify-id-{label}-"))
            .tempdir_in("/tmp")
            .expect("create temp crate dir");
        let path = dir.path().to_path_buf();
        fs::create_dir_all(path.join("src")).unwrap();
        let toml = format!(
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\n\
             edition = \"2024\"\n\n{}",
            if policy { POLICY } else { "" }
        );
        fs::write(path.join("Cargo.toml"), toml).unwrap();
        fs::write(path.join("src/lib.rs"), source).unwrap();
        Self { _dir: dir, path }
    }

    fn new(label: &str, source: &str) -> Self {
        Self::with(label, source, true)
    }
}

fn assert_cli_success(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "expected `cargo-anneal anneal verify` to succeed:\nstdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

#[test]
fn verifies_annotated_pub_fn_id_via_cli() {
    let crate_dir = TempCrateDir::new("annotated-id", ID_SPEC);
    let output = cli().arg(&crate_dir.path).output().unwrap();
    assert_cli_success(&output);
    let mir_lean = capture(&cfg_for(&crate_dir.path)).unwrap();
    assert!(
        mir_lean.contains("Trusted.PostSpec.ensuresEqArg 1"),
        "expected first-order PostSpec in Mir.lean, got:\n{mir_lean}"
    );
}

#[test]
fn verifies_unannotated_pub_fn_id_well_formedness() {
    let crate_dir = TempCrateDir::new("unannotated-id", ID_PLAIN);
    verify_crate(&cfg_for(&crate_dir.path)).unwrap();
}

#[test]
fn rejects_incorrect_id_implementation() {
    let crate_dir = TempCrateDir::new(
        "wrong-id",
        "/// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    0\n}\n",
    );
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.contains("lean failed"),
        "expected Lean kernel rejection for wrong id, got: {err}"
    );
}

/// Because `cargo-anneal` never reads `.anneal/` as input and always compiles
/// its own in-memory capture and static `Proof.lean`, spoofed `.anneal/Mir.lean`
/// or `.anneal/Proof.lean` files cannot cause a buggy crate to pass.
#[test]
fn ignores_tampered_or_spoofed_files_in_dot_anneal() {
    let crate_dir = TempCrateDir::new(
        "spoofed-dot-anneal",
        "/// anneal:spec ensures(ret == x)\n\
         pub fn id(x: usize) -> usize {\n    0\n}\n",
    );
    fs::create_dir_all(crate_dir.path.join(".anneal")).unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Mir.lean"),
        b"import Trusted\nnamespace Mir\ntheorem crate : True := trivial\nend Mir\n",
    )
    .unwrap();
    fs::write(
        crate_dir.path.join(".anneal/Proof.lean"),
        b"import Trusted\nnamespace Proof\ntheorem verify_crate : True := trivial\nend Proof\n",
    )
    .unwrap();
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.contains("lean failed"),
        "expected Lean kernel rejection despite spoofed .anneal/, got: {err}"
    );
}

#[test]
fn rejects_crates_that_read_other_inputs() {
    for (label, source) in [
        (
            "include-str",
            "pub fn id(x: usize) -> usize {\n    \
             let _ = include_str!(\"../Cargo.toml\");\n    x\n}\n",
        ),
        (
            "env-macro",
            "pub fn id(x: usize) -> usize {\n    \
             let _ = env!(\"PATH\");\n    x\n}\n",
        ),
    ] {
        let crate_dir = TempCrateDir::new(label, source);
        let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
        assert!(
            err.contains("anneal-rustc-capture failed")
                || err.contains("extra input file"),
            "{label}: got {err}"
        );
    }
}

#[test]
fn rejects_unsupported_mir_construct_fail_closed() {
    let crate_dir = TempCrateDir::new(
        "unsupported-add",
        "pub fn add(x: u32, y: u32) -> u32 {\n    x.wrapping_add(y)\n}\n",
    );
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.contains("anneal-rustc-capture failed"),
        "got: {err}"
    );
}

#[test]
fn rejects_candidate_features_by_default_without_opt_in() {
    let crate_dir = TempCrateDir::with("default-vetted-only", ID_SPEC, false);
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(
        err.contains("verification requires candidate TCB features"),
        "got: {err}"
    );
}

#[test]
fn rejects_candidate_features_on_stable_release_channel() {
    let crate_dir = TempCrateDir::new("stable", ID_SPEC);
    let mut cfg = cfg_for(&crate_dir.path);
    cfg.release_channel = ReleaseChannel::Stable;
    let err = verify_crate(&cfg).unwrap_err();
    assert!(
        err.contains("stable release channel"),
        "got: {err}"
    );
}

#[test]
fn verifies_via_cli_flag_and_emits_candidate_tcb_audit_section() {
    let crate_dir = TempCrateDir::with("cli-allow", ID_SPEC, false);
    let output = cli()
        .arg("--allow-candidate-features")
        .arg("*")
        .arg(&crate_dir.path)
        .output()
        .unwrap();
    let stdout = assert_cli_success(&output);
    assert!(
        stdout.contains("Candidate-Trusted TCB (Unvetted / Alpha):"),
        "{stdout}"
    );
    assert!(stdout.contains("[candidate-tcb-audit]"), "{stdout}");
}

#[test]
fn rejects_public_generic_transmute() {
    for (label, source) in [
        (
            "assoc-const",
            "pub trait SizeEq<Src, Dst> {\n    const ASSERT: ();\n}\n\
             impl<Src, Dst> SizeEq<Src, Dst> for () {\n    \
             const ASSERT: () = assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());\n}\n\
             pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             let () = <() as SizeEq<Src, Dst>>::ASSERT;\n    \
             unsafe { core::mem::transmute_copy(&x) }\n}\n",
        ),
        (
            "inline-const",
            "pub fn inline_const_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             let () = const { assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>()) };\n    \
             unsafe { core::mem::transmute_copy(&x) }\n}\n",
        ),
        (
            "no-assertion",
            "pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
             unsafe { core::mem::transmute_copy(&x) }\n}\n",
        ),
    ] {
        let crate_dir = TempCrateDir::new(label, source);
        let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
        assert!(
            err.contains("anneal-rustc-capture failed")
                || err.contains("lean failed"),
            "{label}: got {err}"
        );
    }
}

#[test]
fn verifies_concrete_pme_transmute() {
    let crate_dir = TempCrateDir::new(
        "concrete-pme",
        "trait SizeEq<Src, Dst> {\n    const ASSERT: ();\n}\n\
         impl<Src, Dst> SizeEq<Src, Dst> for () {\n    \
         const ASSERT: () = assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());\n}\n\
         fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {\n    \
         let () = <() as SizeEq<Src, Dst>>::ASSERT;\n    \
         unsafe { core::mem::transmute_copy(&x) }\n}\n\
         pub fn f(x: usize) -> usize {\n    transmute_checked::<usize, usize>(x)\n}\n",
    );
    verify_crate(&cfg_for(&crate_dir.path)).unwrap();

    let inline_dir = TempCrateDir::new(
        "inline-const-pme",
        "pub fn inline_const_transmute(x: usize) -> usize {\n    \
         let () = const { assert!(core::mem::size_of::<usize>() == core::mem::size_of::<usize>()) };\n    \
         unsafe { core::mem::transmute_copy(&x) }\n}\n",
    );
    verify_crate(&cfg_for(&inline_dir.path)).unwrap();
}

const NONZERO: &str = "/// anneal:invariant val != 0\n\
     #[repr(transparent)]\n\
     pub struct NonZeroUsize {\n    VAL_DECL,\n}\n\n\
     pub fn make_nonzero(x: usize) -> NonZeroUsize {\n    MAKE_BODY\n}\n\n\
     /// # Safety\n///\n/// `x` must not be zero.\n///\n\
     /// anneal:requires x != 0\n\
     pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {\n    \
     NonZeroUsize { val: x }\n}\n\n\
     pub fn get_unchecked(x: NonZeroUsize) -> usize {\n    \
     if x.val == 0 {\n        unsafe { core::hint::unreachable_unchecked() }\n    \
     } else {\n        x.val\n    }\n}\n";
const MAKE_OK: &str =
    "if x == 0 { NonZeroUsize { val: 1 } } else { NonZeroUsize { val: x } }";

fn nonzero(val_decl: &str, make_body: &str) -> String {
    NONZERO
        .replace("VAL_DECL", val_decl)
        .replace("MAKE_BODY", make_body)
}

#[test]
fn verifies_nonzero_library_crate_with_safe_and_unsafe_apis() {
    let crate_dir =
        TempCrateDir::new("nonzero-lib", &nonzero("val: usize", MAKE_OK));
    let report = verify_crate_with_report(&cfg_for(&crate_dir.path)).unwrap();
    assert!(report.output_text.contains("verified crate `sample`"));
    let mir_lean = capture(&cfg_for(&crate_dir.path)).unwrap();
    assert!(mir_lean.contains("Trusted.FieldAccess.priv"));
}

#[test]
fn rejects_nonzero_library_when_safe_fn_violates_invariant() {
    let crate_dir = TempCrateDir::new(
        "nonzero-buggy-zero",
        &nonzero("val: usize", "let _ = x; NonZeroUsize { val: 0 }"),
    );
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(err.contains("lean failed"), "got: {err}");
}

#[test]
fn rejects_nonzero_library_when_field_is_pub_safe() {
    let crate_dir = TempCrateDir::new(
        "nonzero-pub-field",
        &nonzero("pub val: usize", MAKE_OK),
    );
    let err = verify_crate(&cfg_for(&crate_dir.path)).unwrap_err();
    assert!(err.contains("lean failed"), "got: {err}");
}

#[test]
fn rejects_symlinked_manifest_and_lib_rs_and_extra_targets() {
    let rejected = |c: &TempCrateDir| {
        let err = verify_crate(&cfg_for(&c.path)).unwrap_err();
        assert!(err.contains("target-crate:"), "got: {err}");
    };
    let c = TempCrateDir::new("symlink-lib", ID_PLAIN);
    fs::rename(c.path.join("src/lib.rs"), c.path.join("lib.rs.real")).unwrap();
    symlink(c.path.join("lib.rs.real"), c.path.join("src/lib.rs")).unwrap();
    rejected(&c);

    let c = TempCrateDir::new("symlink-toml", ID_PLAIN);
    fs::rename(c.path.join("Cargo.toml"), c.path.join("real.toml")).unwrap();
    symlink(c.path.join("real.toml"), c.path.join("Cargo.toml")).unwrap();
    rejected(&c);

    for extra in ["build.rs", "src/main.rs", "src/proof.lean"] {
        let c = TempCrateDir::new("extra", ID_PLAIN);
        fs::write(c.path.join(extra), b"fn main() {}\n").unwrap();
        rejected(&c);
    }

    let c = TempCrateDir::new("bin-target", ID_PLAIN);
    let toml = fs::read_to_string(c.path.join("Cargo.toml")).unwrap();
    fs::write(
        c.path.join("Cargo.toml"),
        format!("{toml}\n[[bin]]\nname = \"helper\"\npath = \"src/lib.rs\"\n"),
    )
    .unwrap();
    rejected(&c);
}

#[test]
fn captures_alloc_passthrough_with_doc_spec() {
    let crate_dir = TempCrateDir::new(
        "alloc-passthrough",
        "/// anneal:spec ensures(ret == x)\n\
         pub fn alloc_passthrough(x: usize) -> usize {\n    \
         let r = &x;\n    *r\n}\n",
    );
    verify_crate(&cfg_for(&crate_dir.path)).unwrap();
    let mir_lean = capture(&cfg_for(&crate_dir.path)).unwrap();
    assert!(mir_lean.contains("Trusted.PostSpec.ensuresEqArg 1"));
}

#[test]
fn rejects_unsupported_items() {
    for (label, src) in [
        ("enum-item", "pub enum E { A }\npub fn id(x: usize) -> usize { x }\n"),
        (
            "unsafe-trait",
            "pub unsafe trait Bad {}\npub fn id(x: usize) -> usize { x }\n",
        ),
        (
            "uncalled-private-fn",
            "fn bad(x: usize) -> usize { x }\npub fn id(x: usize) -> usize { x }\n",
        ),
    ] {
        let crate_dir = TempCrateDir::with(label, src, true);
        let err = capture(&cfg_for(&crate_dir.path)).unwrap_err();
        assert!(
            err.contains("anneal-rustc-capture failed"),
            "expected capture failure for {label}, got: {err}"
        );
    }
}

#[test]
fn verifies_under_hostile_environment_and_cargo_configs() {
    let crate_dir = TempCrateDir::new("hostile-env", ID_PLAIN);
    let evil = tempfile::Builder::new()
        .prefix("anneal-evil-")
        .tempdir_in("/tmp")
        .unwrap();
    let e = evil.path();
    let config =
        "[build]\nrustc-wrapper = \"/bin/false\"\nrustflags = [\"--cfg\", \"evil\"]\n";
    fs::create_dir_all(e.join(".cargo")).unwrap();
    fs::write(e.join(".cargo/config.toml"), config).unwrap();
    fs::write(e.join("config.toml"), config).unwrap();
    fs::create_dir_all(e.join("work")).unwrap();
    fs::create_dir_all(e.join("lib")).unwrap();
    for lib in ["libleanshared.so", "librustc_driver-5d5a3c5207375ffc.so"] {
        fs::write(e.join("lib").join(lib), b"not an ELF file").unwrap();
    }

    let output = cli()
        .arg(&crate_dir.path)
        .current_dir(e.join("work"))
        .env("CARGO_HOME", e)
        .env("HOME", e)
        .env("XDG_CACHE_HOME", e)
        .env("RUSTC", "/bin/false")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTFLAGS", "--cfg evil")
        .env("RUSTC_LOG", "debug")
        .env("LD_LIBRARY_PATH", e.join("lib"))
        .env("LEAN_PATH", e)
        .output()
        .expect("invoke cargo-anneal binary");
    assert_cli_success(&output);
}
