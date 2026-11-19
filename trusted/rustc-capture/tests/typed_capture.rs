// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Check explicit typed capture and its separation from raw compiler arguments.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;
use sha2::{Digest, Sha256};

struct Capture {
    directory: tempfile::TempDir,
    source: PathBuf,
    output: PathBuf,
}

impl Capture {
    fn new(source: &[u8]) -> Self {
        let directory = tempfile::tempdir().expect("create capture fixture");
        let source_path = directory.path().join("input.rs");
        std::fs::write(&source_path, source).expect("write capture fixture");
        let output = directory.path().join("output");
        Self {
            directory,
            source: source_path,
            output,
        }
    }

    fn command(&self) -> Command {
        self.command_with("session", true)
    }

    fn command_with(&self, crate_name: &str, declare_source: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"));
        command
            .current_dir(self.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&self.source)
            .arg(format!("--crate-name={crate_name}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&self.output)
            .arg("--sysroot")
            .arg(sysroot());
        if declare_source {
            command.arg("--source-file").arg(&self.source);
        }
        command
    }

    fn selected_command(&self) -> Command {
        let mut command = self.command();
        command.arg("--select=selected");
        command
    }

    fn manifest(&self) -> Value {
        serde_json::from_slice(
            &std::fs::read(self.output.join("capture.json")).expect("read capture manifest"),
        )
        .expect("parse capture manifest")
    }

    fn assert_no_capture_artifacts(&self) {
        for name in ["capture.json", "Captured.lean"] {
            assert!(
                std::fs::symlink_metadata(self.output.join(name)).is_err(),
                "capture artifact {name} exists after failure"
            );
        }
    }
}

fn sysroot() -> std::ffi::OsString {
    std::env::var_os("ANNEAL_TEST_RUST_SYSROOT")
        .expect("set ANNEAL_TEST_RUST_SYSROOT to the pinned Rust distribution")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn status(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).expect("typed capture returns one JSON status")
}

#[test]
fn no_arguments_show_help_without_running_the_compiler() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .output()
        .expect("run capture without arguments");
    assert!(output.status.success(), "{output:?}");
    assert!(stdout(&output).contains("Usage:"), "{output:?}");
    assert!(stdout(&output).contains("capture"), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn explicit_capture_requires_typed_arguments_and_has_its_own_help() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .arg("capture")
        .output()
        .expect("run capture without typed arguments");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .args(["capture", "--help"])
        .output()
        .expect("run typed capture help");
    assert!(output.status.success(), "{output:?}");
    assert!(stdout(&output).contains("--crate-root"), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn separator_preserves_a_raw_input_named_capture() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let source = fixture.directory.path().join("capture");
    std::fs::rename(&fixture.source, &source).expect("name raw source capture");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(fixture.directory.path())
        .args([
            "--",
            "capture",
            "--crate-name=session",
            "--crate-type=lib",
            "--emit=metadata",
            "-o",
            "session.rmeta",
        ])
        .arg("--sysroot")
        .arg(sysroot())
        .output()
        .expect("run raw source named capture");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        stderr(&output).contains("compiler analysis callback reached; verification not performed"),
        "{output:?}"
    );
    assert!(fixture.directory.path().join("session.rmeta").is_file());
}

#[test]
fn typed_options_do_not_select_typed_mode_without_the_subcommand() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .args(["--crate-root", "input.rs"])
        .output()
        .expect("pass typed option to raw compiler mode");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        stderr(&output).contains("Unrecognized option"),
        "{output:?}"
    );
    assert!(stderr(&output).contains("crate-root"), "{output:?}");
}

#[test]
fn selected_capture_keeps_unselected_unsupported_items_in_the_census() {
    let fixture = Capture::new(
        b"pub fn selected(value: u64) -> u64 { value }\n\
          pub fn unsupported(value: f64) -> f64 { value }\n",
    );
    let output = fixture
        .selected_command()
        .output()
        .expect("capture selected supported function");
    assert!(output.status.success(), "{output:?}");
    assert_eq!(status(&output)["status"], "captured", "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 2);
    assert_eq!(manifest["scope"]["kind"], "selected_unit");
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1);
    let census = manifest["census"].as_array().expect("complete census");
    for (path, selected) in [("selected", true), ("unsupported", false)] {
        let item = census
            .iter()
            .find(|item| item["path"] == path)
            .expect("both function bodies are inventoried");
        assert_eq!(item["has_body"], true);
        assert_eq!(item["required"], true);
        assert_eq!(item["selected"], selected);
    }
    assert!(fixture.output.join("Captured.lean").is_file());
}

#[test]
fn whole_crate_capture_refuses_an_unsupported_function() {
    let fixture = Capture::new(
        b"pub fn selected(value: u64) -> u64 { value }\n\
          pub fn unsupported(value: f64) -> f64 { value }\n",
    );
    let output = fixture
        .command()
        .arg("--scope=crate")
        .output()
        .expect("capture crate with an unsupported function");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{output:?}");
    assert!(
        failure["unsupported"]
            .as_array()
            .expect("unsupported obligations")
            .iter()
            .any(|item| item["path"] == "unsupported"),
        "{failure}"
    );
    fixture.assert_no_capture_artifacts();
}

#[test]
fn source_hashes_bind_the_exact_crlf_input_bytes() {
    let source = b"pub fn selected(value: u64) -> u64 {\r\n    value\r\n}\r\n";
    let fixture = Capture::new(source);
    let output = fixture
        .selected_command()
        .output()
        .expect("capture CRLF source input");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let files = manifest["source_files"].as_array().expect("source records");
    assert_eq!(files.len(), 1, "{manifest}");
    assert_eq!(files[0]["sha256"], format!("{:x}", Sha256::digest(source)));
    assert_eq!(files[0]["read_kind"], "text");
}

#[test]
fn typed_argument_and_compiler_failures_leave_no_capture_artifacts() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let output = fixture
        .selected_command()
        .arg("--unknown-anneal-test-option")
        .output()
        .expect("run invalid typed arguments");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
    fixture.assert_no_capture_artifacts();

    for source in [
        b"pub fn selected( {\n".as_slice(),
        b"pub fn selected() -> u64 { \"wrong type\" }\n".as_slice(),
    ] {
        let fixture = Capture::new(source);
        let output = fixture
            .selected_command()
            .output()
            .expect("run typed capture with compiler errors");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn metadata_failure_after_typed_analysis_prohibits_capture_artifacts() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    // The name is valid Rust but its metadata filename exceeds the supported
    // hosts' filesystem component limit. This fails after typed analysis without
    // pre-creating an output directory that the publisher must now refuse.
    let output = fixture
        .command_with(&"m".repeat(256), true)
        .arg("--select=selected")
        .output()
        .expect("run typed capture with metadata output failure");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[cfg(unix)]
#[test]
fn typed_non_utf8_program_name_is_rejected_before_the_ice_hook() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::process::CommandExt;

    let fixture = Capture::new(b"pub fn selected() {}\n");
    let output = fixture
        .selected_command()
        .arg0(std::ffi::OsString::from_vec(vec![0xff]))
        .env_remove("RUST_BACKTRACE")
        .output()
        .expect("run typed capture with non-UTF-8 program name");
    assert!(!output.status.success(), "{output:?}");
    assert!(
        stderr(&output).contains("compiler program name is not UTF-8"),
        "{output:?}"
    );
    assert!(!stderr(&output).contains("panicked"), "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn source_allowlist_is_required_and_enforced_for_modules() {
    let fixture = Capture::new(b"mod side;\npub fn selected(value: u64) -> u64 { value }\n");
    let side = fixture.directory.path().join("side.rs");
    std::fs::write(&side, "pub fn unselected() {}\n").unwrap();
    let output = fixture
        .command_with("session", false)
        .arg("--select=selected")
        .output()
        .expect("omit the source allowlist");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        status(&output)["diagnostics"]
            .to_string()
            .contains("--source-file")
    );
    fixture.assert_no_capture_artifacts();

    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    // An undeclared ordinary module is absent to module resolution. Explicit
    // include reads are checked separately below so refusal remains required
    // even when rustc can recover from the loader's I/O error.
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    assert!(
        stderr(&output).contains("file not found for module"),
        "{output:?}"
    );
    fixture.assert_no_capture_artifacts();

    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(side)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        fixture.manifest()["source_files"].as_array().unwrap().len(),
        2
    );
}

#[test]
fn monomorphization_errors_outside_the_selected_body_prohibit_capture() {
    // The selected body's syntax is unchanged between the two cases. The
    // separate exported function makes ordinary code generation evaluate the
    // generic constant, so only the compiler-completion guard distinguishes it.
    for (argument, success) in [(0, false), (1, true)] {
        let source = format!(
            "pub fn selected(value: u64) -> u64 {{ value }}\n\
             fn generic<const N: usize>() {{ const {{ assert!(N > 0); }} }}\n\
             pub fn other() {{ generic::<{argument}>(); }}\n"
        );
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.success(), success, "{output:?}");
        if success {
            assert_eq!(status(&output)["status"], "captured", "{output:?}");
            assert_eq!(std::fs::read_dir(&fixture.output).unwrap().count(), 2);
        } else {
            assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
            assert!(stderr(&output).contains("E0080"), "{output:?}");
            fixture.assert_no_capture_artifacts();
            assert!(!fixture.output.exists());
        }
    }
}

#[test]
fn existing_destinations_are_refused_without_changing_their_contents() {
    for populated in [false, true] {
        let fixture = Capture::new(b"pub fn selected() {}\n");
        std::fs::create_dir(&fixture.output).unwrap();
        if populated {
            std::fs::write(fixture.output.join("caller-data"), b"preserve").unwrap();
        }
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            stdout(&output).contains("new output directory"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
        assert_eq!(
            std::fs::read_dir(&fixture.output).unwrap().count(),
            usize::from(populated)
        );
        if populated {
            assert_eq!(
                std::fs::read(fixture.output.join("caller-data")).unwrap(),
                b"preserve"
            );
        }
    }
}

#[cfg(unix)]
#[test]
fn existing_output_symlink_is_refused_without_touching_its_target() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let target = fixture.directory.path().join("caller-directory");
    std::fs::create_dir(&target).unwrap();
    std::fs::write(target.join("caller-data"), b"preserve").unwrap();
    std::os::unix::fs::symlink(&target, &fixture.output).unwrap();
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(
        stdout(&output).contains("new output directory"),
        "{output:?}"
    );
    assert_eq!(
        std::fs::read(target.join("caller-data")).unwrap(),
        b"preserve"
    );
    assert_eq!(std::fs::read_dir(target).unwrap().count(), 1);
    assert!(
        std::fs::symlink_metadata(&fixture.output)
            .unwrap()
            .file_type()
            .is_symlink()
    );
}

#[test]
fn unicode_function_identity_is_data_in_the_captured_subject() {
    // The manifest keeps UTF-8 text while Lean receives numeric character data.
    // Check both representations at a non-ASCII boundary used by real names.
    let fixture = Capture::new("pub unsafe fn café() -> u64 { 0 }\n".as_bytes());
    let output = fixture
        .command()
        .arg("--select=café")
        .output()
        .expect("capture a Unicode function identity");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(
        manifest["program"]["bodies"][0]["identity"],
        "rust-path-v1::café"
    );
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(!lean.contains("café"));
    assert!(lean.contains("(_root_.Char.ofNat 233)"));
}

#[test]
fn function_identities_survive_unrelated_impl_insertion_and_reordering() {
    // Impl ordinals change when another impl is inserted. The same method name
    // on different self types must keep its own semantic owner in the key.
    let before = Capture::new(
        b"pub struct A; pub struct B;\n\
          impl A { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl B { pub unsafe fn entry() -> u64 { 0 } }\n",
    );
    let after = Capture::new(
        b"pub struct A; pub struct B; pub struct C;\n\
          impl C { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl B { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl A { pub unsafe fn entry() -> u64 { 0 } }\n",
    );
    let identities = |fixture: &Capture| {
        let output = fixture
            .command()
            .args(["--select=A::entry", "--select=B::entry"])
            .output()
            .expect("capture selected associated functions");
        assert!(output.status.success(), "{output:?}");
        let manifest = fixture.manifest();
        manifest["selected"]
            .as_array()
            .unwrap()
            .iter()
            .map(|selected| {
                let index = selected["body_index"].as_u64().unwrap() as usize;
                (
                    selected["path"].as_str().unwrap().to_owned(),
                    manifest["program"]["bodies"][index]["identity"]
                        .as_str()
                        .unwrap()
                        .to_owned(),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>()
    };
    let expected = std::collections::BTreeMap::from([
        ("A::entry".to_owned(), "rust-path-v1::A::entry".to_owned()),
        ("B::entry".to_owned(), "rust-path-v1::B::entry".to_owned()),
    ]);
    assert_eq!(identities(&before), expected);
    assert_eq!(identities(&after), expected);
}

#[test]
fn trait_impl_identity_uses_the_semantic_owner() {
    // Trait members can share a name across impls. Their contract keys must
    // retain the self/trait owner rather than collapse to that member name.
    let fixture = Capture::new(
        b"pub struct A; pub struct B;\n\
          pub trait T { unsafe fn entry() -> u64; }\n\
          impl T for A { unsafe fn entry() -> u64 { 0 } }\n\
          impl T for B { unsafe fn entry() -> u64 { 0 } }\n",
    );
    let output = fixture
        .command()
        .args(["--select=<A as T>::entry", "--select=<B as T>::entry"])
        .output()
        .expect("capture selected trait-implementation functions");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let identities: std::collections::BTreeSet<_> = manifest["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|body| body["identity"].as_str().unwrap())
        .collect();
    assert_eq!(
        identities,
        std::collections::BTreeSet::from([
            "rust-path-v1::<A as T>::entry",
            "rust-path-v1::<B as T>::entry",
        ])
    );
}

#[test]
fn cfg_values_are_literals_not_response_files() {
    // Keep the response file outside the declared source inventory. Expansion
    // would inject `injected`, bypassing this source's compilation guard while
    // the capture manifest still reported the original @path as its cfg.
    const SOURCE: &[u8] = b"#[cfg(not(injected))]\ncompile_error!(\"missing declared cfg\");\npub fn selected() -> u64 { 0 }\n";
    let external = tempfile::tempdir().unwrap();
    let response = external.path().join("compiler-flags.rsp");
    std::fs::write(&response, b"dummy\n--cfg\ninjected\n").unwrap();
    for path in [response, external.path().join("missing.rsp")] {
        let fixture = Capture::new(SOURCE);
        let cfg = format!("@{}", path.to_str().unwrap());
        let output = fixture
            .selected_command()
            .arg(format!("--cfg={cfg}"))
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "cfg response path was accepted:\n{}\n{}",
            stdout(&output),
            stderr(&output)
        );
        assert_eq!(status(&output)["status"], "compiler_failed");
        // Both an existing response and a nonexistent path must reach rustc's
        // cfg parser. A response-file read would instead load extra flags or
        // produce an argument-file I/O error before cfg parsing.
        assert!(stderr(&output).contains("invalid `--cfg` argument"));
        assert!(!stderr(&output).contains("failed to load argument file"));
        fixture.assert_no_capture_artifacts();
    }

    // Preserve ordinary flag and quoted-string cfgs, including @ inside a
    // legitimate string value. Rustc remains the authority for cfg grammar.
    let fixture = Capture::new(SOURCE);
    let output = fixture
        .selected_command()
        .arg("--cfg=injected")
        .arg(r#"--cfg=feature="@literal""#)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(
        fixture.manifest()["configuration"]["cfg"],
        serde_json::json!([r#"feature="@literal""#, "injected"])
    );
}

// Compare complete artifacts, not only exit status: an ambient file must not
// silently change the compiler census, captured body, or recorded read set.
fn capture_pair(fixture: &Capture) -> [Vec<u8>; 2] {
    ["capture.json", "Captured.lean"].map(|name| {
        std::fs::read(fixture.output.join(name)).expect("read successful capture artifact")
    })
}

#[test]
fn declared_namespace_hides_ambient_module_alternatives() {
    let mut fixture = Capture::new(b"mod side;\npub fn selected() -> u64 { 0 }\n");
    let side = fixture.directory.path().join("side.rs");
    let secondary = fixture.directory.path().join("side/mod.rs");
    std::fs::write(&side, "pub fn other() {}\n").unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "initial declared module: {output:?}"
    );
    let expected = capture_pair(&fixture);

    std::fs::create_dir(secondary.parent().unwrap()).unwrap();
    std::fs::write(&secondary, "pub fn ambient() {}\n").unwrap();
    fixture.output = fixture.directory.path().join("with-ambient-file");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "undeclared alternative changed compilation: {output:?}"
    );
    assert_eq!(capture_pair(&fixture), expected);

    // Declaring both names deliberately changes the configured compilation.
    // Hiding all module probes would miss rustc's required ambiguity error.
    fixture.output = fixture.directory.path().join("both-declared");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .arg("--source-file")
        .arg(&secondary)
        .output()
        .unwrap();
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    assert!(stderr(&output).contains("found at both"), "{output:?}");
    fixture.assert_no_capture_artifacts();

    fixture.output = fixture.directory.path().join("secondary-declared");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&secondary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared secondary module: {output:?}"
    );
    assert_eq!(
        fixture.manifest()["source_files"].as_array().unwrap().len(),
        2
    );

    #[cfg(unix)]
    {
        // Target membership alone would expose this unlisted alias and restore
        // the same hidden ambiguity, despite the target's declared bytes.
        std::fs::remove_file(&secondary).unwrap();
        std::os::unix::fs::symlink(&side, &secondary).unwrap();
        fixture.output = fixture.directory.path().join("with-ambient-alias");
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&side)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "undeclared alias changed compilation: {output:?}"
        );
        assert_eq!(capture_pair(&fixture), expected);
    }
}

#[test]
fn declared_namespace_preserves_parent_paths_and_hides_missing_prefixes() {
    let mut fixture = Capture::new(b"pub fn selected() -> u64 { 0 }\n");
    let sub = fixture.directory.path().join("sub");
    std::fs::create_dir(&sub).unwrap();
    fixture.source = sub.join("input.rs");
    std::fs::write(
        &fixture.source,
        "#[path=\"../shared.rs\"] mod shared;\npub fn selected() -> u64 { 0 }\n",
    )
    .unwrap();
    let shared = fixture.directory.path().join("shared.rs");
    std::fs::write(&shared, "pub fn other() {}\n").unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&shared)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared ancestor ../ path: {output:?}"
    );

    // A canceled directory still has to exist in the declared namespace. The
    // answer must stay the same when the ambient directory appears later.
    std::fs::write(
        &fixture.source,
        "#[path=\"missing/../../shared.rs\"] mod shared;\npub fn selected() -> u64 { 0 }\n",
    )
    .unwrap();
    for present in [false, true] {
        if present {
            std::fs::create_dir(sub.join("missing")).unwrap();
        }
        fixture.output = fixture
            .directory
            .path()
            .join(format!("missing-prefix-{present}"));
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&shared)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "ambient prefix admitted: {output:?}"
        );
        assert!(
            stdout(&output).contains("undeclared compiler read"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn declared_namespace_guards_text_and_binary_include_reads() {
    let mut fixture = Capture::new(
        b"const TEXT: &str = include_str!(\"text.txt\");\n\
        const BINARY: &[u8] = include_bytes!(\"binary.dat\");\n\
        pub fn selected() -> u64 { 0 }\n",
    );
    let text = fixture.directory.path().join("text.txt");
    let binary = fixture.directory.path().join("binary.dat");
    std::fs::write(&text, b"line one\r\nline two\r\n").unwrap();
    std::fs::write(&binary, [0, 255, 13, 10]).unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&text)
        .arg("--source-file")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared text/binary include: {output:?}"
    );
    let sources = fixture.manifest()["source_files"]
        .as_array()
        .unwrap()
        .clone();
    for (path, bytes, kind) in [
        (&text, std::fs::read(&text).unwrap(), "binary"),
        (&binary, std::fs::read(&binary).unwrap(), "binary"),
    ] {
        let entry = sources
            .iter()
            .find(|entry| entry["path"] == path.to_str().unwrap())
            .unwrap();
        assert_eq!(entry["sha256"], format!("{:x}", Sha256::digest(bytes)));
        assert_eq!(entry["read_kind"], kind);
    }
    fixture.output = fixture.directory.path().join("undeclared-include");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&text)
        .output()
        .unwrap();
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    assert!(
        stdout(&output).contains("undeclared compiler read"),
        "{output:?}"
    );
    fixture.assert_no_capture_artifacts();

    #[cfg(unix)]
    {
        let alias = fixture.directory.path().join("text-alias.txt");
        std::os::unix::fs::symlink(&text, &alias).unwrap();
        std::fs::write(&fixture.source,
            "const TEXT: &str = include_str!(\"text-alias.txt\");\npub fn selected() -> u64 { 0 }\n").unwrap();
        fixture.output = fixture.directory.path().join("undeclared-include-alias");
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&text)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "undeclared read alias admitted: {output:?}"
        );
        assert!(
            stdout(&output).contains("undeclared compiler read"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_output_destinations_fail_before_publication_and_remain_retryable() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    for form in ["final", "ancestor", "relative", "symlink"] {
        let mut fixture = Capture::new(b"pub fn selected() -> u64 { 0 }\n");
        let non_utf8 = OsString::from_vec(b"output-\xff".to_vec());
        let native_parent = fixture.directory.path().join(&non_utf8);
        let mut cwd = fixture.directory.path().to_path_buf();
        let destination = if form == "final" {
            fixture.directory.path().join(&non_utf8)
        } else {
            std::fs::create_dir(&native_parent).unwrap();
            native_parent.join("output")
        };
        fixture.output = match form {
            "relative" => {
                // A UTF-8 argv spelling can resolve through a native cwd.
                cwd = native_parent.clone();
                PathBuf::from("output")
            }
            "symlink" => {
                // The publisher canonicalizes parents. Its returned receipt
                // path must be checked, not just the UTF-8 symlink spelling.
                let alias = fixture.directory.path().join("alias");
                std::os::unix::fs::symlink(&native_parent, &alias).unwrap();
                alias.join("output")
            }
            _ => destination.clone(),
        };
        for attempt in 0..2 {
            let output = fixture
                .selected_command()
                .current_dir(&cwd)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(1),
                "{form}/{attempt}: {output:?}"
            );
            assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
            assert!(
                !destination.exists(),
                "failed receipt left a published destination ({form}/{attempt}): {output:?}"
            );
            assert!(
                stdout(&output).contains("output destination must be UTF-8"),
                "{form}/{attempt}: {output:?}"
            );
            assert!(output.stderr.is_empty(), "{form}/{attempt}: {output:?}");
            let parent = destination.parent().unwrap();
            assert!(std::fs::read_dir(parent).unwrap().all(|entry| {
                !entry
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .starts_with(".anneal-capture-")
            }));
        }
        // Refusal reserves no output name and leaves the source usable. A
        // corrected UTF-8 destination can publish the complete pair normally.
        fixture.output = fixture.directory.path().join("valid-output");
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{form}: {output:?}");
        assert_eq!(status(&output)["status"], "captured");
        assert_eq!(std::fs::read_dir(&fixture.output).unwrap().count(), 2);
    }
}

#[test]
fn captured_safety_bits_follow_safe_and_unsafe_declarations() {
    let fixture = Capture::new(
        b"pub fn safe_entry() -> u64 { 0 }\n\
          pub unsafe fn unsafe_entry() -> u64 { 0 }\n",
    );
    let output = fixture
        .command()
        .args(["--select=safe_entry", "--select=unsafe_entry"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 2);
    for (identity, expected) in [
        ("rust-path-v1::safe_entry", false),
        ("rust-path-v1::unsafe_entry", true),
    ] {
        let body = bodies
            .iter()
            .find(|body| body["identity"] == identity)
            .unwrap();
        assert_eq!(body["is_unsafe"], expected, "{body}");
    }
}

#[test]
fn enum_representations_follow_admitted_zst_and_scalar_tag_rules() {
    let empty_source = b"pub enum Empty {}\npub fn selected(x: Empty) -> u64 { match x {} }\n";
    for crate_scope in [false, true] {
        let fixture = Capture::new(empty_source);
        let mut cmd = if crate_scope {
            let mut cmd = fixture.command();
            cmd.arg("--scope=crate");
            cmd
        } else {
            fixture.selected_command()
        };
        let output = cmd.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{failure}");
        assert!(
            failure
                .to_string()
                .contains("uninhabited zero-variant enums are unsupported"),
            "{failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    let repr_single =
        b"#[repr(isize)]\npub enum ReprSingle { Only = 7 }\npub fn selected(x: ReprSingle) -> isize { match x { ReprSingle::Only => 7 } }\n";
    let fixture = Capture::new(repr_single);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["discr_is_size"], true, "{ty}");
    assert_eq!(ty["discr_signed"], true, "{ty}");
    assert_eq!(ty["tag_repr"]["kind"], "scalar", "{ty}");
    assert_eq!(ty["tag_repr"]["bits"], 64, "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!([7]), "{ty}");

    let zst_single =
        b"pub enum Single { Only = 42 }\npub fn selected(x: Single) -> isize { match x { Single::Only => 42 } }\n";
    let fixture = Capture::new(zst_single);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["tag_repr"]["kind"], "zero_sized", "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!([42]), "{ty}");

    let repr_u8 = b"#[repr(u8)]\npub enum ExplicitU8 { Ten = 10, Twenty = 20 }\npub fn selected(x: ExplicitU8) -> u8 { match x { ExplicitU8::Ten => 10, ExplicitU8::Twenty => 20 } }\n";
    let fixture = Capture::new(repr_u8);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["discr_bits"], 8, "{ty}");
    assert_eq!(ty["discr_signed"], false, "{ty}");
    assert_eq!(ty["tag_repr"]["bits"], 8, "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!([10, 20]), "{ty}");

    let empty_crate = Capture::new(b"");
    let output = empty_crate.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure
            .to_string()
            .contains("captured program contains no executable bodies"),
        "{failure}"
    );
    empty_crate.assert_no_capture_artifacts();
}

#[test]
fn negative_isize_enum_discriminants_are_captured_as_64_bit_twos_complement() {
    let source = b"\
        #[repr(isize)]\n\
        pub enum Signed {\n\
            Neg = -1,\n\
            Zero = 0,\n\
            Pos = 1,\n\
        }\n\
        pub fn selected(s: Signed) -> isize {\n\
            match s {\n\
                Signed::Neg => -1,\n\
                Signed::Zero => 0,\n\
                Signed::Pos => 1,\n\
            }\n\
        }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .selected_command()
        .output()
        .expect("capture signed repr(isize) enum");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let discriminants = manifest["program"]["bodies"][0]["local_tys"][1]["discriminants"]
        .as_array()
        .expect("enum discriminants");
    let values: Vec<u64> = discriminants
        .iter()
        .map(|v| v.as_u64().expect("u64 discriminant"))
        .collect();
    assert_eq!(values, vec![u64::MAX, 0, 1]);
    let lean =
        std::fs::read_to_string(fixture.output.join("Captured.lean")).expect("read Captured.lean");
    assert!(
        lean.contains("[18446744073709551615, 0, 1]"),
        "expected 64-bit two's-complement discriminant list in Captured.lean:\n{lean}"
    );
}

#[test]
fn retag_flags_are_recorded_on_scalar_use_and_reference_assignments_are_refused() {
    let scalar_fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let output = scalar_fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = scalar_fixture.manifest();
    let stmt = &manifest["program"]["bodies"][0]["blocks"][0]["statements"][0];
    assert_eq!(stmt["value"]["kind"], "use", "{stmt}");
    assert_eq!(stmt["value"]["with_retag"], true, "{stmt}");
    let lean = std::fs::read_to_string(scalar_fixture.output.join("Captured.lean")).unwrap();
    let mir_dialect = manifest["mir_dialect"].as_str().expect("mir_dialect");
    assert!(
        lean.contains(&format!("Trusted.Rustc.{mir_dialect}.MirAst.Rvalue.use")),
        "{lean}"
    );
    assert!(!lean.contains("Rvalue.unsupported"), "{lean}");

    let ref_fixture = Capture::new(b"pub fn selected(x: &u64) -> &u64 { x }\n");
    let output = ref_fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    ref_fixture.assert_no_capture_artifacts();
}

// The identity `build.rs` selected for this driver. Fake compilers below
// report it, or deliberately report something else.
const LINKED_COMMIT: &str = env!("ANNEAL_LINKED_RUSTC_COMMIT");
const LINKED_DATE: &str = env!("ANNEAL_LINKED_RUSTC_DATE");
const LINKED_DIALECT: &str = env!("ANNEAL_LINKED_MIR_DIALECT");

fn verbose_version(version: &str, commit: &str, date: &str) -> String {
    format!(
        "rustc {version}\nbinary: rustc\ncommit-hash: {commit}\ncommit-date: {date}\n\
         host: x86_64-unknown-linux-gnu\nrelease: 1.0.0-dev\nLLVM version: 22.1.6\n"
    )
}

/// Write a stand-in compiler that answers exactly `--version --verbose` with
/// `report` and `status`, and refuses any compilation request. It uses only
/// shell builtins: capture probes compilers with `PATH=/usr/bin:/bin`, which a
/// build sandbox may leave empty.
///
/// A short-lived child writes the file. A child that another test thread
/// forks while this process holds the file open for writing keeps that
/// descriptor until its own `exec`, and executing the file meanwhile fails
/// with ETXTBSY ("Text file busy").
#[cfg(unix)]
fn fake_rustc(directory: &Path, name: &str, report: &str, status: i32) -> PathBuf {
    use std::io::Write as _;

    assert!(!report.contains('\''), "{report}");
    let path = directory.join(name);
    let script = format!(
        "#!/bin/sh\nif [ \"$#\" -eq 2 ] && [ \"$1\" = --version ] && [ \"$2\" = --verbose ]; then\n\
         printf '%s' '{report}'\nexit {status}\nfi\nexit 97\n"
    );
    let mut child = Command::new("/bin/sh")
        .args([
            "-c",
            "cat > \"$1\" && chmod 755 \"$1\"",
            "install-executable",
        ])
        .arg(&path)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .expect("start executable installer");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    assert!(
        child.wait().unwrap().success(),
        "install {}",
        path.display()
    );
    path
}

#[test]
fn rustc_identity_is_recorded_for_explicit_and_default_compilers() {
    let rustc = PathBuf::from(sysroot()).join("bin/rustc");
    for explicit in [true, false] {
        let fixture = Capture::new(b"pub fn selected(value: u64) -> u64 { value }\n");
        let mut command = fixture.selected_command();
        if explicit {
            command.arg("--rustc").arg(&rustc);
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "{output:?}");
        let manifest = fixture.manifest();
        let compiler = &manifest["compiler"];
        assert_eq!(manifest["mir_dialect"], LINKED_DIALECT, "{manifest}");
        assert_eq!(compiler["mir_dialect"], LINKED_DIALECT, "{manifest}");
        assert_eq!(compiler["commit"], LINKED_COMMIT, "{manifest}");
        assert_eq!(compiler["commit_date"], LINKED_DATE, "{manifest}");
        assert!(
            compiler["version"]
                .as_str()
                .unwrap()
                .contains(&LINKED_COMMIT[..9]),
            "{manifest}"
        );
        // An explicit compiler is recorded at its canonical path. Without
        // one, the probe uses bin/rustc of the canonical session sysroot.
        let expected = if explicit {
            rustc.canonicalize().unwrap()
        } else {
            PathBuf::from(sysroot())
                .canonicalize()
                .unwrap()
                .join("bin/rustc")
        };
        assert_eq!(compiler["rustc"], expected.to_str().unwrap(), "{manifest}");
        let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
        assert!(
            lean.contains(&format!("import Trusted.Rustc.{LINKED_DIALECT}.MirAst\n")),
            "{lean}"
        );
    }
}

#[cfg(unix)]
#[test]
fn fuchsia_style_rustc_reporting_the_linked_build_is_accepted() {
    // Fuchsia's compilers put their revisions in the version line's
    // description; only the commit-hash and commit-date lines identify them.
    let fixture = Capture::new(b"pub fn selected(value: u64) -> u64 { value }\n");
    let tools = tempfile::tempdir().unwrap();
    let report = verbose_version(
        &format!("1.101.0-dev (git_revisions:{LINKED_COMMIT},llvm:0123456789abcdef)"),
        LINKED_COMMIT,
        LINKED_DATE,
    );
    let rustc = fake_rustc(tools.path(), "fuchsia-rustc", &report, 0);
    let output = fixture
        .selected_command()
        .arg("--rustc")
        .arg(&rustc)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["compiler"]["commit"], LINKED_COMMIT, "{manifest}");
    assert_eq!(
        manifest["compiler"]["rustc"],
        rustc.canonicalize().unwrap().to_str().unwrap(),
        "{manifest}"
    );
}

#[cfg(unix)]
#[test]
fn rustc_that_is_not_the_linked_build_is_refused_before_compilation() {
    const SUPPORTED: &[(&str, &str, &str)] = &[
        (
            "V2026_10_22_R7189d39d9",
            "7189d39d9ce936881b8132c6addeaf3e295cd455",
            "2026-10-22",
        ),
        (
            "V2026_05_31_R14210df0e",
            "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
            "2026-05-31",
        ),
        (
            "V2026_05_30_Rf8a08b688",
            "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
            "2026-05-30",
        ),
    ];
    let mut cases: Vec<(String, String)> = SUPPORTED
        .iter()
        .filter(|(dialect, ..)| *dialect != LINKED_DIALECT)
        .map(|(dialect, commit, date)| {
            (
                verbose_version("1.0.0", commit, date),
                format!("is {dialect} (commit-hash {commit}"),
            )
        })
        .collect();
    assert_eq!(
        cases.len(),
        SUPPORTED.len() - 1,
        "linked dialect is supported"
    );
    let unknown = "0123456789abcdef0123456789abcdef01234567";
    cases.extend([
        // A different build of the linked commit is not the linked build.
        (
            verbose_version("1.0.0", LINKED_COMMIT, "1999-12-31"),
            "commit-date 1999-12-31".to_owned(),
        ),
        (
            verbose_version("1.0.0", unknown, LINKED_DATE),
            format!(
                "is unsupported V{}_R012345678",
                LINKED_DATE.replace('-', "_")
            ),
        ),
        // An injected version line cannot add a matching commit-hash.
        (
            verbose_version(
                &format!("1.0.0\ncommit-hash: {LINKED_COMMIT}"),
                unknown,
                LINKED_DATE,
            ),
            "repeats commit-hash".to_owned(),
        ),
        (
            verbose_version("1.0.0", "unknown", "unknown"),
            "full lowercase hexadecimal commit".to_owned(),
        ),
    ]);
    for (index, (report, diagnostic)) in cases.iter().enumerate() {
        let fixture = Capture::new(b"pub fn selected() {}\n");
        let tools = tempfile::tempdir().unwrap();
        let rustc = fake_rustc(tools.path(), &format!("rustc-{index}"), report, 0);
        let output = fixture
            .selected_command()
            .arg("--rustc")
            .arg(&rustc)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "tool_failed", "{failure}");
        assert!(
            failure.to_string().contains(diagnostic.as_str()),
            "{failure}"
        );
        // The early check precedes output reservation and compilation.
        assert!(!fixture.output.exists(), "{output:?}");
    }

    // A failing, missing, or non-UTF-8 compiler path is refused the same way.
    use std::os::unix::ffi::OsStringExt as _;
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let tools = tempfile::tempdir().unwrap();
    let report = verbose_version("1.0.0", LINKED_COMMIT, LINKED_DATE);
    let valid = fake_rustc(tools.path(), "valid-rustc", &report, 0);
    let non_utf8_target = tools
        .path()
        .join(std::ffi::OsString::from_vec(vec![b'r', b'u', 0xff]));
    std::fs::copy(&valid, &non_utf8_target).unwrap();
    let utf8_to_non_utf8 = tools.path().join("utf8-link");
    std::os::unix::fs::symlink(&non_utf8_target, &utf8_to_non_utf8).unwrap();
    let non_utf8_to_utf8 = tools
        .path()
        .join(std::ffi::OsString::from_vec(vec![b'l', b'n', 0xff]));
    std::os::unix::fs::symlink(&valid, &non_utf8_to_utf8).unwrap();
    let failing = fake_rustc(tools.path(), "failing-rustc", &report, 3);
    for (rustc, diagnostic) in [
        (failing, "--version --verbose failed"),
        (tools.path().join("missing-rustc"), "cannot resolve --rustc"),
        (non_utf8_to_utf8, "--rustc path must be UTF-8"),
        (utf8_to_non_utf8, "compiler path must be UTF-8"),
    ] {
        let output = fixture
            .selected_command()
            .arg("--rustc")
            .arg(&rustc)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
        assert!(stdout(&output).contains(diagnostic), "{output:?}");
        assert!(!fixture.output.exists(), "{output:?}");
    }

    // A non-UTF-8 --sysroot (spelling or canonical target) is also refused as
    // `tool_failed` before output reservation or `rustc_driver`'s ICE-hook
    // argv check, even when `--rustc` itself is valid UTF-8.
    let non_utf8_sysroot = tools
        .path()
        .join(std::ffi::OsString::from_vec(vec![b's', b'y', 0xff]));
    std::fs::create_dir(&non_utf8_sysroot).unwrap();
    let utf8_to_non_utf8_sysroot = tools.path().join("utf8-sysroot-link");
    std::os::unix::fs::symlink(&non_utf8_sysroot, &utf8_to_non_utf8_sysroot).unwrap();
    let non_utf8_to_utf8_sysroot = tools
        .path()
        .join(std::ffi::OsString::from_vec(vec![b's', b'l', 0xff]));
    std::os::unix::fs::symlink(sysroot(), &non_utf8_to_utf8_sysroot).unwrap();
    for (bad_sysroot, with_rustc, diagnostic) in [
        (
            &non_utf8_to_utf8_sysroot,
            false,
            "--sysroot path must be UTF-8",
        ),
        (
            &non_utf8_to_utf8_sysroot,
            true,
            "--sysroot path must be UTF-8",
        ),
        (
            &utf8_to_non_utf8_sysroot,
            true,
            "sysroot path must be UTF-8",
        ),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"));
        command
            .current_dir(fixture.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&fixture.output)
            .arg("--sysroot")
            .arg(bad_sysroot)
            .arg("--source-file")
            .arg(&fixture.source)
            .arg("--select=selected");
        if with_rustc {
            command.arg("--rustc").arg(&valid);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
        assert!(stdout(&output).contains(diagnostic), "{output:?}");
        assert!(!fixture.output.exists(), "{output:?}");
    }
}

#[test]
fn captures_all_six_64_bit_little_endian_targets_and_rejects_others() {
    let no_core_src = br#"#![allow(internal_features)]
#![feature(no_core, lang_items)]
#![no_core]
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy: Sized {}
pub fn selected(x: u64) -> u64 { x }
"#;
    for triple in [
        "x86_64-unknown-linux-gnu",
        "aarch64-unknown-linux-gnu",
        "riscv64gc-unknown-linux-gnu",
        "x86_64-unknown-fuchsia",
        "aarch64-unknown-fuchsia",
        "riscv64gc-unknown-fuchsia",
    ] {
        let fixture = Capture::new(no_core_src);
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
            .current_dir(fixture.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg(format!("--target={triple}"))
            .arg("--out-dir")
            .arg(&fixture.output)
            .arg("--sysroot")
            .arg(sysroot())
            .arg("--source-file")
            .arg(&fixture.source)
            .arg("--select=selected")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "target {triple} failed:\nstdout:\n{}\nstderr:\n{}",
            stdout(&output),
            stderr(&output)
        );
        let manifest = fixture.manifest();
        assert_eq!(manifest["configuration"]["target"], triple);
        assert_eq!(manifest["configuration"]["pointer_bits"], 64);
        assert_eq!(manifest["configuration"]["endian"], "little");
    }

    for unsupported in [
        "i686-unknown-linux-gnu",
        "s390x-unknown-linux-gnu",
        "wasm32-unknown-unknown",
        "x86_64-apple-darwin",
        "armv7-unknown-linux-gnueabihf",
    ] {
        let fixture = Capture::new(no_core_src);
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
            .current_dir(fixture.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg(format!("--target={unsupported}"))
            .arg("--out-dir")
            .arg(&fixture.output)
            .arg("--sysroot")
            .arg(sysroot())
            .arg("--source-file")
            .arg(&fixture.source)
            .arg("--select=selected")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{unsupported}: {output:?}");
        assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
        assert!(!fixture.output.exists(), "{unsupported}");
    }
}

#[cfg(unix)]
#[test]
fn authenticates_extern_crates_and_dependency_dirs_and_rejects_tampering() {
    let sysroot_path = PathBuf::from(sysroot());
    let rustc = sysroot_path.join("bin/rustc");
    let workspace = tempfile::tempdir().unwrap();
    let deps_dir = workspace.path().join("deps");
    std::fs::create_dir(&deps_dir).unwrap();

    let leaf_rs = workspace.path().join("leaf_types.rs");
    std::fs::write(&leaf_rs, b"pub enum LeafBit { Zero = 0, One = 1 }\n").unwrap();
    let leaf_rmeta = deps_dir.join("libleaf_types.rmeta");
    let st = Command::new(&rustc)
        .env("LD_LIBRARY_PATH", sysroot_path.join("lib"))
        .args([
            "--edition=2024",
            "--crate-name=leaf_types",
            "--crate-type=lib",
            "--target=x86_64-unknown-linux-gnu",
            "--emit=metadata",
            "-o",
        ])
        .arg(&leaf_rmeta)
        .arg(&leaf_rs)
        .status()
        .unwrap();
    assert!(st.success());

    let dep_rs = workspace.path().join("dep_types.rs");
    std::fs::write(
        &dep_rs,
        b"pub use leaf_types::LeafBit;\npub enum Mode { Little = 0, Big = 1 }\n",
    )
    .unwrap();
    let dep_rmeta = deps_dir.join("libdep_types.rmeta");
    let st = Command::new(&rustc)
        .env("LD_LIBRARY_PATH", sysroot_path.join("lib"))
        .args([
            "--edition=2024",
            "--crate-name=dep_types",
            "--crate-type=lib",
            "--target=x86_64-unknown-linux-gnu",
            "--emit=metadata",
            "-o",
        ])
        .arg(&dep_rmeta)
        .arg(format!("--extern=leaf_types={}", leaf_rmeta.display()))
        .arg(&dep_rs)
        .status()
        .unwrap();
    assert!(st.success());

    let subject_src = br#"
use dep_types::{LeafBit, Mode};
pub enum LocalMode { A = 0, B = 1 }
pub fn selected(m: Mode, b: LeafBit, l: LocalMode) -> u64 {
    match m {
        Mode::Little => match b {
            LeafBit::Zero => match l {
                LocalMode::A => 0xff,
                LocalMode::B => 1,
            },
            LeafBit::One => 2,
        },
        Mode::Big => 3,
    }
}
"#;
    let fixture = Capture::new(subject_src);
    let output = fixture
        .selected_command()
        .arg(format!("--extern=dep_types={}", dep_rmeta.display()))
        .arg(format!("-Ldependency={}", deps_dir.display()))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    let expected_dep_sha = format!("{:x}", Sha256::digest(std::fs::read(&dep_rmeta).unwrap()));
    let expected_leaf_sha = format!("{:x}", Sha256::digest(std::fs::read(&leaf_rmeta).unwrap()));
    let observed = manifest["externs"].as_array().unwrap();
    assert!(
        observed
            .iter()
            .any(|e| e["crate_name"] == "dep_types" && e["sha256"] == expected_dep_sha),
        "{observed:?}"
    );
    assert!(
        observed
            .iter()
            .any(|e| e["crate_name"] == "leaf_types" && e["sha256"] == expected_leaf_sha),
        "{observed:?}"
    );
    // External fieldless enums carry a non-zero upper 32-bit CrateNum,
    // never colliding with `LOCAL_CRATE` (`0`) enum IDs.
    let local_tys = manifest["program"]["bodies"][0]["local_tys"]
        .as_array()
        .unwrap();
    let arg_enum_ids: Vec<u64> = local_tys[1..=3]
        .iter()
        .map(|t| t["id"].as_u64().expect("enum id"))
        .collect();
    assert!(arg_enum_ids[0] >= (1u64 << 32), "{arg_enum_ids:?}");
    assert!(arg_enum_ids[1] >= (1u64 << 32), "{arg_enum_ids:?}");
    assert_ne!(arg_enum_ids[0], arg_enum_ids[1], "{arg_enum_ids:?}");
    assert!(arg_enum_ids[2] < (1u64 << 32), "{arg_enum_ids:?}");

    // Invalid `--extern` crate identifiers fail closed.
    for bad_spec in [
        format!("--bad={}", dep_rmeta.display()),
        format!("@rsp={}", dep_rmeta.display()),
        format!("priv:dep={}", dep_rmeta.display()),
        format!("my-crate={}", dep_rmeta.display()),
        "missing_equals".to_string(),
    ] {
        let bad_fix = Capture::new(b"pub fn selected() {}\n");
        let out = bad_fix
            .selected_command()
            .arg(format!("--extern={bad_spec}"))
            .output()
            .unwrap();
        assert!(!out.status.success(), "{bad_spec}");
        assert_eq!(status(&out)["status"], "unsupported", "{bad_spec}: {out:?}");
        assert!(!bad_fix.output.exists());
    }

    // Without `-Ldependency=deps`, transitive `leaf_types` fails closed.
    let missing_dep_dir = Capture::new(subject_src);
    let out = missing_dep_dir
        .selected_command()
        .arg(format!("--extern=dep_types={}", dep_rmeta.display()))
        .output()
        .unwrap();
    assert!(!out.status.success());
    missing_dep_dir.assert_no_capture_artifacts();

    // Symlinked .rmeta is rejected fail-closed.
    let sym_rmeta = workspace.path().join("sym.rmeta");
    std::os::unix::fs::symlink(&dep_rmeta, &sym_rmeta).unwrap();
    let sym_fix = Capture::new(subject_src);
    let out = sym_fix
        .selected_command()
        .arg(format!("--extern=dep_types={}", sym_rmeta.display()))
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert_eq!(status(&out)["status"], "unsupported");
    assert!(!sym_fix.output.exists());
}
