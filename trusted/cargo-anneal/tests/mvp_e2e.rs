// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exercise the installed verification boundary with real Rust and Lean tools.
//!
//! Build `anneal-rustc-capture` before running this test. The harness accepts
//! `ANNEAL_MVP_CLI`, `ANNEAL_MVP_CAPTURE`, `ANNEAL_MVP_LEAN`, and
//! `ANNEAL_MVP_SYSROOT` overrides for separately installed tools. Missing tools
//! fail the test with setup diagnostics; they never turn it into a skipped pass.

use serde_json::{Value, json};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use tempfile::TempDir;

const SPEC: &str = include_str!("fixtures/scalar/Spec.lean");
const PROOF: &str = include_str!("fixtures/scalar/Proof.lean");
const SOURCE: &str = include_str!("fixtures/scalar/lib.rs");
const UNSUPPORTED: &str = include_str!("fixtures/scalar/unsupported.rs");
const DEPENDENCY: &str = include_str!("fixtures/scalar/dependency.rs");

struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
}

impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        let cli = override_path("ANNEAL_MVP_CLI")
            .or_else(|| override_path("ANNEAL_CLI"))
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_MVP_CLI");
        let capture = override_path("ANNEAL_MVP_CAPTURE")
            .or_else(|| override_path("ANNEAL_CAPTURE"))
            .or_else(|| {
                install_root
                    .as_ref()
                    .map(|root| root.join("bin/anneal-rustc-capture"))
                    .filter(|path| path.is_file())
            })
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_MVP_CAPTURE",
        );
        let lean = override_path("ANNEAL_MVP_LEAN")
            .or_else(|| override_path("ANNEAL_LEAN"))
            .or_else(|| {
                install_root
                    .as_ref()
                    .map(|root| root.join("lean/bin/lean"))
                    .filter(|path| path.is_file())
            })
            .unwrap_or_else(fallback_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_MVP_LEAN");
        let sysroot = override_path("ANNEAL_MVP_SYSROOT")
            .or_else(|| override_path("ANNEAL_SYSROOT"))
            .or_else(|| override_path("ANNEAL_TEST_RUST_SYSROOT"))
            .or_else(|| {
                install_root
                    .as_ref()
                    .map(|root| root.join("rust"))
                    .filter(|path| path.join("lib").is_dir())
            })
            .unwrap_or_else(|| {
                for toolchain in [
                    "nightly-2026-10-23",
                    "nightly-2026-06-01",
                    "nightly-2026-05-31",
                ] {
                    if let Ok(output) = Command::new("rustup")
                        .args(["run", toolchain, "rustc", "--print", "sysroot"])
                        .output()
                        && output.status.success()
                    {
                        return PathBuf::from(
                            String::from_utf8(output.stdout)
                                .expect("rustc sysroot must be UTF-8")
                                .trim(),
                        );
                    }
                }
                let output = Command::new("rustc")
                    .args(["--print", "sysroot"])
                    .output()
                    .expect("install the pinned compiler or set ANNEAL_MVP_SYSROOT");
                assert!(
                    output.status.success(),
                    "cannot find the pinned compiler sysroot; set ANNEAL_MVP_SYSROOT:\n{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                PathBuf::from(
                    String::from_utf8(output.stdout)
                        .expect("rustc sysroot must be UTF-8")
                        .trim(),
                )
            });
        assert!(
            sysroot.join("lib").is_dir(),
            "missing compiler sysroot {}; set ANNEAL_MVP_SYSROOT",
            sysroot.display()
        );
        Self {
            cli,
            capture,
            lean,
            sysroot,
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .arg("--capture")
            .arg(&self.capture)
            .arg("--lean")
            .arg(&self.lean)
            .arg("--sysroot")
            .arg(&self.sysroot);
        command
    }
}

fn override_path(name: &str) -> Option<PathBuf> {
    std::env::var_os(name).map(PathBuf::from)
}

#[cfg(feature = "setup")]
fn fallback_lean_path() -> PathBuf {
    cargo_anneal::default_lean_path()
}

#[cfg(not(feature = "setup"))]
fn fallback_lean_path() -> PathBuf {
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/root"));
    home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
}

fn required_file(path: PathBuf, description: &str, variable: &str) -> PathBuf {
    assert!(
        path.is_file(),
        "missing {description} at {}; set {variable}",
        path.display()
    );
    fs::canonicalize(path).expect("resolve test tool path")
}

struct Fixture {
    directory: TempDir,
    request: Value,
}

impl Fixture {
    fn new() -> Self {
        let directory = tempfile::Builder::new()
            .prefix("anneal-mvp-e2e-")
            .tempdir()
            .expect("create regression fixture");
        let rust = directory.path().join("rust");
        let lean = directory.path().join("lean");
        fs::create_dir(&rust).unwrap();
        fs::create_dir(&lean).unwrap();
        fs::write(rust.join("lib.rs"), SOURCE).unwrap();
        fs::write(lean.join("Spec.lean"), SPEC).unwrap();
        fs::write(lean.join("Proof.lean"), PROOF).unwrap();
        // Adjacent compiled files must not replace the declared proof source.
        fs::write(lean.join("Proof.olean"), b"not a Lean object file").unwrap();
        let request = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": rust,
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": lean,
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                ]
            }
        });
        Self { directory, request }
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.directory.path().join(relative)
    }

    fn write(&self, relative: &str, contents: impl AsRef<[u8]>) {
        fs::write(self.path(relative), contents).unwrap();
    }

    fn run(&self, tools: &Tools, name: &str, request: &Value) -> Receipt {
        let request_path = self.path(&format!("{name}.json"));
        fs::write(&request_path, serde_json::to_vec_pretty(request).unwrap()).unwrap();
        self.execute(
            name,
            tools
                .command()
                .arg("--request")
                .arg(request_path)
                .arg("--artifacts")
                .arg(self.path(name)),
        )
    }

    fn execute(&self, name: &str, command: &mut Command) -> Receipt {
        eprintln!("MVP CLI regression: {name}");
        let output = command
            .current_dir(self.directory.path())
            .output()
            .unwrap_or_else(|error| panic!("cannot run {name}: {error}"));
        let value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "{name} did not return a JSON receipt: {error}\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        });
        Receipt {
            name: name.to_owned(),
            value,
            output,
        }
    }
}

struct Receipt {
    name: String,
    value: Value,
    output: Output,
}

impl Receipt {
    fn expect(&self, code: i32, status: &str, phase: Option<&str>) {
        assert_eq!(
            self.output.status.code(),
            Some(code),
            "{} returned an unexpected exit code:\n{}\nstderr:\n{}",
            self.name,
            self.value,
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(
            self.value["status"], status,
            "{}: {}",
            self.name, self.value
        );
        if let Some(phase) = phase {
            assert_eq!(self.value["phase"], phase, "{}: {}", self.name, self.value);
        }
    }
}

fn lean_source(imports: &str, declarations: &str) -> String {
    let (header, _) = SPEC.split_once("prelude").unwrap();
    format!("{header}prelude\n{imports}\n\n{declarations}\n")
}

fn selected(request: &Value) -> Value {
    let mut request = request.clone();
    request["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    request
}

#[cfg(unix)]
#[test]
fn canonicalizes_symlinked_temporary_directory_source_bindings() {
    use sha2::{Digest, Sha256};
    use std::os::unix::fs::symlink;

    let tools = Tools::discover();
    let fixture = Fixture::new();
    let temporary = fixture.path("temporary-physical");
    let alias = fixture.path("temporary-alias");
    fs::create_dir(&temporary).unwrap();
    symlink(&temporary, &alias).unwrap();
    let request = fixture.path("symlinked-request.json");
    fs::write(
        &request,
        serde_json::to_vec_pretty(&fixture.request).unwrap(),
    )
    .unwrap();

    // Set TMPDIR only for the verifier process. The Rust test's own temporary
    // directory and other concurrently scheduled tests keep their environment.
    let accepted = fixture.execute(
        "symlinked-temporary-directory",
        tools
            .command()
            .env("TMPDIR", &alias)
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(fixture.path("symlinked-artifacts")),
    );
    accepted.expect(0, "crate_verified", None);
    assert_eq!(accepted.value["audit"]["exactType"], true);
    assert_eq!(accepted.value["audit"]["replay"], true);
    let bytes = fs::read(fixture.path("symlinked-artifacts/capture/capture.json")).unwrap();
    let captured: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(captured["source_files"].as_array().unwrap().len(), 1);
    let input = &captured["source_files"][0];
    let input_path = PathBuf::from(input["path"].as_str().unwrap());
    assert!(input_path.starts_with(fs::canonicalize(&temporary).unwrap()));
    assert_eq!(input["path"], captured["configuration"]["crate_root"]);
    assert_eq!(
        input["sha256"],
        format!("{:x}", Sha256::digest(SOURCE.as_bytes()))
    );
    assert_eq!(input["sha256"], accepted.value["sources"][0]["sha256"]);
    assert_eq!(
        accepted.value["capture_sha256"],
        format!("{:x}", Sha256::digest(&bytes))
    );
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());

    // Canonical temporary paths must not broaden the compiler's read allowlist.
    // An absolute include exists on disk but is not a declared source input.
    let undeclared = fixture.path("undeclared.rs");
    fs::write(&undeclared, "0").unwrap();
    fixture.write(
        "rust/lib.rs",
        format!(
            "pub fn zero() -> u64 {{ include!({}) }}\n",
            serde_json::to_string(&undeclared).unwrap()
        ),
    );
    fixture
        .execute(
            "undeclared-through-symlinked-temporary-directory",
            tools
                .command()
                .env("TMPDIR", &alias)
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(fixture.path("undeclared-artifacts")),
        )
        .expect(1, "unsupported", Some("capture"));
    assert!(
        !fixture
            .path("undeclared-artifacts/capture/capture.json")
            .exists()
    );
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());
}

// Keep this mutation matrix in one test so its backend invocations stay serial.
// Other tests also launch Lean; use one Rust test thread to bound their memory.
#[test]
fn verifies_real_source_and_rejects_boundary_mutations() {
    let tools = Tools::discover();
    let fixture = Fixture::new();

    let accepted = fixture.run(&tools, "whole-crate", &fixture.request);
    accepted.expect(0, "crate_verified", None);
    assert_eq!(accepted.value["experimental"], true);
    assert_eq!(accepted.value["scope"], json!({"kind": "crate"}));
    assert_eq!(accepted.value["selected"][0]["path"], "zero");
    for field in [
        "request_sha256",
        "capture_sha256",
        "capture_binary_sha256",
        "model_manifest_sha256",
        "specification_manifest_sha256",
    ] {
        assert_eq!(accepted.value[field].as_str().unwrap().len(), 64);
    }
    assert!(fixture.path("whole-crate/capture/Captured.lean").is_file());
    assert!(
        fixture
            .path("whole-crate/generated/Expected.lean")
            .is_file()
    );
    assert!(fixture.path("whole-crate/audit-request.json").is_file());
    assert!(fixture.path("whole-crate/result.json").is_file());

    // Keep the specification and proof fixed while changing the Rust body.
    // A fresh successful capture must not let the old source proof verify
    // a different implementation.
    fixture.write("rust/lib.rs", SOURCE.replace("    0\n", "    1\n"));
    fixture
        .run(&tools, "changed-source", &fixture.request)
        .expect(1, "proof_failed", Some("audit"));
    let changed_capture: Value = serde_json::from_slice(
        &fs::read(fixture.path("changed-source/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_ne!(
        accepted.value["sources"][0]["sha256"],
        changed_capture["source_files"][0]["sha256"]
    );
    fixture.write("rust/lib.rs", SOURCE);

    // Each negative compiles a different attempted shortcut around the
    // canonical closed theorem. Require proof rejection, not a missing
    // tool or malformed receipt that could make a negative pass vacuously.
    for (name, declarations) in [
        ("wrong-root", "theorem Proof.verify : True := True.intro"),
        (
            "axiom",
            "axiom fabricated : Expected.claim\ntheorem Proof.verify : Expected.claim := fabricated",
        ),
        ("sorry", "theorem Proof.verify : Expected.claim := by sorry"),
        (
            "extra-hypothesis",
            "theorem Proof.verify (assumed : Expected.claim) : Expected.claim := assumed",
        ),
    ] {
        fixture.write(
            "lean/Proof.lean",
            lean_source("import Expected", declarations),
        );
        fixture
            .run(&tools, name, &fixture.request)
            .expect(1, "proof_failed", Some("audit"));
    }
    fixture.write("lean/Proof.lean", PROOF);

    let mut wrong_role = fixture.request.clone();
    wrong_role["proof"]["sources"][0]["role"] = json!("proof");
    fixture
        .run(&tools, "wrong-declaration-role", &wrong_role)
        .expect(1, "unsupported", Some("proof"));

    let shadowed = PROOF
        .replace(
            "theorem verify : Expected.claim := by",
            "def Spec.specs : Specs := ⟨fun _ _ => False, fun _ => True⟩\n\n\
             theorem verify : CrateTheorem ⟨program, Spec.specs⟩ := by",
        )
        .replace(
            concat!(
                "  · constructor\n",
                "    · exact behavior_of_returns (body := body) rfl rfl rfl\n",
                "        (run_initial_success runs).2\n",
                "    · intro args value beh\n",
                "      let ⟨valid, returned⟩ := returns_of_behavior (body := body) rfl beh\n",
                "      cases args with\n",
                "      | nil => exact ⟨rfl, (run_result_unique runs returned).symm⟩\n",
                "      | cons _ _ => cases valid",
            ),
            "  · exact True.intro",
        );
    fixture.write("lean/Proof.lean", shadowed);
    fixture
        .run(&tools, "shadowed-specification", &fixture.request)
        .expect(1, "proof_failed", Some("audit"));
    fixture.write("lean/Proof.lean", PROOF);

    // Syntax can conceal a specification dependency in a proof-role module.
    // Check the origin boundary itself, rather than crediting an unrelated
    // elaboration error as rejection of the hidden helper.
    fixture.write(
        "lean/Extra.lean",
        lean_source(
            "import Trusted.MirSemantics",
            "macro \"hiddenProperty\" : term => `(True)",
        ),
    );
    fixture.write(
        "lean/Spec.lean",
        lean_source(
            "import Trusted.MirSemantics\nimport Extra",
            "namespace Spec\ndef specs : Trusted.MirSemantics.Specs :=\n  ⟨fun _ _ => False, fun _ => hiddenProperty⟩\nend Spec",
        ),
    );
    let mut hidden_spec = fixture.request.clone();
    hidden_spec["proof"]["sources"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "module": "Extra", "path": "Extra.lean", "role": "proof"
        }));
    let hidden = fixture.run(&tools, "hidden-specification-macro", &hidden_spec);
    hidden.expect(1, "proof_failed", Some("audit"));
    let detail = hidden.value["detail"].as_str().unwrap();
    assert!(
        detail.contains("specification")
            || detail.contains("role")
            || detail.contains("Spec cannot import Extra"),
        "macro fixture must fail at the specification origin boundary: {detail}"
    );
    fixture.write("lean/Spec.lean", SPEC);

    // Selected-unit success intentionally leaves unrelated items uncovered;
    // the same crate must fail whole-crate capture. Test both observations
    // so a partial success cannot be presented as complete coverage.
    fixture.write("rust/lib.rs", UNSUPPORTED);
    let mut selected_request = selected(&fixture.request);
    selected_request["scope"]["roots"] = json!(["zero", "zero"]);
    selected_request["compilation"]["cfg"] = json!(["omega", "alpha", "omega"]);
    let normalized = fixture.run(&tools, "selected-outside-closure", &selected_request);
    normalized.expect(0, "selected_unit_verified", None);
    assert_eq!(normalized.value["scope"]["roots"], json!(["zero"]));
    assert_eq!(
        normalized.value["configuration"]["cfg"],
        json!(["alpha", "omega"])
    );
    assert!(
        normalized.value["census"]
            .as_array()
            .unwrap()
            .iter()
            .any(|item| { item["path"] == "unsupported" && item["selected"] == false })
    );
    selected_request["scope"]["roots"] = json!(["zero"]);
    selected_request["compilation"]["cfg"] = json!(["alpha", "omega"]);
    let ordered = fixture.run(&tools, "normalized-request", &selected_request);
    ordered.expect(0, "selected_unit_verified", None);
    assert_eq!(
        normalized.value["request_sha256"],
        ordered.value["request_sha256"]
    );
    fixture
        .run(&tools, "whole-unsupported", &fixture.request)
        .expect(1, "unsupported", Some("capture"));

    fixture.write("rust/lib.rs", DEPENDENCY);
    fixture
        .run(
            &tools,
            "unsupported-dependency",
            &selected(&fixture.request),
        )
        .expect(1, "unsupported", Some("capture"));
    fixture.write("rust/lib.rs", SOURCE);

    let manifest = fixture.path("rust/Cargo.toml");
    let manifest_base = "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[lib]\npath = \"lib.rs\"\n";
    fixture.write(
        "rust/Cargo.toml",
        format!("{manifest_base}[features]\ndefault = [\"extra\"]\nextra = []\n"),
    );
    fixture
        .execute(
            "cargo-default-features",
            tools
                .command()
                .arg("--manifest-path")
                .arg(&manifest)
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(1, "unsupported", Some("cargo"));
    fixture.write("rust/Cargo.toml", manifest_base);
    fs::remove_file(fixture.path("lean/Extra.lean")).unwrap();
    // Hidden directories inside `--proof-dir` and ambient `RUSTC` overrides
    // must not perturb the Cargo shortcut.
    fs::create_dir(fixture.path("lean/.cache")).unwrap();
    fixture.write("lean/.cache/Ignored.lean", b"not valid Lean syntax");
    fixture
        .execute(
            "cargo-feature-free-library",
            tools
                .command()
                .env("RUSTC", fixture.path("nonexistent-rustc"))
                .arg("--manifest-path")
                .arg(&manifest)
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(0, "crate_verified", None);

    // Workspace-root compiler overrides must also be refused when verifying a
    // member crate via `--manifest-path`.
    let ws_root = fixture.path("workspace-override");
    fs::create_dir_all(ws_root.join(".cargo")).unwrap();
    fs::create_dir_all(ws_root.join("member")).unwrap();
    fs::write(
        ws_root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    fs::write(
        ws_root.join(".cargo/config.toml"),
        "[build]\nrustflags = [\"--cfg=override_flag\"]\n",
    )
    .unwrap();
    fs::write(ws_root.join("member/Cargo.toml"), manifest_base).unwrap();
    fs::write(ws_root.join("member/lib.rs"), SOURCE).unwrap();
    fixture
        .execute(
            "cargo-workspace-compiler-override",
            tools
                .command()
                .arg("--manifest-path")
                .arg(ws_root.join("member/Cargo.toml"))
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(1, "unsupported", Some("cargo"));

    let mut reserved_anneal = fixture.request.clone();
    reserved_anneal["proof"]["sources"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "module": "Anneal.Shadow", "path": "Proof.lean", "role": "proof"
        }));
    fixture
        .run(&tools, "reserved-anneal-module", &reserved_anneal)
        .expect(1, "unsupported", Some("proof"));

    // Retention must preserve caller-owned evidence even when the new
    // request itself is invalid. This checks operation ordering as well as
    // the create-only filesystem rule.
    let mut invalid = fixture.request.clone();
    invalid["schema_version"] = json!(0);
    let sentinel = fixture.path("whole-crate/sentinel");
    fs::write(&sentinel, b"keep existing evidence").unwrap();
    fixture
        .run(&tools, "whole-crate", &invalid)
        .expect(2, "tool_failed", Some("retention"));
    assert_eq!(fs::read(sentinel).unwrap(), b"keep existing evidence");

    let request_path = fixture.path("missing-capture.json");
    fs::write(&request_path, serde_json::to_vec(&fixture.request).unwrap()).unwrap();
    fixture
        .execute(
            "missing-capture-is-an-error",
            Command::new(&tools.cli)
                .arg("verify")
                .arg("--request")
                .arg(request_path)
                .arg("--capture")
                .arg(fixture.path("missing-capture"))
                .arg("--lean")
                .arg(&tools.lean)
                .arg("--sysroot")
                .arg(&tools.sysroot),
        )
        .expect(2, "tool_failed", Some("capture-tool"));

    // This source never returns. Its root still requires safety of every
    // reachable prefix, while the authored property proves no return exists.
    fixture.write("rust/lib.rs", include_str!("fixtures/spin/lib.rs"));
    fixture.write("lean/Spec.lean", include_str!("fixtures/spin/Spec.lean"));
    fixture.write("lean/Proof.lean", include_str!("fixtures/spin/Proof.lean"));
    fixture
        .run(&tools, "safe-divergence", &fixture.request)
        .expect(0, "crate_verified", None);

    // Exercise bundled `Anneal.PureLift` compilation and kernel replay under
    // `targetAudit` when an authored proof imports `Anneal.PureLift`.
    fixture.write("rust/lib.rs", SOURCE);
    fixture.write("lean/Spec.lean", SPEC);
    let pure_lift_proof = PROOF
        .replace(
            "import Anneal.MirWp",
            "import Anneal.MirWp\nimport Anneal.PureLift",
        )
        .replace(
            "theorem verify : Expected.claim := by\n",
            "theorem verify : Expected.claim :=\n  let _ : Anneal.PureLift.mirListGet? program.bodies 0 = some body := rfl\n  by\n",
        );
    fixture.write("lean/Proof.lean", pure_lift_proof);
    let pure_lift_receipt = fixture.run(&tools, "bundled-pure-lift", &fixture.request);
    pure_lift_receipt.expect(0, "crate_verified", None);
    assert_eq!(pure_lift_receipt.value["audit"]["exactType"], true);
    assert_eq!(pure_lift_receipt.value["audit"]["replay"], true);
}

#[test]
fn unsafe_contracts_remain_bound_to_function_identities() {
    let tools = Tools::discover();
    let fixture = Fixture::new();
    let original = include_str!("fixtures/unsafe_identity/lib.rs");
    fixture.write("rust/lib.rs", original);
    fixture.write(
        "lean/Spec.lean",
        include_str!("fixtures/unsafe_identity/Spec.lean"),
    );
    fixture.write(
        "lean/Proof.lean",
        include_str!("fixtures/unsafe_identity/Proof.lean"),
    );
    fixture
        .run(&tools, "unsafe-identity-before", &fixture.request)
        .expect(0, "crate_verified", None);

    // Preserve the captured operational bodies and the reviewed specification,
    // while moving the uncallable body from `locked` to the unrestricted `open`.
    // An ordinal predicate would follow the faulting body's old slot and accept.
    // Keep both Lean sources unchanged. Rewriting a predicate in response to
    // the mutation would change the reviewed contract instead of testing its
    // binding.
    let changed = original
        .replace("fn locked", "fn temporary")
        .replace("fn open", "fn locked")
        .replace("fn temporary", "fn open");
    fixture.write("rust/lib.rs", changed);
    fixture
        .run(&tools, "unsafe-identity-after", &fixture.request)
        .expect(1, "proof_failed", Some("audit"));
}

#[test]
fn declared_cfg_cannot_expand_compiler_response_files() {
    let tools = Tools::discover();
    let fixture = Fixture::new();
    fixture.write(
        "rust/lib.rs",
        format!("{SOURCE}\n#[cfg(not(injected))]\ncompile_error!(\"missing declared cfg\");\n"),
    );
    // This file is deliberately outside source_root and source_files. Its
    // harmless second cfg would make the compilation succeed if rustc treated
    // a declared cfg as an argument file instead of a literal cfg value.
    let response = fixture.path("compiler-flags.rsp");
    fs::write(&response, b"dummy\n--cfg\ninjected\n").unwrap();
    for (name, path) in [
        ("cfg-existing-response", response),
        ("cfg-missing-response", fixture.path("missing.rsp")),
    ] {
        let mut request = fixture.request.clone();
        request["compilation"]["cfg"] = json!([format!("@{}", path.to_str().unwrap())]);
        fixture
            .run(&tools, name, &request)
            .expect(2, "compiler_failed", Some("capture"));
        let diagnostic =
            fs::read_to_string(fixture.path(&format!("{name}/capture.stderr"))).unwrap();
        assert!(diagnostic.contains("invalid `--cfg` argument"));
        assert!(!diagnostic.contains("failed to load argument file"));
        assert!(
            !fixture
                .path(&format!("{name}/capture/capture.json"))
                .exists()
        );
    }

    // A normal bare flag and a quoted @ string remain unchanged in the
    // authenticated configuration and still verify with the installed tools.
    let mut request = fixture.request.clone();
    let cfg = json!([r#"feature="@literal""#, "injected"]);
    request["compilation"]["cfg"] = cfg.clone();
    let receipt = fixture.run(&tools, "cfg-literal-values", &request);
    receipt.expect(0, "crate_verified", None);
    assert_eq!(receipt.value["configuration"]["cfg"], cfg);
}

#[cfg(unix)]
#[test]
fn verifies_multi_crate_externs_and_dependency_dirs_and_rejects_tampering() {
    use sha2::{Digest, Sha256};
    use std::io::Write as _;
    use std::os::unix::fs::symlink;

    let tools = Tools::discover();
    let fixture = Fixture::new();
    let rustc = tools.sysroot.join("bin/rustc");
    let deps_dir = fixture.path("deps");
    let rlibs_dir = fixture.path("rlibs");
    fs::create_dir(&deps_dir).unwrap();
    fs::create_dir(&rlibs_dir).unwrap();

    // Compile transitive crate `leaf_types` into `deps/libleaf_types.rmeta`.
    let leaf_src = fixture.path("leaf_types.rs");
    fs::write(&leaf_src, b"pub enum LeafBit { Zero = 0, One = 1 }\n").unwrap();
    let leaf_rmeta = deps_dir.join("libleaf_types.rmeta");
    assert!(
        Command::new(&rustc)
            .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
            .args([
                "--edition=2024",
                "--crate-name=leaf_types",
                "--crate-type=lib",
                "--target=x86_64-unknown-linux-gnu",
                "--emit=metadata",
                "-o",
            ])
            .arg(&leaf_rmeta)
            .arg(&leaf_src)
            .status()
            .unwrap()
            .success()
    );

    // Compile `dep_types` (re-exporting `LeafBit` and defining `Mode`) as both
    // `.rmeta` and `.rlib`.
    let dep_src = fixture.path("dep_types.rs");
    fs::write(
        &dep_src,
        b"pub use leaf_types::LeafBit;\n\
          pub enum Mode { Little = 0, Big = 1 }\n",
    )
    .unwrap();
    let dep_rmeta = deps_dir.join("libdep_types.rmeta");
    let dep_rlib = rlibs_dir.join("libdep_types.rlib");
    for (emit, out_path) in [("metadata", &dep_rmeta), ("link", &dep_rlib)] {
        assert!(
            Command::new(&rustc)
                .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
                .args([
                    "--edition=2024",
                    "--crate-name=dep_types",
                    "--crate-type=rlib",
                    "--target=x86_64-unknown-linux-gnu",
                    &format!("--emit={emit}"),
                    "-o",
                ])
                .arg(out_path)
                .arg(format!("--extern=leaf_types={}", leaf_rmeta.display()))
                .arg(&dep_src)
                .status()
                .unwrap()
                .success()
        );
    }

    fixture.write(
        "rust/lib.rs",
        "use dep_types::{LeafBit, Mode};\n\
         pub fn classify(mode: Mode, bit: LeafBit) -> u64 {\n\
             match mode {\n\
                 Mode::Little => match bit {\n\
                     LeafBit::Zero => 0x0f,\n\
                     LeafBit::One => 0xff,\n\
                 },\n\
                 Mode::Big => 0,\n\
             }\n\
         }\n",
    );
    fixture.write(
        "lean/Spec.lean",
        lean_source(
            "import Trusted.MirSemantics",
            r#"namespace Spec
open Trusted.MirModel Trusted.MirSemantics

def u64Val (n : Nat) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 n⟩

def callArgs (body : Body) (m b : Nat) : List Val :=
  match body.locals with
  | _ :: .enum mTy :: .enum bTy :: _ => [.enumVal mTy m, .enumVal bTy b]
  | _ => []

noncomputable def ReturnsU64 (p : Program) (args : List Val) (n : Nat) : Prop :=
  Behavior (entryProgForBody p 0) { args := args } (.returned ⟨u64Val n, ⟨[]⟩⟩)

noncomputable def specs : Specs :=
  ⟨fun _ _ => False, fun program => ∃ body, program.bodies = [body] ∧
    ReturnsU64 program (callArgs body 0 0) 0x0f ∧
    ReturnsU64 program (callArgs body 0 1) 0xff ∧
    ReturnsU64 program (callArgs body 1 0) 0 ∧
    ReturnsU64 program (callArgs body 1 1) 0⟩

end Spec"#,
        ),
    );
    fixture.write(
        "lean/Proof.lean",
        lean_source(
            "import Expected\nimport Anneal.MirWp",
            r#"namespace Proof
open Trusted.MirModel Trusted.MirSemantics Anneal.MirWp Spec

noncomputable def program : Program :=
  interpretV2026_10_22_R7189d39d9 Captured.program

noncomputable def body : Body := program.bodies[0]

noncomputable def mTy : EnumTy :=
  match body.locals with
  | _ :: .enum t :: _ => t
  | _ => ⟨0, .isize, true, .zeroSized, []⟩

noncomputable def bTy : EnumTy :=
  match body.locals with
  | _ :: _ :: .enum t :: _ => t
  | _ => ⟨0, .isize, true, .zeroSized, []⟩

theorem natListBeq_eq {xs ys : List Nat} (h : natListBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      change (Nat.beq x y && natListBeq xs ys) = true at h
      have h1 : Nat.beq x y = true := by
        cases h_xy : Nat.beq x y
        · rw [h_xy] at h; cases h
        · rfl
      have h2 : natListBeq xs ys = true := by
        rw [h1] at h; exact h
      rw [Nat.eq_of_beq_eq_true h1, ih h2]

theorem intWidth_beq_eq {w1 w2 : IntWidth} (h : IntWidth.beq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | cases h

theorem enumTagRepr_beq_eq {r1 r2 : EnumTagRepr}
    (h : EnumTagRepr.beq r1 r2 = true) : r1 = r2 := by
  cases r1 with
  | zeroSized =>
    cases r2 with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar w1 s1 =>
    cases r2 with
    | zeroSized => cases h
    | scalar w2 s2 =>
      cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | rfl | cases h

theorem enumTy_beq_eq {e1 e2 : EnumTy} (h : EnumTy.beq e1 e2 = true) : e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 discs1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 discs2 =>
      unfold EnumTy.beq at h
      dsimp only at h
      cases h1 : Nat.beq id1 id2 <;>
        cases h2 : IntWidth.beq dw1 dw2 <;>
        cases h3 : (ds1 == ds2) <;>
        cases h4 : EnumTagRepr.beq tr1 tr2 <;>
        cases h5 : natListBeq discs1 discs2 <;>
        rw [h1, h2, h3, h4, h5] at h <;>
        try cases h
      rw [Nat.eq_of_beq_eq_true h1, intWidth_beq_eq h2, eq_of_beq h3,
        enumTagRepr_beq_eq h4, natListBeq_eq h5]

theorem checkVal_enum2 {ety : EnumTy} (h_ds : ety.discriminants = [0, 1]) {v : Val}
    (h : checkVal v (.enum ety) = true) : v = .enumVal ety 0 ∨ v = .enumVal ety 1 := by
  cases v with
  | enumVal ety' var =>
    cases h_adm : (enumAdmitted ety' && Nat.blt var ety'.discriminants.length) with
    | false => simp [checkVal, Val.ty?, h_adm] at h
    | true =>
      have h_ty : MirTy.beq (.enum ety') (.enum ety) = true := by
        unfold checkVal Val.ty? at h
        dsimp only at h
        rw [h_adm] at h
        exact h
      unfold MirTy.beq at h_ty
      dsimp only at h_ty
      have h_eq := enumTy_beq_eq h_ty
      subst h_eq
      have h_blt : Nat.blt var 2 = true := by
        rw [h_ds] at h_adm
        cases h_e : enumAdmitted ety' <;> rw [h_e] at h_adm
        · cases h_adm
        · exact h_adm
      have h_lt : var < 2 := Nat.le_of_ble_eq_true h_blt
      cases var with
      | zero => exact Or.inl rfl
      | succ n =>
        cases n with
        | zero => exact Or.inr rfl
        | succ k =>
          exact False.elim (Nat.not_lt_zero k
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h_lt)))
  | scalar sv => cases h_wf : sv.wf <;> simp [checkVal, Val.ty?, h_wf, MirTy.beq] at h
  | bool _ | ptr _ | unit | tuple _ | bytes _ => cases h

theorem run00 : run body 8 (initial body (callArgs body 0 0)) = some (u64Val 0x0f) := rfl
theorem run01 : run body 8 (initial body (callArgs body 0 1)) = some (u64Val 0xff) := rfl
theorem run10 : run body 8 (initial body (callArgs body 1 0)) = some (u64Val 0) := rfl
theorem run11 : run body 8 (initial body (callArgs body 1 1)) = some (u64Val 0) := rfl

theorem paramTys_eq :
    (body.locals.drop 1).take body.argumentCount = [.enum mTy, .enum bTy] := rfl

theorem callArgs_eq (m b : Nat) :
    callArgs body m b = [.enumVal mTy m, .enumVal bTy b] := rfl

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
      have same : body = selected := Option.some.inj found
      subst selected
      refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      rw [paramTys_eq] at valid
      cases args with
      | nil => cases valid
      | cons a0 rest0 =>
        cases rest0 with
        | nil => simp [checkArgsMatch] at valid
        | cons a1 rest1 =>
          cases rest1 with
          | cons _ _ => simp [checkArgsMatch] at valid
          | nil =>
            simp only [checkArgsMatch, Bool.and_eq_true] at valid
            match checkVal_enum2 (ety := mTy) rfl valid.1,
                  checkVal_enum2 (ety := bTy) rfl valid.2.1 with
            | .inl ha0, .inl ha1 =>
              rw [ha0, ha1, ← callArgs_eq 0 0]; exact (run_initial_success run00).1
            | .inl ha0, .inr ha1 =>
              rw [ha0, ha1, ← callArgs_eq 0 1]; exact (run_initial_success run01).1
            | .inr ha0, .inl ha1 =>
              rw [ha0, ha1, ← callArgs_eq 1 0]; exact (run_initial_success run10).1
            | .inr ha0, .inr ha1 =>
              rw [ha0, ha1, ← callArgs_eq 1 1]; exact (run_initial_success run11).1
    | succ _ => cases found
  · exact ⟨body, rfl,
      behavior_of_returns rfl rfl rfl (run_initial_success run00).2,
      behavior_of_returns rfl rfl rfl (run_initial_success run01).2,
      behavior_of_returns rfl rfl rfl (run_initial_success run10).2,
      behavior_of_returns rfl rfl rfl (run_initial_success run11).2⟩

end Proof"#,
        ),
    );

    let dep_rmeta_sha = format!("{:x}", Sha256::digest(fs::read(&dep_rmeta).unwrap()));
    let dep_rlib_sha = format!("{:x}", Sha256::digest(fs::read(&dep_rlib).unwrap()));
    let leaf_rmeta_sha = format!("{:x}", Sha256::digest(fs::read(&leaf_rmeta).unwrap()));

    // Positive verification with `.rmeta` + `dependency_dirs` and with `.rlib`.
    for (case_name, rel_ext_path, expected_ext_sha) in [
        (
            "multi-crate-rmeta",
            "deps/libdep_types.rmeta",
            &dep_rmeta_sha,
        ),
        ("multi-crate-rlib", "rlibs/libdep_types.rlib", &dep_rlib_sha),
    ] {
        let mut req = fixture.request.clone();
        req["compilation"]["externs"] = json!([
            {"crate_name": "dep_types", "path": rel_ext_path}
        ]);
        req["compilation"]["dependency_dirs"] = json!(["deps"]);
        let receipt = fixture.run(&tools, case_name, &req);
        receipt.expect(0, "crate_verified", None);
        assert_eq!(receipt.value["audit"]["exactType"], true);
        assert_eq!(receipt.value["audit"]["replay"], true);
        assert_eq!(
            receipt.value["externs"],
            json!([{
                "crate_name": "dep_types",
                "relative_path": rel_ext_path,
                "sha256": expected_ext_sha,
            }])
        );
        let loaded = receipt.value["loaded_externs"].as_array().unwrap();
        assert!(
            loaded
                .iter()
                .any(|e| e["crate_name"] == "dep_types" && e["sha256"] == *expected_ext_sha),
            "{loaded:?}"
        );
        assert!(
            loaded
                .iter()
                .any(|e| e["crate_name"] == "leaf_types" && e["sha256"] == leaf_rmeta_sha),
            "{loaded:?}"
        );
    }

    let mut base_req = fixture.request.clone();
    base_req["compilation"]["externs"] = json!([
        {"crate_name": "dep_types", "path": "deps/libdep_types.rmeta"}
    ]);
    base_req["compilation"]["dependency_dirs"] = json!(["deps"]);

    // Negative 1: invalid `--extern` crate names fail closed at `request`.
    for (idx, bad_name) in ["--bad", "@rsp", "priv:dep", "my-crate", "_"]
        .into_iter()
        .enumerate()
    {
        let mut bad_req = base_req.clone();
        bad_req["compilation"]["externs"] = json!([
            {"crate_name": bad_name, "path": "deps/libdep_types.rmeta"}
        ]);
        fixture
            .run(&tools, &format!("bad-extern-name-{idx}"), &bad_req)
            .expect(1, "unsupported", Some("request"));
    }

    // Negative 2: symlinked `.rmeta` or `..` path fails closed at `inputs`.
    let sym_rmeta = deps_dir.join("sym_dep.rmeta");
    symlink(&dep_rmeta, &sym_rmeta).unwrap();
    let mut sym_req = base_req.clone();
    sym_req["compilation"]["externs"] = json!([
        {"crate_name": "dep_types", "path": "deps/sym_dep.rmeta"}
    ]);
    fixture
        .run(&tools, "symlink-extern", &sym_req)
        .expect(1, "unsupported", Some("inputs"));
    fs::remove_file(&sym_rmeta).unwrap();

    let mut escape_req = base_req.clone();
    escape_req["compilation"]["externs"] = json!([
        {"crate_name": "dep_types", "path": "../libdep_types.rmeta"}
    ]);
    fixture
        .run(&tools, "escape-extern", &escape_req)
        .expect(1, "unsupported", Some("inputs"));

    // Negative 3a: pre-run `.rmeta` header corruption fails at `capture`.
    let orig_dep_bytes = fs::read(&dep_rmeta).unwrap();
    let mut corrupted = orig_dep_bytes.clone();
    for byte in corrupted.iter_mut().take(8) {
        *byte ^= 0xff;
    }
    fs::write(&dep_rmeta, &corrupted).unwrap();
    fixture
        .run(&tools, "corrupted-rmeta", &base_req)
        .expect(2, "compiler_failed", Some("capture"));
    fs::write(&dep_rmeta, &orig_dep_bytes).unwrap();

    // Negative 3b: semantic `.rmeta` mutation (swapping `Mode` discriminants
    // without updating the proof) changes `externs[0].sha256` and fails proof!
    let mutated_dep_src = fixture.path("dep_types_mutated.rs");
    fs::write(
        &mutated_dep_src,
        b"pub use leaf_types::LeafBit;\n\
          pub enum Mode { Little = 1, Big = 0 }\n",
    )
    .unwrap();
    assert!(
        Command::new(&rustc)
            .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
            .args([
                "--edition=2024",
                "--crate-name=dep_types",
                "--crate-type=rlib",
                "--target=x86_64-unknown-linux-gnu",
                "--emit=metadata",
                "-o",
            ])
            .arg(&dep_rmeta)
            .arg(format!("--extern=leaf_types={}", leaf_rmeta.display()))
            .arg(&mutated_dep_src)
            .status()
            .unwrap()
            .success()
    );
    fixture
        .run(&tools, "swapped-discriminant-rmeta", &base_req)
        .expect(1, "proof_failed", Some("audit"));
    fs::write(&dep_rmeta, &orig_dep_bytes).unwrap();

    // Negative 4: mid-run `.rmeta` tamper (mutating `dep_rmeta` after capture)
    // is caught by the post-audit `binding` SHA-256 check!
    let wrapper = fixture.path("tamper-capture-wrapper.sh");
    let script = format!(
        "#!/bin/sh\n'{}' \"$@\"\nrc=$?\nprintf 'tampered' >> '{}'\nexit $rc\n",
        tools.capture.display(),
        dep_rmeta.display()
    );
    let mut installer = Command::new("/bin/sh")
        .args(["-c", "cat > \"$1\" && chmod 755 \"$1\"", "install"])
        .arg(&wrapper)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    installer
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    assert!(installer.wait().unwrap().success());

    let req_path = fixture.path("mid-run-tamper.json");
    fs::write(&req_path, serde_json::to_vec_pretty(&base_req).unwrap()).unwrap();
    fixture
        .execute(
            "mid-run-rmeta-tamper",
            Command::new(&tools.cli)
                .arg("verify")
                .arg("--request")
                .arg(&req_path)
                .arg("--capture")
                .arg(&wrapper)
                .arg("--lean")
                .arg(&tools.lean)
                .arg("--sysroot")
                .arg(&tools.sysroot),
        )
        .expect(2, "tool_failed", Some("binding"));
    fs::write(&dep_rmeta, &orig_dep_bytes).unwrap();

    // Negative 5: dropping a new `.rmeta` into `deps/` during verification is
    // caught by `watched_dep_dirs` re-scanning at `binding`.
    let rogue_rmeta = deps_dir.join("librogue.rmeta");
    let inject_wrapper = fixture.path("inject-dep-wrapper.sh");
    let inject_script = format!(
        "#!/bin/sh\n'{}' \"$@\"\nrc=$?\nprintf 'rogue' > '{}'\nexit $rc\n",
        tools.capture.display(),
        rogue_rmeta.display()
    );
    let mut installer = Command::new("/bin/sh")
        .args(["-c", "cat > \"$1\" && chmod 755 \"$1\"", "install"])
        .arg(&inject_wrapper)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    installer
        .stdin
        .take()
        .unwrap()
        .write_all(inject_script.as_bytes())
        .unwrap();
    assert!(installer.wait().unwrap().success());

    fixture
        .execute(
            "mid-run-dep-dir-inject",
            Command::new(&tools.cli)
                .arg("verify")
                .arg("--request")
                .arg(&req_path)
                .arg("--capture")
                .arg(&inject_wrapper)
                .arg("--lean")
                .arg(&tools.lean)
                .arg("--sysroot")
                .arg(&tools.sysroot),
        )
        .expect(2, "tool_failed", Some("binding"));
    let _ = fs::remove_file(&rogue_rmeta);

    // Negative 6: unclean relative paths (trailing `/` or repeated `//`),
    // invalid `crate_name`/`edition`, and hyphen-prefixed `roots` fail closed
    // as `unsupported` (`exit 1`) rather than `tool_failed` (`exit 2`).
    for (idx, (bad_req, expected_phase)) in [
        (
            {
                let mut r = base_req.clone();
                r["compilation"]["dependency_dirs"] = json!(["deps/"]);
                r
            },
            "inputs",
        ),
        (
            {
                let mut r = base_req.clone();
                r["compilation"]["externs"] = json!([
                    {"crate_name": "dep_types", "path": "deps//libdep_types.rmeta"}
                ]);
                r
            },
            "inputs",
        ),
        (
            {
                let mut r = base_req.clone();
                r["compilation"]["source_files"] = json!(["lib.rs/"]);
                r
            },
            "inputs",
        ),
        (
            {
                let mut r = base_req.clone();
                r["compilation"]["crate_name"] = json!("--help");
                r
            },
            "request",
        ),
        (
            {
                let mut r = base_req.clone();
                r["compilation"]["edition"] = json!("9999");
                r
            },
            "request",
        ),
        (
            {
                let mut r = base_req.clone();
                r["scope"] = json!({"kind": "selected_unit", "roots": ["--help"]});
                r
            },
            "capture",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        fixture
            .run(&tools, &format!("unclean-or-flag-req-{idx}"), &bad_req)
            .expect(1, "unsupported", Some(expected_phase));
    }
}

#[cfg(unix)]
#[test]
fn verifies_with_work_dir_under_nonexistent_and_readonly_tmpdir() {
    use std::os::unix::fs::PermissionsExt as _;

    let tools = Tools::discover();
    let fixture = Fixture::new();
    let writable_work = fixture.path("ninja-action-scratch");
    fs::create_dir(&writable_work).unwrap();
    let ro_tmp = fixture.path("readonly-tmp");
    fs::create_dir(&ro_tmp).unwrap();
    fs::set_permissions(&ro_tmp, fs::Permissions::from_mode(0o500)).unwrap();
    let nonexistent_tmp = fixture.path("nonexistent_ro_tmp");

    let req_path = fixture.path("hermetic-work-dir.json");
    fs::write(
        &req_path,
        serde_json::to_vec_pretty(&fixture.request).unwrap(),
    )
    .unwrap();

    for (idx, bad_tmp) in [&nonexistent_tmp, &ro_tmp].into_iter().enumerate() {
        let artifacts_dir = fixture.path(&format!("work-dir-artifacts-{idx}"));
        let receipt = fixture.execute(
            &format!("work-dir-request-{idx}"),
            tools
                .command()
                .env("TMPDIR", bad_tmp)
                .arg("--request")
                .arg(&req_path)
                .arg("--work-dir")
                .arg(&writable_work)
                .arg("--artifacts")
                .arg(&artifacts_dir),
        );
        receipt.expect(0, "crate_verified", None);
        assert!(!nonexistent_tmp.exists());
        assert_eq!(fs::read_dir(&ro_tmp).unwrap().count(), 0);
        assert_eq!(fs::read_dir(&writable_work).unwrap().count(), 0);
        assert!(artifacts_dir.join("result.json").is_file());
        assert!(!artifacts_dir.join("tmp").exists());
    }

    // Exercise `--manifest-path` (`cargo metadata` + `capture` + `Checker`)
    // under `TMPDIR=/nonexistent_ro_tmp` with `--work-dir`.
    let manifest = fixture.path("rust/Cargo.toml");
    fixture.write(
        "rust/Cargo.toml",
        "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[lib]\npath = \"lib.rs\"\n",
    );
    let shortcut_receipt = fixture.execute(
        "work-dir-cargo-shortcut",
        tools
            .command()
            .env("TMPDIR", &nonexistent_tmp)
            .arg("--manifest-path")
            .arg(&manifest)
            .arg("--proof-dir")
            .arg(fixture.path("lean"))
            .arg("--work-dir")
            .arg(&writable_work),
    );
    shortcut_receipt.expect(0, "crate_verified", None);
    assert!(!nonexistent_tmp.exists());
    assert_eq!(fs::read_dir(&writable_work).unwrap().count(), 0);
    fs::set_permissions(&ro_tmp, fs::Permissions::from_mode(0o700)).unwrap();
}

#[test]
fn verifies_all_six_64_bit_little_endian_targets_and_rejects_others() {
    let tools = Tools::discover();
    let fixture = Fixture::new();
    let rustc = tools.sysroot.join("bin/rustc");
    let deps_dir = fixture.path("deps");
    fs::create_dir(&deps_dir).unwrap();
    let mini_core_src = fixture.path("mini_core.rs");
    fs::write(
        &mini_core_src,
        "#![allow(internal_features)]\n#![feature(no_core, lang_items)]\n#![no_core]\n\
         #[lang = \"pointee_sized\"]\npub trait PointeeSized {}\n\
         #[lang = \"meta_sized\"]\npub trait MetaSized: PointeeSized {}\n\
         #[lang = \"sized\"]\npub trait Sized: MetaSized {}\n\
         #[lang = \"copy\"]\npub trait Copy: Sized {}\n",
    )
    .unwrap();
    fixture.write(
        "rust/lib.rs",
        "#![feature(no_core)]\n#![no_core]\nextern crate mini_core;\n\
         pub fn zero() -> u64 { 0 }\n",
    );

    for (idx, triple) in [
        "x86_64-unknown-linux-gnu",
        "aarch64-unknown-linux-gnu",
        "riscv64gc-unknown-linux-gnu",
        "x86_64-unknown-fuchsia",
        "aarch64-unknown-fuchsia",
        "riscv64gc-unknown-fuchsia",
    ]
    .into_iter()
    .enumerate()
    {
        let rel_rmeta = format!("deps/libmini_core_{idx}.rmeta");
        let out_rmeta = fixture.path(&rel_rmeta);
        assert!(
            Command::new(&rustc)
                .env("LD_LIBRARY_PATH", tools.sysroot.join("lib"))
                .args([
                    "--edition=2024",
                    "--crate-name=mini_core",
                    "--crate-type=lib",
                    &format!("--target={triple}"),
                    "--emit=metadata",
                    "-o",
                ])
                .arg(&out_rmeta)
                .arg(&mini_core_src)
                .status()
                .unwrap()
                .success(),
            "failed to compile mini_core for {triple}"
        );
        let mut req = fixture.request.clone();
        req["compilation"]["target"] = json!(triple);
        req["compilation"]["externs"] = json!([
            {"crate_name": "mini_core", "path": rel_rmeta}
        ]);
        let receipt = fixture.run(&tools, &format!("target-ok-{idx}"), &req);
        receipt.expect(0, "crate_verified", None);
        assert_eq!(receipt.value["configuration"]["target"], triple);
        assert_eq!(receipt.value["configuration"]["pointer_bits"], 64);
        assert_eq!(receipt.value["configuration"]["endian"], "little");
    }

    for (idx, bad_triple) in [
        "i686-unknown-linux-gnu",
        "s390x-unknown-linux-gnu",
        "wasm32-unknown-unknown",
        "x86_64-apple-darwin",
    ]
    .into_iter()
    .enumerate()
    {
        let mut req = fixture.request.clone();
        req["compilation"]["target"] = json!(bad_triple);
        fixture
            .run(&tools, &format!("target-bad-{idx}"), &req)
            .expect(1, "unsupported", Some("request"));
    }
}
