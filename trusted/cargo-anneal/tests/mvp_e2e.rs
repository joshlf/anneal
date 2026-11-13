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
        let cli = override_path("ANNEAL_MVP_CLI")
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_MVP_CLI");
        let capture = override_path("ANNEAL_MVP_CAPTURE")
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_MVP_CAPTURE",
        );
        let lean = override_path("ANNEAL_MVP_LEAN").unwrap_or_else(cargo_anneal::default_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_MVP_LEAN");
        let sysroot = override_path("ANNEAL_MVP_SYSROOT").unwrap_or_else(|| {
            let output = Command::new("rustup")
                .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
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
             theorem verify : CrateTheorem Captured.program Spec.specs := by",
        )
        .replace(
            concat!(
                "    · intro selected found value returned\n",
                "      have same : body = selected := Option.some.inj found\n",
                "      subst selected\n",
                "      exact (run_result_unique (runs []) returned).symm",
            ),
            "    · exact True.intro",
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
            "import Trusted.Mvp",
            "macro \"hiddenProperty\" : term => `(True)",
        ),
    );
    fixture.write(
        "lean/Spec.lean",
        lean_source(
            "import Trusted.Mvp\nimport Extra",
            "namespace Spec\ndef specs : Trusted.Mvp.Specs :=\n  ⟨fun _ _ => False, fun _ => hiddenProperty⟩\nend Spec",
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
    fixture
        .execute(
            "cargo-feature-free-library",
            tools
                .command()
                .arg("--manifest-path")
                .arg(&manifest)
                .arg("--proof-dir")
                .arg(fixture.path("lean")),
        )
        .expect(0, "crate_verified", None);

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
