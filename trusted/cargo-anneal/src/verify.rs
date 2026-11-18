// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bind one configured compilation to its canonical Lean verification claim.
//!
//! The proof package supplies specifications and proof terms. It cannot supply
//! the source model, captured subject or expected proposition. Those inputs are
//! staged independently and passed to the compiled-environment auditor.

use crate::compilers;
use cargo_anneal::{Checker, TargetAuditRequest, TargetBindings, TargetModule, TargetRole};
use clap::Args;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Instant;

// Generated resources keep installed and packaged builds independent of the
// source checkout. The explicit regeneration check binds these bytes to the
// canonical audited sources without running a build hook.
include!("bundled_resources.rs");

/// Arguments of the build-neutral verification command.
#[derive(Args)]
pub struct VerifyArgs {
    /// JSON compilation/proof request, with paths relative to its directory.
    #[arg(
        long,
        conflicts_with = "manifest_path",
        required_unless_present = "manifest_path"
    )]
    request: Option<PathBuf>,
    /// A feature-free library for the x86_64-unknown-linux-gnu scalar profile.
    #[arg(long, required_unless_present = "request")]
    manifest_path: Option<PathBuf>,
    /// Directory containing Spec.lean and Proof.lean, for the Cargo shortcut.
    #[arg(long, requires = "manifest_path")]
    proof_dir: Option<PathBuf>,
    /// Select a function by its compiler path; omit to require the whole crate.
    #[arg(long, requires = "manifest_path")]
    select: Vec<String>,
    /// Pinned capture driver; defaults to the installed bundle, then a sibling.
    #[arg(long)]
    capture: Option<PathBuf>,
    /// Pinned Lean executable; authenticated by the foundation lock.
    #[arg(long)]
    lean: Option<PathBuf>,
    /// Pinned compiler sysroot, for a separately installed capture driver.
    #[arg(long)]
    sysroot: Option<PathBuf>,
    /// Compiler executable that must report `--rustc-version`; the capture
    /// driver checks it against its linked compiler too. Without `--sysroot`,
    /// the distribution containing it supplies the sysroot.
    #[arg(long, value_name = "PATH", requires = "rustc_version")]
    rustc: Option<PathBuf>,
    /// Expected compiler of `--rustc` and the capture: a MIR dialect such as
    /// V2026_10_22_R7189d39d9, or the full 40-hex commit.
    #[arg(long, value_name = "ID", requires = "rustc")]
    rustc_version: Option<String>,
    /// New UTF-8 directory path for retained capture, sources and audit
    /// evidence.
    #[arg(long)]
    artifacts: Option<PathBuf>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    schema_version: u32,
    compilation: Compilation,
    scope: Scope,
    proof: Proof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Compilation {
    source_root: PathBuf,
    crate_root: PathBuf,
    crate_name: String,
    #[serde(default = "edition")]
    edition: String,
    #[serde(default = "target")]
    target: String,
    #[serde(default)]
    cfg: Vec<String>,
    source_files: Vec<PathBuf>,
}

fn edition() -> String {
    "2024".to_owned()
}

// This target belongs to the verification profile. Archive variants select
// executables for the host running Anneal; adding a host must not expand the
// semantic domain. Capture admits only this triple before compiler setup in
// `trusted/rustc-capture/src/main.rs` (`run`).
// A compatible custom sysroot can provide this target's libraries on another
// host. Keep library availability under the compiler's authority so neither a
// host ban nor a guessed standard-library inventory rejects that configuration.
fn target() -> String {
    "x86_64-unknown-linux-gnu".to_owned()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Scope {
    SelectedUnit { roots: Vec<String> },
    Crate,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Proof {
    source_root: PathBuf,
    #[serde(default = "spec_name")]
    specification: String,
    #[serde(default = "proof_name")]
    theorem: String,
    #[serde(default)]
    specification_module: Option<String>,
    #[serde(default)]
    theorem_module: Option<String>,
    sources: Vec<ProofSource>,
}

fn spec_name() -> String {
    "Spec.specs".to_owned()
}

fn proof_name() -> String {
    "Proof.verify".to_owned()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofSource {
    module: String,
    path: PathBuf,
    role: AuthoredRole,
}

/// Authored inputs cannot claim ownership of the model, captured program,
/// or expected proposition. Those roles would let a proof producer replace
/// the meaning of the obligation instead of proving it.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum AuthoredRole {
    Specification,
    Proof,
}

#[derive(Clone, Serialize)]
struct SourceIdentity {
    relative_path: PathBuf,
    sha256: String,
}

struct Error {
    status: &'static str,
    phase: &'static str,
    detail: String,
}

type Result<T> = std::result::Result<T, Error>;

fn error(status: &'static str, phase: &'static str, detail: impl ToString) -> Error {
    Error {
        status,
        phase,
        detail: detail.to_string(),
    }
}

fn io(phase: &'static str, failure: std::io::Error) -> Error {
    error("tool_failed", phase, failure)
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn identifier(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(cargo_anneal::is_lean_ident)
}

/// Verify that an already canonical tool executable is a regular file and
/// return its SHA-256 digest without opening FIFOs, directories, or devices.
fn regular_tool_digest(path: &Path, phase: &'static str) -> Result<String> {
    cargo_anneal::regular(path, phase).map_err(|e| error("tool_failed", phase, e.message))?;
    Ok(digest(&fs::read(path).map_err(|e| io(phase, e))?))
}

/// Authenticate the capture's compiler against the schema version and the
/// closed compiler table: the full commit selects the entry, the commit date
/// and both dialect fields must name that same entry, `rustc` and `sysroot`
/// must be non-empty UTF-8 strings, and the linked libraries' `version` text
/// must report that commit's nine-digit prefix. The dialect selects the
/// subject's syntax module and the canonical root, so a capture cannot pair
/// one compiler with another dialect's theorem.
fn authenticated_compiler(manifest: &Value) -> Option<&'static compilers::SupportedCompiler> {
    if manifest["schema_version"] != 2 {
        return None;
    }
    let compiler = compilers::by_commit(manifest["compiler"]["commit"].as_str()?)?;
    let non_empty = |field: &str| {
        manifest["compiler"][field]
            .as_str()
            .is_some_and(|value| !value.is_empty())
    };
    (manifest["compiler"]["commit_date"] == compiler.commit_date
        && manifest["compiler"]["mir_dialect"] == compiler.mir_dialect
        && manifest["mir_dialect"] == compiler.mir_dialect
        && non_empty("rustc")
        && non_empty("sysroot")
        && manifest["compiler"]["version"]
            .as_str()
            .is_some_and(|version| version.contains(&compiler.commit[..9])))
    .then_some(compiler)
}

/// A compiler declared by `--rustc-version` and confirmed from `--rustc`.
struct DeclaredCompiler {
    /// Original `--rustc` spelling, used if `rustc` resolves into a store blob
    /// beneath a symlinked `<root>/bin/rustc` distribution.
    given: PathBuf,
    /// Canonical `--rustc`, passed unchanged to the capture driver.
    rustc: PathBuf,
    /// Validated UTF-8 form of `rustc`, matched against `capture.json`.
    rustc_utf8: String,
    expected: &'static compilers::SupportedCompiler,
    /// Digest of the probed executable, rechecked when accepting the result.
    sha256: String,
}

/// Check the operator's compiler declaration before capture (boundary 1).
///
/// `--rustc-version` must name a supported compiler, and `--rustc` must
/// report exactly its commit and commit date. The capture driver then checks
/// the same executable against its linked compiler, and `run` checks the
/// compiler recorded in `capture.json` against this declaration. The probe
/// runs with a cleared environment, like capture, so ambient variables such
/// as `RUSTC_OVERRIDE_VERSION_STRING` or `LD_LIBRARY_PATH` cannot change the
/// report.
fn declared_compiler(given: &Path, id: &str) -> Result<DeclaredCompiler> {
    let expected = compilers::resolve(id).ok_or_else(|| {
        error(
            "unsupported",
            "compiler",
            format!(
                "unsupported --rustc-version {id:?}; use one of: {}",
                compilers::supported_list()
            ),
        )
    })?;
    if given.to_str().is_none() {
        return Err(error(
            "tool_failed",
            "compiler",
            "--rustc path must be UTF-8",
        ));
    }
    let rustc = fs::canonicalize(given).map_err(|e| {
        error(
            "tool_failed",
            "compiler",
            format!("cannot resolve --rustc {}: {e}", given.display()),
        )
    })?;
    let Some(rustc_utf8) = rustc.to_str().map(str::to_owned) else {
        return Err(error(
            "tool_failed",
            "compiler",
            "--rustc target path must be UTF-8",
        ));
    };
    let sha256 = regular_tool_digest(&rustc, "compiler")?;
    let output = Command::new(&rustc)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .args(["--version", "--verbose"])
        .output()
        .map_err(|e| io("compiler", e))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stderr = stderr.trim();
        let detail = if stderr.is_empty() {
            String::new()
        } else {
            format!(": {stderr}")
        };
        return Err(error(
            "tool_failed",
            "compiler",
            format!(
                "{} --version --verbose failed with {}{detail}",
                rustc.display(),
                output.status,
            ),
        ));
    }
    let text = String::from_utf8(output.stdout).map_err(|_| {
        error(
            "tool_failed",
            "compiler",
            format!(
                "{} --version --verbose printed non-UTF-8 text",
                rustc.display()
            ),
        )
    })?;
    let identity = compilers::CompilerIdentity::parse(&text).map_err(|e| {
        error(
            "tool_failed",
            "compiler",
            format!("{}: {e}", rustc.display()),
        )
    })?;
    if !identity.is(expected) {
        return Err(error(
            "tool_failed",
            "compiler",
            format!(
                "--rustc {} reports commit-hash {} and commit-date {}, but --rustc-version {id} is {} (commit-hash {}, commit-date {})",
                rustc.display(),
                identity.commit,
                identity.commit_date,
                expected.mir_dialect,
                expected.commit,
                expected.commit_date
            ),
        ));
    }
    Ok(DeclaredCompiler {
        given: given.to_path_buf(),
        rustc,
        rustc_utf8,
        expected,
        sha256,
    })
}

/// Return the root of the Rust distribution containing `canonical_rustc` (or
/// the symlink-farm `<root>/bin/rustc` at `given`).
///
/// A distribution keeps its compiler at `<root>/bin/rustc` and its libraries
/// under `<root>/lib/rustlib`. Checking `canonical_rustc` first resolves an
/// external alias such as `/tmp/rustc-alias -> <root>/bin/rustc` to `<root>`,
/// and prefers `<real>/bin/rustc`'s distribution over a stale
/// `/usr/lib/rustlib` when `/usr/bin/rustc` links into `<real>`. Falling back
/// to `given` handles symlink-joined distributions (such as Nix `symlinkJoin`
/// or Bazel sandboxes) whose `<root>/bin/rustc` links to a standalone store
/// blob while `<root>` supplies `lib/rustlib`. A standalone wrapper outside
/// `<root>/bin/rustc` needs an explicit `--sysroot`.
fn distribution_sysroot(given: &Path, canonical_rustc: &Path) -> Result<PathBuf> {
    let valid_root = |root: &Path| {
        root.join("lib/rustlib").is_dir()
            && fs::canonicalize(root.join("bin/rustc"))
                .is_ok_and(|path| path == canonical_rustc)
    };
    if let Some(root) = canonical_rustc
        .parent()
        .filter(|bin| bin.file_name() == Some("bin".as_ref()))
        .and_then(Path::parent)
        .filter(|root| valid_root(root))
    {
        return Ok(root.to_path_buf());
    }
    if given.file_name() == Some("rustc".as_ref()) {
        let given_bin = match given.parent() {
            Some(parent) if parent.as_os_str().is_empty() => std::env::current_dir().ok(),
            Some(parent) => fs::canonicalize(parent).ok(),
            None => None,
        };
        if let Some(root) = given_bin
            .as_deref()
            .filter(|bin| bin.file_name() == Some("bin".as_ref()))
            .and_then(Path::parent)
            .filter(|root| valid_root(root))
        {
            return Ok(root.to_path_buf());
        }
    }
    Err(error(
        "tool_failed",
        "compiler",
        format!(
            "--rustc {} is not bin/rustc of a Rust distribution; pass --sysroot",
            canonical_rustc.display()
        ),
    ))
}

/// Require the bundled model to contain the authenticated dialect's syntax
/// module and canonical `MirSemantics` roots (boundary 2).
///
/// `Captured.lean` imports `Trusted.Rustc.<dialect>.MirAst`, and
/// `Expected.lean` states `Trusted.MirSemantics.<dialect>.*Theorem` over it.
/// Without both bundled definitions, this CLI cannot check that dialect at all;
/// refuse it before staging any Lean source rather than fail inside proof
/// checking.
fn require_dialect_syntax(bundle: &[(&str, &str)], mir_dialect: &str) -> Result<()> {
    let syntax = format!("trusted/lean/Trusted/Rustc/{mir_dialect}/MirAst.lean");
    if !bundle.iter().any(|(relative, _)| *relative == syntax) {
        return Err(error(
            "tool_failed",
            "model",
            format!(
                "the bundled model lacks {syntax}; MIR dialect {mir_dialect} cannot be checked"
            ),
        ));
    }
    let has_semantics_roots = bundle
        .iter()
        .find(|(relative, _)| *relative == "trusted/lean/Trusted/MirSemantics.lean")
        .is_some_and(|(_, text)| text.contains(&format!("\nnamespace {mir_dialect}\n")));
    if !has_semantics_roots {
        return Err(error(
            "tool_failed",
            "model",
            format!(
                "the bundled Trusted.MirSemantics lacks namespace {mir_dialect}; MIR dialect {mir_dialect} cannot be checked"
            ),
        ));
    }
    Ok(())
}

/// Require `Captured.lean` to carry the exact fixed header for the
/// authenticated dialect's syntax module (boundary 2).
///
/// Capture renders a fixed header: leading `--` copyright comments and blank
/// lines, `prelude`, one `import` of `Trusted.Rustc.<dialect>.MirAst`, and
/// `namespace Captured` (where Lean's module header parser terminates). Dialect
/// modules may re-export one another's definitions, and a line filter looking
/// only for a leading `import` token would miss `public`/`private`/`meta`
/// imports or inline `/- ... -/` block comments, so every header line before
/// `namespace Captured` must match this skeleton.
fn require_captured_syntax(captured: &str, mir_dialect: &str) -> Result<()> {
    let expected = format!("import Trusted.Rustc.{mir_dialect}.MirAst");
    let mut lines = captured
        .lines()
        .skip_while(|line| line.is_empty() || line.starts_with("--"));
    let prelude = lines.next();
    let import = lines.next();
    let after_import = lines.find(|line| !line.is_empty());
    if prelude == Some("prelude")
        && import == Some(expected.as_str())
        && after_import == Some("namespace Captured")
    {
        return Ok(());
    }
    let imports: Vec<&str> = captured
        .lines()
        .filter(|line| line.split_whitespace().next() == Some("import"))
        .collect();
    Err(error(
        "tool_failed",
        "capture",
        format!(
            "Captured.lean lacks the exact {mir_dialect} header (imports {imports:?}), \
             but the capture's compiler has MIR dialect {mir_dialect}"
        ),
    ))
}

/// Detect whether a Lean source file's module header `import` declarations
/// reference `Anneal.PureLift` or any `Anneal.PureLift.*` submodule, ignoring
/// occurrences inside `--` line comments, nested `/- ... -/` block comments,
/// and any tokens after the Lean 4 module header ends.
fn source_imports_pure_lift(bytes: &[u8]) -> bool {
    let Ok(text) = std::str::from_utf8(bytes) else {
        return false;
    };
    let raw = text.as_bytes();
    let mut stripped = String::with_capacity(text.len());
    let mut i = 0;
    let mut block_depth = 0usize;
    while i < raw.len() {
        if block_depth > 0 {
            if i + 1 < raw.len() && raw[i] == b'/' && raw[i + 1] == b'-' {
                block_depth += 1;
                i += 2;
            } else if i + 1 < raw.len() && raw[i] == b'-' && raw[i + 1] == b'/' {
                block_depth -= 1;
                if block_depth == 0 {
                    stripped.push(' ');
                }
                i += 2;
            } else {
                i += 1;
            }
        } else if i + 1 < raw.len() && raw[i] == b'/' && raw[i + 1] == b'-' {
            block_depth = 1;
            i += 2;
        } else if i + 1 < raw.len() && raw[i] == b'-' && raw[i + 1] == b'-' {
            i += 2;
            while i < raw.len() && raw[i] != b'\n' {
                i += 1;
            }
            stripped.push('\n');
        } else if i + 2 < raw.len()
            && raw[i] == b'\''
            && raw[i + 1] == b'"'
            && raw[i + 2] == b'\''
        {
            stripped.push(' ');
            i += 3;
        } else if i + 3 < raw.len()
            && raw[i] == b'\''
            && raw[i + 1] == b'\\'
            && raw[i + 2] == b'"'
            && raw[i + 3] == b'\''
        {
            stripped.push(' ');
            i += 4;
        } else if raw[i] == b'"' {
            stripped.push(' ');
            i += 1;
            while i < raw.len() && raw[i] != b'"' {
                if raw[i] == b'\\' && i + 1 < raw.len() {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            if i < raw.len() {
                i += 1;
            }
        } else {
            let ch = text[i..].chars().next().expect("valid UTF-8 char boundary");
            stripped.push(ch);
            i += ch.len_utf8();
        }
    }
    let mut tokens = stripped.split_whitespace().peekable();
    while let Some(tok) = tokens.next() {
        match tok {
            "module" | "prelude" | "public" | "private" | "meta" => continue,
            "import" => {
                if tokens.peek() == Some(&"all") {
                    tokens.next();
                }
                let Some(module) = tokens.next() else {
                    break;
                };
                let normalized: String = module
                    .chars()
                    .filter(|&c| c != '«' && c != '»')
                    .collect();
                if normalized == "Anneal.PureLift"
                    || normalized.starts_with("Anneal.PureLift.")
                {
                    return true;
                }
            }
            // In Lean 4 (`Lean.Parser.Module.header`), `import` clauses cannot
            // appear after the first non-header command token.
            _ => break,
        }
    }
    false
}

fn module_of(name: &str) -> Result<String> {
    if !identifier(name) || !name.contains('.') {
        return Err(error(
            "unsupported",
            "request",
            "expected a qualified Lean declaration name",
        ));
    }
    Ok(name.rsplit_once('.').unwrap().0.to_owned())
}

/// Require a declared regular file beneath an already canonical root.
///
/// Relative paths cannot escape the staging namespace. Canonical equality
/// also rejects symlink traversal; adjacent compiled Lean files are never read.
fn declared_file(root: &Path, relative: &Path) -> Result<PathBuf> {
    if relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(error(
            "unsupported",
            "inputs",
            "input paths must be clean relative paths",
        ));
    }
    let path = root.join(relative);
    let meta = fs::symlink_metadata(&path).map_err(|e| io("inputs", e))?;
    if !meta.is_file()
        || meta.file_type().is_symlink()
        || fs::canonicalize(&path).map_err(|e| io("inputs", e))? != path
    {
        return Err(error(
            "unsupported",
            "inputs",
            format!("not a declared regular file: {}", path.display()),
        ));
    }
    Ok(path)
}

fn root(base: &Path, path: &Path) -> Result<PathBuf> {
    fs::canonicalize(base.join(path)).map_err(|e| io("inputs", e))
}

fn write(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| io("staging", e))?;
    }
    fs::write(path, bytes).map_err(|e| io("staging", e))
}

fn encoded<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec_pretty(value).map_err(|e| error("tool_failed", "json", e))
}

fn reject_compiler_overrides(dir: &Path) -> Result<()> {
    for forbidden in [
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        if dir.join(forbidden).exists() {
            return Err(error(
                "unsupported",
                "cargo",
                "compiler overrides need an explicit configured compilation",
            ));
        }
    }
    Ok(())
}

// Cargo is an input-discovery shortcut, not a second verification profile.
// Reject configurations this adapter cannot reproduce before building the
// same explicit request consumed by the build-neutral path.
fn cargo_request(args: &VerifyArgs, manifest: &Path) -> Result<(Request, PathBuf)> {
    let manifest = fs::canonicalize(manifest).map_err(|e| io("cargo", e))?;
    let source_root = manifest
        .parent()
        .ok_or_else(|| error("unsupported", "cargo", "manifest path has no parent directory"))?
        .to_path_buf();
    reject_compiler_overrides(&source_root)?;
    let probe_cwd = tempfile::tempdir().map_err(|e| io("cargo", e))?;
    let mut cargo = Command::new("cargo");
    cargo.current_dir(probe_cwd.path()).env_clear();
    for key in ["PATH", "HOME", "CARGO_HOME", "RUSTUP_HOME", "TMPDIR"] {
        if let Some(value) = std::env::var_os(key) {
            cargo.env(key, value);
        }
    }
    let output = cargo
        .args([
            "metadata",
            "--format-version=1",
            "--no-deps",
            "--offline",
            "--manifest-path",
        ])
        .arg(&manifest)
        .output()
        .map_err(|e| io("cargo", e))?;
    if !output.status.success() {
        return Err(error(
            "compiler_failed",
            "cargo",
            String::from_utf8_lossy(&output.stderr),
        ));
    }
    let metadata: Value =
        serde_json::from_slice(&output.stdout).map_err(|e| error("tool_failed", "cargo", e))?;
    let package = metadata["packages"]
        .as_array()
        .and_then(|packages| {
            packages
                .iter()
                .find(|p| p["manifest_path"].as_str() == manifest.to_str())
        })
        .ok_or_else(|| {
            error(
                "unsupported",
                "cargo",
                "choose a package Cargo.toml, not a virtual workspace",
            )
        })?;
    if package["features"]
        .as_object()
        .is_none_or(|features| !features.is_empty())
    {
        return Err(error(
            "unsupported",
            "cargo",
            "Cargo features require an explicit configured compilation request",
        ));
    }
    if package["dependencies"]
        .as_array()
        .is_none_or(|deps| !deps.is_empty())
    {
        return Err(error(
            "unsupported",
            "cargo",
            "Cargo shortcut requires a dependency-free library; use an explicit compilation request",
        ));
    }
    let targets = package["targets"]
        .as_array()
        .ok_or_else(|| error("tool_failed", "cargo", "missing Cargo targets"))?;
    if targets.iter().any(|t| {
        t["kind"]
            .as_array()
            .is_some_and(|ks| ks.iter().any(|k| k == "custom-build" || k == "proc-macro"))
    }) {
        return Err(error(
            "unsupported",
            "cargo",
            "build scripts and procedural macros need an explicit configured compilation",
        ));
    }
    let library = targets
        .iter()
        .find(|t| {
            t["kind"]
                .as_array()
                .is_some_and(|ks| ks.iter().any(|k| k == "lib"))
        })
        .ok_or_else(|| {
            error(
                "unsupported",
                "cargo",
                "Cargo shortcut requires a library target",
            )
        })?;
    let workspace_root = metadata["workspace_root"]
        .as_str()
        .and_then(|root| fs::canonicalize(root).ok());
    for ancestor in source_root.ancestors() {
        reject_compiler_overrides(ancestor)?;
        if workspace_root.as_deref() == Some(ancestor) {
            break;
        }
    }
    let crate_root = Path::new(library["src_path"].as_str().unwrap_or_default())
        .strip_prefix(&source_root)
        .map_err(|_| error("unsupported", "cargo", "library root escapes package"))?
        .to_path_buf();
    // This shortcut declares a namespace of .rs files. Other compiler inputs
    // require an explicit request: importing every package file would also
    // stage unrelated data, proof packages and build outputs.
    let mut source_files = Vec::new();
    for entry in walkdir::WalkDir::new(&source_root)
        .follow_links(false)
        .into_iter()
        .filter_entry(|e| {
            e.depth() == 0
                || (!e.file_name().to_string_lossy().starts_with('.') && e.file_name() != "target")
        })
    {
        let entry = entry.map_err(|e| error("tool_failed", "cargo", e))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "rs") {
            source_files.push(
                entry
                    .path()
                    .strip_prefix(&source_root)
                    .unwrap()
                    .to_path_buf(),
            );
        }
    }
    source_files.sort();
    let proof_root = fs::canonicalize(args.proof_dir.as_ref().ok_or_else(|| {
        error(
            "unsupported",
            "request",
            "--proof-dir is required with --manifest-path",
        )
    })?)
    .map_err(|e| io("proof", e))?;
    let mut sources = Vec::new();
    for entry in walkdir::WalkDir::new(&proof_root)
        .follow_links(false)
        .into_iter()
        .filter_entry(|e| {
            e.depth() == 0 || !e.file_name().to_string_lossy().starts_with('.')
        })
    {
        let entry = entry.map_err(|e| error("tool_failed", "proof", e))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "lean") {
            let path = entry
                .path()
                .strip_prefix(&proof_root)
                .unwrap()
                .to_path_buf();
            let module = path
                .with_extension("")
                .to_string_lossy()
                .replace(std::path::MAIN_SEPARATOR, ".");
            sources.push(ProofSource {
                role: if module == "Spec" || module.starts_with("Spec.") {
                    AuthoredRole::Specification
                } else {
                    AuthoredRole::Proof
                },
                module,
                path,
            });
        }
    }
    sources.sort_by(|a, b| a.module.cmp(&b.module));
    let scope = if args.select.is_empty() {
        Scope::Crate
    } else {
        Scope::SelectedUnit {
            roots: args.select.clone(),
        }
    };
    Ok((
        Request {
            schema_version: 1,
            compilation: Compilation {
                source_root,
                crate_root,
                crate_name: library["name"].as_str().unwrap_or_default().to_owned(),
                edition: library["edition"].as_str().unwrap_or("2024").to_owned(),
                target: target(),
                cfg: Vec::new(),
                source_files,
            },
            scope,
            proof: Proof {
                source_root: proof_root,
                specification: spec_name(),
                theorem: proof_name(),
                specification_module: None,
                theorem_module: None,
                sources,
            },
        },
        manifest.parent().unwrap().to_path_buf(),
    ))
}

fn load_request(args: &VerifyArgs) -> Result<(Request, PathBuf)> {
    if let Some(path) = &args.request {
        let path = fs::canonicalize(path).map_err(|e| io("request", e))?;
        let bytes = fs::read(&path).map_err(|e| io("request", e))?;
        let request: Request =
            serde_json::from_slice(&bytes).map_err(|e| error("unsupported", "request", e))?;
        Ok((request, path.parent().unwrap().to_path_buf()))
    } else {
        cargo_request(args, args.manifest_path.as_ref().unwrap())
    }
}

fn run(args: &VerifyArgs, work: &Path) -> Result<Value> {
    let start = Instant::now();
    let (mut request, base) = load_request(args)?;
    if request.schema_version != 1 || request.compilation.source_files.is_empty() {
        return Err(error(
            "unsupported",
            "request",
            "unsupported or empty compilation request",
        ));
    }
    request.compilation.cfg.sort();
    request.compilation.cfg.dedup();
    if let Scope::SelectedUnit { roots } = &mut request.scope {
        roots.sort();
        roots.dedup();
    }
    if !identifier(&request.proof.specification) || !identifier(&request.proof.theorem) {
        return Err(error(
            "unsupported",
            "request",
            "invalid Lean declaration identifier",
        ));
    }
    let spec_module = match &request.proof.specification_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => {
            return Err(error(
                "unsupported",
                "request",
                "invalid specification module",
            ));
        }
        None => module_of(&request.proof.specification)?,
    };
    let theorem_module = match &request.proof.theorem_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => return Err(error("unsupported", "request", "invalid theorem module")),
        None => module_of(&request.proof.theorem)?,
    };
    // Selection roots and cfg entries have set semantics here. Hash their
    // normalized form so spelling order and duplicates cannot give the same
    // configured subject different request identities.
    let request_bytes = encoded(&request)?;
    let request_sha256 = digest(&request_bytes);
    write(&work.join("request.json"), &request_bytes)?;

    // Rust and Lean consume private snapshots, not paths they can resolve
    // back into the caller's live checkout. Record the original bytes too:
    // the final identity check must still bind the receipt to those inputs.
    let source_root = root(&base, &request.compilation.source_root)?;
    let rust_stage = work.join("rust");
    fs::create_dir_all(&rust_stage).map_err(|e| io("staging", e))?;
    let mut originals = Vec::new();
    let mut sources = Vec::new();
    let mut paths = BTreeSet::new();
    for relative in &request.compilation.source_files {
        if !paths.insert(relative.clone()) {
            return Err(error("unsupported", "inputs", "duplicate source input"));
        }
        let original = declared_file(&source_root, relative)?;
        let bytes = fs::read(&original).map_err(|e| io("inputs", e))?;
        let sha256 = digest(&bytes);
        write(&rust_stage.join(relative), &bytes)?;
        originals.push((original, sha256.clone()));
        sources.push(SourceIdentity {
            relative_path: relative.clone(),
            sha256,
        });
    }
    if !paths.contains(&request.compilation.crate_root) {
        return Err(error(
            "unsupported",
            "inputs",
            "crate_root is not a declared source",
        ));
    }
    // The invocation owns tool selection; target requests cannot name a
    // compiler executable. Adapter correctness is a stated TCB assumption.
    // Its digest identifies the selected build and detects later changes.
    // Prefer the installed bundle so its capture adapter and default Rust
    // sysroot stay paired. Development tools remain explicit operator choices;
    // a sibling is the fallback only when no installed bundle is resolved.
    let installed = crate::setup::installed();
    if let Some(given_capture) = &args.capture
        && given_capture.to_str().is_none()
    {
        return Err(error(
            "tool_failed",
            "capture-tool",
            "--capture path must be UTF-8",
        ));
    }
    let capture = args
        .capture
        .clone()
        .or_else(|| {
            installed
                .as_ref()
                .map(|root| root.join("bin/anneal-rustc-capture"))
        })
        .unwrap_or_else(|| {
            std::env::current_exe()
                .unwrap_or_default()
                .with_file_name("anneal-rustc-capture")
        });
    let capture = fs::canonicalize(capture).map_err(|e| io("capture-tool", e))?;
    if capture.to_str().is_none() {
        return Err(error(
            "tool_failed",
            "capture-tool",
            "capture executable path must be UTF-8",
        ));
    }
    let capture_binary_sha256 = regular_tool_digest(&capture, "capture-tool")?;
    // Boundary 1, before capture: a compiler declaration must hold for the
    // `--rustc` executable itself, and the bundled model must already support
    // its dialect before invoking capture. clap accepts both options together.
    let declared = match (&args.rustc, &args.rustc_version) {
        (Some(rustc), Some(id)) => {
            let declared = declared_compiler(rustc, id)?;
            require_dialect_syntax(BUNDLE, declared.expected.mir_dialect)?;
            Some(declared)
        }
        _ => None,
    };
    let capture_dir = work.join("capture");
    // Capture reserves and publishes a new output directory itself; precreating
    // it here would violate its create-only publication contract.
    // Do not let a target crate's ambient compiler wrappers or search paths
    // enter the capture process. The only added library path below comes
    // from the operator-selected compiler installation.
    let mut command = Command::new(&capture);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .args(["capture", "--crate-root"])
        .arg(rust_stage.join(&request.compilation.crate_root))
        .args([
            "--crate-name",
            &request.compilation.crate_name,
            "--edition",
            &request.compilation.edition,
            "--target",
            &request.compilation.target,
            "--out-dir",
        ])
        .arg(&capture_dir)
        .current_dir(&rust_stage);
    if let Some(given_sysroot) = &args.sysroot
        && given_sysroot.to_str().is_none()
    {
        return Err(error(
            "tool_failed",
            "sysroot",
            "--sysroot path must be UTF-8",
        ));
    }
    // An explicit sysroot wins. A declared compiler otherwise brings its own
    // distribution's libraries, which an installed bundle need not match.
    let selected_sysroot = match (&args.sysroot, &declared) {
        (Some(sysroot), _) => Some(sysroot.clone()),
        (None, Some(declared)) => Some(distribution_sysroot(&declared.given, &declared.rustc)?),
        (None, None) => installed.as_ref().map(|root| root.join("rust")),
    };
    let selected_sysroot_utf8 = if let Some(sysroot) = &selected_sysroot {
        let sysroot = fs::canonicalize(sysroot).map_err(|e| io("sysroot", e))?;
        let Some(sysroot_utf8) = sysroot.to_str().map(str::to_owned) else {
            let detail = if args.sysroot.is_some() {
                "--sysroot target path must be UTF-8"
            } else {
                "sysroot path must be UTF-8"
            };
            return Err(error("tool_failed", "sysroot", detail));
        };
        // The library search path belongs to the explicitly selected compiler
        // installation, never to a target crate's ambient environment.
        command.env("LD_LIBRARY_PATH", sysroot.join("lib"));
        command.arg("--sysroot").arg(sysroot);
        Some(sysroot_utf8)
    } else {
        None
    };
    if let Some(declared) = &declared {
        command.arg("--rustc").arg(&declared.rustc);
    }
    match &request.scope {
        Scope::Crate => {
            command.args(["--scope", "crate"]);
        }
        Scope::SelectedUnit { roots } => {
            if roots.is_empty() {
                return Err(error("unsupported", "request", "empty selected scope"));
            }
            for name in roots {
                command.arg("--select").arg(name);
            }
        }
    }
    // Preserve each cfg as option data through capture's parser. Capture must
    // use the joined form again when rebuilding compiler argv: the pinned
    // response-file expansion gate is "arg.strip_prefix('@')", before --cfg
    // parsing. Extracting the String must not restore a standalone @file arg.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L14-L32
    for cfg in &request.compilation.cfg {
        command.arg(format!("--cfg={cfg}"));
    }
    for source in &sources {
        command
            .arg("--source-file")
            .arg(rust_stage.join(&source.relative_path));
    }
    let capture_start = Instant::now();
    let output = command.output().map_err(|e| io("capture", e))?;
    write(&work.join("capture.stdout"), &output.stdout)?;
    write(&work.join("capture.stderr"), &output.stderr)?;
    if !output.status.success() {
        let envelope: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
        let status = match envelope["status"].as_str() {
            Some("unsupported") => "unsupported",
            Some("compiler_failed") => "compiler_failed",
            _ => "tool_failed",
        };
        let detail = if envelope.is_object() {
            envelope.to_string()
        } else {
            String::from_utf8_lossy(&output.stderr).into_owned()
        };
        return Err(error(status, "capture", detail));
    }
    let capture_ms = capture_start.elapsed().as_millis();
    let capture_bytes = fs::read(capture_dir.join("capture.json")).map_err(|e| io("capture", e))?;
    let manifest: Value =
        serde_json::from_slice(&capture_bytes).map_err(|e| error("tool_failed", "capture", e))?;
    // Capture schema 2 binds unsafe caller requirements to source identities.
    // An old program without that required Body field belongs to another model
    // ABI; reject it before compiling proofs. Request schema 1 is independent.
    // The commit, commit date, and both dialect fields must name one supported
    // compiler; a capture cannot select another dialect's syntax or root.
    let Some(compiler) = authenticated_compiler(&manifest) else {
        return Err(error(
            "tool_failed",
            "capture",
            "unexpected capture schema or compiler",
        ));
    };
    let mir_dialect = compiler.mir_dialect;
    // Boundary 1, after capture: the capture must report the declared compiler,
    // the exact executable checked before capture, and any selected sysroot.
    if let Some(declared) = &declared
        && (compiler != declared.expected
            || manifest["compiler"]["rustc"].as_str() != Some(declared.rustc_utf8.as_str()))
    {
        return Err(error(
            "tool_failed",
            "capture",
            format!(
                "capture reports compiler {} with rustc {}, but --rustc-version declares {} and --rustc is {}",
                compiler.mir_dialect,
                manifest["compiler"]["rustc"],
                declared.expected.mir_dialect,
                declared.rustc_utf8
            ),
        ));
    }
    if let Some(expected_sysroot) = &selected_sysroot_utf8
        && manifest["compiler"]["sysroot"].as_str() != Some(expected_sysroot.as_str())
    {
        return Err(error(
            "tool_failed",
            "capture",
            format!(
                "capture reports sysroot {}, but verification selected {expected_sysroot}",
                manifest["compiler"]["sysroot"],
            ),
        ));
    }
    // Boundary 2: the rendered subject must use the same dialect's syntax.
    let captured_lean = capture_dir.join("Captured.lean");
    let captured_bytes = fs::read(&captured_lean).map_err(|e| io("capture", e))?;
    let captured_text =
        std::str::from_utf8(&captured_bytes).map_err(|e| error("tool_failed", "capture", e))?;
    require_captured_syntax(captured_text, mir_dialect)?;
    // Authenticate configuration and scope before compiling any authored
    // Lean. A valid theorem about another target or a narrower selection
    // cannot satisfy this request.
    let (scope_kind, program_scope, requested_roots) = match &request.scope {
        Scope::Crate => ("crate", "crate", Vec::new()),
        Scope::SelectedUnit { roots } => ("selected_unit", "unit", roots.clone()),
    };
    if manifest["scope"]["kind"] != scope_kind
        || manifest["scope"]["roots"] != json!(requested_roots)
        || manifest["program"]["scope"] != program_scope
        || manifest["configuration"]["crate_name"] != request.compilation.crate_name
        || manifest["configuration"]["target"] != request.compilation.target
        || manifest["configuration"]["edition"] != request.compilation.edition
        || manifest["configuration"]["cfg"] != json!(request.compilation.cfg)
    {
        return Err(error(
            "tool_failed",
            "capture",
            "capture differs from the requested compilation or scope",
        ));
    }
    // Every observed compiler read must match a staged, declared input.
    // Unused declared files remain in the receipt identity; they need not
    // become compiler reads merely because the request staged them.
    let source_by_path: BTreeMap<_, _> = sources
        .iter()
        .map(|s| (rust_stage.join(&s.relative_path), &s.sha256))
        .collect();
    for source in manifest["source_files"].as_array().ok_or_else(|| {
        error(
            "tool_failed",
            "capture",
            "missing observed source inventory",
        )
    })? {
        let path = PathBuf::from(source["path"].as_str().unwrap_or_default());
        let Some(expected) = source_by_path.get(&path) else {
            return Err(error(
                "tool_failed",
                "capture",
                "compiler read an undeclared source",
            ));
        };
        if source["sha256"].as_str() != Some(expected.as_str()) {
            return Err(error(
                "tool_failed",
                "capture",
                "compiler read different source bytes",
            ));
        }
    }
    let capture_sha256 = digest(&capture_bytes);

    // Boundary 2: refuse a dialect this CLI's model cannot express before
    // staging any Lean source.
    require_dialect_syntax(BUNDLE, mir_dialect)?;
    let bundle = work.join("anneal");
    let mut modules = Vec::new();
    let mut bundled_theory_modules = Vec::new();
    let mut model_identity = Vec::new();
    // Installed theory remains proof code even though it ships with the
    // model. Only primitive trusted modules may determine the canonical
    // proposition; packaging must not promote proof helpers into its TCB.
    for (relative, text) in BUNDLE {
        let path = bundle.join(relative);
        write(&path, text.as_bytes())?;
        model_identity.push((*relative, digest(text.as_bytes())));
        if relative.ends_with(".lean") && relative.starts_with("trusted/lean/") {
            modules.push(TargetModule {
                module: relative
                    .trim_start_matches("trusted/lean/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: path,
                expected_sha256: digest(text.as_bytes()),
                role: TargetRole::Model,
            });
        } else if relative.ends_with(".lean") && relative.starts_with("theory/") {
            bundled_theory_modules.push(TargetModule {
                module: relative
                    .trim_start_matches("theory/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: path,
                expected_sha256: digest(text.as_bytes()),
                role: TargetRole::Proof,
            });
        }
    }
    let model_manifest_sha256 = digest(&encoded(&model_identity)?);
    // Stage exactly the bytes whose syntax module was checked above.
    modules.push(TargetModule {
        module: "Captured".to_owned(),
        expected_sha256: digest(&captured_bytes),
        source: captured_lean,
        role: TargetRole::Capture,
    });

    // Module names choose destinations in the private stage. Reserve the
    // runner-owned names before writing anything so authored files cannot
    // shadow the model, captured subject, or generated expectation.
    let proof_root = root(&base, &request.proof.source_root)?;
    let mut module_names: BTreeSet<_> = modules
        .iter()
        .chain(bundled_theory_modules.iter())
        .map(|m| m.module.clone())
        .collect();
    let mut spec_identity = Vec::new();
    let mut uses_pure_lift = false;
    for input in &request.proof.sources {
        if !identifier(&input.module)
            || ["Expected", "Captured", "Trusted", "Anneal"].contains(&input.module.as_str())
            || input.module.starts_with("Trusted.")
            || input.module.starts_with("Anneal.")
            || !module_names.insert(input.module.clone())
        {
            return Err(error(
                "unsupported",
                "proof",
                "invalid, duplicate or reserved proof module",
            ));
        }
        let original = declared_file(&proof_root, &input.path)?;
        let bytes = fs::read(&original).map_err(|e| io("proof", e))?;
        if source_imports_pure_lift(&bytes) {
            uses_pure_lift = true;
        }
        let sha256 = digest(&bytes);
        originals.push((original, sha256.clone()));
        let source = work
            .join("authored")
            .join(input.module.replace('.', "/"))
            .with_extension("lean");
        write(&source, &bytes)?;
        let role = match input.role {
            AuthoredRole::Specification => {
                spec_identity.push((input.module.clone(), sha256.clone()));
                TargetRole::Specification
            }
            AuthoredRole::Proof => TargetRole::Proof,
        };
        modules.push(TargetModule {
            module: input.module.clone(),
            source,
            expected_sha256: sha256,
            role,
        });
    }
    for theory_mod in bundled_theory_modules {
        if theory_mod.module == "Anneal.MirWp"
            || (uses_pure_lift
                && (theory_mod.module == "Anneal.PureLift"
                    || theory_mod.module.starts_with("Anneal.PureLift.")))
        {
            modules.push(theory_mod);
        }
    }
    if !modules
        .iter()
        .any(|m| m.module == spec_module && matches!(m.role, TargetRole::Specification))
        || !modules
            .iter()
            .any(|m| m.module == theorem_module && matches!(m.role, TargetRole::Proof))
    {
        return Err(error(
            "unsupported",
            "proof",
            "specification and theorem must have their declared source roles",
        ));
    }
    // Keep the reviewed specification identity separate from ordinary
    // proof edits. The auditor also checks actual compiled dependencies,
    // so a helper that changes a specification's meaning needs its role.
    let specification_manifest_sha256 = digest(&encoded(&spec_identity)?);
    let root_name = match request.scope {
        Scope::Crate => "CrateTheorem",
        Scope::SelectedUnit { .. } => "UnitTheorem",
    };
    // Only validated declaration identifiers enter this fixed template. The
    // authored proof package never supplies an expected proposition or model.
    let header = "-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n";
    let expected = format!(
        "{header}prelude\nimport Trusted.MirSemantics\nimport Captured\nimport {spec_module}\n\nnamespace Expected\ndef claim : Prop := _root_.Trusted.MirSemantics.{mir_dialect}.{root_name} (_root_.Trusted.MirSemantics.{mir_dialect}.Crate.mk _root_.Captured.program _root_.{})\nend Expected\n",
        request.proof.specification
    );
    let expected_path = work.join("generated/Expected.lean");
    write(&expected_path, expected.as_bytes())?;
    modules.push(TargetModule {
        module: "Expected".to_owned(),
        source: expected_path,
        expected_sha256: digest(expected.as_bytes()),
        role: TargetRole::Expected,
    });
    let audit_request = TargetAuditRequest {
        modules,
        theorem_module,
        theorem_name: request.proof.theorem.clone(),
        expected_module: "Expected".to_owned(),
        expected_declaration: "Expected.claim".to_owned(),
        canonical_root: format!("Trusted.MirSemantics.{mir_dialect}.{root_name}"),
        subject_declaration: "Captured.program".to_owned(),
        specification_declaration: request.proof.specification.clone(),
        bindings: TargetBindings {
            request_sha256: request_sha256.clone(),
            capture_sha256: capture_sha256.clone(),
            model_manifest_sha256: model_manifest_sha256.clone(),
            specification_manifest_sha256: specification_manifest_sha256.clone(),
        },
    };
    write(&work.join("audit-request.json"), &encoded(&audit_request)?)?;
    let proof_start = Instant::now();
    // Authored elaboration is not acceptance. The inspector must replay
    // the exact closed root and enforce origin roles before a receipt can
    // report verification success. Operational failures stay distinct from
    // a successfully executed checker rejecting a proof.
    let mut checker = Checker::new(&bundle, args.lean.as_deref()).map_err(|e| io("audit", e))?;
    let audit = checker.run_target(&audit_request).map_err(|e| {
        error(
            if e.code == 1 {
                "proof_failed"
            } else {
                "tool_failed"
            },
            "audit",
            e.to_string(),
        )
    })?;
    let proof_ms = proof_start.elapsed().as_millis();
    // Snapshot identity is checked again at the accepting boundary. Logical
    // type equality cannot authenticate unused source or configuration hashes.
    for (path, expected) in &originals {
        if digest(&fs::read(path).map_err(|e| io("binding", e))?) != *expected {
            return Err(error(
                "tool_failed",
                "binding",
                "an input changed during verification",
            ));
        }
    }
    if regular_tool_digest(&capture, "binding")? != capture_binary_sha256 {
        return Err(error(
            "tool_failed",
            "binding",
            "capture executable changed during verification",
        ));
    }
    if let Some(declared) = &declared
        && regular_tool_digest(&declared.rustc, "binding")? != declared.sha256
    {
        return Err(error(
            "tool_failed",
            "binding",
            "declared compiler executable changed during verification",
        ));
    }
    let status = match request.scope {
        Scope::Crate => "crate_verified",
        Scope::SelectedUnit { .. } => "selected_unit_verified",
    };
    // These assumptions delimit the result, including development builds
    // selected by the operator. Identity hashes make the subject and tool
    // choice reviewable; they do not prove the trusted adapter correct.
    let result = json!({
        "schema_version": 1, "status": status, "experimental": true,
        "request_sha256": request_sha256, "capture_sha256": capture_sha256,
        "capture_binary_sha256": capture_binary_sha256,
        "compiler": manifest["compiler"],
        "rustc_binary_sha256": declared.as_ref().map(|declared| &declared.sha256),
        "model_manifest_sha256": model_manifest_sha256,
        "specification_manifest_sha256": specification_manifest_sha256,
        "scope": request.scope, "selected": manifest["selected"],
        "census": manifest["census"], "sources": sources,
        "configuration": manifest["configuration"], "audit": audit,
        "timing_ms": {"capture": capture_ms, "proof_and_audit": proof_ms, "total": start.elapsed().as_millis()},
        "assumptions": ["faithful pinned compiler capture", "experimental pointer-free MIR semantics", "Lean kernel and admitted foundation", "intact compiler and verification environment"],
        "deferred": ["hostile Lean elaborator effects", "complete review-surface reporting", "source-to-deployed-binary correspondence"]
    });
    write(&work.join("result.json"), &encoded(&result)?)?;
    Ok(result)
}

fn verification_stage() -> std::io::Result<tempfile::TempDir> {
    // Capture canonicalizes source paths before recording its read inventory.
    // Create the stage below a canonical parent so compiler arguments and our
    // inventory keys use that same namespace, even when TMPDIR is a symlink.
    // TempDir owns the resulting physical path and still handles its cleanup.
    let parent = fs::canonicalize(std::env::temp_dir())?;
    let mut builder = tempfile::Builder::new();
    builder.prefix("anneal-verification-");
    // Snapshots contain source and diagnostics that other local users should
    // not read. Set permissions at creation instead of relying on the umask.
    // This is Unix user privacy, not isolation from same-user host access.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    builder.tempdir_in(parent)
}

pub fn main(args: VerifyArgs) -> ExitCode {
    // Receipts encode the artifact destination as JSON text. Check its exact
    // spelling before staging or retention can create evidence, so an encoding
    // failure cannot leave an export with no receipt. Carry the checked text
    // into retention and reporting; lossy conversion would change its path.
    let artifacts = match args.artifacts.as_deref() {
        Some(path) => match path.to_str() {
            Some(path) => Some(path),
            None => {
                println!(
                    "{}",
                    json!({"schema_version":1,"status":"tool_failed","phase":"retention",
                        "detail":"artifact destination path must be UTF-8"})
                );
                return ExitCode::from(2);
            }
        },
        None => None,
    };
    let stage = match verification_stage() {
        Ok(stage) => stage,
        Err(failure) => {
            println!(
                "{}",
                json!({"schema_version":1,"status":"tool_failed","phase":"staging","detail":failure.to_string()})
            );
            return ExitCode::from(2);
        }
    };
    // Preserve diagnostic evidence for rejected requests as well as proved
    // ones. Export failure takes precedence over the verification result:
    // the requested evidence operation has not completed successfully.
    let outcome = run(&args, stage.path());
    // Retention is create-only. A caller cannot accidentally overwrite a proof
    // package or an earlier verification receipt by choosing an existing path.
    let retained = if let Some(destination) = artifacts {
        match retain(stage.path(), Path::new(destination)) {
            Ok(()) => Some(destination),
            Err(failure) => {
                println!(
                    "{}",
                    json!({"schema_version":1,"status":"tool_failed","phase":failure.phase,"detail":failure.detail})
                );
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    match outcome {
        Ok(mut result) => {
            if let Some(path) = retained {
                result["artifacts"] = json!(path);
            }
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!(
                "{}",
                json!({"schema_version":1,"status":failure.status,"phase":failure.phase,"detail":failure.detail,"artifacts":retained})
            );
            ExitCode::from(
                if matches!(failure.status, "unsupported" | "proof_failed") {
                    1
                } else {
                    2
                },
            )
        }
    }
}

/// Copy diagnostics into a destination owned by this export.
///
/// Existing destinations are never changed. A failed copy removes the newly
/// created directory; a cleanup failure identifies possibly incomplete output.
/// Callers report success only after every file has been copied.
fn retain(source: &Path, destination: &Path) -> Result<()> {
    // Exported evidence contains the same private inputs as the stage. Set
    // the Unix mode at creation so no permissive chmod window exposes them.
    let directory = fs::DirBuilder::new();
    #[cfg(unix)]
    let directory = {
        use std::os::unix::fs::DirBuilderExt;
        let mut directory = directory;
        directory.mode(0o700);
        directory
    };
    // Acquire ownership with create-only admission before entering any
    // cleanup path. A caller's existing directory must never be deleted
    // merely because retention failed to claim its requested destination.
    directory
        .create(destination)
        .map_err(|e| io("retention", e))?;
    if let Err(failure) = copy_artifacts(source, destination) {
        // The destination belongs to this export, so a failed copy can be
        // removed without leaving a path that blocks retry. If removal
        // fails too, report possible partial output rather than claiming
        // either a complete export or a clean filesystem rollback.
        if let Err(cleanup) = fs::remove_dir_all(destination) {
            return Err(error(
                "tool_failed",
                "retention",
                format!(
                    "{}; incomplete artifacts may remain at {} (cleanup failed: {cleanup})",
                    failure.detail,
                    destination.display()
                ),
            ));
        }
        return Err(failure);
    }
    Ok(())
}

fn copy_artifacts(source: &Path, destination: &Path) -> Result<()> {
    for entry in walkdir::WalkDir::new(source)
        .min_depth(1)
        .follow_links(false)
    {
        let entry = entry.map_err(|e| error("tool_failed", "retention", e))?;
        let relative = entry.path().strip_prefix(source).unwrap();
        if entry.file_type().is_symlink() {
            return Err(error(
                "tool_failed",
                "retention",
                "unexpected staging symlink",
            ));
        }
        let target = destination.join(relative);
        if entry.file_type().is_dir() {
            fs::create_dir(&target).map_err(|e| io("retention", e))?;
        } else {
            fs::copy(entry.path(), target).map_err(|e| io("retention", e))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn verification_directories_are_private_with_umask_022() {
        use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

        const CHILD: &str = "ANNEAL_VERIFICATION_DIRECTORY_PERMISSION_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let stage = verification_stage().unwrap();
            fs::write(stage.path().join("input.rs"), b"private source bytes").unwrap();
            let parent = tempfile::tempdir().unwrap();
            let destination = parent.path().join("artifacts");
            assert!(retain(stage.path(), &destination).is_ok());
            assert_eq!(
                fs::read(destination.join("input.rs")).unwrap(),
                b"private source bytes"
            );

            let existing = parent.path().join("existing");
            fs::DirBuilder::new().mode(0o750).create(&existing).unwrap();
            fs::write(existing.join("keep"), b"caller bytes").unwrap();
            assert!(retain(stage.path(), &existing).is_err());
            assert_eq!(
                fs::metadata(&existing).unwrap().permissions().mode() & 0o777,
                0o750
            );
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller bytes");
            assert!(!existing.join("input.rs").exists());

            assert_eq!(
                (
                    fs::metadata(stage.path()).unwrap().permissions().mode() & 0o777,
                    fs::metadata(&destination).unwrap().permissions().mode() & 0o777,
                ),
                (0o700, 0o700)
            );
            return;
        }

        // Umask is process-wide. Change it only in a fresh child so this
        // regression cannot race other tests running in the parent binary.
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 022; exec \"$@\"", "anneal-private-directories"])
            .arg(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "verify::tests::verification_directories_are_private_with_umask_022",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "permission probe failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn declaration_names_cannot_inject_lean_commands() {
        for valid in ["Spec.specs", "A.B_2.proof", "Proof.verify"] {
            assert!(identifier(valid));
        }
        for invalid in [
            "",
            ".Proof",
            "Proof..verify",
            "Proof.verify\naxiom x : False",
            "Proof.(verify)",
            "Proof.7bad",
        ] {
            assert!(!identifier(invalid));
        }
    }

    #[test]
    fn declared_inputs_reject_escape_and_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("source.rs"), "pub fn f() {}").unwrap();
        let root = fs::canonicalize(dir.path()).unwrap();
        assert!(declared_file(&root, Path::new("source.rs")).is_ok());
        assert!(declared_file(&root, Path::new("../source.rs")).is_err());
        assert!(declared_file(&root, Path::new("/source.rs")).is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink("source.rs", root.join("alias.rs")).unwrap();
            assert!(declared_file(&root, Path::new("alias.rs")).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn artifact_retention_cleans_failed_copy_and_allows_retry() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::create_dir(source.path().join("logs")).unwrap();
        fs::write(source.path().join("logs/compiler.stderr"), b"diagnostics").unwrap();
        let outside = tempfile::tempdir().unwrap();
        let sentinel = outside.path().join("keep");
        fs::write(&sentinel, b"outside bytes").unwrap();
        let link = source.path().join("unexpected");
        symlink(&sentinel, &link).unwrap();
        let export_parent = tempfile::tempdir().unwrap();
        let destination = export_parent.path().join("artifacts");

        let Err(failure) = retain(source.path(), &destination) else {
            panic!("a staging symlink must reject retention");
        };
        assert_eq!(failure.status, "tool_failed");
        assert_eq!(failure.phase, "retention");
        assert!(!destination.exists(), "a failed export must be removed");
        assert_eq!(fs::read(&sentinel).unwrap(), b"outside bytes");

        fs::remove_file(link).unwrap();
        assert!(retain(source.path(), &destination).is_ok());
        assert_eq!(
            fs::read(destination.join("logs/compiler.stderr")).unwrap(),
            b"diagnostics"
        );
    }

    #[test]
    fn artifact_retention_preserves_existing_empty_destination() {
        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let destination = tempfile::tempdir().unwrap();
        assert!(retain(source.path(), destination.path()).is_err());
        assert!(destination.path().is_dir());
        assert_eq!(fs::read_dir(destination.path()).unwrap().count(), 0);
    }

    #[cfg(unix)]
    #[test]
    fn artifact_retention_preserves_existing_symlink_destination() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("keep"), b"outside bytes").unwrap();
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");
        symlink(outside.path(), &destination).unwrap();
        assert!(retain(source.path(), &destination).is_err());
        assert!(fs::symlink_metadata(&destination).unwrap().is_symlink());
        assert_eq!(
            fs::read(outside.path().join("keep")).unwrap(),
            b"outside bytes"
        );
        assert!(!outside.path().join("new").exists());
    }

    #[test]
    fn artifact_retention_never_overwrites() {
        let source = tempfile::tempdir().unwrap();
        let target = tempfile::tempdir().unwrap();
        fs::write(target.path().join("keep"), b"valuable").unwrap();
        assert!(retain(source.path(), target.path()).is_err());
        assert_eq!(fs::read(target.path().join("keep")).unwrap(), b"valuable");
    }

    #[test]
    fn compiler_authentication_requires_one_entry_for_commit_date_and_dialects() {
        let fields = |commit: &str, date: &str, version: &str, top: &str, scoped: &str| {
            json!({
                "schema_version": 2,
                "mir_dialect": top,
                "compiler": {
                    "commit": commit,
                    "commit_date": date,
                    "version": version,
                    "mir_dialect": scoped,
                    "rustc": "/opt/rust/bin/rustc",
                    "sysroot": "/opt/rust",
                },
            })
        };
        for compiler in compilers::SUPPORTED_COMPILERS {
            let (commit, date, dialect) =
                (compiler.commit, compiler.commit_date, compiler.mir_dialect);
            let upstream_ver = format!("1.101.0-nightly ({} {date})", &commit[..9]);
            let fuchsia_ver = format!("1.101.0-dev (git_revisions:{commit},llvm:0123)");
            for ver in [&upstream_ver, &fuchsia_ver] {
                let valid = fields(commit, date, ver, dialect, dialect);
                assert_eq!(authenticated_compiler(&valid), Some(compiler));
            }

            let valid = fields(commit, date, &upstream_ver, dialect, dialect);
            let mut wrong_schema = valid.clone();
            wrong_schema["schema_version"] = json!(1);
            let mut missing_date = valid.clone();
            missing_date["compiler"]
                .as_object_mut()
                .unwrap()
                .remove("commit_date");
            let mut missing_version = valid.clone();
            missing_version["compiler"]
                .as_object_mut()
                .unwrap()
                .remove("version");
            let mut missing_rustc = valid.clone();
            missing_rustc["compiler"]
                .as_object_mut()
                .unwrap()
                .remove("rustc");
            let mut empty_rustc = valid.clone();
            empty_rustc["compiler"]["rustc"] = json!("");
            let mut null_rustc = valid.clone();
            null_rustc["compiler"]["rustc"] = Value::Null;
            let mut missing_sysroot = valid.clone();
            missing_sysroot["compiler"]
                .as_object_mut()
                .unwrap()
                .remove("sysroot");
            let mut empty_sysroot = valid.clone();
            empty_sysroot["compiler"]["sysroot"] = json!("");
            for invalid in [
                wrong_schema,
                missing_date,
                missing_version,
                missing_rustc,
                empty_rustc,
                null_rustc,
                missing_sysroot,
                empty_sysroot,
                fields(commit, "2026-01-01", &upstream_ver, dialect, dialect),
                fields(commit, date, "1.80.0 (000000000 2025-01-01)", dialect, dialect),
                fields(&commit.to_uppercase(), date, &upstream_ver, dialect, dialect),
                fields(&commit[..9], date, &upstream_ver, dialect, dialect),
            ] {
                assert_eq!(authenticated_compiler(&invalid), None, "{invalid}");
            }
            for other in compilers::SUPPORTED_COMPILERS {
                if other == compiler {
                    continue;
                }
                let other_ver = format!("1.98.0-nightly ({} {})", &other.commit[..9], other.commit_date);
                // Either dialect field, or both, naming another compiler's
                // dialect must reject; so must another compiler's date or
                // version string.
                for invalid in [
                    fields(commit, date, &upstream_ver, other.mir_dialect, dialect),
                    fields(commit, date, &upstream_ver, dialect, other.mir_dialect),
                    fields(commit, date, &upstream_ver, other.mir_dialect, other.mir_dialect),
                    fields(commit, other.commit_date, &upstream_ver, dialect, dialect),
                    fields(commit, date, &other_ver, dialect, dialect),
                ] {
                    assert_eq!(authenticated_compiler(&invalid), None, "{invalid}");
                }
            }
        }
    }

    #[test]
    fn every_supported_dialect_has_bundled_syntax_and_canonical_roots() {
        let semantics = BUNDLE
            .iter()
            .find(|(relative, _)| *relative == "trusted/lean/Trusted/MirSemantics.lean")
            .map(|(_, text)| *text)
            .expect("bundled MirSemantics");
        for compiler in compilers::SUPPORTED_COMPILERS {
            let dialect = compiler.mir_dialect;
            assert!(require_dialect_syntax(BUNDLE, dialect).is_ok(), "{dialect}");
            // Expected.lean names these roots inside the dialect namespace.
            let namespace = format!("\nnamespace {dialect}\n");
            let start = semantics.find(&namespace).expect(&namespace);
            let end = semantics[start..]
                .find(&format!("\nend {dialect}\n"))
                .expect("end of dialect namespace");
            let body = &semantics[start..start + end];
            for root in [
                "structure Crate where",
                "def CrateTheorem (c : Crate)",
                "def UnitTheorem (c : Crate)",
            ] {
                assert!(body.contains(root), "{dialect} lacks {root}");
            }
        }
    }

    #[test]
    fn a_dialect_without_bundled_syntax_is_refused() {
        for compiler in compilers::SUPPORTED_COMPILERS {
            let dialect = compiler.mir_dialect;
            let syntax = format!("trusted/lean/Trusted/Rustc/{dialect}/MirAst.lean");
            let without: Vec<_> = BUNDLE
                .iter()
                .copied()
                .filter(|(relative, _)| *relative != syntax)
                .collect();
            assert_eq!(without.len() + 1, BUNDLE.len());
            let failure = require_dialect_syntax(&without, dialect).unwrap_err();
            assert_eq!((failure.status, failure.phase), ("tool_failed", "model"));
            assert!(failure.detail.contains(&syntax), "{}", failure.detail);

            let stripped_semantics: Vec<_> = BUNDLE
                .iter()
                .map(|&(relative, text)| {
                    if relative == "trusted/lean/Trusted/MirSemantics.lean" {
                        (
                            relative,
                            Box::leak(
                                text.replace(
                                    &format!("\nnamespace {dialect}\n"),
                                    "\nnamespace OmittedDialect\n",
                                )
                                .into_boxed_str(),
                            ) as &'static str,
                        )
                    } else {
                        (relative, text)
                    }
                })
                .collect();
            let failure = require_dialect_syntax(&stripped_semantics, dialect).unwrap_err();
            assert_eq!((failure.status, failure.phase), ("tool_failed", "model"));
            assert!(
                failure
                    .detail
                    .contains(&format!("lacks namespace {dialect}")),
                "{}",
                failure.detail
            );
        }
    }

    #[test]
    fn captured_subject_must_import_exactly_the_authenticated_syntax() {
        let header = "-- Copyright 2026 The Fuchsia Authors\n--\n-- those terms.\n\n";
        let subject = |imports: &str| {
            format!(
                "{header}prelude\n{imports}\nnamespace Captured\n\ndef program : X := y\n\nend Captured\n"
            )
        };
        let accepted = subject("import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst\n");
        assert!(require_captured_syntax(&accepted, "V2026_05_31_R14210df0e").is_ok());
        for (text, dialect) in [
            (accepted.clone(), "V2026_10_22_R7189d39d9"),
            (subject(""), "V2026_05_31_R14210df0e"),
            (
                subject(
                    "import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst\n\
                     import Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst\n",
                ),
                "V2026_05_31_R14210df0e",
            ),
            (
                subject(
                    "import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst\n  \
                     import Trusted.MirSemantics\n",
                ),
                "V2026_05_31_R14210df0e",
            ),
            (
                subject(
                    "import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst\n\
                     public import Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst\n",
                ),
                "V2026_05_31_R14210df0e",
            ),
            (
                subject(
                    "/- comment -/ import Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst\n\
                     import Trusted.Rustc.V2026_05_31_R14210df0e.MirAst\n",
                ),
                "V2026_05_31_R14210df0e",
            ),
            (
                accepted.replacen("prelude\n", "", 1),
                "V2026_05_31_R14210df0e",
            ),
            (
                accepted.replacen("namespace Captured\n", "namespace Other\n", 1),
                "V2026_05_31_R14210df0e",
            ),
        ] {
            let failure = require_captured_syntax(&text, dialect).unwrap_err();
            assert_eq!((failure.status, failure.phase), ("tool_failed", "capture"));
        }
    }

    #[cfg(unix)]
    #[test]
    fn declared_compilers_bring_their_own_distribution_sysroot() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(root.path()).unwrap();
        let distribution = root.join("toolchain");
        fs::create_dir_all(distribution.join("bin")).unwrap();
        fs::create_dir_all(distribution.join("lib/rustlib")).unwrap();
        let rustc = distribution.join("bin/rustc");
        fs::write(&rustc, b"").unwrap();
        assert_eq!(
            distribution_sysroot(&rustc, &rustc).ok(),
            Some(distribution.clone())
        );

        // An alias into `<distribution>/bin/rustc` prefers `<distribution>`
        // even when the alias's own parent happens to contain a decoy
        // `lib/rustlib` (such as `/usr/bin/rustc -> /opt/rust/bin/rustc`).
        let usr = root.join("usr");
        fs::create_dir_all(usr.join("bin")).unwrap();
        fs::create_dir_all(usr.join("lib/rustlib")).unwrap();
        let usr_rustc = usr.join("bin/rustc");
        symlink(&rustc, &usr_rustc).unwrap();
        assert_eq!(
            distribution_sysroot(&usr_rustc, &rustc).ok(),
            Some(distribution.clone())
        );

        // A symlink-joined distribution (`flake.nix` `testSysroot`, Bazel
        // execroots) whose `bin/rustc` points to a standalone store blob
        // resolves to the symlink-joined distribution root.
        let store = root.join("store");
        fs::create_dir_all(&store).unwrap();
        let store_blob = store.join("anneal-build-rustc");
        fs::write(&store_blob, b"").unwrap();
        let joined = root.join("joined-toolchain");
        fs::create_dir_all(joined.join("bin")).unwrap();
        fs::create_dir_all(joined.join("lib/rustlib")).unwrap();
        let joined_rustc = joined.join("bin/rustc");
        symlink(&store_blob, &joined_rustc).unwrap();
        assert_eq!(
            distribution_sysroot(&joined_rustc, &store_blob).ok(),
            Some(joined)
        );

        // A wrapper elsewhere, or one beside the compiler under another name,
        // does not identify a distribution.
        let wrapper = distribution.join("bin/rustc-wrapper");
        fs::write(&wrapper, b"").unwrap();
        let outside = root.join("rustc");
        fs::write(&outside, b"").unwrap();
        for (given, canon) in [
            (wrapper.clone(), wrapper),
            (outside.clone(), outside),
            (store_blob.clone(), store_blob),
        ] {
            let failure = distribution_sysroot(&given, &canon).unwrap_err();
            assert_eq!((failure.status, failure.phase), ("tool_failed", "compiler"));
            assert!(
                failure.detail.contains("pass --sysroot"),
                "{}",
                failure.detail
            );
        }
        fs::remove_dir(distribution.join("lib/rustlib")).unwrap();
        assert!(distribution_sysroot(&rustc, &rustc).is_err());
    }

    #[test]
    fn pure_lift_import_scanner_detects_imports_and_ignores_comments_and_strings() {
        for imported in [
            "prelude\nimport Anneal.PureLift\n",
            "prelude\nimport Expected\nimport Anneal.PureLift.MirBridge\n",
            "prelude\npublic meta import all Anneal.PureLift.Lens\n",
            "/- doc -/\nprelude\nimport /- inline -/ Anneal.PureLift\n",
            "prelude\nimport «Anneal».«PureLift»\n",
        ] {
            assert!(
                source_imports_pure_lift(imported.as_bytes()),
                "failed to detect PureLift import in {imported:?}"
            );
        }
        for not_imported in [
            "prelude\n-- import Anneal.PureLift\nimport Anneal.MirWp\n",
            "/-! Mentions import Anneal.PureLift in doc -/\nprelude\nimport Anneal.MirWp\n",
            "/- outer /- nested -/ import Anneal.PureLift -/\nprelude\nimport Expected\n",
            "prelude\nimport Expected\ndef s : String := \"import Anneal.PureLift\"\n",
            "prelude\nimport Expected\ndef q : Char := '\"'\ndef s : String := \"import Anneal.PureLift\"\n",
            "prelude\nimport Expected\nopen Anneal\n-- post-header tokens cannot introduce imports\ndef fake : Nat := 0\n",
            "prelude\nimport Anneal.PureLiftOther\n",
        ] {
            assert!(
                !source_imports_pure_lift(not_imported.as_bytes()),
                "falsely detected PureLift import in {not_imported:?}"
            );
        }
    }
}
