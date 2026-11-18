// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command behavior through direct invocation and Cargo's subcommand dispatch.

use std::env;
use std::path::Path;
use std::process::{Command, Output};

#[derive(Clone, Copy, Debug)]
enum Route {
    Direct,
    Cargo,
}

fn command(route: Route, workdir: &Path) -> Command {
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal"));
    assert!(
        binary.is_file(),
        "missing test binary: {}",
        binary.display()
    );
    let mut command = match route {
        Route::Direct => Command::new(binary),
        Route::Cargo => {
            let mut command = Command::new(env!("CARGO"));
            command.arg("anneal");
            command.env("CARGO_HOME", workdir.join("cargo-home"));
            let mut paths = vec![
                binary
                    .parent()
                    .expect("test binary has a parent")
                    .to_path_buf(),
            ];
            if let Some(path) = env::var_os("PATH") {
                paths.extend(env::split_paths(&path));
            }
            command.env(
                "PATH",
                env::join_paths(paths).expect("construct subcommand search path"),
            );
            command
        }
    };
    command.current_dir(workdir);
    command
}

fn assert_result(output: &Output, code: i32, stdout: &str, stderr: &str) {
    let actual_stdout = String::from_utf8_lossy(&output.stdout);
    let actual_stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.code() == Some(code)
            && actual_stdout.contains(stdout)
            && actual_stderr.contains(stderr),
        "expected status {code}, stdout containing {stdout:?}, stderr \
         containing {stderr:?}; got status {}\nstdout:\n{actual_stdout}\n\
         stderr:\n{actual_stderr}",
        output.status
    );
}

#[test]
fn help_and_version_work_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &[][..],
            &["help"],
            &["-h"],
            &["--help"],
            &["setup", "-h"],
            &["setup", "--help"],
            &["help", "setup"],
            &["verify", "-h"],
            &["verify", "--help"],
            &["help", "verify"],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, "Usage:", "");
            assert!(output.stderr.is_empty(), "{output:?}");
        }
        for arg in ["-V", "--version"] {
            let output = command(route, project.path())
                .arg(arg)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(
                &output,
                0,
                &format!("cargo-anneal {}", env!("CARGO_PKG_VERSION")),
                "",
            );
            assert!(output.stderr.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn malformed_arguments_fail_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &["unknown"][..],
            &["--unknown"],
            &["setup", "--unknown"],
            &["setup", "--local-archive"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &[
                "verify",
                "--request",
                "request.json",
                "--manifest-path",
                "Cargo.toml",
            ],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 2, "", "error:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}

#[cfg(target_os = "linux")]
fn local_archive(path: &Path) {
    archive_entries(path, &[("marker.txt", b"current-run CLI archive", 0o644)]);
}

#[cfg(target_os = "linux")]
fn archive_entries(path: &Path, entries: &[(&str, &[u8], u32)]) {
    let file = std::fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);
    for (name, contents, mode) in entries {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(*mode);
        header.set_cksum();
        archive
            .append_data(&mut header, name, *contents)
            .expect("write archive fixture");
    }
    archive
        .into_inner()
        .expect("finish tar archive")
        .finish()
        .expect("finish compressed archive");
}

#[cfg(target_os = "linux")]
#[test]
fn setup_uses_fresh_child_cache_for_each_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    let archive = project.path().join("local archive.tar.zst");
    local_archive(&archive);
    for route in [Route::Direct, Route::Cargo] {
        let cache = tempfile::tempdir().expect("create owned cache");
        // On Linux, exocrate's user-global location honors XDG_CACHE_HOME.
        // Override it only in the child so this test process keeps its cache.
        let output = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&archive)
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "Installed Anneal toolchain at ", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let installed = Path::new(
            stdout
                .trim_end()
                .strip_prefix("Installed Anneal toolchain at ")
                .expect("setup reports its installation root"),
        );
        assert!(
            installed.starts_with(cache.path()),
            "{}",
            installed.display()
        );
        assert_eq!(
            std::fs::read(installed.join("marker.txt")).expect("read installed current-run marker"),
            b"current-run CLI archive"
        );

        for name in ["missing", "broken"] {
            let failed_cache = tempfile::tempdir().expect("create fresh cache");
            let bad_archive = project.path().join(format!("{name}.tar.zst"));
            if name == "broken" {
                std::fs::write(&bad_archive, b"invalid archive").expect("write broken archive");
            }
            let output = command(route, project.path())
                .env("XDG_CACHE_HOME", failed_cache.path())
                .args(["setup", "--local-archive"])
                .arg(&bad_archive)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 1, "", "error: failed to install Anneal toolchain:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
        assert!(installed.join("marker.txt").is_file());
    }
}

#[cfg(unix)]
#[test]
fn rejects_non_utf8_artifact_paths_before_staging_or_retention() {
    use std::ffi::OsString;
    use std::fs;
    use std::os::unix::ffi::OsStringExt;

    let project = tempfile::tempdir().expect("create artifact-path fixture");
    let request = project.path().join("request.json");
    let request_bytes = b"not JSON\n";
    fs::write(&request, request_bytes).unwrap();
    for route in [Route::Direct, Route::Cargo] {
        let absent = project.path().join(OsString::from_vec(
            format!("{route:?}-new-")
                .into_bytes()
                .into_iter()
                .chain([0xff])
                .collect(),
        ));
        let existing = project.path().join(OsString::from_vec(
            format!("{route:?}-existing-")
                .into_bytes()
                .into_iter()
                .chain([0xff])
                .collect(),
        ));
        fs::create_dir(&existing).unwrap();
        fs::write(existing.join("keep"), b"caller evidence").unwrap();
        for destination in [&absent, &existing] {
            let output = command(route, project.path())
                .arg("verify")
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(destination)
                .output()
                .unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout)
                .expect("invalid artifact path returns a JSON receipt");
            assert_eq!(receipt["schema_version"], 1);
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], "retention");
            assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
            assert!(receipt.get("artifacts").is_none(), "{receipt}");
            assert!(!absent.exists());
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
            assert_eq!(fs::read(&request).unwrap(), request_bytes);
        }
        // A missing temp parent would fail stage creation. The encoding check
        // must run first, without reading a request or creating either path.
        let missing_tmp = project.path().join(format!("{route:?}-missing-temp"));
        let output = command(route, project.path())
            .env("TMPDIR", &missing_tmp)
            .arg("verify")
            .arg("--request")
            .arg(project.path().join("missing-request"))
            .arg("--artifacts")
            .arg(&absent)
            .output()
            .unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["phase"], "retention");
        assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
        assert!(!missing_tmp.exists());
        assert!(!absent.exists());

        // UTF-8 paths retain the normal rejected-request evidence and receipt.
        // This control needs no compiler or Lean process.
        let ordinary = project.path().join(format!("{route:?}-ordinary-evidence"));
        let output = command(route, project.path())
            .arg("verify")
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&ordinary)
            .output()
            .unwrap();
        assert_result(&output, 1, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["status"], "unsupported");
        assert_eq!(receipt["phase"], "request");
        assert_eq!(receipt["artifacts"].as_str(), ordinary.to_str());
        assert!(ordinary.is_dir());
        assert_eq!(fs::read(&request).unwrap(), request_bytes);
    }
}

#[test]
fn early_verification_failures_have_versioned_receipts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let existing = project.path().join("existing");
    fs::create_dir(&existing).unwrap();
    fs::write(existing.join("keep"), b"caller evidence").unwrap();
    for route in [Route::Direct, Route::Cargo] {
        for phase in ["staging", "retention"] {
            let mut child = command(route, project.path());
            child.arg("verify").arg("--request").arg(&request);
            if phase == "staging" {
                child.env("TMPDIR", project.path().join("missing-temp"));
            } else {
                child.arg("--artifacts").arg(&existing);
            }
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 1, "{receipt}");
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], phase);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
        }
    }
}

#[cfg(target_os = "linux")]
#[test]
fn capture_discovery_prefers_explicit_then_installed_then_sibling() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let bin = project.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let cli = bin.join("cargo-anneal");
    // Copy in a child process for the reason given on `executable`: an
    // in-process copy intermittently made the first launch fail with ETXTBSY.
    let copied = Command::new("cp")
        .arg(env!("CARGO_BIN_EXE_cargo-anneal"))
        .arg(&cli)
        .status()
        .unwrap();
    assert!(copied.success());
    let script = |label| {
        format!(
            "#!/bin/sh\nprintf '%s\\n' '{{\"status\":\"unsupported\",\"detail\":\"{label}\"}}'\nexit 2\n"
        )
    };
    for (path, label) in [
        (bin.join("anneal-rustc-capture"), "sibling"),
        (bin.join("explicit"), "explicit"),
    ] {
        executable(&path, &script(label));
    }
    let archive = project.path().join("tools.tar.zst");
    let cached = script("installed");
    archive_entries(
        &archive,
        &[
            ("bin/anneal-rustc-capture", cached.as_bytes(), 0o755),
            ("rust/marker", b"paired sysroot", 0o644),
        ],
    );
    let cache = project.path().join("cache");
    let setup = Command::new(&cli)
        .current_dir(project.path())
        .env("XDG_CACHE_HOME", &cache)
        .args(["setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&setup, 0, "Installed Anneal toolchain at ", "");
    let rust = project.path().join("rust");
    fs::create_dir(&rust).unwrap();
    fs::write(rust.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version":1,
            "compilation":{"source_root":rust,"crate_root":"lib.rs","crate_name":"fixture",
                "edition":"2024","target":"x86_64-unknown-linux-gnu","source_files":["lib.rs"]},
            "scope":{"kind":"crate"},"proof":{"source_root":"unused","sources":[]}
        }))
        .unwrap(),
    )
    .unwrap();
    // These fixture tools refuse capture. Their marker diagnoses selection;
    // they cannot produce a fake verification result and never start Lean.
    for expected in ["installed", "explicit", "sibling"] {
        let mut child = Command::new(&cli);
        child
            .current_dir(project.path())
            .arg("verify")
            .arg("--request")
            .arg(&request);
        child.env(
            "XDG_CACHE_HOME",
            if expected == "sibling" {
                project.path().join("empty-cache")
            } else {
                cache.clone()
            },
        );
        if expected == "explicit" {
            child.arg("--capture").arg(bin.join("explicit"));
        }
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        let detail: serde_json::Value =
            serde_json::from_str(receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(detail["detail"], expected, "{receipt}");
    }
    let help = Command::new(&cli)
        .args(["verify", "--help"])
        .output()
        .unwrap();
    assert_result(
        &help,
        0,
        "defaults to the installed bundle, then a sibling",
        "",
    );
}

#[test]
fn cargo_shortcut_declares_only_its_documented_source_namespace() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    fs::create_dir_all(package.join("src")).unwrap();
    fs::create_dir(package.join("proof")).unwrap();
    fs::create_dir(package.join(".hidden")).unwrap();
    fs::create_dir(package.join("target")).unwrap();
    fs::write(
        package.join("Cargo.toml"),
        "[package]\nname = \"source_namespace\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(
        package.join("src/lib.rs"),
        b"pub fn zero() -> u64 { include!(\"zero.inc\") }\n",
    )
    .unwrap();
    fs::write(package.join("src/unused.rs"), b"unused declared input\n").unwrap();
    fs::write(package.join("src/zero.inc"), b"0u64\n").unwrap();
    fs::write(
        package.join(".hidden/ignored.rs"),
        b"not a shortcut input\n",
    )
    .unwrap();
    fs::write(package.join("target/ignored.rs"), b"not a shortcut input\n").unwrap();
    fs::write(
        package.join("proof/Spec.lean"),
        b"not compiled by this check\n",
    )
    .unwrap();
    let evidence = project.path().join("evidence");
    // A missing capture tool stops after request construction and staging,
    // so this checks actual shortcut inventory without compiling the fixture.
    let mut child = command(Route::Direct, project.path());
    let mut paths = vec![Path::new(env!("CARGO")).parent().unwrap().to_path_buf()];
    if let Some(path) = env::var_os("PATH") {
        paths.extend(env::split_paths(&path));
    }
    child
        .env("PATH", env::join_paths(paths).unwrap())
        .arg("verify")
        .arg("--manifest-path")
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--artifacts")
        .arg(&evidence);
    let output = child.output().unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 1);
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    let request: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
    assert_eq!(
        request["compilation"]["source_files"],
        serde_json::json!(["src/lib.rs", "src/unused.rs"])
    );
    assert!(!evidence.join("rust/src/zero.inc").exists());
    assert!(!evidence.join("rust/.hidden").exists());
    assert!(!evidence.join("rust/target").exists());
    assert!(!evidence.join("rust/proof").exists());
}

/// Create an executable from a short-lived child process.
///
/// A child that another test thread forks while this multithreaded process
/// holds a file open for writing keeps that descriptor until its own `exec`.
/// Executing the file in that window fails with ETXTBSY ("Text file busy"),
/// so test executables are never written by the test process itself.
#[cfg(target_os = "linux")]
fn executable(path: &Path, script: &str) {
    use std::io::Write as _;
    let mut child = Command::new("/bin/sh")
        .args([
            "-c",
            "cat > \"$1\" && chmod 755 \"$1\"",
            "install-executable",
        ])
        .arg(path)
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
}

/// Write a compiler stand-in that answers exactly `--version --verbose` with
/// the given identity lines and status, and fails anything else. It uses only
/// shell builtins because the verifier probes with `PATH=/usr/bin:/bin`.
#[cfg(target_os = "linux")]
fn fake_rustc(path: &Path, identity: &str, status: i32) {
    assert!(!identity.contains('\''), "{identity}");
    executable(
        path,
        &format!(
            "#!/bin/sh\nif [ \"$#\" -eq 2 ] && [ \"$1\" = --version ] && [ \"$2\" = --verbose ]; then\n\
             printf '%s' '{identity}'\nexit {status}\nfi\nexit 97\n"
        ),
    );
}

#[cfg(target_os = "linux")]
fn verbose_version(version: &str, commit: &str, date: &str) -> String {
    format!(
        "rustc {version}\nbinary: rustc\ncommit-hash: {commit}\ncommit-date: {date}\n\
         host: x86_64-unknown-linux-gnu\nrelease: 1.101.0-dev\nLLVM version: 22.1.6\n"
    )
}

/// Write a request that a stand-in capture driver can refuse before Lean.
#[cfg(target_os = "linux")]
fn capture_only_request(project: &Path) -> std::path::PathBuf {
    let rust = project.join("rust");
    std::fs::create_dir_all(&rust).unwrap();
    std::fs::write(rust.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    let request = project.join("request.json");
    std::fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version":1,
            "compilation":{"source_root":rust,"crate_root":"lib.rs","crate_name":"fixture",
                "edition":"2024","target":"x86_64-unknown-linux-gnu","source_files":["lib.rs"]},
            "scope":{"kind":"crate"},"proof":{"source_root":"unused","sources":[]}
        }))
        .unwrap(),
    )
    .unwrap();
    request
}

const FUCHSIA_7189: &str =
    "1.101.0-dev (git_revisions:7189d39d9ce936881b8132c6addeaf3e295cd455,llvm:0123456789abcdef)";
const COMMIT_7189: &str = "7189d39d9ce936881b8132c6addeaf3e295cd455";

#[test]
fn rustc_and_rustc_version_must_be_passed_together() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for (args, missing) in [
            (
                &["verify", "--request", "request.json", "--rustc", "rustc"][..],
                "--rustc-version",
            ),
            (
                &[
                    "verify",
                    "--request",
                    "request.json",
                    "--rustc-version",
                    "V2026_10_22_R7189d39d9",
                ],
                "--rustc <PATH>",
            ),
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 2, "", missing);
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}

/// Boundary 1 refuses an unsupported declaration, or a compiler that does not
/// report the declared build, before the capture driver runs.
#[cfg(target_os = "linux")]
#[test]
fn declared_compiler_must_be_supported_and_reported_by_rustc() {
    let project = tempfile::tempdir().unwrap();
    let request = capture_only_request(project.path());
    let reached = project.path().join("capture-reached");
    let capture = project.path().join("capture");
    executable(
        &capture,
        &format!(
            "#!/bin/sh\n: > '{}'\nprintf '%s\\n' '{{\"status\":\"unsupported\"}}'\nexit 2\n",
            reached.display()
        ),
    );
    let tools = project.path().join("tools");
    std::fs::create_dir(&tools).unwrap();
    let rustc = |name: &str, identity: &str, status: i32| {
        let path = tools.join(name);
        fake_rustc(&path, identity, status);
        path
    };
    let fuchsia = rustc(
        "fuchsia",
        &verbose_version(FUCHSIA_7189, COMMIT_7189, "2026-10-22"),
        0,
    );
    let cases = [
        (
            fuchsia.clone(),
            "V2026_01_01_R000000000",
            "unsupported",
            "unsupported --rustc-version",
        ),
        (
            fuchsia.clone(),
            "7189d39d9",
            "unsupported",
            "V2026_10_22_R7189d39d9 (commit",
        ),
        (
            fuchsia.clone(),
            "V2026_05_31_R14210df0e",
            "tool_failed",
            "but --rustc-version V2026_05_31_R14210df0e is V2026_05_31_R14210df0e",
        ),
        (
            rustc(
                "rebuilt",
                &verbose_version("1.101.0", COMMIT_7189, "2026-10-23"),
                0,
            ),
            COMMIT_7189,
            "tool_failed",
            "commit-date 2026-10-23",
        ),
        (
            rustc(
                "injected",
                &verbose_version(
                    &format!("1.101.0\ncommit-hash: {COMMIT_7189}"),
                    "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
                    "2026-10-22",
                ),
                0,
            ),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "repeats commit-hash",
        ),
        (
            rustc(
                "failing",
                &verbose_version(FUCHSIA_7189, COMMIT_7189, "2026-10-22"),
                3,
            ),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "--version --verbose failed",
        ),
        (
            tools.join("missing"),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "cannot resolve --rustc",
        ),
        (
            tools.clone(),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "expected a regular file",
        ),
        (
            std::path::PathBuf::from("/dev/null"),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "expected a regular file",
        ),
        // A wrapper outside a distribution needs an explicit --sysroot.
        (
            fuchsia.clone(),
            "V2026_10_22_R7189d39d9",
            "tool_failed",
            "pass --sysroot",
        ),
    ];
    for (rustc, id, status, diagnostic) in cases {
        let output = Command::new(env!("CARGO_BIN_EXE_cargo-anneal"))
            .current_dir(project.path())
            .env("XDG_CACHE_HOME", project.path().join("empty-cache"))
            .arg("verify")
            .arg("--request")
            .arg(&request)
            .arg("--capture")
            .arg(&capture)
            .arg("--rustc")
            .arg(&rustc)
            .args(["--rustc-version", id])
            .output()
            .unwrap();
        let code = if status == "unsupported" { 1 } else { 2 };
        assert_result(&output, code, diagnostic, "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], status, "{receipt}");
        assert_eq!(receipt["phase"], "compiler", "{receipt}");
        assert!(!reached.exists(), "capture ran after {receipt}");
    }
}

/// A Fuchsia-style compiler that reports the declared build passes boundary 1
/// and reaches capture with its canonical path and distribution sysroot.
#[cfg(target_os = "linux")]
#[test]
fn declared_fuchsia_compiler_reaches_capture_with_its_distribution() {
    let project = tempfile::tempdir().unwrap();
    let root = std::fs::canonicalize(project.path()).unwrap();
    let request = capture_only_request(&root);
    let distribution = root.join("fuchsia-rust");
    std::fs::create_dir_all(distribution.join("bin")).unwrap();
    std::fs::create_dir_all(distribution.join("lib/rustlib")).unwrap();
    let rustc = distribution.join("bin/rustc");
    fake_rustc(
        &rustc,
        &verbose_version(FUCHSIA_7189, COMMIT_7189, "2026-10-22"),
        0,
    );
    let alias = root.join("rustc-alias");
    std::os::unix::fs::symlink(&rustc, &alias).unwrap();
    let recorded = root.join("capture-arguments");
    let capture = root.join("capture");
    executable(
        &capture,
        &format!(
            "#!/bin/sh\nprintf '%s\\n' \"$@\" > '{}'\n\
             printf '%s\\n' '{{\"status\":\"unsupported\",\"detail\":\"recorded\"}}'\nexit 2\n",
            recorded.display()
        ),
    );
    let explicit = root.join("explicit-sysroot");
    std::fs::create_dir(&explicit).unwrap();
    let store = root.join("store");
    std::fs::create_dir(&store).unwrap();
    let store_rustc = store.join("fuchsia-rustc-blob");
    fake_rustc(
        &store_rustc,
        &verbose_version(FUCHSIA_7189, COMMIT_7189, "2026-10-22"),
        0,
    );
    let joined_dist = root.join("fuchsia-symlink-dist");
    std::fs::create_dir_all(joined_dist.join("bin")).unwrap();
    std::fs::create_dir_all(joined_dist.join("lib/rustlib")).unwrap();
    let joined_rustc = joined_dist.join("bin/rustc");
    std::os::unix::fs::symlink(&store_rustc, &joined_rustc).unwrap();
    for (given_rustc, canon_rustc, expected_dist, id, sysroot) in [
        (&alias, &rustc, &distribution, "V2026_10_22_R7189d39d9", None),
        (&alias, &rustc, &distribution, COMMIT_7189, None),
        (
            &alias,
            &rustc,
            &distribution,
            "V2026_10_22_R7189d39d9",
            Some(&explicit),
        ),
        (
            &joined_rustc,
            &store_rustc,
            &joined_dist,
            "V2026_10_22_R7189d39d9",
            None,
        ),
    ] {
        let _ = std::fs::remove_file(&recorded);
        let mut child = Command::new(env!("CARGO_BIN_EXE_cargo-anneal"));
        child
            .current_dir(&root)
            .env("XDG_CACHE_HOME", root.join("empty-cache"))
            .arg("verify")
            .arg("--request")
            .arg(&request)
            .arg("--capture")
            .arg(&capture)
            .arg("--rustc")
            .arg(given_rustc)
            .args(["--rustc-version", id]);
        if let Some(sysroot) = sysroot {
            child.arg("--sysroot").arg(sysroot);
        }
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        let detail: serde_json::Value =
            serde_json::from_str(receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(detail["detail"], "recorded", "{receipt}");
        let arguments = std::fs::read_to_string(&recorded).unwrap();
        let arguments: Vec<_> = arguments.lines().collect();
        let value = |flag: &str| {
            let index = arguments.iter().position(|arg| *arg == flag).unwrap();
            arguments[index + 1]
        };
        assert_eq!(
            value("--rustc"),
            canon_rustc.to_str().unwrap(),
            "{arguments:?}"
        );
        assert_eq!(
            value("--sysroot"),
            sysroot.unwrap_or(expected_dist).to_str().unwrap(),
            "{arguments:?}"
        );
    }
}
