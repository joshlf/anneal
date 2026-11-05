// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-rustc-capture`: compiles a target crate's `src/lib.rs` with the
//! pinned `rustc`, as a `rustc_driver` client, and writes `Mir.lean`
//! describing the crate in the vocabulary of `Trusted/`.
//!
//! ```text
//! anneal-rustc-capture --sysroot DIR --edition YEAR --crate-name NAME
//!                      --src PATH/src/lib.rs --out PATH/Mir.lean
//! ```
//!
//! # What the capture trusts and checks
//!
//! The capture *is* `rustc`: the same compiler libraries, in the same
//! process, run the parser, macro expander, name resolver, type checker,
//! borrow checker, and MIR pipeline. The capture reads `rustc`'s results
//! directly (`hook.rs`, `extract.rs`, `items.rs`); no Rust source text or
//! textual MIR is parsed anywhere. Its own decisions are limited to:
//!
//! - which `rustc` invocations to run (`rustc_args`, `CONFIGS`), fixed here
//!   rather than taken from the caller, apart from the sysroot, the edition,
//!   the crate name, and the source path;
//! - that the crate means the same under Cargo's debug and release
//!   configurations (`main` compares the two renderings);
//! - which files `rustc` may read (`GuardedFileLoader`, and the source-map
//!   and dependency checks in `check_inputs`);
//! - the translation into the IR, which rejects everything outside the
//!   fragment the Lean model describes; and
//! - the rendering of the IR as Lean (`lean.rs`).
//!
//! # Host duties
//!
//! The host (`cargo-anneal`) must run this binary with the pinned
//! toolchain's `lib/` directory as its only shared-library search path, pass
//! the pinned toolchain's `rust/` directory as `--sysroot`, authenticate
//! every file under both (including `librustc_driver-*.so`, `libLLVM*.so`,
//! and the sysroot's `libcore`/`libstd` `.rlib`/`.rmeta` files) against the
//! toolchain manifest, and run it with an empty environment (rustc consults
//! variables such as `RUSTC_LOG`, `RUST_TARGET_PATH`, and `SOURCE_DATE_EPOCH`).
//! The host reads `--edition` and `--crate-name` from the crate's
//! `Cargo.toml`, and must reject `[profile]` settings outside the two
//! configurations in `CONFIGS` (for example `panic = "abort"`).
//!
//! The output is a deterministic function of `src/lib.rs`, the arguments,
//! and the toolchain: it contains no paths, timestamps, or hash-ordered
//! data. The host can therefore bind the verified source by running the
//! capture itself and compiling exactly the `Mir.lean` it wrote.
//!
//! Source citations are paths in `rust-lang/rust` at the pinned toolchain
//! commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
//! (`https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/<path>`),
//! whose sources ship in the pinned toolchain's `rustc-src` component.

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod extract;
mod hook;
mod ir;
mod items;
mod lean;
mod spec;

use std::fs;
use std::io::{self, Read};
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::sync::{Arc, Mutex};

use rustc_driver::Compilation;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_span::FileName;
use rustc_span::source_map::{FileLoader, RealFileLoader};

/// Command-line arguments. All five are required.
struct Args {
    sysroot: PathBuf,
    edition: String,
    crate_name: String,
    src: PathBuf,
    src_dev_ino: (u64, u64),
    out: PathBuf,
}

/// Verifies that `path` is an absolute path with no `.` or `..` segments and
/// that every existing prefix from `/` up to `path` is not a symbolic link.
fn check_no_symlinks_on_path(
    path: &Path,
    flag: &str,
    must_exist: bool,
) -> Result<Option<fs::Metadata>, String> {
    if !path.is_absolute() {
        return Err(format!(
            "`{flag}` must be an absolute path: {}",
            path.display()
        ));
    }
    let mut cur = PathBuf::new();
    let mut last_meta = None;
    for comp in path.components() {
        match comp {
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::Normal(seg) => cur.push(seg),
            _ => {
                return Err(format!(
                    "`{flag}` must not contain `.` or `..` segments: {}",
                    path.display()
                ));
            }
        }
        match fs::symlink_metadata(&cur) {
            Ok(meta) => {
                if meta.file_type().is_symlink() {
                    return Err(format!(
                        "`{flag}` contains symlink component `{}`",
                        cur.display()
                    ));
                }
                last_meta = Some(meta);
            }
            Err(e) if !must_exist && cur == path && e.kind() == io::ErrorKind::NotFound => {
                last_meta = None;
            }
            Err(e) => {
                return Err(format!("`{flag}` ({}): {e}", cur.display()));
            }
        }
    }
    Ok(last_meta)
}

/// Opens `path` as a regular file and verifies that `symlink_metadata` (`lstat`)
/// and open-handle `metadata` (`fstat`) both report the same regular-file
/// `(dev, ino)` (matching `expected` when given).
fn open_verified_regular_file(
    path: &Path,
    expected: Option<(u64, u64)>,
) -> io::Result<(fs::File, (u64, u64))> {
    let lmeta = fs::symlink_metadata(path)?;
    let f = fs::File::open(path)?;
    let fmeta = f.metadata()?;
    let dev_ino = (lmeta.dev(), lmeta.ino());
    if !lmeta.is_file()
        || !fmeta.is_file()
        || dev_ino != (fmeta.dev(), fmeta.ino())
        || expected.is_some_and(|exp| exp != dev_ino)
    {
        return Err(io::Error::other(
            "src/lib.rs inode or file type changed during capture",
        ));
    }
    Ok((f, dev_ino))
}

/// Validates standalone crate layout when `--src` is `src/lib.rs`:
/// - `src/` must contain no entry other than `lib.rs` (rejecting extra `.rs`
///   files, subdirectories, or symlinks);
/// - the parent crate directory must not contain `build.rs`; and
/// - the crate directory and its ancestors (up to the user home boundary) must
///   not contain `.cargo/config`, `.cargo/config.toml`, `rust-toolchain`, or
///   `rust-toolchain.toml`.
fn check_crate_context(src: &Path) -> Result<(), String> {
    let Some(src_dir) = src.parent() else {
        return Ok(());
    };
    if src_dir.file_name() != Some("src".as_ref()) {
        return Ok(());
    }
    let entries = fs::read_dir(src_dir)
        .map_err(|e| format!("{}: {e}", src_dir.display()))?;
    for entry in entries {
        let entry =
            entry.map_err(|e| format!("{}: {e}", src_dir.display()))?;
        if entry.file_name() != "lib.rs" {
            return Err(format!(
                "extra entry `{}` in `{}`: a verified crate consists of \
                 `src/lib.rs` only",
                entry.path().display(),
                src_dir.display()
            ));
        }
    }
    let Some(crate_dir) = src_dir.parent() else {
        return Ok(());
    };
    if fs::symlink_metadata(crate_dir.join("build.rs")).is_ok() {
        return Err(format!(
            "`{}` is not allowed in a verified crate",
            crate_dir.join("build.rs").display()
        ));
    }
    if let Ok(meta) = fs::symlink_metadata(crate_dir.join("Cargo.toml"))
        && !meta.is_file()
    {
        return Err(format!(
            "`{}` must be a regular file",
            crate_dir.join("Cargo.toml").display()
        ));
    }
    if fs::symlink_metadata(crate_dir.join(".cargo")).is_ok() {
        return Err(format!(
            "`{}` is not allowed in a verified crate",
            crate_dir.join(".cargo").display()
        ));
    }
    for anc in crate_dir.ancestors() {
        if anc.join(".gemini").exists() {
            break;
        }
        for forbidden in [
            ".cargo/config",
            ".cargo/config.toml",
            "rust-toolchain",
            "rust-toolchain.toml",
        ] {
            let p = anc.join(forbidden);
            if fs::symlink_metadata(&p).is_ok() {
                return Err(format!(
                    "ambient toolchain or cargo configuration `{}` is not \
                     allowed above `{}`",
                    p.display(),
                    crate_dir.display()
                ));
            }
        }
    }
    Ok(())
}

fn parse_args() -> Result<Args, String> {
    let mut it = std::env::args().skip(1);
    let (mut sysroot, mut edition, mut crate_name, mut src, mut out) =
        (None, None, None, None, None);
    while let Some(flag) = it.next() {
        let val =
            it.next().ok_or_else(|| format!("missing value for `{flag}`"))?;
        let slot = match flag.as_str() {
            "--sysroot" => &mut sysroot,
            "--edition" => &mut edition,
            "--crate-name" => &mut crate_name,
            "--src" => &mut src,
            "--out" => &mut out,
            _ => return Err(format!("unknown argument `{flag}`")),
        };
        if slot.replace(val).is_some() {
            return Err(format!("`{flag}` given twice"));
        }
    }
    let edition = edition.ok_or("missing --edition")?;
    if edition != "2024" {
        return Err(format!(
            "unsupported edition `{edition}` (only edition `2024` is supported)"
        ));
    }
    // The host derives the name from `Cargo.toml` (`package.name` or
    // `lib.name`, with `-` replaced by `_`, as Cargo does). It must be a
    // plain identifier so that it cannot smuggle further `rustc` flags.
    let crate_name = crate_name.ok_or("missing --crate-name")?;
    let mut cs = crate_name.chars();
    if !(cs.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_'))
    {
        return Err(format!("invalid crate name `{crate_name}`"));
    }
    let sysroot = PathBuf::from(sysroot.ok_or("missing --sysroot")?);
    let sysroot_meta = check_no_symlinks_on_path(&sysroot, "--sysroot", true)?
        .ok_or_else(|| format!("missing `--sysroot` {}", sysroot.display()))?;
    if !sysroot_meta.is_dir() {
        return Err(format!(
            "--sysroot must be a directory: {}",
            sysroot.display()
        ));
    }

    let src = PathBuf::from(src.ok_or("missing --src")?);
    // The host validates the crate layout; this restates the minimum the
    // file guard below relies on: an absolute path with no symlinks to a
    // regular file named `lib.rs`, with `(dev, ino)` verified across `lstat`
    // and `fstat` so that the guard's check means "this exact regular file".
    let lmeta = check_no_symlinks_on_path(&src, "--src", true)?
        .ok_or_else(|| format!("missing `--src` {}", src.display()))?;
    if !lmeta.is_file() || src.file_name() != Some("lib.rs".as_ref()) {
        return Err(format!(
            "--src must be an absolute path to a regular file named lib.rs: {}",
            src.display()
        ));
    }
    let (_, src_dev_ino) = open_verified_regular_file(
        &src,
        Some((lmeta.dev(), lmeta.ino())),
    )
    .map_err(|e| format!("{}: {e}", src.display()))?;
    check_crate_context(&src)?;

    let out = PathBuf::from(out.ok_or("missing --out")?);
    if let Some(out_meta) = check_no_symlinks_on_path(&out, "--out", false)?
        && !out_meta.is_file()
    {
        return Err(format!(
            "--out exists and is not a regular file: {}",
            out.display()
        ));
    }

    Ok(Args {
        sysroot,
        edition,
        crate_name,
        src,
        src_dev_ino,
        out,
    })
}

/// The build configurations under which the crate is captured.
///
/// Cargo's two standard profiles differ, as far as the meaning of a crate's
/// own code is concerned, in `debug_assertions` and `overflow_checks` (the
/// `dev` profile enables both; `release` disables both), and `ub_checks`
/// follows `debug_assertions` by default. A crate can branch on them
/// (`#[cfg(debug_assertions)]`, `cfg!(..)`, `debug_assert!`), and overflow
/// checks add `Assert` terminators. The capture compiles the crate under
/// both and requires the two `Mir.lean` renderings to be identical (see
/// `main`), so the verified program is the program either profile builds.
/// No other flags change the crate's PostCleanup MIR (see `rustc_args`).
const CONFIGS: &[(&str, &[&str])] = &[
    ("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"]),
    ("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"]),
];

/// The `rustc` command line for one configuration.
///
/// - `--crate-type lib`: target crates are libraries.
/// - `--crate-name`: from the host, as Cargo would pass it.
/// - Apart from the configuration flags in `CONFIGS`, no `--cfg`, `-C`, `-Z`,
///   `--extern`, or `-L` flags: the only crates the target can name are the
///   sysroot's, and the panic strategy is `rustc`'s default, `unwind`.
/// - No `-C opt-level` or `-Z mir-opt-level` flag is needed: the passes that
///   produce `Runtime(PostCleanup)` MIR do not consult the MIR optimization
///   level (only the later `run_optimization_passes` does), and the
///   optimization level otherwise matters only through the defaults of the
///   flags `CONFIGS` sets explicitly.
fn rustc_args(a: &Args, config: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = vec![
        "anneal-rustc-capture".into(),
        "--sysroot".into(),
        a.sysroot.display().to_string(),
        "--edition".into(),
        a.edition.clone(),
        "--crate-type".into(),
        "lib".into(),
        "--crate-name".into(),
        a.crate_name.clone(),
    ];
    v.extend(config.iter().map(|s| s.to_string()));
    v.push(a.src.display().to_string());
    v
}

/// A `FileLoader` that lets `rustc` read exactly one file, `src`.
///
/// `rustc` reads every source file through the session's `FileLoader`
/// (`compiler/rustc_span/src/source_map.rs#L81-L96`): the crate root, files
/// of out-of-line `mod` items, `include!` (`read_file`), and
/// `include_str!`/`include_bytes!` (`read_binary_file`, which also registers
/// the file in the source map: `source_map.rs#L256-L266`). Denying every
/// other path makes all of those fail during compilation, before any MIR
/// exists. Metadata of sysroot crates is not read through this interface.
///
/// The loader also records the exact text it returned for `src`, so `main`
/// can check that every configuration compiled the same text.
struct GuardedFileLoader {
    src: PathBuf,
    src_dev_ino: (u64, u64),
    read: Arc<Mutex<Option<String>>>,
}

impl FileLoader for GuardedFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == self.src
            && fs::symlink_metadata(path).is_ok_and(|m| {
                m.is_file() && (m.dev(), m.ino()) == self.src_dev_ino
            })
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if path != self.src {
            return Err(io::Error::other(format!(
                "anneal: reading `{}` is not allowed: a verified crate \
                 consists of src/lib.rs only",
                path.display()
            )));
        }
        let (mut f, _) =
            open_verified_regular_file(path, Some(self.src_dev_ino))?;
        let mut text = String::new();
        f.read_to_string(&mut text)?;
        let mut read = self.read.lock().unwrap();
        if read.as_ref().is_some_and(|prev| *prev != text) {
            return Err(io::Error::other("src/lib.rs changed between reads"));
        }
        *read = Some(text.clone());
        Ok(text)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other(format!(
            "anneal: reading `{}` is not allowed: a verified crate consists \
             of src/lib.rs only",
            path.display()
        )))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

struct Callbacks {
    src: PathBuf,
    src_dev_ino: (u64, u64),
    read: Arc<Mutex<Option<String>>>,
    result: Option<Result<String, String>>,
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.file_loader = Some(Box::new(GuardedFileLoader {
            src: self.src.clone(),
            src_dev_ino: self.src_dev_ino,
            read: self.read.clone(),
        }));
        config.override_queries = Some(hook::override_queries);
        hook::reset();
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let r = check_inputs(tcx, &self.src)
            .and_then(|()| items::capture_crate(tcx).map(|c| lean::render(&c)));
        self.result = Some(r);
        // Analysis is all the capture needs; skip codegen.
        Compilation::Stop
    }
}

/// Detective checks that `rustc` consumed no input besides `src/lib.rs`.
///
/// These back up `GuardedFileLoader` with `rustc`'s own records:
///
/// - Every file `rustc` loaded is in the source map. Files of sysroot crates
///   appear as *imported* files (spans decoded from metadata) and are
///   authenticated by the host with the rest of the sysroot; every other
///   file must be `src/lib.rs`.
/// - `Session::env_depinfo` records every environment variable read by
///   `env!`/`option_env!` (and by proc macros), and `Session::file_depinfo`
///   every extra file tracked for dependency info
///   (`compiler/rustc_session/src/session.rs#L155-L159`;
///   `compiler/rustc_builtin_macros/src/env.rs#L55`). Either being non-empty
///   means the crate's meaning depends on host state other than
///   `src/lib.rs`, so the capture fails. (`env!` cannot be bound like a
///   file: the variable's value is not an input the host authenticates.)
fn check_inputs(tcx: TyCtxt<'_>, src: &Path) -> Result<(), String> {
    let sess = tcx.sess;
    let mut errs = Vec::new();
    for sf in sess.source_map().files().iter() {
        if sf.is_imported() {
            continue;
        }
        match &sf.name {
            FileName::Real(r) if r.local_path() == Some(src) => {}
            other => errs.push(format!(
                "rustc loaded a source file other than src/lib.rs: {other:?}"
            )),
        }
    }
    for (var, _) in sess.env_depinfo.borrow().iter() {
        errs.push(format!(
            "the crate reads environment variable `{var}` (env!/option_env!)"
        ));
    }
    for f in sess.file_depinfo.borrow().iter() {
        errs.push(format!("the crate depends on file `{f}`"));
    }
    if errs.is_empty() { Ok(()) } else { Err(errs.join("\n")) }
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("anneal-rustc-capture: {e}");
            return ExitCode::FAILURE;
        }
    };
    // Capture under every configuration, in this process, one compiler
    // session after another. Each session starts from fresh `rustc` state;
    // `Callbacks::config` clears the hook's record of bodies.
    let mut outputs: Vec<(&str, String, String)> = Vec::new();
    for (name, flags) in CONFIGS {
        let mut cb = Callbacks {
            src: args.src.clone(),
            src_dev_ino: args.src_dev_ino,
            read: Arc::new(Mutex::new(None)),
            result: None,
        };
        let status = rustc_driver::catch_with_exit_code(|| {
            rustc_driver::run_compiler(&rustc_args(&args, flags), &mut cb)
        });
        let rendered = match cb.result {
            Some(Ok(s)) if status == ExitCode::SUCCESS => s,
            Some(Err(e)) => {
                eprintln!(
                    "anneal-rustc-capture: unsupported crate ({name} \
                     configuration):\n{e}"
                );
                return ExitCode::FAILURE;
            }
            _ => {
                eprintln!(
                    "anneal-rustc-capture: compilation failed ({name} \
                     configuration)"
                );
                return ExitCode::FAILURE;
            }
        };
        let Some(text) = cb.read.lock().unwrap().clone() else {
            eprintln!(
                "anneal-rustc-capture: src/lib.rs was not read ({name} \
                 configuration)"
            );
            return ExitCode::FAILURE;
        };
        outputs.push((name, rendered, text));
    }
    let (first, rendered, text) = &outputs[0];
    for (name, other, other_text) in &outputs[1..] {
        if other_text != text {
            eprintln!(
                "anneal-rustc-capture: src/lib.rs changed during capture"
            );
            return ExitCode::FAILURE;
        }
        if other != rendered {
            eprintln!(
                "anneal-rustc-capture: unsupported crate: its MIR differs \
                 between the {first} and {name} configurations (for example \
                 through `cfg(debug_assertions)`, `debug_assert!`, or \
                 overflow checks), so no single verified program describes \
                 both builds"
            );
            return ExitCode::FAILURE;
        }
    }
    let rendered = rendered.clone();
    if let Err(e) = std::fs::write(&args.out, rendered) {
        eprintln!(
            "anneal-rustc-capture: cannot write {}: {e}",
            args.out.display()
        );
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
