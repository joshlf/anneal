// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the `trusted/audit` repository boundary gate and
//! `TrustedBoundary.lean` kernel-environment inspector.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};

use serde_json::json;

use anneal_audit::{
    Checker, Failure, ImportEdge, InspectorRequest, Json, ModuleArtifacts, PARTS, TrustTier,
    check_cargo_boundary, default_lean_path, sha256_file,
};

const HEADER: &str = "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n";

struct TempFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
}

impl TempFixture {
    fn new(source: Option<&str>) -> Self {
        let checkout = repo_root();
        let dir = tempfile::Builder::new()
            .prefix("anneal-boundary-test-")
            .tempdir()
            .unwrap();
        let root = dir.path().to_path_buf();
        fs::create_dir_all(root.join("trusted/audit")).unwrap();
        fs::create_dir_all(root.join("trusted/lean")).unwrap();
        fs::copy(
            checkout.join("trusted/lean/lean-toolchain"),
            root.join("trusted/lean/lean-toolchain"),
        )
        .unwrap();
        fs::copy(
            checkout.join("trusted/lean/foundation-lock.json"),
            root.join("trusted/lean/foundation-lock.json"),
        )
        .unwrap();
        fs::copy(
            checkout.join("trusted/audit/TrustedBoundary.lean"),
            root.join("trusted/audit/TrustedBoundary.lean"),
        )
        .unwrap();
        fs::write(
            root.join("trusted/lean/Trusted.lean"),
            source.unwrap_or(HEADER).as_bytes(),
        )
        .unwrap();
        Self { _dir: dir, root }
    }

    fn check_expected(
        &mut self,
        expected_code: Option<i32>,
        expected_phase: Option<&str>,
        expected_executed: Option<bool>,
    ) -> Result<Json, Failure> {
        let mut checker = Checker::new(&self.root, None).unwrap();
        checker.set_require_mir_wp(false);
        let outcome = checker.run();
        match &outcome {
            Err(err) => {
                assert_eq!(
                    Some(err.code),
                    expected_code,
                    "unexpected error code for {}: {err}",
                    err.phase
                );
                if let Some(phase) = expected_phase {
                    assert_eq!(err.phase, phase, "unexpected phase: {err}");
                }
                if let Some(exp_exec) = expected_executed {
                    assert_eq!(
                        checker.execution_began, exp_exec,
                        "unexpected execution_began for {err}"
                    );
                }
            }
            Ok(_) => {
                assert!(
                    expected_code.is_none(),
                    "expected rejection {:?}, got success",
                    expected_phase
                );
            }
        }
        outcome
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn copy_dir_all(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(&entry.path(), &dst.join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Verifies that an empty `Trusted.lean` importing only locked `Init.*`
/// modules passes tool admission, preflight, compilation, and foundation
/// kernel replay with zero `Trusted` declarations and zero reached axioms.
#[test]
fn audits_empty_inventory_and_foundation_replay() {
    let mut fix = TempFixture::new(Some(HEADER));
    let rep = fix.check_expected(None, None, None).unwrap();
    assert_eq!(
        rep.get("kernelDeclarations").and_then(Json::as_i64),
        Some(0)
    );
    assert_eq!(rep.get("axioms"), Some(&json!([])));
    assert_eq!(rep.get("replay"), Some(&json!(true)));
}

/// Verifies that `tests/fixtures/positive.lean` passes under hostile
/// `LEAN_PATH` and `LEAN_SYSROOT` environment variables pointing at corrupt
/// `.olean` files, and that `private` helpers, `opaque` definitions, recursors,
/// typeclass instances, and coercions are all recorded in the dependency
/// closure.
#[test]
fn audits_positive_fixture_under_hostile_ambient_paths() {
    let positive_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/positive.lean");
    let positive = fs::read_to_string(positive_path).unwrap();
    let fix = TempFixture::new(Some(&positive));
    let stale = fix.root.join("stale");
    fs::create_dir_all(&stale).unwrap();
    fs::write(stale.join("Trusted.olean"), b"not an olean").unwrap();

    let mut hostile_env: Vec<(String, String)> = env::vars().collect();
    hostile_env.push((
        "LEAN_PATH".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    hostile_env.push((
        "LEAN_SYSROOT".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    let mut checker = Checker::new_with_env(&fix.root, None, hostile_env).unwrap();
    let rep = checker.run().unwrap();

    let decls = rep.get("declarations").and_then(Json::as_array).unwrap();
    let k_decls = rep
        .get("kernelDeclarations")
        .and_then(Json::as_i64)
        .unwrap();
    assert_eq!(k_decls, decls.len() as i64);
    assert!(decls.len() > 30);

    let mut decl_map: BTreeMap<String, &Json> = BTreeMap::new();
    for d in decls {
        let name = d.get("name").and_then(Json::as_str).unwrap().to_string();
        decl_map.insert(name, d);
    }
    let helper = decl_map
        .keys()
        .find(|n| n.starts_with("_private.") && n.ends_with(".Outside.helper"))
        .expect("missing private helper")
        .clone();
    let sealed_deps: BTreeSet<&str> = decl_map["Outside.sealed"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    assert!(sealed_deps.contains(helper.as_str()));
    assert_eq!(
        decl_map["Outside.sealed"]
            .get("kind")
            .and_then(Json::as_str),
        Some("opaque")
    );
    assert!(decl_map.contains_key("Outside.Box.rec"));
    assert!(decl_map.contains_key("Outside.Indexed.rec"));
    assert!(decl_map.keys().any(|n| n.starts_with("Outside.Tree")));

    let inferred_deps: Vec<&str> = decl_map["Outside.inferred"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let coerced_deps: BTreeSet<&str> = decl_map["Outside.coerced"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let axioms: BTreeSet<&str> = rep
        .get("axioms")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let expected_axioms: BTreeSet<&str> = ["Classical.choice", "Quot.sound", "propext"]
        .into_iter()
        .collect();
    assert!(inferred_deps.iter().any(|n| n.contains("instWrap")));
    assert!(coerced_deps.contains("Outside.Box.value"));
    assert!(decl_map.keys().any(|n| n.contains("instCoe")));
    assert!(
        decl_map
            .values()
            .all(|d| d.get("module").and_then(Json::as_str) == Some("Trusted"))
    );
    assert_eq!(axioms, expected_axioms);
}

/// Verifies that adding an `Init.*` module to `foundation-lock.json` is
/// sufficient to admit that module and track its typeclass instances in
/// dependency closures without modifying `audit.rs` or `TrustedBoundary.lean`.
#[test]
fn admits_lock_only_foundation_growth() {
    let src = format!(
        "{HEADER}import Init.Data.PLift\ndef usesExtra (x : PLift Nat) : Bool := decide (x = x)\n"
    );
    let mut fix = TempFixture::new(Some(&src));
    let lock_path = fix.root.join("trusted/lean/foundation-lock.json");
    let mut lock: Json = serde_json::from_str(&fs::read_to_string(&lock_path).unwrap()).unwrap();
    let extra = "Init.Data.PLift";
    lock["modules"].as_object_mut().unwrap().remove(extra);
    lock["graph"].as_object_mut().unwrap().remove(extra);
    fs::write(&lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();
    let _ = fix.check_expected(Some(1), Some("preflight"), Some(false));

    let lean_exec = fs::canonicalize(default_lean_path()).unwrap();
    let prefix = lean_exec.parent().unwrap().parent().unwrap();
    let mut extra_parts = serde_json::Map::new();
    for part in PARTS {
        let p = prefix
            .join("lib/lean")
            .join(format!("Init/Data/PLift.{part}"));
        if p.exists() {
            let digest = sha256_file(&p, "foundation").unwrap();
            extra_parts.insert(part.to_string(), json!(digest));
        } else {
            extra_parts.insert(part.to_string(), Json::Null);
        }
    }
    let src_digest =
        sha256_file(&prefix.join("src/lean/Init/Data/PLift.lean"), "foundation").unwrap();
    lock["modules"][extra] = json!({
        "sourceSha256": src_digest,
        "parts": extra_parts,
    });
    lock["graph"][extra] = json!([{
        "module": "Init.Core",
        "importAll": false,
        "isExported": true,
        "isMeta": false,
    }]);
    fs::write(&lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();

    let rep = fix.check_expected(None, None, None).unwrap();
    let has_plift = rep
        .get("declarations")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .find(|d| d.get("name").and_then(Json::as_str) == Some("usesExtra"))
        .and_then(|d| d.get("dependencies"))
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .any(|x| x.as_str() == Some("instDecidableEqPLift"));
    assert!(
        rep.get("graph")
            .and_then(Json::as_object)
            .unwrap()
            .contains_key(extra)
    );
    assert!(has_plift);
}

/// Verifies that Phase 1 (`"preflight"`) rejects forbidden headers, imports,
/// commands (`#eval`), terms (`unsafe`, `by_elab`), tactics (`native_decide`,
/// `decide +native`), attributes (`@[extern]`, `@[implemented_by]`), and
/// invalid or missing `-- anneal-trust-tier:` directives before Lean ever
/// compiles or executes the file (`execution_began == false`).
#[test]
fn rejects_forbidden_syntax_and_attributes_without_executing_eval() {
    let base_fix = TempFixture::new(None);
    let sentinel = base_fix.root.join("must-not-exist");
    let eval_sentinel_src = format!(
        "{HEADER}#eval IO.FS.writeFile \"{}\" \"executed\"\n",
        sentinel.display()
    );

    let full_run_negatives: Vec<(&str, String)> = vec![
        (
            "implicit default Init",
            "-- anneal-trust-tier: vetted\nimport Init.Core\ndef x : Nat := 0\n".to_string(),
        ),
        (
            "foreign namespace spoof",
            format!("{HEADER}import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n"),
        ),
        (
            "Std import",
            "-- anneal-trust-tier: vetted\nprelude\nimport Std\n".to_string(),
        ),
        ("evaluation sentinel", eval_sentinel_src),
    ];

    for (_label, src) in &full_run_negatives {
        let mut f = TempFixture::new(Some(src));
        let _ = f.check_expected(Some(1), Some("preflight"), Some(false));
        assert!(!sentinel.exists(), "evaluation sentinel executed!");
    }

    let inspector_negatives: Vec<(&str, String)> = vec![
        (
            "module header",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nimport Init.Core\n"
                .to_string(),
        ),
        (
            "direct meta import",
            "-- anneal-trust-tier: vetted\nprelude\nmeta import Init.Core\n"
                .to_string(),
        ),
        (
            "direct all import",
            "-- anneal-trust-tier: vetted\nprelude\nimport all Init.Core\n"
                .to_string(),
        ),
        (
            "public import",
            "-- anneal-trust-tier: vetted\nprelude\npublic import Init.Core\n"
                .to_string(),
        ),
        (
            "nested unsafe",
            format!("{HEADER}open Nat in\nunsafe def x : Nat := 0\n"),
        ),
        (
            "term unsafe generated hook",
            format!("{HEADER}def generatedUnsafe : Nat := unsafe 0\n"),
        ),
        (
            "mutual unsafe",
            format!("{HEADER}mutual\n unsafe def x : Nat := 0\nend\n"),
        ),
        (
            "nested forbidden command",
            format!("{HEADER}open Nat in\n#eval 0\n"),
        ),
        (
            "nested attribute",
            format!(
                "{HEADER}structure X where\n @[extern \"foreign\"] x : Nat\n"
            ),
        ),
        (
            "implemented_by",
            format!("{HEADER}@[implemented_by other] def x : Nat := 0\n"),
        ),
        (
            "attribute removal",
            format!("{HEADER}attribute [-extern] Nat.add\n"),
        ),
        (
            "deriving",
            format!("{HEADER}structure X where\n x : Nat\nderiving Repr\n"),
        ),
        ("open scoped", format!("{HEADER}open scoped Nat\n")),
        (
            "set_option wrapper",
            format!(
                "{HEADER}set_option debug.skipKernelTC true in\ndef x : Nat := 0\n"
            ),
        ),
        ("custom macro", format!("{HEADER}macro \"x\" : term => `(0)\n")),
        (
            "native shortcut",
            format!("{HEADER}theorem x : True := by native_decide\n"),
        ),
        (
            "native decide config",
            format!("{HEADER}theorem x : True := by decide +native\n"),
        ),
        (
            "by_elab",
            format!(
                "{HEADER}def x : Nat := by_elab return Lean.mkNatLit 0\n"
            ),
        ),
        (
            "missing module trust tier",
            "prelude\nimport Init.NotationExtra\ndef x : Nat := 0\n"
                .to_string(),
        ),
        (
            "unknown candidate feature",
            "-- anneal-trust-tier: candidate:nonexistent\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "multiple module trust tiers",
            "-- anneal-trust-tier: vetted\n-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "invalid module trust tier",
            "-- anneal-trust-tier: bogus\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "legacy declaration trust attribute",
            format!("{HEADER}@[vetted] def x : Nat := 0\n"),
        ),
        ("malformed recovery", format!("{HEADER}def broken : :=\n")),
        (
            "decide +kernel",
            format!("{HEADER}theorem x : True := by decide +kernel\n"),
        ),
        ("decideBang", format!("{HEADER}theorem x : True := by decide!\n")),
        (
            "bv_decide",
            format!("{HEADER}theorem x : True := by bv_decide\n"),
        ),
        ("rfl'", format!("{HEADER}theorem x : True := by rfl'\n")),
        (
            "grind set_option",
            format!(
                "{HEADER}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        (
            "include_str",
            format!(
                "{HEADER}def x : String := include_str \"Trusted.lean\"\n"
            ),
        ),
        (
            "noncomputable section",
            format!("{HEADER}noncomputable section\n"),
        ),
        (
            "_root_ escape",
            format!(
                "{HEADER}namespace Trusted\ndef _root_.Spoof : Nat := 0\nend Trusted\n"
            ),
        ),
        (
            "section inside in-command",
            format!("{HEADER}section S in\ndef x : Nat := 0\n"),
        ),
        (
            "namespace inside in-command",
            format!("{HEADER}namespace A in\ndef x : Nat := 0\n"),
        ),
        (
            "with_decl_name% term",
            format!("{HEADER}def f : Nat := with_decl_name% Foo 0\n"),
        ),
        (
            "private_decl% term",
            format!("{HEADER}def f : Name := private_decl% f\n"),
        ),
        (
            "decl_name% term",
            format!("{HEADER}def f : Name := decl_name%\n"),
        ),
        (
            "namespace on RHS of in-command",
            format!("{HEADER}open Nat in\nnamespace A\n"),
        ),
        (
            "empty French-quote identifier",
            format!("{HEADER}def «» : Nat := 0\n"),
        ),
        (
            "tactic block in Trusted module",
            format!("{HEADER}theorem x : Eq 0 0 := by rfl\n"),
        ),
    ];

    let mut checker = Checker::new(&base_fix.root, None).unwrap();
    checker.tool_admission().unwrap();
    for (idx, (label, src)) in inspector_negatives.iter().enumerate() {
        let neg_path = checker.stage.join(format!("neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Trusted".to_string(), neg_path)],
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }

    // Verify that `SourceRole.theory` (`Anneal`) admits allowed tactics (`by
    // rfl`) while still rejecting disallowed tactics and tactic configurations
    // (`native_decide`, `decide +native`, `decide +kernel`, `decide!`,
    // `bv_decide`, `rfl'`, `grind`, `sorry`).
    let theory_header = "prelude\nimport Init.NotationExtra\n";
    let theory_pos_path = checker.stage.join("theory-pos.lean");
    fs::write(
        &theory_pos_path,
        format!("{theory_header}theorem ok : Eq 0 0 := by rfl\n").as_bytes(),
    )
    .unwrap();
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), theory_pos_path)],
        })
        .expect("expected theory module with `by rfl` to pass preflight");

    let theory_negatives: Vec<(&str, String)> = vec![
        (
            "theory native_decide",
            format!("{theory_header}theorem x : True := by native_decide\n"),
        ),
        (
            "theory decide +native",
            format!("{theory_header}theorem x : True := by decide +native\n"),
        ),
        (
            "theory decide +kernel",
            format!("{theory_header}theorem x : True := by decide +kernel\n"),
        ),
        (
            "theory decideBang",
            format!("{theory_header}theorem x : True := by decide!\n"),
        ),
        (
            "theory bv_decide",
            format!("{theory_header}theorem x : True := by bv_decide\n"),
        ),
        (
            "theory rfl'",
            format!("{theory_header}theorem x : True := by rfl'\n"),
        ),
        (
            "theory grind set_option",
            format!(
                "{theory_header}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        (
            "theory by sorry",
            format!("{theory_header}theorem x : False := by sorry\n"),
        ),
        (
            "theory term sorry",
            format!("{theory_header}theorem x : False := sorry\n"),
        ),
    ];
    for (idx, (label, src)) in theory_negatives.iter().enumerate() {
        let neg_path = checker.stage.join(format!("theory-neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), neg_path)],
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }
}

/// Verifies that `"preflight"` rejects surface `sorry` syntax before
/// compilation (`execution_began == false`), and that Phase 2 (`"audit"`)
/// rejects direct `sorryAx` applications (which use only allowed function
/// application syntax, so they reach Phase 2 where `sorryAx` is excluded from
/// `foundation-lock.json`'s axiom allowlist), both in `Trusted.lean` and in an
/// unimported `Trusted/Unused.lean` module discovered by `scan_lean_tree`.
#[test]
fn rejects_sorry_and_unreferenced_module_with_sorry() {
    let mut f_sorry = TempFixture::new(Some(&format!("{HEADER}theorem bad : False := by sorry\n")));
    let _ = f_sorry.check_expected(Some(1), Some("preflight"), Some(false));

    let mut f_sorry_ax = TempFixture::new(Some(&format!(
        "{HEADER}theorem bad : False := sorryAx False true\n"
    )));
    let _ = f_sorry_ax.check_expected(Some(1), Some("audit"), Some(true));

    let mut f_unused = TempFixture::new(None);
    fs::create_dir_all(f_unused.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_unused.root.join("trusted/lean/Trusted/Unused.lean"),
        format!("{HEADER}theorem unreferenced : False := sorryAx False true\n").as_bytes(),
    )
    .unwrap();
    let _ = f_unused.check_expected(Some(1), Some("audit"), Some(true));
}

/// Verifies that cyclic imports between modules are rejected during
/// `"preflight"` before compilation begins.
#[test]
fn rejects_source_import_cycles() {
    let mut fix = TempFixture::new(Some(&format!("{HEADER}import Trusted.Other\n")));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/Other.lean"),
        format!("{HEADER}import Trusted\n").as_bytes(),
    )
    .unwrap();
    let _ = fix.check_expected(Some(1), Some("preflight"), Some(false));
}

/// Verifies that `scan_lean_tree` rejects symlinks and pre-existing `.olean`
/// artifacts in the source tree, and `tool_admission` rejects `Init.*`
/// companion files on disk that are marked `null` in `foundation-lock.json`.
#[test]
fn rejects_symlinks_stale_oleans_and_unexpected_foundation_companions() {
    let mut f_sym = TempFixture::new(None);
    symlink(
        f_sym.root.join("trusted/lean/Trusted.lean"),
        f_sym.root.join("trusted/lean/Alias.lean"),
    )
    .unwrap();
    let _ = f_sym.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_stale = TempFixture::new(None);
    fs::write(f_stale.root.join("trusted/lean/Trusted.olean"), b"stale").unwrap();
    let _ = f_stale.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_companion = TempFixture::new(None);
    let lp = f_companion.root.join("trusted/lean/foundation-lock.json");
    let mut l: Json = serde_json::from_str(&fs::read_to_string(&lp).unwrap()).unwrap();
    l["modules"]["Init.Prelude"]["parts"]["olean.private"] = Json::Null;
    fs::write(&lp, serde_json::to_vec(&l).unwrap()).unwrap();
    let _ = f_companion.check_expected(Some(2), Some("foundation"), Some(false));

    let mut f_bad_sha = TempFixture::new(None);
    let lp_sha = f_bad_sha.root.join("trusted/lean/foundation-lock.json");
    let mut l_sha: Json = serde_json::from_str(&fs::read_to_string(&lp_sha).unwrap()).unwrap();
    l_sha["modules"]["Init.Prelude"]["parts"]["olean"] =
        json!("0000000000000000000000000000000000000000000000000000000000000000");
    fs::write(&lp_sha, serde_json::to_vec(&l_sha).unwrap()).unwrap();
    let err_sha = f_bad_sha
        .check_expected(Some(2), Some("foundation"), Some(false))
        .unwrap_err();
    assert!(
        err_sha
            .message
            .contains("foundation artifact SHA-256 mismatch for Init/Prelude.olean"),
        "unexpected error: {err_sha}"
    );

    let mut f_missing_root = TempFixture::new(None);
    fs::remove_file(f_missing_root.root.join("trusted/lean/Trusted.lean")).unwrap();
    fs::create_dir_all(f_missing_root.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_missing_root.root.join("trusted/lean/Trusted/Sub.lean"),
        HEADER.as_bytes(),
    )
    .unwrap();
    let err_missing_root = f_missing_root
        .check_expected(Some(1), Some("snapshot"), Some(false))
        .unwrap_err();
    assert!(
        err_missing_root
            .message
            .contains("missing Trusted.lean umbrella"),
        "unexpected error: {err_missing_root}"
    );

    let mut f_non_lean = TempFixture::new(None);
    fs::write(
        f_non_lean.root.join("trusted/lean/notes.txt"),
        b"unexpected",
    )
    .unwrap();
    let err_non_lean = f_non_lean
        .check_expected(Some(1), Some("snapshot"), Some(false))
        .unwrap_err();
    assert!(
        err_non_lean
            .message
            .contains("unexpected non-Lean file in source tree: notes.txt"),
        "unexpected error: {err_non_lean}"
    );

    let f_env = TempFixture::new(None);
    let chk_env = Checker::new_with_env(
        &f_env.root,
        None,
        vec![
            ("LD_PRELOAD".to_string(), "/tmp/evil.so".to_string()),
            ("LD_LIBRARY_PATH".to_string(), "/tmp".to_string()),
            ("RUSTC_WRAPPER".to_string(), "/tmp/evil".to_string()),
            ("HOME".to_string(), "/tmp/home".to_string()),
            ("PATH".to_string(), "/tmp/evil-bin".to_string()),
        ],
    )
    .unwrap();
    assert!(!chk_env.environment.contains_key("LD_PRELOAD"));
    assert!(!chk_env.environment.contains_key("LD_LIBRARY_PATH"));
    assert!(!chk_env.environment.contains_key("RUSTC_WRAPPER"));
    assert_eq!(
        chk_env.environment.get("HOME").map(String::as_str),
        Some("/tmp/home")
    );
    assert_eq!(
        chk_env.environment.get("PATH").map(String::as_str),
        Some("/usr/bin:/bin")
    );
}

/// Verifies defense-in-depth in Phase 2 (`"audit"`): even if a `.lean` file
/// declaring an `axiom` were compiled directly into a `.olean` (bypassing
/// `"preflight"`), `verifyAndCollectLocals` rejects the `.olean` because every
/// constant in `data.constants` is checked for `ci.isAxiom`, even when
/// unreferenced.
#[test]
fn rejects_unused_compiled_axiom() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.tool_admission().unwrap();
    let imports = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let setup_path = checker.write_setup_json("Trusted", &imports).unwrap();
    let unchecked = checker.stage.join("UnusedAxiom.lean");
    fs::write(
        &unchecked,
        b"prelude\nimport Init.Core\nnamespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n",
    )
    .unwrap();
    let out = checker.stage.join("Trusted.olean");
    checker
        .process(
            "axiom-fixture",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                unchecked.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.insert(
            "Trusted".to_string(),
            ModuleArtifacts {
                olean_parts: vec![out.to_string_lossy().into_owned()],
                ir_parts: Vec::new(),
            },
        );
        adm.graph.insert("Trusted".to_string(), imports);
    }
    let ax_err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(ax_err.code, 1);
    assert!(
        ax_err.message.contains("Trusted axiom AnyNamespace.unused"),
        "unexpected error: {ax_err}"
    );
}

/// Verifies that `check_cargo_boundary` rejects Cargo workspace members
/// outside `trusted/` and `path` dependencies from `trusted/` crates to paths
/// outside `trusted/`.
#[test]
fn rejects_cargo_workspace_members_and_path_deps_outside_trusted() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(None);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::copy(
        checkout.join("trusted/audit/Cargo.toml"),
        fix.root.join("trusted/audit/Cargo.toml"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &fix.root.join("trusted/rustc-capture"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &fix.root.join("trusted/cargo-anneal"),
    )
    .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::create_dir_all(fix.root.join("crates/untrusted-helper/src")).unwrap();
    fs::write(
        fix.root.join("crates/untrusted-helper/Cargo.toml"),
        b"[package]\nname = \"untrusted-helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(fix.root.join("crates/untrusted-helper/src/lib.rs"), b"").unwrap();
    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/cargo-anneal\",\n    \"crates/untrusted-helper\",\n]\n",
    )
    .unwrap();
    let err_member = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_member
            .message
            .contains("workspace member outside trusted/: crates/untrusted-helper")
    );

    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::write(
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_dep = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(err_dep.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper"
    ));

    fs::copy(
        checkout.join("trusted/rustc-capture/Cargo.toml"),
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
    )
    .unwrap();
    fs::create_dir_all(fix.root.join(".cargo")).unwrap();
    fs::write(
        fix.root.join(".cargo/config.toml"),
        b"[build]\nrustc-wrapper = \"evil\"\n",
    )
    .unwrap();
    let err_cargo_cfg = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_cargo_cfg
            .message
            .contains("forbidden Cargo/toolchain override at repository root: .cargo")
    );
    fs::remove_dir_all(fix.root.join(".cargo")).unwrap();

    fs::write(
        fix.root.join("rust-toolchain.toml"),
        b"[toolchain]\nchannel = \"nightly\"\n",
    )
    .unwrap();
    let err_toolchain = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_toolchain
            .message
            .contains("forbidden Cargo/toolchain override at repository root: rust-toolchain.toml")
    );
    fs::remove_file(fix.root.join("rust-toolchain.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\n[patch.crates-io]\nserde = { path = \"crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_patch = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_patch
            .message
            .contains("root Cargo.toml may contain only [workspace]"),
        "unexpected error: {err_patch}"
    );
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"evil\"\nversion = \"0.1.0\"\nsource = \"git+https://example.com/evil.git#deadbeef\"\n",
    )
    .unwrap();
    let err_lock = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_lock
            .message
            .contains("untrusted dependency source in Cargo.lock for evil")
    );
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"rogue-local\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let err_rogue_lock = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_rogue_lock
            .message
            .contains("untrusted local package without source in Cargo.lock: rogue-local"),
        "unexpected error: {err_rogue_lock}"
    );
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::copy(checkout.join("Cargo.lock"), fix.root.join("Cargo.lock")).unwrap();
    fs::copy(checkout.join("flake.nix"), fix.root.join("flake.nix")).unwrap();
    fs::copy(checkout.join("flake.lock"), fix.root.join("flake.lock")).unwrap();
    fs::copy(
        checkout.join("trusted/root-manifest.sha256"),
        fix.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::write(fix.root.join("flake.nix"), b"{ }\n").unwrap();
    let err_manifest = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_manifest
            .message
            .contains("root TCB manifest digest mismatch for flake.nix"),
        "unexpected error: {err_manifest}"
    );
}

/// Verifies module-level trust-tier non-contamination and `Trusted` namespace
/// hygiene:
/// - A `vetted` module referencing a `candidate:<feature>` constant is rejected
///   during `"audit"`.
/// - A `candidate:<feature>` module referencing a `vetted` or `candidate:*`
///   constant passes during `"audit"`.
/// - A `theory/Anneal.lean` module attempting to declare a constant inside the
///   reserved `Trusted` namespace (or an `opaque` constant) is rejected during
///   `"audit"`.
#[test]
fn enforces_module_level_trust_tiers_and_namespace_hygiene() {
    // 1. A vetted module (`Trusted.lean`) referencing a candidate constant in
    // `Trusted/Cand.lean` is rejected during `"audit"`.
    let mut f_contam = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.Cand\nnamespace Trusted\ndef badVetted : Prop := candHelper\nend Trusted\n"
    )));
    fs::create_dir_all(f_contam.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_contam.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_contam = f_contam
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_contam.message.contains(
            "vetted constant Trusted.badVetted references candidate:mir_semantics constant Trusted.candHelper"
        ),
        "unexpected error: {err_contam}"
    );

    // 2. Umbrella `Trusted.lean` (`vetted`) importing `Trusted.VettedSub`
    // (`vetted`) and `Trusted.Cand` (`candidate:mir_semantics`), where
    // `Trusted.Cand` references `Trusted.VettedSub` and `theory/Anneal.lean`
    // references both, passes cleanly.
    let mut f_ok = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.VettedSub\nimport Trusted.Cand\n"
    )));
    fs::create_dir_all(f_ok.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/VettedSub.lean"),
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef vettedProp : Prop := True\nend Trusted\n",
    )
    .unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.VettedSub\nnamespace Trusted\ndef candProp : Prop := vettedProp\nend Trusted\n",
    )
    .unwrap();
    fs::create_dir_all(f_ok.root.join("theory")).unwrap();
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ntheorem uses_both : Trusted.candProp := True.intro\nend Anneal\n",
    )
    .unwrap();
    let rep_ok = f_ok.check_expected(None, None, None).unwrap();
    assert_eq!(rep_ok.get("replay"), Some(&json!(true)));

    // 3. `theory/Anneal.lean` attempting to declare a constant inside the
    // reserved `Trusted` namespace is rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
    )
    .unwrap();
    let err_spoof = f_ok
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_spoof.message.contains(
            "non-Trusted module Anneal cannot declare constant Trusted.Spoof in Trusted namespace"
        ),
        "unexpected error: {err_spoof}"
    );

    // 4. `theory/Anneal.lean` attempting to declare an `opaque` constant is
    // rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\nopaque badOpaque : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let err_opaque = f_ok
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_opaque.message.contains(
            "opaque declaration Anneal.badOpaque in Anneal is not allowed outside Trusted"
        ),
        "unexpected error: {err_opaque}"
    );
}

/// Verifies that `verify_upstream_pin` and `Checker::run()` enforce
/// `vendor/lean-miri/UPSTREAM_PIN.json` and reject whole-directory deletion,
/// missing manifests, modified or unlisted `.lean` files, symlinks,
/// unauthorized `patched_files`, and invalid `execution_machine_closure`
/// entries with policy exit code `1`.
#[test]
fn verifies_upstream_pin_and_rejects_tampering() {
    let checkout = repo_root();
    let pin = anneal_audit::verify_upstream_pin(&checkout.join("vendor/lean-miri")).unwrap();
    assert_eq!(pin.schema_version, 2);
    assert_eq!(pin.vendor_tree.file_count, 608);
    assert_eq!(pin.patched_files.len(), 10);
    assert_eq!(pin.execution_machine_closure.len(), 160);

    // 1. Deleting `vendor/` in a repository checkout fails `Checker::run()`
    // with policy exit code `1` (`miri-pin`).
    let mut fix_missing_dir = TempFixture::new(None);
    fs::copy(
        checkout.join("Cargo.toml"),
        fix_missing_dir.root.join("Cargo.toml"),
    )
    .unwrap();
    fs::copy(
        checkout.join("Cargo.lock"),
        fix_missing_dir.root.join("Cargo.lock"),
    )
    .unwrap();
    fs::copy(
        checkout.join("flake.nix"),
        fix_missing_dir.root.join("flake.nix"),
    )
    .unwrap();
    fs::copy(
        checkout.join("flake.lock"),
        fix_missing_dir.root.join("flake.lock"),
    )
    .unwrap();
    fs::copy(
        checkout.join("trusted/root-manifest.sha256"),
        fix_missing_dir.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    fs::copy(
        checkout.join("trusted/audit/Cargo.toml"),
        fix_missing_dir.root.join("trusted/audit/Cargo.toml"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &fix_missing_dir.root.join("trusted/rustc-capture"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &fix_missing_dir.root.join("trusted/cargo-anneal"),
    )
    .unwrap();
    let err_no_vendor = fix_missing_dir
        .check_expected(Some(1), Some("miri-pin"), Some(false))
        .unwrap_err();
    assert!(
        err_no_vendor
            .message
            .contains("expected regular vendor directory"),
        "unexpected error: {err_no_vendor}"
    );

    // Prepare a mutable copy of `vendor/lean-miri` for tampering tests.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    anneal_audit::verify_upstream_pin(&vendor_copy).unwrap();

    // 2. Modified `.lean` file digest mismatch is rejected.
    let target_lean = vendor_copy.join("Miri.lean");
    let orig_lean = fs::read(&target_lean).unwrap();
    fs::write(&target_lean, b"-- tampered\n").unwrap();
    let err_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_tamper.code, 1);
    assert!(
        err_tamper
            .message
            .contains("vendor file SHA-256 mismatch for Miri.lean"),
        "unexpected error: {err_tamper}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 3. Unlisted `.lean` file is rejected.
    let rogue_lean = vendor_copy.join("Miri/Rogue.lean");
    fs::write(&rogue_lean, b"def x := 1\n").unwrap();
    let err_unlisted = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_unlisted.code, 1);
    assert!(
        err_unlisted
            .message
            .contains("unlisted Lean file in vendor/lean-miri: Miri/Rogue.lean"),
        "unexpected error: {err_unlisted}"
    );
    fs::remove_file(&rogue_lean).unwrap();

    // 4. Symlink inside `vendor/lean-miri` is rejected.
    #[cfg(unix)]
    {
        let link_path = vendor_copy.join("Miri/Symlink.lean");
        std::os::unix::fs::symlink(&target_lean, &link_path).unwrap();
        let err_symlink = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
        assert_eq!(err_symlink.code, 1);
        assert!(
            err_symlink
                .message
                .contains("symlink forbidden in vendor/lean-miri"),
            "unexpected error: {err_symlink}"
        );
        fs::remove_file(&link_path).unwrap();
    }

    // 5. Unauthorized `patched_files` entry, mismatched `patched_sha256`
    // between `patched_files` and `vendor_tree`, and missing `patched_sha256`
    // annotation in `vendor_tree` are rejected.
    let pin_path = vendor_copy.join("UPSTREAM_PIN.json");
    let orig_pin_bytes = fs::read(&pin_path).unwrap();
    let mut pin_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_json["patched_files"]
        .as_array_mut()
        .unwrap()
        .push(json!({
            "path": "Miri.lean",
            "upstream_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
            "patched_sha256": "1111111111111111111111111111111111111111111111111111111111111111",
            "rationale": "unauthorized patch"
        }));
    fs::write(&pin_path, serde_json::to_vec(&pin_json).unwrap()).unwrap();
    let err_unauth_patch = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_unauth_patch.code, 1);
    assert!(
        err_unauth_patch
            .message
            .contains("unauthorized patched file in UPSTREAM_PIN.json: Miri.lean"),
        "unexpected error: {err_unauth_patch}"
    );

    let mut pin_mismatch_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_mismatch_json["patched_files"][0]["patched_sha256"] =
        json!("2222222222222222222222222222222222222222222222222222222222222222");
    fs::write(&pin_path, serde_json::to_vec(&pin_mismatch_json).unwrap()).unwrap();
    let err_patch_mismatch = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_patch_mismatch.code, 1);
    assert!(
        err_patch_mismatch
            .message
            .contains("patched_sha256 mismatch between patched_files and vendor_tree"),
        "unexpected error: {err_patch_mismatch}"
    );

    let mut pin_missing_annot_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    for entry in pin_missing_annot_json["vendor_tree"]["files"]
        .as_array_mut()
        .unwrap()
    {
        if entry["path"].as_str() == Some("Miri/Interpreter/Call.lean") {
            entry.as_object_mut().unwrap().remove("patched_sha256");
        }
    }
    fs::write(
        &pin_path,
        serde_json::to_vec(&pin_missing_annot_json).unwrap(),
    )
    .unwrap();
    let err_missing_annot = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_missing_annot.code, 1);
    assert!(
        err_missing_annot.message.contains(
            "inconsistent patched_sha256 annotation in vendor_tree for Miri/Interpreter/Call.lean"
        ),
        "unexpected error: {err_missing_annot}"
    );

    // 6. Forbidden `Miri.Input.NativeMathHost` or empty
    // `execution_machine_closure` is rejected.
    let mut pin_closure_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_closure_json["execution_machine_closure"] = json!([{
        "module": "Miri.Input.NativeMathHost",
        "path": "Miri/Input/NativeMathHost.lean",
        "olean_sha256": "0000000000000000000000000000000000000000000000000000000000000000"
    }]);
    fs::write(&pin_path, serde_json::to_vec(&pin_closure_json).unwrap()).unwrap();
    let err_bad_closure = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_bad_closure.code, 1);
    assert!(
        err_bad_closure
            .message
            .contains("invalid execution_machine_closure entry for Miri.Input.NativeMathHost"),
        "unexpected error: {err_bad_closure}"
    );

    pin_closure_json["execution_machine_closure"] = json!([]);
    fs::write(&pin_path, serde_json::to_vec(&pin_closure_json).unwrap()).unwrap();
    let err_empty_closure = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_empty_closure.code, 1);
    assert!(
        err_empty_closure
            .message
            .contains("expected 160 execution_machine_closure entries in UPSTREAM_PIN.json, got 0"),
        "unexpected error: {err_empty_closure}"
    );

    // 7. Modifying `UPSTREAM_PIN.json` without updating
    // `LOCKED_UPSTREAM_PIN_SHA256` is rejected.
    let mut pin_notes_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_notes_json["notes"]
        .as_array_mut()
        .unwrap()
        .push(json!("extra note"));
    fs::write(&pin_path, serde_json::to_vec(&pin_notes_json).unwrap()).unwrap();
    let err_pin_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_pin_sha.code, 1);
    assert!(
        err_pin_sha
            .message
            .contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_pin_sha}"
    );

    // 8. Missing `UPSTREAM_PIN.json` is rejected with policy exit code `1`.
    fs::remove_file(&pin_path).unwrap();
    let err_missing_pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_missing_pin.code, 1);
    assert!(
        err_missing_pin
            .message
            .contains("missing UPSTREAM_PIN.json"),
        "unexpected error: {err_missing_pin}"
    );
}

/// Verifies that Pass 2 (`"correspondence-audit"`) rejects a `.vendorMiri`
/// module that declares a constant in the reserved `Trusted` or `Anneal` root
/// namespace (including a `private` declaration) or declares an `axiom`, while
/// a vendor constant outside those roots passes those checks and fails only
/// later, when the required correspondence claims are missing.
#[test]
fn rejects_vendor_constants_in_reserved_namespaces() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    // Pass 1 compiles the fixture's `Trusted` umbrella into `<stage>/lib`.
    checker.run().unwrap();
    let trusted_lib = checker.stage.join("lib");
    let vendor_src = checker.stage.join("src/fake-miri");
    let vendor_lib = checker.stage.join("fake-miri-lib");
    let cases: [(&str, &str, Option<&str>); 8] = [
        (
            "Miri.SpoofTrusted",
            "namespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
            Some(
                "external module Miri.SpoofTrusted cannot declare constant \
                 Trusted.Spoof in reserved Trusted namespace",
            ),
        ),
        (
            "Miri.SpoofAnneal",
            "namespace Anneal\ndef Spoof : Nat := 0\nend Anneal\n",
            Some(
                "external module Miri.SpoofAnneal cannot declare constant \
                 Anneal.Spoof in reserved Anneal namespace",
            ),
        ),
        (
            "Miri.SpoofPrivate",
            "namespace Trusted\nprivate def hidden : Nat := 0\nend Trusted\n",
            Some("in reserved Trusted namespace"),
        ),
        (
            "Miri.SpoofAxiom",
            "namespace Miri.SpoofAxiom\naxiom spoofAx : False\nend Miri.SpoofAxiom\n",
            Some("vendor Miri module Miri.SpoofAxiom cannot declare axiom Miri.SpoofAxiom.spoofAx"),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nunsafe def step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "unsafe/partial constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\npartial def step (n : Nat) : Nat := step n\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nopaque step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        (
            "Miri.Benign",
            "namespace Miri.Benign\ndef ok : Nat := 0\nend Miri.Benign\n",
            None,
        ),
    ];
    for (module, body, expected) in cases {
        let rel = module.replace('.', "/");
        let src = vendor_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, format!("prelude\nimport Init.Core\n{body}")).unwrap();
        let out = vendor_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        checker
            .process(
                &format!("compile-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-R".to_string(),
                    vendor_src.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out.to_string_lossy().into_owned(),
                    src.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        let err = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec![module.to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(err.code, 1, "unexpected error code for {module}: {err}");
        assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
        match expected {
            Some(message) => assert!(
                err.message.contains(message),
                "unexpected error for {module}: {err}"
            ),
            None => {
                assert!(
                    !err.message.contains("reserved"),
                    "benign vendor module {module} was rejected: {err}"
                );
                assert!(
                    err.message.contains("missing required claim"),
                    "unexpected error for {module}: {err}"
                );
            }
        }
    }
}

/// Verifies non-backsliding enforcement on `Trusted.MirAst`,
/// `Trusted.MirSemantics`, and `Anneal.MirWp` core theorems and canaries in
/// Pass 1 (`"audit"`) and required correspondence directories and claims in
/// Pass 2 (`--require-correspondence`).
#[test]
fn enforces_mir_wp_and_correspondence_non_backsliding() {
    // 1. With default `Checker::new` (`require_mir_wp == true`), deleting both
    // `Trusted/MirSemantics.lean` and `Anneal/MirWp.lean` (even when
    // `Trusted/MirAst.lean` is present) is rejected fail-closed.
    let fix_missing_both = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\n",
    ));
    fs::create_dir_all(fix_missing_both.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_missing_both.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    let mut checker_missing_both = Checker::new(&fix_missing_both.root, None).unwrap();
    let err_missing_both = checker_missing_both.run().unwrap_err();
    assert_eq!(err_missing_both.code, 1);
    assert!(
        err_missing_both
            .message
            .contains("missing required trusted module Trusted.MirSemantics"),
        "unexpected error: {err_missing_both}"
    );

    // 2. If `Trusted.MirAst` and `Trusted.MirSemantics` are present without
    // `Anneal.MirWp`, Pass 1 `"audit"` rejects.
    let mut fix_no_wp = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nimport Trusted.MirSemantics\n",
    ));
    fs::create_dir_all(fix_no_wp.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    let err_no_wp = fix_no_wp
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_no_wp
            .message
            .contains("missing required theory module Anneal.MirWp"),
        "unexpected error: {err_no_wp}"
    );

    // 3. If `Anneal.MirWp` weakens or omits its required theorems/canaries,
    // Pass 1 `"audit"` rejects.
    let mut fix = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nimport Trusted.MirSemantics\n",
    ));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Anneal.MirWp\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("theory/Anneal/MirWp.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal.MirWp\ntheorem wellFormed_and_spec_of_wp : True := True.intro\nend Anneal.MirWp\n",
    )
    .unwrap();
    let err_wp = fix
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_wp.message.contains(
            "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must prove Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg directly"
        ),
        "unexpected error: {err_wp}"
    );

    // 4. When `require_correspondence` is enabled and correspondence
    // directories are absent, `Checker::run` rejects in `"correspondence"`.
    let fix_missing_corr = TempFixture::new(None);
    let mut checker = Checker::new(&fix_missing_corr.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.set_require_correspondence(true);
    let err_corr = checker.run().unwrap_err();
    assert_eq!(err_corr.code, 1);
    assert_eq!(err_corr.phase, "correspondence");
    assert!(
        err_corr
            .message
            .contains("missing required correspondence directories"),
        "unexpected error: {err_corr}"
    );

    // 5. Pass 2 (`InspectorRequest::CorrespondenceAudit`) enforces
    // `verifyCorrespondenceClaims` (required constant references on
    // `CorrespondenceClaim` and exact claim-type proof checking on
    // `correspondence_claim_holds`) and `verifyRefEvaluatorIndependence`
    // (required Miri primitives and forbidden `Trusted.MirSemantics.*`
    // evaluator references in `evalRefStep` / `initRefState`).
    let compile_stage_mod = |checker: &mut Checker,
                             root_dir: &Path,
                             out_dir: &Path,
                             imports: &[&str],
                             module: &str,
                             body: &str| {
        let rel = module.replace('.', "/");
        let src = root_dir.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = out_dir.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        let mut edges = vec![anneal_audit::ImportEdge {
            module: "Init.Core".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }];
        for imp in imports {
            edges.push(anneal_audit::ImportEdge {
                module: (*imp).to_string(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
        }
        let setup_path = checker.write_setup_json(module, &edges).unwrap();
        checker
            .process(
                &format!("compile-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "--setup".to_string(),
                    setup_path.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out.to_string_lossy().into_owned(),
                    src.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        let available = BTreeMap::from([("olean", out.to_string_lossy().into_owned())]);
        let arts =
            anneal_audit::ModuleArtifacts::from_available(&available, "test", String::new).unwrap();
        checker
            .admitted
            .as_mut()
            .unwrap()
            .artifacts
            .insert(module.to_string(), arts);
    };

    let fix_pass2 = TempFixture::new(None);
    let mut checker_pass2 = Checker::new(&fix_pass2.root, None).unwrap();
    checker_pass2.set_require_mir_wp(false);
    checker_pass2.run().unwrap();
    let trusted_lib = checker_pass2.stage.join("lib");
    let corr_src = checker_pass2.stage.join("src/fake-corr");
    let corr_lib = checker_pass2.stage.join("fake-corr-lib");
    let vendor_src = checker_pass2.stage.join("src/fake-vendor");
    let vendor_lib = checker_pass2.stage.join("fake-vendor-lib");
    let search_paths = vec![trusted_lib.clone(), vendor_lib.clone(), corr_lib.clone()];

    compile_stage_mod(
        &mut checker_pass2,
        &vendor_src,
        &vendor_lib,
        &[],
        "Miri.FakeStubs",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         def step : Nat := 0\n\
         def stepHooks : Nat := 0\n\
         def withValidation : Nat := 0\n\
         def operandHooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionMachine\n\
         namespace Miri.Interpreter.Step\n\
         def step : Nat := 0\n\
         def evalStatement : Nat := 0\n\
         end Miri.Interpreter.Step\n\
         namespace Miri.Interpreter.MachineHooks\n\
         def takeLastPendingMoveDeinit : Nat := 0\n\
         def recordPendingMoveDeinit : Nat := 0\n\
         end Miri.Interpreter.MachineHooks\n\
         namespace Miri.Interpreter.FnArg\n\
         def copyFnArg : Nat := 0\n\
         end Miri.Interpreter.FnArg\n\
         namespace Miri.Interpreter.Call\n\
         def deinitInPlaceArg : Nat := 0\n\
         end Miri.Interpreter.Call\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         end Miri.Memory.ScalarInt\n\
         namespace Miri.Interpreter\n\
         def evalOperand : Nat := 0\n\
         def evalPlaceToOp : Nat := 0\n\
         def localToOp : Nat := 0\n\
         def placeWriteLocalImmediate : Nat := 0\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         def runRvalue : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.Discriminant\n\
         def readDiscriminant : Nat := 0\n\
         def discriminantForVariant : Nat := 0\n\
         end Miri.Interpreter.Discriminant\n\
         namespace Miri.Interpreter.Frame\n\
         def storageLive : Nat := 0\n\
         def storageDead : Nat := 0\n\
         end Miri.Interpreter.Frame\n\
         namespace Miri.Interpreter.ControlFlow\n\
         def goToBlock : Nat := 0\n\
         def evalTerminator : Nat := 0\n\
         def returnFromCurrentFrame : Nat := 0\n\
         end Miri.Interpreter.ControlFlow\n",
    );

    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def WellFormed : Prop := True\n\
         def Behavior : Prop := True\n\
         def Diverges : Prop := True\n\
         def ReachesResult : Prop := True\n\
         def enumAdmitted : Nat := 0\n\
         def evalStep : Nat := 0\n\
         end Trusted.MirSemantics\n",
    );

    // 4a. Weakened `CorrespondenceClaim` (missing
    // `Trusted.MirSemantics.WellFormed` reference) is rejected by
    // `verifyCorrespondenceClaims`.
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\n\
         def CorrespondenceClaim : Prop := True\n\
         end Trusted.Correspondence\n",
    );
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : Trusted.Correspondence.CorrespondenceClaim := True.intro\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let run_corr_audit = |checker: &mut Checker| {
        checker.inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search_paths.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.MirSemantics".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.FakeStubs".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
    };
    let err_weak_claim = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_claim.code, 1);
    assert_eq!(err_weak_claim.phase, "correspondence-audit");
    assert!(
        err_weak_claim.message.contains(
            "claim Trusted.Correspondence.CorrespondenceClaim body must reference Trusted.MirSemantics.WellFormed"
        ),
        "unexpected error: {err_weak_claim}"
    );

    // 4b. When all required claims and proofs are present,
    // `verifyCorrespondenceClaims` succeeds and
    // `verifyRefEvaluatorIndependence` rejects an `evalRefStep` that omits
    // required Miri primitives or illegally references
    // `Trusted.MirSemantics.evalStep`.
    let all_claims_src = |eval_ref_step_body: &str| {
        format!(
            "prelude\nimport Init.Core\nimport Miri.FakeStubs\nimport Trusted.MirSemantics\n\
             namespace Trusted.Correspondence\n\
             def RefWellFormed : Prop := True\n\
             def RefBehavior : Prop := True\n\
             def RefDiverges : Prop := True\n\
             def encodeProg : Nat := 0\n\
             def RefReachesOutcome : Prop := True\n\
             def faultToRefOutcome : Nat := 0\n\
             def CorrespondenceClaim : Prop :=\n\
               Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
               Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
             def FaultEquivalenceClaim : Prop :=\n\
               Trusted.MirSemantics.ReachesResult ∧ RefReachesOutcome ∧\n\
               faultToRefOutcome = encodeProg\n\
             def MiriMoveDeinitWiringClaim : Prop :=\n\
               Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
               Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
               Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.evalOperand ∧\n\
               Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
               Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg\n\
             def DecodeProgEncodeProgClaim : Prop := True\n\
             def EncodeProgTypesCanonicalClaim : Prop := True\n\
             def EncodeStmtNoDormantNoopsClaim : Prop := True\n\
             def EncodeRvalueBinaryOpIffClaim : Prop := True\n\
             def EncodeRvalueUnaryOpIffClaim : Prop := True\n\
             def EncodeStmtAssignIffClaim : Prop := True\n\
             def StateUniqueOfSimulationInvClaim : Prop := True\n\
             def RefStateUniqueOfSimulationInvClaim : Prop := True\n\
             def InitRefStateSimClaim : Prop := True\n\
             def EvalRefStepEqClaim : Prop := True\n\
             def SimOfRefStepClaim : Prop := True\n\
             def SimOfRefReachesClaim : Prop := True\n\
             def RefWellFormedOfWellFormedClaim : Prop := True\n\
             def RefBehaviorOfBehaviorClaim : Prop := True\n\
             def BehaviorOfRefBehaviorClaim : Prop := True\n\
             def BehaviorIffRefBehaviorClaim : Prop := True\n\
             def DivergesIffRefDivergesClaim : Prop := True\n\
             def CanaryD6UseAfterMoveUbClaim : Prop := True\n\
             def CanaryD7aBinopCopyThenMoveOkClaim : Prop := True\n\
             def CanaryD7bBinopMoveThenCopyUbClaim : Prop := True\n\
             def CanaryD7cBinopMoveThenMoveUbClaim : Prop := True\n\
             def CanaryD8SelfMoveOkClaim : Prop := True\n\
             def CanaryD9MoveUnitZstOkClaim : Prop := True\n\
             def CanaryD10AddUncheckedOverflowUbClaim : Prop := True\n\
             def CanaryD11EnumDiscriminantAndConstOkClaim : Prop := True\n\
             def CanaryD12ZstEnumMoveAndDiscrOkClaim : Prop := True\n\
             def CanaryD13EnumInvalidTagAndUninitUbClaim : Prop := True\n\
             def initRefState : Nat := 0\n\
             def evalRefStep : Nat := {eval_ref_step_body}\n\
             end Trusted.Correspondence\n"
        )
    };
    let all_proofs_src = "prelude\nimport Trusted.Correspondence\n\
        namespace Anneal.MirCorrespondenceProof\n\
        open Trusted.Correspondence\n\
        theorem correspondence_claim_holds : CorrespondenceClaim :=\n\
          ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
        theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=\n\
          ⟨True.intro, True.intro, Eq.refl _⟩\n\
        theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim :=\n\
          ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩\n\
        theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim := True.intro\n\
        theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim := True.intro\n\
        theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim := True.intro\n\
        theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim := True.intro\n\
        theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim := True.intro\n\
        theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim := True.intro\n\
        theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim := True.intro\n\
        theorem refState_unique_of_simulationInv : RefStateUniqueOfSimulationInvClaim := True.intro\n\
        theorem initRefState_sim : InitRefStateSimClaim := True.intro\n\
        theorem evalRefStep_eq : EvalRefStepEqClaim := True.intro\n\
        theorem sim_of_refStep : SimOfRefStepClaim := True.intro\n\
        theorem sim_of_refReaches : SimOfRefReachesClaim := True.intro\n\
        theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim := True.intro\n\
        theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim := True.intro\n\
        theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim := True.intro\n\
        theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim := True.intro\n\
        theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim := True.intro\n\
        theorem anneal_corresponds_to_miri : CorrespondenceClaim := correspondence_claim_holds\n\
        theorem reachesResult_fault_iff_refReachesOutcome : FaultEquivalenceClaim := fault_equivalence_claim_holds\n\
        theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim := True.intro\n\
        theorem canary_D7a_binop_copy_then_move_ok : CanaryD7aBinopCopyThenMoveOkClaim := True.intro\n\
        theorem canary_D7b_binop_move_then_copy_ub : CanaryD7bBinopMoveThenCopyUbClaim := True.intro\n\
        theorem canary_D7c_binop_move_then_move_ub : CanaryD7cBinopMoveThenMoveUbClaim := True.intro\n\
        theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim := True.intro\n\
        theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim := True.intro\n\
        theorem canary_D10_add_unchecked_overflow_ub : CanaryD10AddUncheckedOverflowUbClaim := True.intro\n\
        theorem canary_D11_enum_discriminant_and_const_ok : CanaryD11EnumDiscriminantAndConstOkClaim := True.intro\n\
        theorem canary_D12_zst_enum_move_and_discr_ok : CanaryD12ZstEnumMoveAndDiscrOkClaim := True.intro\n\
        theorem canary_D13_enum_invalid_tag_and_uninit_ub : CanaryD13EnumInvalidTagAndUninitUbClaim := True.intro\n\
        end Anneal.MirCorrespondenceProof\n";

    let corr_deps = ["Miri.FakeStubs", "Trusted.MirSemantics"];
    let proof_deps = ["Trusted.Correspondence"];
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src("0"),
    );
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        all_proofs_src,
    );
    let err_missing_miri = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_missing_miri.code, 1);
    assert_eq!(err_missing_miri.phase, "correspondence-audit");
    assert!(
        err_missing_miri.message.contains(
            "reference evaluator cone is missing required Miri primitive Miri.Interpreter.Step.step"
        ),
        "unexpected error: {err_missing_miri}"
    );

    let all_miri_plus_anneal_step = "let _ := (\
        Miri.Interpreter.Step.step, \
        Miri.Interpreter.IntegerOps.binary, \
        Miri.Interpreter.IntegerOps.binaryBool, \
        Miri.Interpreter.IntegerOps.unary, \
        Miri.Memory.ScalarInt.truncateFromUInt, \
        Miri.Memory.ScalarInt.tryFromUInt, \
        Miri.Memory.ScalarInt.tryToBool, \
        Miri.Interpreter.evalOperand, \
        Miri.Interpreter.evalPlaceToOp, \
        Miri.Interpreter.localToOp, \
        Miri.Interpreter.placeWriteLocalImmediate, \
        Miri.Interpreter.evalRvalueIntoPlace, \
        Miri.Interpreter.runRvalue, \
        Miri.Interpreter.Discriminant.readDiscriminant, \
        Miri.Interpreter.Discriminant.discriminantForVariant, \
        Miri.Interpreter.Step.evalStatement, \
        Miri.Interpreter.Frame.storageLive, \
        Miri.Interpreter.Frame.storageDead, \
        Miri.Interpreter.ControlFlow.goToBlock, \
        Miri.Interpreter.ControlFlow.evalTerminator, \
        Miri.Interpreter.ControlFlow.returnFromCurrentFrame); \
        Trusted.MirSemantics.evalStep";
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(all_miri_plus_anneal_step),
    );
    compile_stage_mod(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        all_proofs_src,
    );
    let err_forbidden_anneal = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_forbidden_anneal.code, 1);
    assert_eq!(err_forbidden_anneal.phase, "correspondence-audit");
    assert!(
        err_forbidden_anneal.message.contains(
            "reference evaluator cone illegally references M_anneal evaluator Trusted.MirSemantics.evalStep"
        ),
        "unexpected error: {err_forbidden_anneal}"
    );
}
