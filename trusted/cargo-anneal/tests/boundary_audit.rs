// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the `trusted/audit` boundary gate and
//! `TrustedBoundary.lean` kernel-environment inspector.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use cargo_anneal::audit::{
    Checker, Failure, Json, PARTS, ReleaseChannel, check_cargo_boundary,
    default_lean_path,
};

static FIXTURE_COUNTER: AtomicUsize = AtomicUsize::new(0);

const HEADER: &str = "prelude\nimport Init.Core\n";

const EXPAND_MACRO: &str = "namespace Trusted\n\
@[macro Lean.Parser.Command.declaration, macro Lean.Parser.Command.mutual]\n\
def expandTrustDeclaration : Lean.Macro := fun stx =>\n  \
  let emptyArr : Array Lean.Syntax := Array.mk List.nil\n  \
  let setArg (s : Lean.Syntax) (i : Nat) (v : Lean.Syntax) : Lean.Syntax :=\n    \
    match s, i with\n    \
    | .node info k (.mk (_ :: r)), 0 => .node info k (.mk (v :: r))\n    \
    | .node info k (.mk (a :: _ :: r)), 1 => .node info k (.mk (a :: v :: r))\n    \
    | .node info k (.mk (a :: b :: _ :: r)), 2 => .node info k (.mk (a :: b :: v :: r))\n    \
    | .node info k (.mk (a :: b :: c :: d :: _ :: r)), 4 => .node info k (.mk (a :: b :: c :: d :: v :: r))\n    \
    | other, _ => other\n  \
  let stripAttrs (mods : Lean.Syntax) : Bool × Lean.Syntax :=\n    \
    let attrsNode := mods.getArg 1\n    \
    match attrsNode.getArgs.toList with\n    \
    | .nil => (false, mods)\n    \
    | inner :: _ =>\n      \
      let (changed, kept) := List.foldl (fun (chg, acc) elem =>\n        \
        if elem.getKind == `Lean.Parser.Term.attrInstance then\n          \
          let attr := elem.getArg 1\n          \
          if attr.getKind == `Lean.Parser.Attr.simple &&\n              \
              ((attr.getArg 0).getId == `vetted || (attr.getArg 0).getId == `candidate) then\n            \
            (true, acc)\n          \
          else (chg, acc.push elem)\n        \
        else (chg, acc)) (false, emptyArr) (inner.getArg 1).getArgs.toList\n      \
      if !changed then (false, mods) else\n        \
        match kept.toList with\n        \
        | .nil => (true, setArg mods 1 (.node .none `null emptyArr))\n        \
        | first :: rest =>\n          \
          let sep := List.foldl (fun acc e => (acc.push (.atom .none \",\")).push e) (emptyArr.push first) rest\n          \
          (true, setArg mods 1 (setArg attrsNode 0 (setArg inner 1 (.node .none `null sep))))\n  \
  let stripDecl (s : Lean.Syntax) : Bool × Lean.Syntax :=\n    \
    if s.getKind != `Lean.Parser.Command.declaration then (false, s) else\n      \
      let (mc, mods') := stripAttrs (s.getArg 0)\n      \
      let decl := s.getArg 1\n      \
      let (dc, decl') :=\n        \
        if decl.getKind != `Lean.Parser.Command.inductive then (false, decl) else\n          \
          let (cc, ctors') := List.foldl (fun (c, acc) ctor =>\n            \
            let (kc, m') := stripAttrs (ctor.getArg 2)\n            \
            (c || kc, acc.push (if kc then setArg ctor 2 m' else ctor))) (false, emptyArr) (decl.getArg 4).getArgs.toList\n          \
          (cc, if cc then setArg decl 4 (.node .none `null ctors') else decl)\n      \
      (mc || dc, if mc || dc then setArg (setArg s 0 mods') 1 decl' else s)\n  \
  if stx.getKind == `Lean.Parser.Command.mutual then\n    \
    let (mc, items') := List.foldl (fun (c, acc) item =>\n      \
      let (ic, item') := stripDecl item\n      \
      (c || ic, acc.push item')) (false, emptyArr) (stx.getArg 1).getArgs.toList\n    \
    if mc then pure (setArg stx 1 (.node .none `null items')) else Lean.Macro.throwUnsupported\n  \
  else\n    \
    let (c, stx') := stripDecl stx\n    \
    if c then pure stx' else Lean.Macro.throwUnsupported\n\
end Trusted\n";

struct TempFixture {
    root: PathBuf,
    stages: Vec<PathBuf>,
}

impl TempFixture {
    fn new(source: Option<&str>, full_lock: bool) -> Self {
        let checkout = repo_root();
        let id = FIXTURE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let root = env::temp_dir().join(format!(
            "anneal-boundary-test-{}-{id}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("trusted/audit")).unwrap();
        fs::create_dir_all(root.join("trusted/lean")).unwrap();
        fs::copy(
            checkout.join("trusted/lean/lean-toolchain"),
            root.join("trusted/lean/lean-toolchain"),
        )
        .unwrap();
        if full_lock {
            fs::copy(
                checkout.join("trusted/lean/foundation-lock.json"),
                root.join("trusted/lean/foundation-lock.json"),
            )
            .unwrap();
        } else {
            fs::write(
                root.join("trusted/lean/foundation-lock.json"),
                core_lock_json(&checkout).as_bytes(),
            )
            .unwrap();
        }
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
        Self {
            root,
            stages: Vec::new(),
        }
    }

    fn check_expected(
        &mut self,
        expected_code: Option<i32>,
        expected_phase: Option<&str>,
        expected_executed: Option<bool>,
    ) -> Result<Json, Failure> {
        let mut checker =
            Checker::new(&self.root, None, Some(&self.root)).unwrap();
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
        self.stages.push(checker.stage);
        outcome
    }
}

impl Drop for TempFixture {
    fn drop(&mut self) {
        for stage in &self.stages {
            let _ = fs::remove_dir_all(stage);
        }
        let _ = fs::remove_dir_all(&self.root);
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

fn core_lock_json(checkout: &Path) -> String {
    let full_lock_text =
        fs::read_to_string(checkout.join("trusted/lean/foundation-lock.json"))
            .unwrap();
    let full_lock_data = Json::parse(&full_lock_text).unwrap();
    let core_keys: BTreeSet<&str> = [
        "Init.Prelude",
        "Init.Coe",
        "Init.Notation",
        "Init.Tactics",
        "Init.SizeOf",
        "Init.Core",
    ]
    .into_iter()
    .collect();

    let mut core_lock_obj = full_lock_data.as_obj().unwrap().clone();
    let filtered_modules: BTreeMap<String, Json> = core_lock_obj
        .get("modules")
        .unwrap()
        .as_obj()
        .unwrap()
        .iter()
        .filter(|(k, _)| core_keys.contains(k.as_str()))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let filtered_graph: BTreeMap<String, Json> = core_lock_obj
        .get("graph")
        .unwrap()
        .as_obj()
        .unwrap()
        .iter()
        .filter(|(k, _)| core_keys.contains(k.as_str()))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    core_lock_obj.insert("modules".to_string(), Json::Obj(filtered_modules));
    core_lock_obj.insert("graph".to_string(), Json::Obj(filtered_graph));
    Json::Obj(core_lock_obj).to_compact_string()
}

fn header_with_macro() -> String {
    format!("{HEADER}{EXPAND_MACRO}")
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
    let mut fix =
        TempFixture::new(Some("prelude\nimport Init.NotationExtra\n"), true);
    let rep = fix.check_expected(None, None, None).unwrap();
    assert_eq!(rep.get("kernelDeclarations").and_then(Json::as_i64), Some(0));
    assert_eq!(rep.get("axioms"), Some(&Json::Arr(Vec::new())));
    assert_eq!(rep.get("replay"), Some(&Json::Bool(true)));
}

/// Verifies that `tests/fixtures/positive.lean` passes under hostile
/// `LEAN_PATH` and `LEAN_SYSROOT` environment variables pointing at corrupt
/// `.olean` files, and that `private` helpers, `opaque` definitions, recursors,
/// typeclass instances, and coercions are all recorded in the dependency
/// closure.
#[test]
fn audits_positive_fixture_under_hostile_ambient_paths() {
    let positive_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/positive.lean");
    let positive = fs::read_to_string(positive_path).unwrap();
    let mut fix = TempFixture::new(Some(&positive), true);
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
    let mut checker =
        Checker::new_with_env(&fix.root, None, Some(&fix.root), hostile_env)
            .unwrap();
    let rep = checker.run().unwrap();
    fix.stages.push(checker.stage);

    let decls = rep.get("declarations").and_then(Json::as_arr).unwrap();
    let k_decls = rep.get("kernelDeclarations").and_then(Json::as_i64).unwrap();
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
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    assert!(sealed_deps.contains(helper.as_str()));
    assert_eq!(
        decl_map["Outside.sealed"].get("kind").and_then(Json::as_str),
        Some("opaque")
    );
    assert!(decl_map.contains_key("Outside.Box.rec"));
    assert!(decl_map.contains_key("Outside.Indexed.rec"));
    assert!(decl_map.keys().any(|n| n.starts_with("Outside.Tree")));

    let inferred_deps: Vec<&str> = decl_map["Outside.inferred"]
        .get("dependencies")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let coerced_deps: BTreeSet<&str> = decl_map["Outside.coerced"]
        .get("dependencies")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let axioms: BTreeSet<&str> = rep
        .get("axioms")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let expected_axioms: BTreeSet<&str> =
        ["Classical.choice", "Quot.sound", "propext"]
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
        "{HEADER}import Init.Data.PLift\n{EXPAND_MACRO}@[vetted] def usesExtra (x : PLift Nat) : Bool := decide (x = x)\n"
    );
    let mut fix = TempFixture::new(Some(&src), false);
    let lock_path = fix.root.join("trusted/lean/foundation-lock.json");
    let mut lock = Json::parse(&fs::read_to_string(&lock_path).unwrap()).unwrap();
    let lean_exec = fs::canonicalize(default_lean_path()).unwrap();
    let prefix = lean_exec.parent().unwrap().parent().unwrap();
    let extra = "Init.Data.PLift";
    let mut extra_parts = BTreeMap::new();
    for part in PARTS {
        let p = prefix
            .join("lib/lean")
            .join(format!("Init/Data/PLift.{part}"));
        if p.exists() {
            extra_parts.insert(part.to_string(), Json::Str("present".to_string()));
        } else {
            extra_parts.insert(part.to_string(), Json::Null);
        }
    }
    let mut extra_rec = BTreeMap::new();
    extra_rec.insert(
        "sourceSha256".to_string(),
        Json::Str("present".to_string()),
    );
    extra_rec.insert("parts".to_string(), Json::Obj(extra_parts));
    lock.as_obj_mut()
        .unwrap()
        .get_mut("modules")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .insert(extra.to_string(), Json::Obj(extra_rec));
    let mut edge_obj = BTreeMap::new();
    edge_obj.insert("module".to_string(), Json::Str("Init.Core".to_string()));
    edge_obj.insert("importAll".to_string(), Json::Bool(false));
    edge_obj.insert("isExported".to_string(), Json::Bool(true));
    edge_obj.insert("isMeta".to_string(), Json::Bool(false));
    lock.as_obj_mut()
        .unwrap()
        .get_mut("graph")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .insert(extra.to_string(), Json::Arr(vec![Json::Obj(edge_obj)]));
    fs::write(&lock_path, lock.to_compact_string().as_bytes()).unwrap();

    let rep = fix.check_expected(None, None, None).unwrap();
    let has_plift = rep
        .get("declarations")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .find(|d| d.get("name").and_then(Json::as_str) == Some("usesExtra"))
        .and_then(|d| d.get("dependencies"))
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .any(|x| x.as_str() == Some("instDecidableEqPLift"));
    assert!(
        rep.get("graph")
            .and_then(Json::as_obj)
            .unwrap()
            .contains_key(extra)
    );
    assert!(has_plift);
}

/// Verifies that Phase 1 (`"preflight"`) rejects forbidden headers, imports,
/// commands (`#eval`), terms (`unsafe`, `by_elab`), tactics (`native_decide`,
/// `decide +native`), attributes (`@[extern]`, `@[implemented_by]`), and
/// invalid or missing `@[vetted]` / `@[candidate]` annotations before Lean
/// ever compiles or executes the file (`execution_began == false`).
#[test]
fn rejects_forbidden_syntax_and_attributes_without_executing_eval() {
    let mut base_fix = TempFixture::new(None, false);
    let sentinel = base_fix.root.join("must-not-exist");
    let eval_sentinel_src = format!(
        "{HEADER}#eval IO.FS.writeFile \"{}\" \"executed\"\n",
        sentinel.display()
    );

    let full_run_negatives: Vec<(&str, String)> = vec![
        (
            "implicit default Init",
            "import Init.Core\n@[vetted] def x : Nat := 0\n".to_string(),
        ),
        (
            "foreign namespace spoof",
            format!(
                "{HEADER}import Foreign\nnamespace Trusted\n@[vetted] def x : Nat := 0\nend Trusted\n"
            ),
        ),
        ("Std import", "prelude\nimport Std\n".to_string()),
        ("evaluation sentinel", eval_sentinel_src),
    ];

    for (_label, src) in &full_run_negatives {
        let mut f = TempFixture::new(Some(src), false);
        let _ = f.check_expected(Some(1), Some("preflight"), Some(false));
        assert!(!sentinel.exists(), "evaluation sentinel executed!");
    }

    let inspector_negatives: Vec<(&str, String)> = vec![
        ("module header", "module\nprelude\nimport Init.Core\n".to_string()),
        ("direct meta import", "prelude\nmeta import Init.Core\n".to_string()),
        ("direct all import", "prelude\nimport all Init.Core\n".to_string()),
        ("public import", "prelude\npublic import Init.Core\n".to_string()),
        (
            "nested unsafe",
            format!("{HEADER}open Nat in\n@[vetted] unsafe def x : Nat := 0\n"),
        ),
        (
            "term unsafe generated hook",
            format!("{HEADER}@[vetted] def generatedUnsafe : Nat := unsafe 0\n"),
        ),
        (
            "mutual unsafe",
            format!("{HEADER}mutual\n @[vetted] unsafe def x : Nat := 0\nend\n"),
        ),
        ("nested forbidden command", format!("{HEADER}open Nat in\n#eval 0\n")),
        (
            "nested attribute",
            format!(
                "{HEADER}@[vetted] structure X where\n @[extern \"foreign\"] x : Nat\n"
            ),
        ),
        (
            "implemented_by",
            format!("{HEADER}@[vetted, implemented_by other] def x : Nat := 0\n"),
        ),
        (
            "attribute removal",
            format!("{HEADER}attribute [-extern] Nat.add\n"),
        ),
        (
            "deriving",
            format!("{HEADER}@[vetted] structure X where\n x : Nat\nderiving Repr\n"),
        ),
        ("open scoped", format!("{HEADER}open scoped Nat\n")),
        (
            "set_option wrapper",
            format!(
                "{HEADER}set_option debug.skipKernelTC true in\n@[vetted] def x : Nat := 0\n"
            ),
        ),
        ("custom macro", format!("{HEADER}macro \"x\" : term => `(0)\n")),
        (
            "native shortcut",
            format!("{HEADER}@[vetted] theorem x : True := by native_decide\n"),
        ),
        (
            "native decide config",
            format!("{HEADER}@[vetted] theorem x : True := by decide +native\n"),
        ),
        (
            "by_elab",
            format!(
                "{HEADER}@[vetted] def x : Nat := by_elab return Lean.mkNatLit 0\n"
            ),
        ),
        ("missing trust attribute", format!("{HEADER}def x : Nat := 0\n")),
        (
            "unnamed instance",
            format!("{HEADER}@[vetted] instance : Inhabited Nat := ⟨0⟩\n"),
        ),
        (
            "vetted constructor on candidate inductive",
            format!(
                "{HEADER}@[candidate mir_ast]\ninductive Bad where\n  | @[vetted] mk : Bad\n"
            ),
        ),
        (
            "unknown candidate feature",
            format!("{HEADER}@[candidate nonexistent] def x : Nat := 0\n"),
        ),
        (
            "multiple trust attributes",
            format!("{HEADER}@[vetted, candidate mir_ast] def x : Nat := 0\n"),
        ),
        ("malformed recovery", format!("{HEADER}def broken : :=\n")),
    ];

    let mut checker =
        Checker::new(&base_fix.root, None, Some(&base_fix.root)).unwrap();
    checker.tool_admission().unwrap();
    for (idx, (label, src)) in inspector_negatives.iter().enumerate() {
        let neg_path = checker.stage.join(format!("neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let mut pf_fields = BTreeMap::new();
        pf_fields.insert(
            "sources".to_string(),
            Json::Arr(vec![Json::Arr(vec![
                Json::Str("Trusted".to_string()),
                Json::Str(neg_path.to_string_lossy().into_owned()),
            ])]),
        );
        let err = checker
            .inspect("preflight", pf_fields)
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }
    base_fix.stages.push(checker.stage);
}

/// Verifies that Phase 2 (`"audit"`) rejects `sorry` and `sorryAx` (which is
/// excluded from `foundation-lock.json`'s axiom allowlist), both in
/// `Trusted.lean` and in an unimported `Trusted/Unused.lean` module discovered
/// by `scan_lean_tree`.
#[test]
fn rejects_sorry_and_unreferenced_module_with_sorry() {
    let hm = header_with_macro();
    let mut f_sorry = TempFixture::new(
        Some(&format!("{hm}@[vetted] theorem bad : False := by sorry\n")),
        false,
    );
    let _ = f_sorry.check_expected(Some(1), Some("audit"), Some(true));

    let mut f_sorry_ax = TempFixture::new(
        Some(&format!(
            "{hm}@[vetted] theorem bad : False := sorryAx False true\n"
        )),
        false,
    );
    let _ = f_sorry_ax.check_expected(Some(1), Some("audit"), Some(true));

    let mut f_unused = TempFixture::new(None, false);
    fs::create_dir_all(f_unused.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_unused.root.join("trusted/lean/Trusted/Unused.lean"),
        format!("{hm}@[vetted] theorem unreferenced : False := by sorry\n")
            .as_bytes(),
    )
    .unwrap();
    let _ = f_unused.check_expected(Some(1), Some("audit"), Some(true));
}

/// Verifies that cyclic imports between modules are rejected during
/// `"preflight"` before compilation begins.
#[test]
fn rejects_source_import_cycles() {
    let mut fix = TempFixture::new(
        Some(&format!("{HEADER}import Trusted.Other\n")),
        false,
    );
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
    let mut f_sym = TempFixture::new(None, false);
    symlink(
        f_sym.root.join("trusted/lean/Trusted.lean"),
        f_sym.root.join("trusted/lean/Alias.lean"),
    )
    .unwrap();
    let _ = f_sym.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_stale = TempFixture::new(None, false);
    fs::write(f_stale.root.join("trusted/lean/Trusted.olean"), b"stale")
        .unwrap();
    let _ = f_stale.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_companion = TempFixture::new(None, false);
    let lp = f_companion.root.join("trusted/lean/foundation-lock.json");
    let mut l = Json::parse(&fs::read_to_string(&lp).unwrap()).unwrap();
    l.as_obj_mut()
        .unwrap()
        .get_mut("modules")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .get_mut("Init.Prelude")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .get_mut("parts")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .insert("olean.private".to_string(), Json::Null);
    fs::write(&lp, l.to_compact_string().as_bytes()).unwrap();
    let _ = f_companion.check_expected(
        Some(2),
        Some("foundation"),
        Some(false),
    );
}

/// Verifies defense-in-depth in Phase 2 (`"audit"`): even if a `.lean` file
/// declaring an `axiom` were compiled directly into a `.olean` (bypassing
/// `"preflight"`), `verifyAndCollectLocals` rejects the `.olean` because every
/// constant in `data.constants` is checked for `ci.isAxiom`, even when
/// unreferenced.
#[test]
fn rejects_unused_compiled_axiom() {
    let mut fix = TempFixture::new(None, false);
    let mut checker =
        Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    checker.tool_admission().unwrap();
    let mut imp_obj = BTreeMap::new();
    imp_obj.insert("module".to_string(), Json::Str("Init.Core".to_string()));
    imp_obj.insert("importAll".to_string(), Json::Bool(false));
    imp_obj.insert("isExported".to_string(), Json::Bool(true));
    imp_obj.insert("isMeta".to_string(), Json::Bool(false));
    let imports = vec![Json::Obj(imp_obj)];
    let setup_path = checker.write_setup_json("Trusted", &imports).unwrap();
    let unchecked = checker.stage.join("UnusedAxiom.lean");
    fs::write(
        &unchecked,
        format!(
            "{HEADER}namespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n"
        )
        .as_bytes(),
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
    checker.artifacts.insert(
        "Trusted".to_string(),
        vec![vec![out.to_string_lossy().into_owned()], Vec::new()],
    );
    checker
        .graph
        .insert("Trusted".to_string(), Json::Arr(imports));
    let mut af = BTreeMap::new();
    af.insert(
        "trusted".to_string(),
        Json::Arr(vec![Json::Str("Trusted".to_string())]),
    );
    af.insert("theory".to_string(), Json::Arr(Vec::new()));
    af.insert("hasCrate".to_string(), Json::Bool(false));
    af.insert("trustDeclarations".to_string(), Json::Arr(Vec::new()));
    let ax_err = checker.inspect("audit", af).unwrap_err();
    fix.stages.push(checker.stage);
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
    let mut fix = TempFixture::new(None, false);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
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
    assert!(
        err_dep.message.contains(
            "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper"
        )
    );
}

/// Verifies that `verify_crate` accepts a valid `(Mir, Proof)` pair proving
/// `Trusted.CrateTheorem Mir.crate` via `theory/`, and rejects a `Proof`
/// proving a weaker theorem (`True`), a `Mir` declaring a `theorem`, or a
/// `Mir` importing untrusted `Anneal` (`theory/`).
#[test]
fn enforces_crate_verification_mir_data_only_and_exact_theorem_type() {
    let hm = header_with_macro();
    let mut fix = TempFixture::new(
        Some(&format!(
            "{hm}namespace Trusted\n@[vetted] structure Crate where tag : Nat\n@[vetted] def CrateTheorem (_ : Crate) : Prop := True\nend Trusted\n"
        )),
        false,
    );
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ndef untrustedTag : Nat := 0\ntheorem prove_crate (c : Trusted.Crate) : Trusted.CrateTheorem c := True.intro\nend Anneal\n",
    )
    .unwrap();

    let write_crate = |root: &Path, sub: &str, mir: &str, proof: &str| -> PathBuf {
        let crate_dir = root.join(sub);
        fs::create_dir_all(crate_dir.join("src")).unwrap();
        fs::create_dir_all(crate_dir.join(".anneal")).unwrap();
        fs::write(
            crate_dir.join("src/lib.rs"),
            b"pub fn id(x: usize) -> usize { x }\n",
        )
        .unwrap();
        fs::write(crate_dir.join(".anneal/Mir.lean"), mir.as_bytes()).unwrap();
        fs::write(crate_dir.join(".anneal/Proof.lean"), proof.as_bytes())
            .unwrap();
        crate_dir
    };

    // 1. Valid crate verification using `Anneal.prove_crate` in Proof.
    let c_ok = write_crate(
        &fix.root,
        "crate-ok",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_crate Mir.crate\nend Proof\n",
    );
    let mut chk_ok = Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let rep_ok = chk_ok.verify_crate(&c_ok).unwrap();
    fix.stages.push(chk_ok.stage);
    let cv_ok = rep_ok.get("crateVerification").unwrap();
    assert_eq!(
        cv_ok.get("verifiedTheorem").and_then(Json::as_str),
        Some("Proof.verify_crate")
    );
    assert_eq!(cv_ok.get("replay"), Some(&Json::Bool(true)));

    // 2. Wrong theorem type (`theorem verify_crate : True`).
    let c_wrong_ty = write_crate(
        &fix.root,
        "crate-wrong-ty",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : True := True.intro\nend Proof\n",
    );
    let mut chk_wrong_ty =
        Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let err_wrong_ty = chk_wrong_ty.verify_crate(&c_wrong_ty).unwrap_err();
    fix.stages.push(chk_wrong_ty.stage);
    assert_eq!(err_wrong_ty.code, 1);
    assert_eq!(err_wrong_ty.phase, "audit");
    assert!(
        err_wrong_ty
            .message
            .contains("expected Trusted.CrateTheorem Mir.crate")
    );

    // 3. Theorem declared inside `Mir.lean`.
    let c_mir_thm = write_crate(
        &fix.root,
        "crate-mir-thm",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\ntheorem sneaky : True := True.intro\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_crate Mir.crate\nend Proof\n",
    );
    let mut chk_mir_thm =
        Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let err_mir_thm = chk_mir_thm.verify_crate(&c_mir_thm).unwrap_err();
    fix.stages.push(chk_mir_thm.stage);
    assert_eq!(err_mir_thm.code, 1);
    assert_eq!(err_mir_thm.phase, "audit");
    assert!(
        err_mir_thm
            .message
            .contains("Mir module must contain only data declarations")
    );

    // 4. `Mir.lean` attempting to import untrusted `Anneal`.
    let c_mir_imp = write_crate(
        &fix.root,
        "crate-mir-imp",
        "prelude\nimport Trusted\nimport Anneal\nnamespace Mir\ndef crate : Trusted.Crate := { tag := Anneal.untrustedTag }\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_crate Mir.crate\nend Proof\n",
    );
    let mut chk_mir_imp =
        Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let err_mir_imp = chk_mir_imp.verify_crate(&c_mir_imp).unwrap_err();
    fix.stages.push(chk_mir_imp.stage);
    assert_eq!(err_mir_imp.code, 1);
    assert_eq!(err_mir_imp.phase, "preflight");
    assert!(
        err_mir_imp
            .message
            .contains("Mir.lean imports disallowed modules")
    );
}

/// Verifies `@[vetted]` vs. `@[candidate]` non-contamination and
/// release-channel
/// gating:
/// - A `@[vetted]` definition referencing a `@[candidate]` constant without a
///   `Trusted.candidate` guard is rejected during `"audit"`.
/// - A crate using only `@[vetted]` constructors of an extensible `@[vetted]`
///   inductive passes on `ReleaseChannel::Stable` with zero active candidate
///   features.
/// - A crate using a `@[candidate]` constructor is rejected by default
///   (`VettedOnly`), accepted on `ReleaseChannel::Alpha` when opted in (while
///   reporting unused opted-in features), and rejected on
///   `ReleaseChannel::Stable` even with `allow-candidate-features = ["*"]`.
#[test]
fn enforces_vetted_vs_candidate_non_contamination_and_trust_policy() {
    let hm = header_with_macro();
    let mut f_contam = TempFixture::new(
        Some(&format!(
            "{hm}namespace Trusted\n@[candidate mir_semantics] def candHelper : Prop := True\n@[vetted] def badVetted : Prop := candHelper\nend Trusted\n"
        )),
        false,
    );
    let err_contam = f_contam
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_contam.message.contains(
            "references candidate:mir_semantics declaration Trusted.candHelper without a Trusted.candidate guard"
        )
    );

    let trusted_src = format!(
        "{hm}namespace Trusted\n\
         @[vetted] def candidate (_feature : String) {{α : Sort u}} (x : α) : α := x\n\
         @[vetted] inductive Crate where\n  \
           | base : Crate\n  \
           | @[candidate mir_semantics] ext : Crate\n\
         @[candidate mir_semantics] def evalExt : Prop := True\n\
         @[vetted] def CrateTheorem (c : Crate) : Prop :=\n  \
           match c with\n  \
           | .base => True\n  \
           | .ext => Trusted.candidate \"mir_semantics\" evalExt\n\
         end Trusted\n"
    );
    let mut fix = TempFixture::new(Some(&trusted_src), false);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ntheorem prove_base : Trusted.CrateTheorem Trusted.Crate.base := True.intro\ntheorem prove_ext : Trusted.CrateTheorem Trusted.Crate.ext := True.intro\nend Anneal\n",
    )
    .unwrap();

    // 1. Crate using only `@[vetted]` constructor `base` passes on Stable.
    let c_base = fix.root.join("crate-base");
    fs::create_dir_all(c_base.join("src")).unwrap();
    fs::create_dir_all(c_base.join(".anneal")).unwrap();
    fs::write(c_base.join("src/lib.rs"), b"pub fn id(x: usize) -> usize { x }\n")
        .unwrap();
    fs::write(
        c_base.join(".anneal/Mir.lean"),
        b"prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := Trusted.Crate.base\nend Mir\n",
    )
    .unwrap();
    fs::write(
        c_base.join(".anneal/Proof.lean"),
        b"prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_base\nend Proof\n",
    )
    .unwrap();
    let mut chk_base = Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let rep_base = chk_base
        .verify_crate_with_policy(&c_base, Some(ReleaseChannel::Stable), None)
        .unwrap();
    fix.stages.push(chk_base.stage);
    assert_eq!(
        rep_base
            .get("crateVerification")
            .and_then(|cv| cv.get("candidateFeatures")),
        Some(&Json::Arr(Vec::new()))
    );

    // 2. Crate using `@[candidate mir_semantics]` constructor `ext` is
    // rejected by default VettedOnly, accepted on Alpha when enabled, and
    // rejected on Stable even when enabled.
    let c_ext = fix.root.join("crate-ext");
    fs::create_dir_all(c_ext.join("src")).unwrap();
    fs::create_dir_all(c_ext.join(".anneal")).unwrap();
    fs::write(c_ext.join("src/lib.rs"), b"pub fn id(x: usize) -> usize { x }\n")
        .unwrap();
    fs::write(
        c_ext.join(".anneal/Mir.lean"),
        b"prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := Trusted.Crate.ext\nend Mir\n",
    )
    .unwrap();
    fs::write(
        c_ext.join(".anneal/Proof.lean"),
        b"prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_ext\nend Proof\n",
    )
    .unwrap();

    let mut chk_ext1 = Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let err_ext1 = chk_ext1.verify_crate(&c_ext).unwrap_err();
    fix.stages.push(chk_ext1.stage);
    assert_eq!(err_ext1.code, 1);
    assert_eq!(err_ext1.phase, "candidate-policy");
    assert!(
        err_ext1
            .message
            .contains("candidate-trusted feature `mir_semantics` is not enabled")
    );

    let mut chk_ext2 = Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let allow_list = vec!["mir_semantics".to_string(), "memory".to_string()];
    let rep_ext2 = chk_ext2
        .verify_crate_with_policy(
            &c_ext,
            Some(ReleaseChannel::Alpha),
            Some(&allow_list),
        )
        .unwrap();
    fix.stages.push(chk_ext2.stage);
    let cv_ext2 = rep_ext2.get("crateVerification").unwrap();
    assert_eq!(
        cv_ext2.get("candidateFeatures"),
        Some(&Json::Arr(vec![Json::Str("mir_semantics".to_string())]))
    );
    assert_eq!(
        cv_ext2.get("unusedCandidateFeatures"),
        Some(&Json::Arr(vec![Json::Str("memory".to_string())]))
    );

    let mut chk_ext3 = Checker::new(&fix.root, None, Some(&fix.root)).unwrap();
    let allow_all = vec!["*".to_string()];
    let err_ext3 = chk_ext3
        .verify_crate_with_policy(
            &c_ext,
            Some(ReleaseChannel::Stable),
            Some(&allow_all),
        )
        .unwrap_err();
    fix.stages.push(chk_ext3.stage);
    assert_eq!(err_ext3.code, 1);
    assert_eq!(err_ext3.phase, "candidate-policy");
    assert!(
        err_ext3
            .message
            .contains("stable release channel forbids candidate-trusted features")
    );
}
