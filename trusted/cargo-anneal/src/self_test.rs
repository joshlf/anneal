// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bounded regression fixtures for the `trusted/audit` boundary gate and
//! `TrustedBoundary.lean` inspector.
//!
//! Exercises all 14 positive and negative fixture groups covering foundation
//! lock containment, syntax preflight rejections, complete inventory discovery,
//! cycle detection, symlink and foundation integrity, subprocess protocol
//! faults, statement (`ci.type`) vs. proof (`ci.value?`) origin separation,
//! Cargo workspace DAG containment, `CaptureManifest.json` integrity,
//! `verify-crate` exact theorem checks, and `@[vetted]` vs.
//! `@[candidate <feature>]` non-contamination and trust policy gating.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::audit::{
    Checker, DownstreamTarget, Failure, Json, MAX_BYTES, PARTS, ReleaseChannel,
    TOOLCHAIN, check_cargo_boundary, default_lean_path, digest, dir_byte_size,
    verify_capture_manifest,
};

static SUITE_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Run all 14 bounded regression fixture groups against `checkout` and `lean`.
pub fn run_self_test(checkout: &Path, lean: Option<&Path>) -> i32 {
    let suite_id = SUITE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let suite = env::temp_dir().join(format!(
        "anneal-trusted-tests-{}-{}",
        std::process::id(),
        suite_id
    ));
    if let Err(e) = fs::create_dir_all(&suite) {
        eprintln!("SELF-TEST FAILED: cannot create suite dir: {e}");
        return 2;
    }

    match run_self_test_inner(checkout, lean, &suite) {
        Ok((count, elapsed)) => {
            println!(
                "PASS: {count} fixture groups in {:.1}s; sequential, no research builds",
                elapsed.as_secs_f64()
            );
            let _ = fs::remove_dir_all(&suite);
            0
        }
        Err(msg) => {
            let _ = fs::write(suite.join("failure.traceback"), msg.as_bytes());
            eprintln!(
                "SELF-TEST FAILED: {msg}\nPreserved fixture sources/raw logs: {}",
                suite.display()
            );
            2
        }
    }
}

fn run_self_test_inner(
    checkout: &Path,
    lean: Option<&Path>,
    suite: &Path,
) -> Result<(usize, Duration), String> {
    let started = Instant::now();
    let mut passed: Vec<String> = Vec::new();
    let mut sequence = 0usize;
    let mut disposable: Vec<PathBuf> = Vec::new();

    let check_budget = |suite_dir: &Path| -> Result<(), String> {
        if started.elapsed() > Duration::from_secs(300) {
            return Err("self-test exceeded five-minute envelope".to_string());
        }
        let size = dir_byte_size(suite_dir).map_err(|e| e.to_string())?;
        if size > MAX_BYTES {
            return Err(
                "self-test exceeded 512 MiB retained envelope".to_string()
            );
        }
        Ok(())
    };

    let full_lock_text =
        fs::read_to_string(checkout.join("trusted/lean/foundation-lock.json"))
            .map_err(|e| e.to_string())?;
    let full_lock_data = Json::parse(&full_lock_text)?;
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
    let core_lock_text = Json::Obj(core_lock_obj).to_compact_string();

    let header = "prelude\nimport Init.Core\n";
    let expand_macro = "namespace Trusted\n\
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
    let header_with_macro = format!("{header}{expand_macro}");

    let mut make_fixture =
        |source: Option<&str>, full_lock: bool| -> Result<PathBuf, String> {
            check_budget(suite)?;
            sequence += 1;
            let root = suite.join(format!("fixture-{sequence:03}"));
            fs::create_dir_all(root.join("trusted/audit"))
                .map_err(|e| e.to_string())?;
            fs::create_dir_all(root.join("trusted/lean"))
                .map_err(|e| e.to_string())?;
            fs::copy(
                checkout.join("trusted/lean/lean-toolchain"),
                root.join("trusted/lean/lean-toolchain"),
            )
            .map_err(|e| e.to_string())?;
            if full_lock {
                fs::copy(
                    checkout.join("trusted/lean/foundation-lock.json"),
                    root.join("trusted/lean/foundation-lock.json"),
                )
                .map_err(|e| e.to_string())?;
            } else {
                fs::write(
                    root.join("trusted/lean/foundation-lock.json"),
                    core_lock_text.as_bytes(),
                )
                .map_err(|e| e.to_string())?;
            }
            fs::copy(
                checkout.join("trusted/audit/TrustedBoundary.lean"),
                root.join("trusted/audit/TrustedBoundary.lean"),
            )
            .map_err(|e| e.to_string())?;
            fs::write(
                root.join("trusted/lean/Trusted.lean"),
                source.unwrap_or(header).as_bytes(),
            )
            .map_err(|e| e.to_string())?;
            Ok(root)
        };

    let checked = |root: &Path,
                   expected: Option<i32>,
                   phase: Option<&str>,
                   executed: Option<bool>,
                   check_downstream: bool,
                   targets: Option<&[DownstreamTarget]>,
                   disposable_out: &mut Vec<PathBuf>|
     -> Result<Result<Json, Failure>, String> {
        let mut checker = Checker::new(root, lean, Some(suite))
            .map_err(|e| e.to_string())?;
        let outcome = checker.run_with_targets(check_downstream, targets);
        match &outcome {
            Err(err) => {
                if expected != Some(err.code)
                    || phase.is_some_and(|p| err.phase != p)
                {
                    return Err(format!(
                        "unexpected {}/{}: {}; {}",
                        err.code,
                        err.phase,
                        err,
                        checker.stage.display()
                    ));
                }
                if let Some(exp_exec) = executed
                    && checker.execution_began != exp_exec
                {
                    return Err(format!(
                        "expected execution_began={exp_exec}, got {}",
                        checker.execution_began
                    ));
                }
            }
            Ok(_) => {
                if expected.is_some() {
                    return Err(format!(
                        "expected rejection, got success: {}",
                        checker.stage.display()
                    ));
                }
            }
        }
        disposable_out.push(checker.stage);
        Ok(outcome)
    };

    let mut done = |label: &str,
                    disposable_out: &mut Vec<PathBuf>|
     -> Result<(), String> {
        check_budget(suite)?;
        passed.push(label.to_string());
        println!("  PASS {label}");
        for path in disposable_out.drain(..) {
            let _ = fs::remove_dir_all(path);
        }
        Ok(())
    };

    // Group 1: Empty inventory, exact compiled foundation DAG, replay.
    let f1 = make_fixture(Some("prelude\nimport Init.NotationExtra\n"), true)?;
    let rep1 =
        checked(&f1, None, None, None, false, None, &mut disposable)?.unwrap();
    if rep1.get("kernelDeclarations").and_then(Json::as_i64) != Some(0)
        || rep1.get("axioms") != Some(&Json::Arr(Vec::new()))
        || rep1.get("replay") != Some(&Json::Bool(true))
    {
        return Err("Group 1 assertion failed".to_string());
    }
    done(
        "empty inventory, exact compiled foundation DAG, replay",
        &mut disposable,
    )?;

    // Group 2: positive.lean with hostile ambient search paths and stale outputs.
    let positive =
        fs::read_to_string(checkout.join("tests/trusted-boundary/positive.lean"))
            .map_err(|e| e.to_string())?;
    let f2 = make_fixture(Some(&positive), true)?;
    let stale = suite.join("stale");
    fs::create_dir_all(&stale).map_err(|e| e.to_string())?;
    fs::write(stale.join("Trusted.olean"), b"not an olean")
        .map_err(|e| e.to_string())?;
    let mut hostile_env: Vec<(String, String)> = env::vars().collect();
    hostile_env.push((
        "LEAN_PATH".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    hostile_env.push((
        "LEAN_SYSROOT".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    let mut checker2 =
        Checker::new_with_env(&f2, lean, Some(suite), hostile_env)
            .map_err(|e| e.to_string())?;
    let rep2 = checker2
        .run(false)
        .map_err(|e| format!("Group 2 run failed: {e}"))?;
    disposable.push(checker2.stage);

    let decls2 = rep2.get("declarations").and_then(Json::as_arr).unwrap();
    let k_decls2 =
        rep2.get("kernelDeclarations").and_then(Json::as_i64).unwrap();
    if k_decls2 != decls2.len() as i64 || decls2.len() <= 30 {
        return Err("Group 2 declaration count failed".to_string());
    }
    let mut decl_map: BTreeMap<String, &Json> = BTreeMap::new();
    for d in decls2 {
        let name = d.get("name").and_then(Json::as_str).unwrap().to_string();
        decl_map.insert(name, d);
    }
    let helper = decl_map
        .keys()
        .find(|n| n.starts_with("_private.") && n.ends_with(".Outside.helper"))
        .ok_or("Group 2 missing private helper")?
        .clone();
    let sealed_deps: BTreeSet<&str> = decl_map["Outside.sealed"]
        .get("dependencies")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    if !sealed_deps.contains(helper.as_str())
        || decl_map["Outside.sealed"].get("kind").and_then(Json::as_str)
            != Some("opaque")
        || !decl_map.contains_key("Outside.Box.rec")
        || !decl_map.contains_key("Outside.Indexed.rec")
        || !decl_map.keys().any(|n| n.starts_with("Outside.Tree"))
    {
        return Err("Group 2 structural checks failed".to_string());
    }
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
    let axioms2: BTreeSet<&str> = rep2
        .get("axioms")
        .and_then(Json::as_arr)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let expected_ax2: BTreeSet<&str> =
        ["Classical.choice", "Quot.sound", "propext"]
            .into_iter()
            .collect();
    if !inferred_deps.iter().any(|n| n.contains("instWrap"))
        || !coerced_deps.contains("Outside.Box.value")
        || !decl_map.keys().any(|n| n.contains("instCoe"))
        || !decl_map
            .values()
            .all(|d| d.get("module").and_then(Json::as_str) == Some("Trusted"))
        || axioms2 != expected_ax2
    {
        return Err("Group 2 dependency/axiom checks failed".to_string());
    }
    done(
        "private/opaque/data/mutual/nested/matcher/typeclass/coercion, module ownership, ambient paths",
        &mut disposable,
    )?;

    // Group 3: Reviewed lock-only foundation growth (Init.Data.PLift).
    let f3 = make_fixture(
        Some(
            &(header.to_string()
                + "import Init.Data.PLift\n"
                + expand_macro
                + "@[vetted] def usesExtra (x : PLift Nat) : Bool := decide (x = x)\n"),
        ),
        false,
    )?;
    let lock_path3 = f3.join("trusted/lean/foundation-lock.json");
    let mut lock3 =
        Json::parse(&fs::read_to_string(&lock_path3).map_err(|e| e.to_string())?)?;
    let lean_exec = match lean {
        Some(p) => fs::canonicalize(p).map_err(|e| e.to_string())?,
        None => fs::canonicalize(default_lean_path()).map_err(|e| e.to_string())?,
    };
    let prefix3 = lean_exec.parent().unwrap().parent().unwrap();
    let extra = "Init.Data.PLift";
    let mut extra_parts = BTreeMap::new();
    for part in PARTS {
        let p = prefix3
            .join("lib/lean")
            .join(format!("Init/Data/PLift.{part}"));
        if p.exists() {
            extra_parts.insert(
                part.to_string(),
                Json::Str(digest(&p).map_err(|e| e.to_string())?),
            );
        } else {
            extra_parts.insert(part.to_string(), Json::Null);
        }
    }
    let mut extra_rec = BTreeMap::new();
    extra_rec.insert(
        "sourceSha256".to_string(),
        Json::Str(
            digest(&prefix3.join("src/lean/Init/Data/PLift.lean"))
                .map_err(|e| e.to_string())?,
        ),
    );
    extra_rec.insert("parts".to_string(), Json::Obj(extra_parts));
    lock3
        .as_obj_mut()
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
    lock3
        .as_obj_mut()
        .unwrap()
        .get_mut("graph")
        .unwrap()
        .as_obj_mut()
        .unwrap()
        .insert(extra.to_string(), Json::Arr(vec![Json::Obj(edge_obj)]));
    fs::write(&lock_path3, lock3.to_compact_string().as_bytes())
        .map_err(|e| e.to_string())?;
    let rep3 =
        checked(&f3, None, None, None, false, None, &mut disposable)?.unwrap();
    let has_plift = rep3
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
    if !rep3
        .get("graph")
        .and_then(Json::as_obj)
        .unwrap()
        .contains_key(extra)
        || !has_plift
    {
        return Err("Group 3 PLift check failed".to_string());
    }
    done(
        "reviewed lock-only foundation growth and permitted standard axiom union",
        &mut disposable,
    )?;

    // Group 4: Parsed policy negatives, recursive wrappers/attributes, parser recovery, no eval sentinel.
    let sentinel = suite.join("must-not-exist");
    let eval_sentinel_src = format!(
        "{header}#eval IO.FS.writeFile \"{}\" \"executed\"\n",
        sentinel.display()
    );
    let negative_sources: Vec<(&str, String)> = vec![
        ("implicit default Init", "import Init.Core\n@[vetted] def x : Nat := 0\n".to_string()),
        ("foreign namespace spoof", format!("{header}import Foreign\nnamespace Trusted\n@[vetted] def x : Nat := 0\nend Trusted\n")),
        ("Std import", "prelude\nimport Std\n".to_string()),
        ("module header", "module\nprelude\nimport Init.Core\n".to_string()),
        ("meta import", "module\nprelude\nmeta import Init.Core\n".to_string()),
        ("direct meta import", "prelude\nmeta import Init.Core\n".to_string()),
        ("direct all import", "prelude\nimport all Init.Core\n".to_string()),
        ("public import", "prelude\npublic import Init.Core\n".to_string()),
        ("nested unsafe", format!("{header}open Nat in\n@[vetted] unsafe def x : Nat := 0\n")),
        ("term unsafe generated hook", format!("{header}@[vetted] def generatedUnsafe : Nat := unsafe 0\n")),
        ("mutual unsafe", format!("{header}mutual\n @[vetted] unsafe def x : Nat := 0\nend\n")),
        ("nested forbidden command", format!("{header}open Nat in\n#eval 0\n")),
        ("nested attribute", format!("{header}@[vetted] structure X where\n @[extern \"foreign\"] x : Nat\n")),
        ("implemented_by", format!("{header}@[vetted, implemented_by other] def x : Nat := 0\n")),
        ("attribute removal", format!("{header}attribute [-extern] Nat.add\n")),
        ("deriving", format!("{header}@[vetted] structure X where\n x : Nat\nderiving Repr\n")),
        ("open scoped", format!("{header}open scoped Nat\n")),
        ("set_option wrapper", format!("{header}set_option debug.skipKernelTC true in\n@[vetted] def x : Nat := 0\n")),
        ("custom macro", format!("{header}macro \"x\" : term => `(0)\n")),
        ("native shortcut", format!("{header}@[vetted] theorem x : True := by native_decide\n")),
        ("native decide config", format!("{header}@[vetted] theorem x : True := by decide +native\n")),
        ("by_elab", format!("{header}@[vetted] def x : Nat := by_elab return Lean.mkNatLit 0\n")),
        ("missing trust attribute", format!("{header}def x : Nat := 0\n")),
        ("unnamed instance", format!("{header}@[vetted] instance : Inhabited Nat := ⟨0⟩\n")),
        ("vetted constructor on candidate inductive", format!("{header}@[candidate mir_ast]\ninductive Bad where\n  | @[vetted] mk : Bad\n")),
        ("unknown candidate feature", format!("{header}@[candidate nonexistent] def x : Nat := 0\n")),
        ("multiple trust attributes", format!("{header}@[vetted, candidate mir_ast] def x : Nat := 0\n")),
        ("malformed recovery", format!("{header}def broken : :=\n")),
        ("evaluation sentinel", eval_sentinel_src),
    ];
    let pf_root = make_fixture(None, false)?;
    let mut pf_checker =
        Checker::new(&pf_root, lean, Some(suite)).map_err(|e| e.to_string())?;
    pf_checker.tool_admission().map_err(|e| e.to_string())?;
    let mut batch_cases = Vec::new();
    for (idx, (label, src)) in negative_sources.iter().enumerate() {
        if matches!(
            *label,
            "implicit default Init"
                | "foreign namespace spoof"
                | "Std import"
                | "evaluation sentinel"
        ) {
            let f = make_fixture(Some(src), false)?;
            let _ = checked(
                &f,
                Some(1),
                Some("preflight"),
                Some(false),
                false,
                None,
                &mut disposable,
            )?;
            if sentinel.exists() {
                return Err("evaluation sentinel executed!".to_string());
            }
        } else {
            let neg_path = pf_checker.stage.join(format!("neg-{idx}.lean"));
            fs::write(&neg_path, src.as_bytes()).map_err(|e| e.to_string())?;
            batch_cases.push(Json::Arr(vec![
                Json::Str("Trusted".to_string()),
                Json::Str(neg_path.to_string_lossy().into_owned()),
            ]));
        }
    }
    let mut pf_fields = BTreeMap::new();
    pf_fields.insert("cases".to_string(), Json::Arr(batch_cases));
    pf_checker
        .inspect("preflight-negatives", pf_fields)
        .map_err(|e| format!("Group 4 batch preflight-negatives failed: {e}"))?;
    if sentinel.exists() {
        return Err("evaluation sentinel executed!".to_string());
    }
    let _ = fs::remove_dir_all(&pf_checker.stage);
    done(
        "parsed policy negatives, recursive wrappers/attributes, parser recovery, no eval sentinel",
        &mut disposable,
    )?;

    // Group 5: sorry/direct sorryAx and unused module audited from complete inventory.
    let f5a = make_fixture(
        Some(&format!(
            "{header_with_macro}@[vetted] theorem bad : False := by sorry\n"
        )),
        false,
    )?;
    let _ = checked(
        &f5a,
        Some(1),
        Some("audit"),
        Some(true),
        false,
        None,
        &mut disposable,
    )?;
    let f5b = make_fixture(
        Some(&format!(
            "{header_with_macro}@[vetted] theorem bad : False := sorryAx False true\n"
        )),
        false,
    )?;
    let _ = checked(
        &f5b,
        Some(1),
        Some("audit"),
        Some(true),
        false,
        None,
        &mut disposable,
    )?;
    let f5c = make_fixture(None, false)?;
    fs::create_dir_all(f5c.join("trusted/lean/Trusted"))
        .map_err(|e| e.to_string())?;
    fs::write(
        f5c.join("trusted/lean/Trusted/Unused.lean"),
        format!(
            "{header_with_macro}@[vetted] theorem unreferenced : False := by sorry\n"
        )
        .as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let _ = checked(
        &f5c,
        Some(1),
        Some("audit"),
        Some(true),
        false,
        None,
        &mut disposable,
    )?;
    done(
        "sorry/direct sorryAx and unused module audited from complete inventory",
        &mut disposable,
    )?;

    // Group 6: Source import cycle.
    let f6 = make_fixture(
        Some(&format!("{header}import Trusted.Other\n")),
        false,
    )?;
    fs::create_dir_all(f6.join("trusted/lean/Trusted"))
        .map_err(|e| e.to_string())?;
    fs::write(
        f6.join("trusted/lean/Trusted/Other.lean"),
        format!("{header}import Trusted\n").as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let _ = checked(
        &f6,
        Some(1),
        Some("preflight"),
        Some(false),
        false,
        None,
        &mut disposable,
    )?;
    done("source import cycle", &mut disposable)?;

    // Group 7: symlinks, stale outputs, and foundation bytes.
    for change in [
        "symlink",
        "compiled source artifact",
        "foundation digest",
        "unexpected companion",
    ] {
        let f7 = make_fixture(None, false)?;
        let (phase, code) = if change == "symlink" {
            symlink(
                f7.join("trusted/lean/Trusted.lean"),
                f7.join("trusted/lean/Alias.lean"),
            )
            .map_err(|e| e.to_string())?;
            ("snapshot", 1)
        } else if change == "compiled source artifact" {
            fs::write(f7.join("trusted/lean/Trusted.olean"), b"stale")
                .map_err(|e| e.to_string())?;
            ("snapshot", 1)
        } else {
            let lp = f7.join("trusted/lean/foundation-lock.json");
            let mut l =
                Json::parse(&fs::read_to_string(&lp).map_err(|e| e.to_string())?)?;
            let part = if change == "foundation digest" {
                "olean"
            } else {
                "olean.private"
            };
            let val = if part == "olean" {
                Json::Str("0".repeat(64))
            } else {
                Json::Null
            };
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
                .insert(part.to_string(), val);
            fs::write(&lp, l.to_compact_string().as_bytes())
                .map_err(|e| e.to_string())?;
            ("foundation", 2)
        };
        let _ = checked(
            &f7,
            Some(code),
            Some(phase),
            Some(false),
            false,
            None,
            &mut disposable,
        )?;
    }
    done(
        "symlinks, stale outputs, and foundation byte integrity",
        &mut disposable,
    )?;

    // Group 8: Unused compiled axiom and graphTests.
    let f8 = make_fixture(None, false)?;
    let mut checker8 =
        Checker::new(&f8, lean, Some(suite)).map_err(|e| e.to_string())?;
    checker8.tool_admission().map_err(|e| e.to_string())?;
    let mut imp_obj = BTreeMap::new();
    imp_obj.insert("module".to_string(), Json::Str("Init.Core".to_string()));
    imp_obj.insert("importAll".to_string(), Json::Bool(false));
    imp_obj.insert("isExported".to_string(), Json::Bool(true));
    imp_obj.insert("isMeta".to_string(), Json::Bool(false));
    let imports8 = vec![Json::Obj(imp_obj)];
    let setup_path8 = checker8
        .write_setup_json("Trusted", &imports8)
        .map_err(|e| e.to_string())?;
    let unchecked8 = checker8.stage.join("UnusedAxiom.lean");
    fs::write(
        &unchecked8,
        format!(
            "{header}namespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n"
        )
        .as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let out8 = checker8.stage.join("Trusted.olean");
    checker8
        .process(
            "axiom-fixture",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path8.to_string_lossy().into_owned(),
                "-o".to_string(),
                out8.to_string_lossy().into_owned(),
                unchecked8.to_string_lossy().into_owned(),
            ],
        )
        .map_err(|e| e.to_string())?;
    checker8.artifacts.insert(
        "Trusted".to_string(),
        vec![vec![out8.to_string_lossy().into_owned()], Vec::new()],
    );
    checker8
        .graph
        .insert("Trusted".to_string(), Json::Arr(imports8));
    let mut af8 = BTreeMap::new();
    af8.insert(
        "trusted".to_string(),
        Json::Arr(vec![Json::Str("Trusted".to_string())]),
    );
    af8.insert("trustDeclarations".to_string(), Json::Arr(Vec::new()));
    let ax_err = checker8.inspect("audit", af8).unwrap_err();
    if ax_err.code != 1
        || !ax_err
            .message
            .contains("Trusted axiom AnyNamespace.unused")
    {
        return Err(format!("unexpected axiom error: {ax_err}"));
    }
    let graph_rep = checker8
        .inspect("graph-tests", BTreeMap::new())
        .map_err(|e| e.to_string())?;
    if graph_rep.get("graphTests") != Some(&Json::Bool(true)) {
        return Err("graphTests returned false".to_string());
    }
    let _ = fs::remove_dir_all(&checker8.stage);
    done(
        "unused compiled axiom and independent recursor-rule/opaque/parent/foreign/statement-origin graph oracles",
        &mut disposable,
    )?;

    // Group 9: Status-sensitive subprocess/protocol seam.
    for behavior in [
        "nonzero",
        "empty",
        "malformed",
        "wrong-shape",
        "signal",
        "timeout",
        "policy-exit1",
        "policy-exit2",
        "policy-signal",
        "policy-budget",
    ] {
        let f9 = make_fixture(None, false)?;
        let fake = f9.join("fake-lean");
        let write_last = "for last; do :; done\n";
        let policy_json =
            r#"{"ok":false,"category":"policy","message":"fixture policy"}"#;
        let script_body = match behavior {
            "nonzero" => "exit 7\n".to_string(),
            "empty" => "exit 0\n".to_string(),
            "malformed" => {
                format!("{write_last}printf '%s' 'not-json' > \"$last\"\n")
            }
            "wrong-shape" => {
                format!("{write_last}printf '%s' '[]' > \"$last\"\n")
            }
            "signal" => "kill -TERM $$\n".to_string(),
            "timeout" => "sleep 5\n".to_string(),
            "policy-exit1" => format!(
                "{write_last}printf '%s' '{policy_json}' > \"$last\"\nexit 1\n"
            ),
            "policy-exit2" => format!(
                "{write_last}printf '%s' '{policy_json}' > \"$last\"\nexit 2\n"
            ),
            "policy-signal" => format!(
                "{write_last}printf '%s' '{policy_json}' > \"$last\"\nkill -TERM $$\n"
            ),
            "policy-budget" => format!(
                "{write_last}printf '%s' '{policy_json}' > \"$last\"\nexit 1\n"
            ),
            _ => unreachable!(),
        };
        fs::write(&fake, format!("#!/bin/sh\n{script_body}").as_bytes())
            .map_err(|e| e.to_string())?;
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o700))
            .map_err(|e| e.to_string())?;

        let mut checker9 = Checker::new(&f9, Some(&fake), Some(suite))
            .map_err(|e| e.to_string())?;
        checker9.prefix = f9.clone();
        checker9.foundation = Vec::new();
        let mut lock9 = BTreeMap::new();
        lock9.insert("axioms".to_string(), Json::Arr(Vec::new()));
        checker9.lock = Json::Obj(lock9);
        checker9.inspector = f9.join("unused");

        if behavior == "timeout" {
            checker9.timeout_duration = Duration::from_millis(10);
        } else if behavior == "policy-budget" {
            checker9.max_bytes = 0;
        }

        let err9 = checker9.inspect("graph-tests", BTreeMap::new()).unwrap_err();
        let exp_code = if behavior == "policy-exit1" { 1 } else { 2 };
        if err9.code != exp_code {
            return Err(format!(
                "behavior {behavior} expected code {exp_code}, got {}",
                err9.code
            ));
        }
        let mut status_files = Vec::new();
        for e in fs::read_dir(&checker9.stage).map_err(|e| e.to_string())? {
            let p = e.map_err(|e| e.to_string())?.path();
            if p.to_string_lossy().ends_with(".status.json") {
                status_files.push(p);
            }
        }
        if status_files.len() != 1 {
            return Err(format!(
                "expected 1 status.json for {behavior}, got {}",
                status_files.len()
            ));
        }
        let st = Json::parse(
            &fs::read_to_string(&status_files[0]).map_err(|e| e.to_string())?,
        )?;
        if st.get("timeout").and_then(Json::as_bool)
            != Some(behavior == "timeout")
        {
            return Err(format!("timeout mismatch for {behavior}"));
        }
        if behavior == "nonzero"
            && st.get("returncode").and_then(Json::as_i64) != Some(7)
        {
            return Err("nonzero returncode != 7".to_string());
        }
        if behavior == "signal"
            && !st
                .get("returncode")
                .and_then(Json::as_i64)
                .is_some_and(|c| c < 0)
        {
            return Err("signal returncode not negative".to_string());
        }
        let _ = fs::remove_dir_all(&checker9.stage);
    }
    done(
        "nonzero/empty/malformed/signalled/timed-out producers cannot establish success",
        &mut disposable,
    )?;

    // Group 10: Downstream Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation.
    let mut setup_downstream_fixture =
        |claim_source: &str| -> Result<(PathBuf, Vec<DownstreamTarget>), String> {
            let root = make_fixture(
                Some(&format!(
                    "{header_with_macro}@[vetted] def TrustedClaim : Prop := True\n"
                )),
                false,
            )?;
            fs::create_dir_all(root.join("theory")).map_err(|e| e.to_string())?;
            fs::create_dir_all(root.join("examples"))
                .map_err(|e| e.to_string())?;
            fs::create_dir_all(root.join("tests")).map_err(|e| e.to_string())?;
            fs::write(
                root.join("theory/Anneal.lean"),
                b"prelude\nimport Trusted\nnamespace Anneal\ndef UntrustedProp : Prop := True\ntheorem witness : TrustedClaim := True.intro\nend Anneal\n",
            )
            .map_err(|e| e.to_string())?;
            fs::write(
                root.join("examples/lean-toolchain"),
                format!("{TOOLCHAIN}\n").as_bytes(),
            )
            .map_err(|e| e.to_string())?;
            fs::write(
                root.join("examples/lakefile.toml"),
                b"name = \"AnnealExamples\"\ndefaultTargets = [\"Smoke\"]\n",
            )
            .map_err(|e| e.to_string())?;
            fs::write(
                root.join("examples/Smoke.lean"),
                b"prelude\nimport Anneal\nnamespace AnnealExamples\ntheorem ex : TrustedClaim := Anneal.witness\nend AnnealExamples\n",
            )
            .map_err(|e| e.to_string())?;
            fs::write(root.join("tests/Smoke.lean"), claim_source.as_bytes())
                .map_err(|e| e.to_string())?;
            let targets = vec![
                DownstreamTarget::new(
                    "Anneal",
                    "theory/Anneal.lean",
                    &["Trusted"],
                    "theory",
                ),
                DownstreamTarget::new(
                    "Smoke",
                    "examples/Smoke.lean",
                    &["Anneal"],
                    "examples",
                ),
                DownstreamTarget::new(
                    "SmokeTest",
                    "tests/Smoke.lean",
                    &["Anneal"],
                    "claim",
                ),
            ];
            Ok((root, targets))
        };

    // 10a. Valid claim using theory in proof body (`ci.value?`).
    let (r10a, t10a) = setup_downstream_fixture(
        "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
    )?;
    let rep10a = checked(
        &r10a,
        None,
        None,
        None,
        true,
        Some(&t10a),
        &mut disposable,
    )?
    .unwrap();
    let ds10a = rep10a.get("downstream").unwrap();
    if ds10a.get("replay") != Some(&Json::Bool(true))
        || ds10a.get("claimTheoremsChecked").and_then(Json::as_i64) != Some(1)
    {
        return Err("10a failed".to_string());
    }

    // 10b. Invalid claim referencing Anneal.UntrustedProp in statement (`ci.type`).
    let (r10b, t10b) = setup_downstream_fixture(
        "prelude\nimport Anneal\ndef myClaim : Prop := Anneal.UntrustedProp\ntheorem leaked_stmt : myClaim := True.intro\n",
    )?;
    let err10b = checked(
        &r10b,
        Some(1),
        Some("downstream-audit"),
        Some(true),
        true,
        Some(&t10b),
        &mut disposable,
    )?
    .unwrap_err();
    if !err10b.message.contains(
        "theorem statement of leaked_stmt depends on untrusted theory declaration Anneal.UntrustedProp",
    ) {
        return Err(format!("10b unexpected message: {err10b}"));
    }
    done(
        "statement (ci.type) vs. proof (ci.value?) origin separation",
        &mut disposable,
    )?;

    // Group 11: Cargo workspace DAG boundary for `trusted/`.
    let r11 = make_fixture(None, false)?;
    fs::copy(checkout.join("Cargo.toml"), r11.join("Cargo.toml"))
        .map_err(|e| e.to_string())?;
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &r11.join("trusted/rustc-capture"),
    )
    .map_err(|e| e.to_string())?;
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &r11.join("trusted/cargo-anneal"),
    )
    .map_err(|e| e.to_string())?;
    let c_hashes = check_cargo_boundary(&r11).map_err(|e| e.to_string())?;
    if !c_hashes.contains_key("Cargo.toml")
        || !c_hashes.contains_key("trusted/rustc-capture/Cargo.toml")
        || !c_hashes.contains_key("trusted/cargo-anneal/Cargo.toml")
    {
        return Err("Group 11 missing cargo hashes".to_string());
    }
    fs::create_dir_all(r11.join("crates/untrusted-helper/src"))
        .map_err(|e| e.to_string())?;
    fs::write(
        r11.join("crates/untrusted-helper/Cargo.toml"),
        b"[package]\nname = \"untrusted-helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(r11.join("crates/untrusted-helper/src/lib.rs"), b"")
        .map_err(|e| e.to_string())?;
    fs::write(
        r11.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/cargo-anneal\",\n    \"crates/untrusted-helper\",\n]\n",
    )
    .map_err(|e| e.to_string())?;
    let err11a = checked(
        &r11,
        Some(1),
        Some("cargo-boundary"),
        Some(false),
        false,
        None,
        &mut disposable,
    )?
    .unwrap_err();
    if !err11a
        .message
        .contains("workspace member outside trusted/: crates/untrusted-helper")
    {
        return Err(format!("Group 11a unexpected error: {err11a}"));
    }
    fs::copy(checkout.join("Cargo.toml"), r11.join("Cargo.toml"))
        .map_err(|e| e.to_string())?;
    fs::write(
        r11.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .map_err(|e| e.to_string())?;
    let err11b = checked(
        &r11,
        Some(1),
        Some("cargo-boundary"),
        Some(false),
        false,
        None,
        &mut disposable,
    )?
    .unwrap_err();
    if !err11b.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper",
    ) {
        return Err(format!("Group 11b unexpected error: {err11b}"));
    }
    done(
        "Cargo workspace DAG boundary rejects workspace members and path dependencies outside trusted/",
        &mut disposable,
    )?;

    // Group 12: Cryptographic `CaptureManifest.json` handshake and compilation-completion check.
    let manifest_dir = suite.join("manifest-fixture");
    fs::create_dir_all(manifest_dir.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(manifest_dir.join("Mir")).map_err(|e| e.to_string())?;
    let rs_file = manifest_dir.join("src/lib.rs");
    let mir_file = manifest_dir.join("Mir/Foo.lean");
    fs::write(&rs_file, b"pub fn foo() {}\n").map_err(|e| e.to_string())?;
    fs::write(&mir_file, b"def claim : Prop := True\n")
        .map_err(|e| e.to_string())?;
    let manifest_path = manifest_dir.join("CaptureManifest.json");
    let valid_manifest_str = format!(
        r#"{{"schema":1,"compilation_succeeded":true,"rust_sources":[["src/lib.rs","{}"]],"targets":[{{"def_id":"crate::foo","mir_module_path":"Mir/Foo.lean","mir_module_sha256":"{}"}}]}}"#,
        digest(&rs_file).map_err(|e| e.to_string())?,
        digest(&mir_file).map_err(|e| e.to_string())?
    );
    fs::write(&manifest_path, valid_manifest_str.as_bytes())
        .map_err(|e| e.to_string())?;
    let m_ok = verify_capture_manifest(&manifest_path, &manifest_dir)
        .map_err(|e| e.to_string())?;
    if m_ok.get("compilation_succeeded") != Some(&Json::Bool(true)) {
        return Err("Group 12 valid manifest failed".to_string());
    }
    let bad_manifest_str = valid_manifest_str
        .replace("\"compilation_succeeded\":true", "\"compilation_succeeded\":false");
    fs::write(&manifest_path, bad_manifest_str.as_bytes())
        .map_err(|e| e.to_string())?;
    let err12a =
        verify_capture_manifest(&manifest_path, &manifest_dir).unwrap_err();
    if err12a.code != 1
        || err12a.phase != "manifest"
        || !err12a.message.contains("compilation_succeeded")
    {
        return Err(format!("12a unexpected error: {err12a}"));
    }
    fs::write(&manifest_path, valid_manifest_str.as_bytes())
        .map_err(|e| e.to_string())?;
    fs::write(&mir_file, b"def claim : Prop := True -- tampered\n")
        .map_err(|e| e.to_string())?;
    let err12b =
        verify_capture_manifest(&manifest_path, &manifest_dir).unwrap_err();
    if err12b.code != 1
        || err12b.phase != "manifest"
        || !err12b.message.contains("Mir module digest mismatch")
    {
        return Err(format!("12b unexpected error: {err12b}"));
    }
    let _ = fs::remove_dir_all(&manifest_dir);
    done(
        "CaptureManifest.json compilation_succeeded and SHA-256 integrity checks",
        &mut disposable,
    )?;

    // Group 13: End-to-end `verify_crate` gate (exact `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` check).
    let r15 = make_fixture(
        Some(&format!(
            "{header_with_macro}namespace Trusted\n@[vetted] structure Crate where tag : Nat\n@[vetted] def CrateTheorem (_ : Crate) : Prop := True\nend Trusted\n"
        )),
        false,
    )?;
    fs::create_dir_all(r15.join("theory")).map_err(|e| e.to_string())?;
    fs::write(
        r15.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ntheorem prove_crate (c : Trusted.Crate) : Trusted.CrateTheorem c := True.intro\nend Anneal\n",
    )
    .map_err(|e| e.to_string())?;
    let t15 = vec![DownstreamTarget::new(
        "Anneal",
        "theory/Anneal.lean",
        &["Trusted"],
        "theory",
    )];
    let setup_verify_crate_fixture =
        |sub: &str,
         mir_source: &str,
         proof_source: &str|
         -> Result<PathBuf, String> {
            let crate_dir = r15.join(sub);
            fs::create_dir_all(crate_dir.join("src"))
                .map_err(|e| e.to_string())?;
            fs::create_dir_all(crate_dir.join(".anneal"))
                .map_err(|e| e.to_string())?;
            let rs_p = crate_dir.join("src/lib.rs");
            let mir_p = crate_dir.join(".anneal/Mir.lean");
            let proof_p = crate_dir.join(".anneal/Proof.lean");
            fs::write(&rs_p, b"pub fn id(x: usize) -> usize { x }\n")
                .map_err(|e| e.to_string())?;
            fs::write(&mir_p, mir_source.as_bytes())
                .map_err(|e| e.to_string())?;
            fs::write(&proof_p, proof_source.as_bytes())
                .map_err(|e| e.to_string())?;
            let manifest_json = format!(
                r#"{{"schema":1,"compilation_succeeded":true,"rust_sources":[["src/lib.rs","{}"]],"targets":[{{"def_id":"crate::id","mir_module_path":".anneal/Mir.lean","mir_module_sha256":"{}"}}]}}"#,
                digest(&rs_p).map_err(|e| e.to_string())?,
                digest(&mir_p).map_err(|e| e.to_string())?
            );
            fs::write(
                crate_dir.join(".anneal/CaptureManifest.json"),
                manifest_json.as_bytes(),
            )
            .map_err(|e| e.to_string())?;
            Ok(crate_dir)
        };

    // 15a. Valid crate verification.
    let c15a = setup_verify_crate_fixture(
        "crate-15a",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_crate Mir.crate\nend Proof\n",
    )?;
    let mut chk15a =
        Checker::new(&r15, lean, Some(suite)).map_err(|e| e.to_string())?;
    let rep15a = chk15a
        .verify_crate(&c15a, Some(&t15))
        .map_err(|e| e.to_string())?;
    let cv15a = rep15a.get("crateVerification").unwrap();
    if cv15a.get("verifiedTheorem").and_then(Json::as_str)
        != Some("Proof.verify_crate")
        || cv15a.get("replay") != Some(&Json::Bool(true))
    {
        return Err("15a failed".to_string());
    }
    disposable.push(chk15a.stage);

    // 15b. Wrong theorem type (`theorem verify_crate : True`).
    let c15b = setup_verify_crate_fixture(
        "crate-15b",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : True := True.intro\nend Proof\n",
    )?;
    let mut chk15b =
        Checker::new(&r15, lean, Some(suite)).map_err(|e| e.to_string())?;
    let err15b = chk15b.verify_crate(&c15b, Some(&t15)).unwrap_err();
    if err15b.code != 1
        || err15b.phase != "verify-crate"
        || !err15b
            .message
            .contains("expected Trusted.CrateTheorem Mir.crate")
    {
        return Err(format!("15b unexpected error: {err15b}"));
    }
    disposable.push(chk15b.stage);

    // 15c. Theorem declared inside `Mir.lean`.
    let c15c = setup_verify_crate_fixture(
        "crate-15c",
        "prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := { tag := 0 }\ntheorem sneaky : True := True.intro\nend Mir\n",
        "prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_crate Mir.crate\nend Proof\n",
    )?;
    let mut chk15c =
        Checker::new(&r15, lean, Some(suite)).map_err(|e| e.to_string())?;
    let err15c = chk15c.verify_crate(&c15c, Some(&t15)).unwrap_err();
    if err15c.code != 1
        || err15c.phase != "verify-crate"
        || !err15c
            .message
            .contains("Mir module must contain only data declarations")
    {
        return Err(format!("15c unexpected error: {err15c}"));
    }
    disposable.push(chk15c.stage);
    done(
        "verify-crate mode enforces Mir data-only rule and exact Proof.verify_crate : Trusted.CrateTheorem Mir.crate",
        &mut disposable,
    )?;

    // Group 14: Vetted vs. Candidate Trusted non-contamination (`@[vetted]` vs `@[candidate <feat>]`)
    // and per-crate candidate policy enforcement.
    let f16a = make_fixture(
        Some(&format!(
            "{header_with_macro}namespace Trusted\n@[candidate mir_semantics] def candHelper : Prop := True\n@[vetted] def badVetted : Prop := candHelper\nend Trusted\n"
        )),
        false,
    )?;
    let err16a = checked(
        &f16a,
        Some(1),
        Some("audit"),
        Some(true),
        false,
        None,
        &mut disposable,
    )?
    .unwrap_err();
    if !err16a
        .message
        .contains("references candidate:mir_semantics declaration Trusted.candHelper without a Trusted.candidate guard")
    {
        return Err(format!("16a unexpected error: {err16a}"));
    }

    let trusted16b = format!(
        "{header_with_macro}namespace Trusted\n\
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
    let r16b = make_fixture(Some(&trusted16b), false)?;
    fs::create_dir_all(r16b.join("theory")).map_err(|e| e.to_string())?;
    fs::write(
        r16b.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ntheorem prove_base : Trusted.CrateTheorem Trusted.Crate.base := True.intro\ntheorem prove_ext : Trusted.CrateTheorem Trusted.Crate.ext := True.intro\nend Anneal\n",
    )
    .map_err(|e| e.to_string())?;
    let t16b = vec![DownstreamTarget::new(
        "Anneal",
        "theory/Anneal.lean",
        &["Trusted"],
        "theory",
    )];

    // 16b-1: Crate using only `@[vetted]` constructor `base` passes default VettedOnly and Stable.
    let c16b_base = r16b.join("crate-base");
    fs::create_dir_all(c16b_base.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(c16b_base.join(".anneal")).map_err(|e| e.to_string())?;
    let rs16_base = c16b_base.join("src/lib.rs");
    let mir16_base = c16b_base.join(".anneal/Mir.lean");
    let proof16_base = c16b_base.join(".anneal/Proof.lean");
    fs::write(&rs16_base, b"pub fn id(x: usize) -> usize { x }\n")
        .map_err(|e| e.to_string())?;
    fs::write(
        &mir16_base,
        b"prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := Trusted.Crate.base\nend Mir\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(
        &proof16_base,
        b"prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_base\nend Proof\n",
    )
    .map_err(|e| e.to_string())?;
    let man16_base = format!(
        r#"{{"schema":1,"compilation_succeeded":true,"rust_sources":[["src/lib.rs","{}"]],"targets":[{{"def_id":"crate::id","mir_module_path":".anneal/Mir.lean","mir_module_sha256":"{}"}}]}}"#,
        digest(&rs16_base).map_err(|e| e.to_string())?,
        digest(&mir16_base).map_err(|e| e.to_string())?
    );
    fs::write(
        c16b_base.join(".anneal/CaptureManifest.json"),
        man16_base.as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let mut chk16b_base =
        Checker::new(&r16b, lean, Some(suite)).map_err(|e| e.to_string())?;
    let rep16b_base = chk16b_base
        .verify_crate_with_policy(
            &c16b_base,
            Some(&t16b),
            Some(ReleaseChannel::Stable),
            None,
        )
        .map_err(|e| e.to_string())?;
    if rep16b_base
        .get("crateVerification")
        .and_then(|cv| cv.get("candidateFeatures"))
        != Some(&Json::Arr(Vec::new()))
    {
        return Err("16b-1 expected empty candidateFeatures".to_string());
    }
    disposable.push(chk16b_base.stage);

    // 16b-2: Crate using `@[candidate mir_semantics]` constructor `ext` is rejected by default
    // VettedOnly policy, accepted on Alpha when enabled, and rejected on Stable even when enabled.
    let c16b_ext = r16b.join("crate-ext");
    fs::create_dir_all(c16b_ext.join("src")).map_err(|e| e.to_string())?;
    fs::create_dir_all(c16b_ext.join(".anneal")).map_err(|e| e.to_string())?;
    let rs16_ext = c16b_ext.join("src/lib.rs");
    let mir16_ext = c16b_ext.join(".anneal/Mir.lean");
    let proof16_ext = c16b_ext.join(".anneal/Proof.lean");
    fs::write(&rs16_ext, b"pub fn id(x: usize) -> usize { x }\n")
        .map_err(|e| e.to_string())?;
    fs::write(
        &mir16_ext,
        b"prelude\nimport Trusted\nnamespace Mir\ndef crate : Trusted.Crate := Trusted.Crate.ext\nend Mir\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(
        &proof16_ext,
        b"prelude\nimport Trusted\nimport Anneal\nimport Mir\nnamespace Proof\ntheorem verify_crate : Trusted.CrateTheorem Mir.crate := Anneal.prove_ext\nend Proof\n",
    )
    .map_err(|e| e.to_string())?;
    let man16_ext = format!(
        r#"{{"schema":1,"compilation_succeeded":true,"rust_sources":[["src/lib.rs","{}"]],"targets":[{{"def_id":"crate::id","mir_module_path":".anneal/Mir.lean","mir_module_sha256":"{}"}}]}}"#,
        digest(&rs16_ext).map_err(|e| e.to_string())?,
        digest(&mir16_ext).map_err(|e| e.to_string())?
    );
    fs::write(
        c16b_ext.join(".anneal/CaptureManifest.json"),
        man16_ext.as_bytes(),
    )
    .map_err(|e| e.to_string())?;

    let mut chk16b_ext1 =
        Checker::new(&r16b, lean, Some(suite)).map_err(|e| e.to_string())?;
    let err16b_ext1 = chk16b_ext1
        .verify_crate(&c16b_ext, Some(&t16b))
        .unwrap_err();
    if err16b_ext1.code != 1
        || err16b_ext1.phase != "candidate-policy"
        || !err16b_ext1
            .message
            .contains("candidate-trusted feature `mir_semantics` is not enabled")
    {
        return Err(format!("16b-2 default rejection failed: {err16b_ext1}"));
    }
    disposable.push(chk16b_ext1.stage);

    let mut chk16b_ext2 =
        Checker::new(&r16b, lean, Some(suite)).map_err(|e| e.to_string())?;
    let allow_list = vec!["mir_semantics".to_string(), "memory".to_string()];
    let rep16b_ext2 = chk16b_ext2
        .verify_crate_with_policy(
            &c16b_ext,
            Some(&t16b),
            Some(ReleaseChannel::Alpha),
            Some(&allow_list),
        )
        .map_err(|e| e.to_string())?;
    let cv16b_ext2 = rep16b_ext2.get("crateVerification").unwrap();
    if cv16b_ext2.get("candidateFeatures")
        != Some(&Json::Arr(vec![Json::Str("mir_semantics".to_string())]))
        || cv16b_ext2.get("unusedCandidateFeatures")
            != Some(&Json::Arr(vec![Json::Str("memory".to_string())]))
    {
        return Err(format!(
            "16b-2 alpha opt-in report mismatch: {}",
            cv16b_ext2.to_compact_string()
        ));
    }
    disposable.push(chk16b_ext2.stage);

    let mut chk16b_ext3 =
        Checker::new(&r16b, lean, Some(suite)).map_err(|e| e.to_string())?;
    let allow_all = vec!["*".to_string()];
    let err16b_ext3 = chk16b_ext3
        .verify_crate_with_policy(
            &c16b_ext,
            Some(&t16b),
            Some(ReleaseChannel::Stable),
            Some(&allow_all),
        )
        .unwrap_err();
    if err16b_ext3.code != 1
        || err16b_ext3.phase != "candidate-policy"
        || !err16b_ext3
            .message
            .contains("stable release channel forbids candidate-trusted features")
    {
        return Err(format!("16b-2 stable rejection failed: {err16b_ext3}"));
    }
    disposable.push(chk16b_ext3.stage);
    done(
        "@[vetted] vs @[candidate] non-contamination, guarded match dispatch, and per-crate trust policy",
        &mut disposable,
    )?;

    Ok((passed.len(), started.elapsed()))
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
