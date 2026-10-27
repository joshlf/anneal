//! Bounded regression fixtures for the `trusted/audit` boundary gate and
//! `TrustedBoundary.lean` inspector.
//!
//! Exercises all 14 positive and negative fixture groups covering foundation
//! lock containment, syntax preflight rejections, complete inventory discovery,
//! cycle detection, symlink and artifact freshness, subprocess protocol faults,
//! statement (`ci.type`) vs. proof (`ci.value?`) origin separation, file-local
//! test axioms, Cargo workspace DAG containment, `CaptureManifest.json`
//! integrity, and `verify-crate` exact theorem checks.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::audit::{
    Checker, DownstreamTarget, Failure, Json, MAX_BYTES, PARTS, TOOLCHAIN,
    check_cargo_boundary, default_lean_path, digest, snapshot_with_reader,
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
        let size = dir_bytes(suite_dir).map_err(|e| e.to_string())?;
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
        let _ = fs::remove_dir_all(checker.stage.join("foundation"));
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
    let _ = fs::remove_dir_all(checker2.stage.join("foundation"));
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
                + "import Init.Data.PLift\ndef usesExtra (x : PLift Nat) : Bool := decide (x = x)\n"),
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
        ("implicit default Init", "import Init.Core\ndef x : Nat := 0\n".to_string()),
        ("foreign namespace spoof", format!("{header}import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n")),
        ("Std import", "prelude\nimport Std\n".to_string()),
        ("module header", "module\nprelude\nimport Init.Core\n".to_string()),
        ("meta import", "module\nprelude\nmeta import Init.Core\n".to_string()),
        ("direct meta import", "prelude\nmeta import Init.Core\n".to_string()),
        ("direct all import", "prelude\nimport all Init.Core\n".to_string()),
        ("public import", "prelude\npublic import Init.Core\n".to_string()),
        ("nested unsafe", format!("{header}open Nat in\nunsafe def x : Nat := 0\n")),
        ("term unsafe generated hook", format!("{header}def generatedUnsafe : Nat := unsafe 0\n")),
        ("mutual unsafe", format!("{header}mutual\n unsafe def x : Nat := 0\nend\n")),
        ("nested forbidden command", format!("{header}open Nat in\n#eval 0\n")),
        ("nested attribute", format!("{header}structure X where\n @[extern \"foreign\"] x : Nat\n")),
        ("implemented_by", format!("{header}@[implemented_by other] def x : Nat := 0\n")),
        ("attribute removal", format!("{header}attribute [-extern] Nat.add\n")),
        ("deriving", format!("{header}structure X where\n x : Nat\nderiving Repr\n")),
        ("open scoped", format!("{header}open scoped Nat\n")),
        ("set_option wrapper", format!("{header}set_option debug.skipKernelTC true in\ndef x : Nat := 0\n")),
        ("custom macro", format!("{header}macro \"x\" : term => `(0)\n")),
        ("native shortcut", format!("{header}theorem x : True := by native_decide\n")),
        ("native decide config", format!("{header}theorem x : True := by decide +native\n")),
        ("by_elab", format!("{header}def x : Nat := by_elab return Lean.mkNatLit 0\n")),
        ("malformed recovery", format!("{header}def broken : :=\n")),
        ("evaluation sentinel", eval_sentinel_src),
    ];
    let pf_root = make_fixture(None, false)?;
    let mut pf_checker =
        Checker::new(&pf_root, lean, Some(suite)).map_err(|e| e.to_string())?;
    pf_checker.tool_admission().map_err(|e| e.to_string())?;
    for (idx, (label, src)) in negative_sources.iter().enumerate() {
        if matches!(
            *label,
            "implicit default Init"
                | "foreign namespace spoof"
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
        } else {
            let neg_path = pf_checker.stage.join(format!("neg-{idx}.lean"));
            fs::write(&neg_path, src.as_bytes()).map_err(|e| e.to_string())?;
            let mut pf_fields = BTreeMap::new();
            pf_fields.insert(
                "sources".to_string(),
                Json::Arr(vec![Json::Arr(vec![
                    Json::Str("Trusted".to_string()),
                    Json::Str(neg_path.to_string_lossy().into_owned()),
                ])]),
            );
            match pf_checker.inspect("preflight", pf_fields) {
                Ok(_) => {
                    return Err(format!(
                        "negative preflight case `{label}` unexpectedly succeeded"
                    ));
                }
                Err(err) if err.code == 1 && err.phase == "preflight" => {}
                Err(err) => {
                    return Err(format!(
                        "negative preflight case `{label}` unexpected failure: {err}"
                    ));
                }
            }
        }
        if sentinel.exists() {
            return Err("evaluation sentinel executed!".to_string());
        }
    }
    let _ = fs::remove_dir_all(&pf_checker.stage);
    done(
        "parsed policy negatives, recursive wrappers/attributes, parser recovery, no eval sentinel",
        &mut disposable,
    )?;

    // Group 5: sorry/direct sorryAx and unused module audited from complete inventory.
    let f5a = make_fixture(
        Some(&format!("{header}theorem bad : False := by sorry\n")),
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
        Some(&format!("{header}theorem bad : False := sorryAx False true\n")),
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
        format!("{header}theorem unreferenced : False := by sorry\n").as_bytes(),
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

    // Group 7: symlinks/stale outputs/foundation bytes and deterministic case-collision observation.
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
    let f7_case = make_fixture(None, false)?;
    let case_err = snapshot_with_reader(
        &f7_case.join("trusted/lean"),
        &|dir| {
            let mut entries = Vec::new();
            for e in fs::read_dir(dir)? {
                entries.push(e?.file_name().to_string_lossy().into_owned());
            }
            entries.sort();
            entries.push("trusted.lean".to_string());
            Ok(entries)
        },
    )
    .unwrap_err();
    if case_err.code != 1 || !case_err.message.contains("case-colliding") {
        return Err(format!("unexpected case-collision error: {case_err}"));
    }
    done(
        "symlinks/stale outputs/foundation bytes and deterministic case-collision observation",
        &mut disposable,
    )?;

    // Group 8: Directory observation failure is distinct from an empty inventory.
    let f8 = make_fixture(None, false)?;
    let walk_err =
        snapshot_with_reader(&f8.join("trusted/lean"), &|_dir| {
            Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "fixture unreadable nested directory",
            ))
        })
        .unwrap_err();
    if walk_err.code != 2 || !walk_err.message.contains("incomplete") {
        return Err(format!("unexpected walk error: {walk_err}"));
    }
    done(
        "directory observation failure is distinct from an empty inventory",
        &mut disposable,
    )?;

    // Group 9: Unused compiled axiom and graphTests.
    let f9 = make_fixture(None, false)?;
    let mut checker9 =
        Checker::new(&f9, lean, Some(suite)).map_err(|e| e.to_string())?;
    checker9.tool_admission().map_err(|e| e.to_string())?;
    let mut imp_obj = BTreeMap::new();
    imp_obj.insert("module".to_string(), Json::Str("Init.Core".to_string()));
    imp_obj.insert("importAll".to_string(), Json::Bool(false));
    imp_obj.insert("isExported".to_string(), Json::Bool(true));
    imp_obj.insert("isMeta".to_string(), Json::Bool(false));
    let imports9 = vec![Json::Obj(imp_obj)];
    let mut sf9 = BTreeMap::new();
    sf9.insert("module".to_string(), Json::Str("Trusted".to_string()));
    sf9.insert("imports".to_string(), Json::Arr(imports9.clone()));
    let setup9 = checker9.inspect("setup", sf9).map_err(|e| e.to_string())?;
    let setup_path9 = checker9.stage.join("axiom.setup.json");
    fs::write(&setup_path9, setup9.to_compact_string().as_bytes())
        .map_err(|e| e.to_string())?;
    let unchecked9 = checker9.stage.join("UnusedAxiom.lean");
    fs::write(
        &unchecked9,
        format!(
            "{header}namespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n"
        )
        .as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let out9 = checker9.stage.join("Trusted.olean");
    checker9
        .process(
            "axiom-fixture",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path9.to_string_lossy().into_owned(),
                "-o".to_string(),
                out9.to_string_lossy().into_owned(),
                unchecked9.to_string_lossy().into_owned(),
            ],
        )
        .map_err(|e| e.to_string())?;
    checker9.artifacts.insert(
        "Trusted".to_string(),
        vec![vec![out9.to_string_lossy().into_owned()], Vec::new()],
    );
    checker9
        .graph
        .insert("Trusted".to_string(), Json::Arr(imports9));
    let mut af9 = BTreeMap::new();
    af9.insert(
        "trusted".to_string(),
        Json::Arr(vec![Json::Str("Trusted".to_string())]),
    );
    let ax_err = checker9.inspect("audit", af9).unwrap_err();
    if ax_err.code != 1
        || !ax_err
            .message
            .contains("Trusted axiom AnyNamespace.unused")
    {
        return Err(format!("unexpected axiom error: {ax_err}"));
    }
    let graph_rep = checker9
        .inspect("graph-tests", BTreeMap::new())
        .map_err(|e| e.to_string())?;
    if graph_rep.get("graphTests") != Some(&Json::Bool(true)) {
        return Err("graphTests returned false".to_string());
    }
    let _ = fs::remove_dir_all(&checker9.stage);
    done(
        "unused compiled axiom and independent recursor-rule/opaque/parent/foreign/statement-origin graph oracles",
        &mut disposable,
    )?;

    // Group 10: Complete final rediscovery and staged-artifact freshness.
    let f10 = make_fixture(None, false)?;
    let mut checker10 =
        Checker::new(&f10, lean, Some(suite)).map_err(|e| e.to_string())?;
    checker10.tool_admission().map_err(|e| e.to_string())?;
    let original10 = f10.join("trusted/lean/Trusted.lean");
    let policy10 = f10.join("trusted/lean/foundation-lock.json");
    let tool10 = f10.join("trusted/audit/TrustedBoundary.lean");
    let orig_bytes = fs::read(&original10).map_err(|e| e.to_string())?;
    let pol_bytes = fs::read(&policy10).map_err(|e| e.to_string())?;
    let tool_bytes = fs::read(&tool10).map_err(|e| e.to_string())?;

    for idx in 0..6 {
        match idx {
            0 => {
                fs::write(f10.join("trusted/lean/New.lean"), header.as_bytes())
                    .map_err(|e| e.to_string())?;
            }
            1 => {
                fs::remove_file(&original10).map_err(|e| e.to_string())?;
            }
            2 => {
                fs::rename(&original10, f10.join("trusted/lean/Renamed.lean"))
                    .map_err(|e| e.to_string())?;
            }
            3 => {
                fs::write(
                    &original10,
                    format!("{header}def changed : Nat := 1\n").as_bytes(),
                )
                .map_err(|e| e.to_string())?;
            }
            4 => {
                fs::write(&policy10, b"{}").map_err(|e| e.to_string())?;
            }
            _ => {
                fs::write(&tool10, b"changed inspector")
                    .map_err(|e| e.to_string())?;
            }
        }
        let ferr = checker10.freshness().unwrap_err();
        if ferr.code != 2 || ferr.phase != "freshness" {
            return Err(format!("unexpected freshness error: {ferr}"));
        }
        let _ = fs::remove_file(f10.join("trusted/lean/New.lean"));
        let _ = fs::remove_file(f10.join("trusted/lean/Renamed.lean"));
        fs::write(&original10, &orig_bytes).map_err(|e| e.to_string())?;
        fs::write(&policy10, &pol_bytes).map_err(|e| e.to_string())?;
        fs::write(&tool10, &tool_bytes).map_err(|e| e.to_string())?;
    }
    let staged_src10 = checker10.source_copy.join("Trusted.lean");
    fs::write(
        &staged_src10,
        format!("{header}def changedInStage : Nat := 9\n").as_bytes(),
    )
    .map_err(|e| e.to_string())?;
    let serr = checker10.freshness().unwrap_err();
    if serr.code != 2 || !serr.message.contains("staged Trusted") {
        return Err(format!("unexpected staged source error: {serr}"));
    }
    fs::write(&staged_src10, &orig_bytes).map_err(|e| e.to_string())?;
    let priv_art = checker10
        .expected_artifacts
        .keys()
        .find(|p| p.ends_with(".olean.private"))
        .unwrap()
        .clone();
    fs::write(&priv_art, b"truncated").map_err(|e| e.to_string())?;
    let aerr = checker10.freshness().unwrap_err();
    if aerr.code != 2 || !aerr.message.contains("artifact changed") {
        return Err(format!("unexpected artifact error: {aerr}"));
    }
    let _ = fs::remove_dir_all(&checker10.stage);
    done(
        "complete source/policy/tool rediscovery and staged-artifact freshness",
        &mut disposable,
    )?;

    // Group 11: Status-sensitive subprocess/protocol seam.
    for behavior in [
        "nonzero",
        "empty",
        "malformed",
        "wrong-shape",
        "invalid-success-schema",
        "invalid-audit-count",
        "signal",
        "timeout",
        "policy-exit1",
        "policy-exit2",
        "policy-signal",
        "policy-budget",
    ] {
        let f11 = make_fixture(None, false)?;
        let fake = f11.join("fake-lean");
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
            "invalid-success-schema" => format!(
                "{write_last}printf '%s' '{{\"ok\":true,\"result\":{{\"graph\":[]}}}}' > \"$last\"\n"
            ),
            "invalid-audit-count" => format!(
                "{write_last}printf '%s' '{{\"ok\":true,\"result\":{{\"graph\":{{}},\"declarations\":[],\"kernelDeclarations\":1,\"compilerOnlyNames\":0,\"reachableDeclarations\":1,\"axioms\":[],\"replay\":true}}}}' > \"$last\"\n"
            ),
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

        let mut checker11 = Checker::new(&f11, Some(&fake), Some(suite))
            .map_err(|e| e.to_string())?;
        checker11.prefix = f11.clone();
        checker11.foundation = Vec::new();
        let mut lock11 = BTreeMap::new();
        lock11.insert("axioms".to_string(), Json::Arr(Vec::new()));
        checker11.lock = Json::Obj(lock11);
        checker11.inspector = f11.join("unused");

        if behavior == "timeout" {
            checker11.timeout_duration = Duration::from_millis(10);
        } else if behavior == "policy-budget" {
            checker11.max_bytes = 0;
        }

        let res11 = if behavior == "invalid-audit-count" {
            let mut m = BTreeMap::new();
            m.insert(
                "trusted".to_string(),
                Json::Arr(vec![Json::Str("Trusted".to_string())]),
            );
            checker11.inspect("audit", m)
        } else {
            checker11.inspect("foundation", BTreeMap::new())
        };
        let err11 = res11.unwrap_err();
        let exp_code = if behavior == "policy-exit1" { 1 } else { 2 };
        if err11.code != exp_code {
            return Err(format!(
                "behavior {behavior} expected code {exp_code}, got {}",
                err11.code
            ));
        }
        let mut status_files = Vec::new();
        for e in fs::read_dir(&checker11.stage).map_err(|e| e.to_string())? {
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
        let _ = fs::remove_dir_all(&checker11.stage);
    }
    done(
        "nonzero/empty/malformed/signalled/timed-out producers cannot establish success",
        &mut disposable,
    )?;

    // Group 12: Downstream Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation
    // and file-local test-axiom enforcement.
    let mut setup_downstream_fixture =
        |claim_source: &str,
         test_a_source: Option<&str>,
         test_b_source: Option<&str>|
         -> Result<(PathBuf, Vec<DownstreamTarget>), String> {
            let root = make_fixture(
                Some(&format!("{header}def TrustedClaim : Prop := True\n")),
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
            let mut targets = vec![
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
            if let Some(ta) = test_a_source {
                fs::write(root.join("tests/TestA.lean"), ta.as_bytes())
                    .map_err(|e| e.to_string())?;
                targets.push(DownstreamTarget::new(
                    "TestA",
                    "tests/TestA.lean",
                    &["Anneal"],
                    "test",
                ));
            }
            if let Some(tb) = test_b_source {
                fs::write(root.join("tests/TestB.lean"), tb.as_bytes())
                    .map_err(|e| e.to_string())?;
                targets.push(DownstreamTarget::new(
                    "TestB",
                    "tests/TestB.lean",
                    &["Anneal", "TestA"],
                    "test",
                ));
            }
            Ok((root, targets))
        };

    // 12a. Valid claim + file-local test axiom.
    let (r12a, t12a) = setup_downstream_fixture(
        "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
        Some("prelude\nimport Anneal\naxiom local_ax : TrustedClaim\ntheorem uses_local : TrustedClaim := local_ax\n"),
        None,
    )?;
    let rep12a = checked(
        &r12a,
        None,
        None,
        None,
        true,
        Some(&t12a),
        &mut disposable,
    )?
    .unwrap();
    let ds12a = rep12a.get("downstream").unwrap();
    if ds12a.get("replay") != Some(&Json::Bool(true))
        || ds12a.get("claimTheoremsChecked").and_then(Json::as_i64) != Some(1)
        || ds12a.get("localTestAxioms").and_then(Json::as_i64) != Some(1)
    {
        return Err("12a failed".to_string());
    }

    // 12b. Invalid claim referencing Anneal.UntrustedProp in statement.
    let (r12b, t12b) = setup_downstream_fixture(
        "prelude\nimport Anneal\ndef myClaim : Prop := Anneal.UntrustedProp\ntheorem leaked_stmt : myClaim := True.intro\n",
        None,
        None,
    )?;
    let err12b = checked(
        &r12b,
        Some(1),
        Some("downstream-audit"),
        Some(true),
        true,
        Some(&t12b),
        &mut disposable,
    )?
    .unwrap_err();
    if !err12b.message.contains(
        "theorem statement of leaked_stmt depends on untrusted theory declaration Anneal.UntrustedProp",
    ) {
        return Err(format!("12b unexpected message: {err12b}"));
    }

    // 12c. Invalid cross-file test axiom.
    let (r12c, t12c) = setup_downstream_fixture(
        "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
        Some("prelude\nimport Anneal\naxiom local_ax : TrustedClaim\n"),
        Some("prelude\nimport Anneal\nimport TestA\ntheorem cross_file : TrustedClaim := local_ax\n"),
    )?;
    let err12c = checked(
        &r12c,
        Some(1),
        Some("downstream-audit"),
        Some(true),
        true,
        Some(&t12c),
        &mut disposable,
    )?
    .unwrap_err();
    if !err12c
        .message
        .contains("depends on foreign axiom local_ax from TestA")
    {
        return Err(format!("12c unexpected message: {err12c}"));
    }
    done(
        "statement (ci.type) vs. proof (ci.value?) origin separation and file-local test-axiom boundary",
        &mut disposable,
    )?;

    // Group 13: Cargo workspace DAG boundary for `trusted/`.
    let r13 = make_fixture(None, false)?;
    fs::copy(checkout.join("Cargo.toml"), r13.join("Cargo.toml"))
        .map_err(|e| e.to_string())?;
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &r13.join("trusted/rustc-capture"),
    )
    .map_err(|e| e.to_string())?;
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &r13.join("trusted/cargo-anneal"),
    )
    .map_err(|e| e.to_string())?;
    let c_hashes = check_cargo_boundary(&r13).map_err(|e| e.to_string())?;
    if !c_hashes.contains_key("Cargo.toml")
        || !c_hashes.contains_key("trusted/rustc-capture/Cargo.toml")
        || !c_hashes.contains_key("trusted/cargo-anneal/Cargo.toml")
    {
        return Err("Group 13 missing cargo hashes".to_string());
    }
    fs::create_dir_all(r13.join("crates/untrusted-helper/src"))
        .map_err(|e| e.to_string())?;
    fs::write(
        r13.join("crates/untrusted-helper/Cargo.toml"),
        b"[package]\nname = \"untrusted-helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .map_err(|e| e.to_string())?;
    fs::write(r13.join("crates/untrusted-helper/src/lib.rs"), b"")
        .map_err(|e| e.to_string())?;
    fs::write(
        r13.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/cargo-anneal\",\n    \"crates/untrusted-helper\",\n]\n",
    )
    .map_err(|e| e.to_string())?;
    let err13a = checked(
        &r13,
        Some(1),
        Some("cargo-boundary"),
        Some(false),
        false,
        None,
        &mut disposable,
    )?
    .unwrap_err();
    if !err13a
        .message
        .contains("workspace member outside trusted/: crates/untrusted-helper")
    {
        return Err(format!("Group 13a unexpected error: {err13a}"));
    }
    fs::copy(checkout.join("Cargo.toml"), r13.join("Cargo.toml"))
        .map_err(|e| e.to_string())?;
    fs::write(
        r13.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .map_err(|e| e.to_string())?;
    let err13b = checked(
        &r13,
        Some(1),
        Some("cargo-boundary"),
        Some(false),
        false,
        None,
        &mut disposable,
    )?
    .unwrap_err();
    if !err13b.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper",
    ) {
        return Err(format!("Group 13b unexpected error: {err13b}"));
    }
    done(
        "Cargo workspace DAG boundary rejects workspace members and path dependencies outside trusted/",
        &mut disposable,
    )?;

    // Group 14: Cryptographic `CaptureManifest.json` handshake and compilation-completion check.
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
        return Err("Group 14 valid manifest failed".to_string());
    }
    let bad_manifest_str = valid_manifest_str
        .replace("\"compilation_succeeded\":true", "\"compilation_succeeded\":false");
    fs::write(&manifest_path, bad_manifest_str.as_bytes())
        .map_err(|e| e.to_string())?;
    let err14a =
        verify_capture_manifest(&manifest_path, &manifest_dir).unwrap_err();
    if err14a.code != 1
        || err14a.phase != "manifest"
        || !err14a.message.contains("compilation_succeeded")
    {
        return Err(format!("14a unexpected error: {err14a}"));
    }
    fs::write(&manifest_path, valid_manifest_str.as_bytes())
        .map_err(|e| e.to_string())?;
    fs::write(&mir_file, b"def claim : Prop := True -- tampered\n")
        .map_err(|e| e.to_string())?;
    let err14b =
        verify_capture_manifest(&manifest_path, &manifest_dir).unwrap_err();
    if err14b.code != 1
        || err14b.phase != "manifest"
        || !err14b.message.contains("Mir module digest mismatch")
    {
        return Err(format!("14b unexpected error: {err14b}"));
    }
    let _ = fs::remove_dir_all(&manifest_dir);
    done(
        "CaptureManifest.json compilation_succeeded and SHA-256 integrity checks",
        &mut disposable,
    )?;

    Ok((passed.len(), started.elapsed()))
}

fn dir_bytes(root: &Path) -> io::Result<u64> {
    let mut total = 0u64;
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let meta = fs::symlink_metadata(entry.path())?;
            if meta.file_type().is_dir() && !meta.file_type().is_symlink() {
                stack.push(entry.path());
            } else if meta.file_type().is_file() {
                total = total.saturating_add(meta.len());
            }
        }
    }
    Ok(total)
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
