// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the indirect-call candidate generators:
//! `VTableAndFnPtrMutator` and `ClosureAndAddrEqMutator` (`miri-difftest`) and
//! `IndirectDispatchOutliner` (`itree-difftest`).
//!
//! The generation tests check, from fixed PRNG seeds, that every template of
//! the four construct classes is emitted deterministically (`&T as &dyn Trait`
//! unsizing with dynamic dispatch; indirect `fn` pointer calls with
//! `FnPtrToPtr` and the function-pointer `PointerCoercion`s; `addr_eq` on wide
//! pointers that share a data address but differ in slice length or vtable;
//! closures capturing by value and by reference next to borrows), and that
//! every candidate compiles at `-C opt-level=0` and `-C opt-level=2`.
//!
//! The two live tests run every template through the real oracles: Miri
//! (`-Zmiri-tree-borrows`) against Anneal's Lean semantics, and native traces
//! against Lean `TraceCheck`.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

use anneal_difftest::instrument::EnvSchedule;
use anneal_difftest::itree_eval::{
    ITREE_SAFE_SEEDS, ItreeEvalOptions, compile_rust_strict_opt,
    evaluate_itree_batches_with_options,
};
use anneal_difftest::miri_eval::{
    MiriEvalOptions, evaluate_miri_batches_with_options, resolve_rustc_bin,
};
use anneal_difftest::mutators_itree::{
    GeneratedItreeCandidate, ITREE_CONCOLIC_BASE_INPUTS, IndirectDispatchOutliner, ItreeAstMutator,
    ItreeConcreteEvaluator, ItreeConcreteEvent, annotate_itree_external_callees,
    contains_unsafe_token, generate_itree_batch, itree_candidate_replay_is_faithful,
    reconstruct_itree_mutation_steps, stage_itree_candidate_items,
};
use anneal_difftest::mutators_miri::{
    ClosureAndAddrEqMutator, DetRng, GeneratedMiriCandidate, MIRI_CORPUS_CRATE_HEADER,
    MiriAstMutator, MutationMode, VTableAndFnPtrMutator, build_standalone_candidate_source,
    generate_miri_corpus_batch, load_miri_diff_corpus_seeds, miri_candidate_replay_is_faithful,
    reconstruct_miri_mutation_steps,
};
use cargo_anneal::{ComparisonVerdict, DivergenceKind, MiriOutcome};

/// Serializes the two live-oracle tests, which each build Lean modules.
static LIVE_ORACLE_LOCK: Mutex<()> = Mutex::new(());

struct TempDir(PathBuf);

impl std::ops::Deref for TempDir {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn unique_temp_dir(label: &str) -> TempDir {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!(
        "anneal_vtable_fnptr_test_{label}_{}_{stamp}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    TempDir(dir)
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repository root")
        .to_path_buf()
}

/// Compiles `source` with `rustc --edition=2024 --crate-type=lib -A warnings
/// -C opt-level=<opt_level>`, returning `rustc`'s stderr on failure.
fn compile_at_opt_level(label: &str, opt_level: &str, source: &str) -> Result<(), String> {
    compile_with_lints(label, "-A", opt_level, source)
}

/// Compiles `source` with `rustc --edition=2024 --crate-type=lib <lint_flag>
/// warnings -C opt-level=<opt_level>` (`lint_flag` is `-A` or `-D`), returning
/// `rustc`'s stderr on failure.
fn compile_with_lints(
    label: &str,
    lint_flag: &str,
    opt_level: &str,
    source: &str,
) -> Result<(), String> {
    let dir = unique_temp_dir(&format!("rustc_{label}_o{opt_level}"));
    let mut child = Command::new(resolve_rustc_bin())
        .args([
            "--edition=2024",
            "--crate-type=lib",
            lint_flag,
            "warnings",
            "-C",
        ])
        .arg(format!("opt-level={opt_level}"))
        .arg("-o")
        .arg(dir.join("libcand.rlib"))
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn rustc for `{label}`: {e}"))?;
    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(source.as_bytes())
            .map_err(|e| format!("failed writing `{label}` to rustc: {e}"))?;
    }
    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed waiting on rustc for `{label}`: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// What the live Miri + Anneal comparison of a template must conclude.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    /// Miri and Anneal agree (on the value, the panic site, or the UB site).
    Agree,
    /// Miri passes; Anneal agrees or, at the coercion its semantics does not
    /// model (`&T` to `&dyn Trait`, closure to `fn` pointer), reports a
    /// conservative false-positive UB.
    AgreeOrFalsePositiveUb,
}

/// One template of a Miri indirect-call mutator.
struct MiriTemplate {
    label: &'static str,
    /// The construct classes of the brief that the template exercises.
    classes: &'static [&'static str],
    mode: MutationMode,
    /// Substrings the template's source has (see [`has_marker`]).
    has: &'static [&'static str],
    /// Substring (a single token run, never wrapped) the template's source
    /// lacks.
    lacks: &'static str,
    expect: Expect,
}

const DYN: &str = "dyn_unsize_and_dispatch";
const FN_PTR: &str = "fn_pointer_and_coercions";
const ADDR_EQ: &str = "wide_pointer_addr_eq";
const CLOSURE: &str = "capturing_closure";

const VTABLE_TEMPLATES: &[MiriTemplate] = &[
    MiriTemplate {
        label: "fn_ptr_chain",
        classes: &[FN_PTR],
        mode: MutationMode::Pass,
        has: &[
            // `ReifyFnPointer`, `UnsafeFnPointer`, `FnPtrToPtr` (from both
            // pointer types), `MutToConstPointer`, and both indirect calls.
            "__vt_fp: fn(u32) -> u32 = __anneal_fnptr_callee_",
            "__vt_ufp: unsafe fn(u32) -> u32 = __vt_fp",
            "__vt_fp as *const ()",
            "__vt_ufp as *const ()",
            "__vt_const_ptr: *const u32 = __vt_mut_ptr",
            "__vt_fp(__vt_seed)",
            "unsafe { __vt_ufp(",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "dyn_dispatch",
        classes: &[DYN, ADDR_EQ],
        mode: MutationMode::Pass,
        has: &[
            "__vt_dyn: &dyn __AnnealVtableTrait",
            "as &dyn __AnnealVtableTrait",
            "__vt_dyn_alt: &dyn __AnnealVtableAlt",
            "as &dyn __AnnealVtableAlt",
            "__vt_dyn.eval_vt(__vt_seed)",
            "__vt_dyn_alt.eval_alt()",
            // One data address, two vtables.
            "core::ptr::addr_eq(__vt_dyn, __vt_dyn_alt)",
        ],
        lacks: "__vt_fp",
        expect: Expect::AgreeOrFalsePositiveUb,
    },
    MiriTemplate {
        label: "closure_fn_ptr",
        classes: &[FN_PTR],
        mode: MutationMode::Pass,
        has: &[
            // `ClosureFnPointer`, then `UnsafeFnPointer` and `FnPtrToPtr`.
            "__vt_cfp: fn(u32) -> u32 = |__vt_z: u32|",
            "__vt_cufp: unsafe fn(u32) -> u32 = __vt_cfp",
            "__vt_cfp as *const ()",
            "__vt_cfp(__vt_seed)",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::AgreeOrFalsePositiveUb,
    },
    MiriTemplate {
        label: "fn_ptr_callee_overflow",
        classes: &[FN_PTR],
        mode: MutationMode::Panic,
        has: &[
            "__vt_ovf_sum: u32 = __vt_v +",
            "unsafe { __vt_ufp(__vt_near_max) }",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "fn_ptr_driver_overflow",
        classes: &[FN_PTR],
        mode: MutationMode::Panic,
        has: &[
            "__vt_fp(__vt_seed ^ __vt_bias)",
            "__vt_ovf_base + __vt_ovf_step",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "fn_ptr_callee_unchecked_add",
        classes: &[FN_PTR],
        mode: MutationMode::Ub,
        has: &[
            "unsafe { unchecked_add(__vt_v,",
            "unsafe { __vt_ufp(__vt_near_max) }",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "fn_ptr_driver_unchecked_add",
        classes: &[FN_PTR],
        mode: MutationMode::Ub,
        has: &[
            "__vt_fp(__vt_seed ^ __vt_bias)",
            "unchecked_add(u32::MAX, __vt_ub_step)",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
];

const CLOSURE_TEMPLATES: &[MiriTemplate] = &[
    MiriTemplate {
        label: "wide_slices",
        classes: &[ADDR_EQ],
        mode: MutationMode::Pass,
        has: &[
            // Lengths 3 and 1 at one data address.
            "__clos_full: *const [u32; 3] = &raw const __clos_arr",
            "__clos_head: *const [u32; 1] = __clos_full as *const [u32; 1]",
            "__clos_long: *const [u32] = __clos_full",
            "__clos_short: *const [u32] = __clos_head",
            "size_of_val(__clos_long)",
            "size_of_val(__clos_short)",
            "__anneal_wide_slice_addr_eq_",
            "(__clos_p as *const ()) == (__clos_q as *const ())",
        ],
        lacks: "__clos_agg",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "wide_slices_uncalled_closure",
        classes: &[ADDR_EQ, CLOSURE],
        mode: MutationMode::Pass,
        has: &[
            "__anneal_wide_slice_addr_eq_",
            // An `AggregateKind::Closure` that captures `&__clos_cap` while
            // `__clos_cap` is also borrowed directly.
            "__clos_agg = |__clos_u: u32| wrapping_add(__clos_cap, __clos_u)",
            "__clos_keep: &u32 = &__clos_cap",
        ],
        lacks: "::__::",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "closure_by_value",
        classes: &[CLOSURE],
        mode: MutationMode::Pass,
        has: &[
            "::__::eval(move ||",
            "wrapping_add(__clos_cap,",
            "::__::apply_keep(",
        ],
        lacks: "::__::eval_once(",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "closure_by_shared_ref",
        classes: &[CLOSURE],
        mode: MutationMode::Pass,
        has: &[
            "__clos_shared: &u32 = &__clos_base",
            "__clos_raw: *const u32 = &raw const *__clos_shared",
            "::__::eval(||",
            "(*__clos_shared) ^ __clos_bias",
            "unsafe { *__clos_raw }",
        ],
        lacks: "move",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "closure_by_unique_ref",
        classes: &[CLOSURE],
        mode: MutationMode::Pass,
        has: &[
            "__clos_root: *mut u32 = &raw mut __clos_slot",
            "__clos_child: &mut u32 = unsafe { &mut *__clos_root }",
            "::__::eval_once(move ||",
            "*__clos_child = (*__clos_child) ^ __clos_owned.0",
            "__clos_parent: u32 = unsafe { *__clos_root }",
        ],
        lacks: "::__::apply_keep(",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "wide_slices_oob_index",
        classes: &[ADDR_EQ],
        mode: MutationMode::Panic,
        has: &[
            "__anneal_wide_slice_addr_eq_",
            "__clos_oob_arr[__clos_oob_idx]",
        ],
        lacks: "::__::",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "closure_by_value_oob_index",
        classes: &[CLOSURE],
        mode: MutationMode::Panic,
        has: &["::__::apply_keep(", "__clos_oob_arr[__clos_oob_idx]"],
        lacks: "addr_eq",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "wide_slices_unchecked_add",
        classes: &[ADDR_EQ],
        mode: MutationMode::Ub,
        has: &[
            "__anneal_wide_slice_addr_eq_",
            "unchecked_add(u32::MAX, __clos_ub_step)",
        ],
        lacks: "::__::",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "closure_by_value_unchecked_add",
        classes: &[CLOSURE],
        mode: MutationMode::Ub,
        has: &[
            "::__::apply_keep(",
            "unchecked_add(u32::MAX, __clos_ub_step)",
        ],
        lacks: "addr_eq",
        expect: Expect::Agree,
    },
];

/// Number of PRNG seeds scanned per `(mutator, mode)` for its templates.
const TEMPLATE_SCAN_SEEDS: u64 = 96;

/// The source of `fn_name`, a closed seed with one integer local, after one
/// `mode` pass of `mutator` from PRNG seed `s`.
fn miri_mutant_fn_source(
    mutator: &dyn MiriAstMutator,
    mode: MutationMode,
    fn_name: &str,
    s: u64,
) -> String {
    let seed = format!("pub fn {fn_name}() -> u32 {{\n    let x: u32 = 10u32;\n    x ^ 1u32\n}}\n");
    let mut file = syn::parse_file(&seed).expect("parse seed");
    let mut rng = DetRng::new(s);
    let mut locals = Vec::new();
    mutator.mutate_with_mode(&mut file, &mut rng, mode, &mut locals);
    prettyplease::unparse(&file)
}

/// `text` without whitespace and without the trailing comma that `prettyplease`
/// puts before a `)` when it breaks an argument list over several lines.
/// Comparing dense forms makes a marker independent of how the printer wraps
/// the line it appears on.
fn dense(text: &str) -> String {
    let no_space: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    no_space.replace(",)", ")")
}

/// Whether `source` has `marker`, up to whitespace and line wrapping.
fn has_marker(source: &str, marker: &str) -> bool {
    dense(source).contains(&dense(marker))
}

fn template_matches(template: &MiriTemplate, fn_source: &str) -> bool {
    template.has.iter().all(|m| has_marker(fn_source, m)) && !fn_source.contains(template.lacks)
}

/// For every template of `mutator`, the candidate that the first matching PRNG
/// seed (in `0..TEMPLATE_SCAN_SEEDS`) produces, named `<prefix>_<label>`. No
/// PRNG seed is used for two templates, so that no two candidates share the
/// tag that suffixes their driver items.
///
/// Panics if a PRNG seed produces a source that matches no template or more
/// than one template of its mode, or if a template is never produced.
fn miri_template_candidates(
    mutator: &dyn MiriAstMutator,
    templates: &'static [MiriTemplate],
    prefix: &str,
    first_id: usize,
) -> Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> {
    let mut out: Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> = Vec::new();
    let mut used_seeds = BTreeSet::new();
    for template in templates {
        let fn_name = format!("{prefix}_{}", template.label);
        let found = (0..TEMPLATE_SCAN_SEEDS).find_map(|s| {
            if used_seeds.contains(&s) {
                return None;
            }
            let fn_source = miri_mutant_fn_source(mutator, template.mode, &fn_name, s);
            let matching: Vec<&str> = templates
                .iter()
                .filter(|t| t.mode == template.mode && template_matches(t, &fn_source))
                .map(|t| t.label)
                .collect();
            assert_eq!(
                matching.len(),
                1,
                "`{}` {:?} PRNG seed {s} matches templates {matching:?}:\n{fn_source}",
                mutator.name(),
                template.mode
            );
            (matching[0] == template.label).then_some((s, fn_source))
        });
        let (s, fn_source) = found.unwrap_or_else(|| {
            panic!(
                "`{}` never emitted template `{}` under {:?}",
                mutator.name(),
                template.label,
                template.mode
            )
        });
        used_seeds.insert(s);
        let source = build_standalone_candidate_source(&fn_source);
        out.push((
            template,
            GeneratedMiriCandidate {
                id: first_id + out.len(),
                seed_index: 0,
                seed_name: "indirect_call_seed".to_string(),
                fn_name,
                seed_u64: s,
                applied_mutators: vec![mutator.name().to_string()],
                tracked_locals: vec![("x".to_string(), "u32".to_string())],
                fn_source,
                source,
            },
        ));
    }
    out
}

/// Every template of both Miri indirect-call mutators.
fn all_miri_template_candidates() -> Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> {
    let mut out = miri_template_candidates(&VTableAndFnPtrMutator, VTABLE_TEMPLATES, "vt", 0);
    let first_id = out.len();
    out.extend(miri_template_candidates(
        &ClosureAndAddrEqMutator,
        CLOSURE_TEMPLATES,
        "clos",
        first_id,
    ));
    out
}

/// The four `IndirectDispatchOutliner` templates: label, construct classes,
/// and the substrings that identify the template.
const ITREE_TEMPLATES: [(&str, &[&str], &[&str]); 4] = [
    (
        "dyn_dispatch",
        &[DYN, ADDR_EQ],
        &[
            "&holder as &dyn AnnealDynProbe",
            "&holder as &dyn AnnealDynAlt",
            "as_probe.probe(seed)",
            "as_alt.alt()",
            "core::ptr::addr_eq(as_probe, as_alt)",
        ],
    ),
    (
        "fn_pointer",
        &[FN_PTR],
        &[
            "op: fn(u32, u32) -> u32 = if",
            "lifted: fn(u32, u32) -> u32 = |a: u32, b: u32|",
            "op(seed, delta)",
            "lifted(first,",
        ],
    ),
    (
        "closures",
        &[CLOSURE],
        &[
            "by_ref = |x: u32| (x >> 1) ^ bias",
            "by_val = move |x: u32|",
            "let mut bump = |d: u32|",
            "acc = (acc >> 1) ^ d",
        ],
    ),
    (
        "slice_addr_eq",
        &[ADDR_EQ],
        &[
            "whole: &[u32] = &arr",
            "[lead @ .., _, _] = &arr",
            "[_, tail @ ..] = &arr",
            "core::ptr::addr_eq(whole, short)",
            "core::ptr::addr_eq(whole, shifted)",
        ],
    ),
];

/// `ITREE_SAFE_SEEDS[seed_index]` after one `IndirectDispatchOutliner` pass
/// from PRNG seed `s`.
fn itree_mutant_source(seed_index: usize, s: u64) -> String {
    let mut file = syn::parse_file(ITREE_SAFE_SEEDS[seed_index]).expect("parse ITree seed");
    let mut rng = DetRng::new(s);
    IndirectDispatchOutliner.mutate(&mut file, &mut rng);
    prettyplease::unparse(&file)
}

/// One candidate per `IndirectDispatchOutliner` template and ITree seed, in
/// batch order (`id` is the position in the returned batch).
fn itree_template_candidates() -> Vec<(&'static str, GeneratedItreeCandidate)> {
    let mut out: Vec<(&'static str, GeneratedItreeCandidate)> = Vec::new();
    for seed_index in 0..ITREE_SAFE_SEEDS.len() {
        for (label, _, _) in ITREE_TEMPLATES {
            let found = (0..TEMPLATE_SCAN_SEEDS).find_map(|s| {
                let source = itree_mutant_source(seed_index, s);
                let matching: Vec<&str> = ITREE_TEMPLATES
                    .iter()
                    .filter(|(_, _, ms)| ms.iter().all(|m| has_marker(&source, m)))
                    .map(|(l, _, _)| *l)
                    .collect();
                assert_eq!(
                    matching.len(),
                    1,
                    "PRNG seed {s} on ITree seed {seed_index} matches {matching:?}:\n{source}"
                );
                (matching[0] == label).then_some((s, source))
            });
            let (s, source) = found.unwrap_or_else(|| {
                panic!("`IndirectDispatchOutliner` never emitted `{label}` on seed {seed_index}")
            });
            out.push((
                label,
                GeneratedItreeCandidate {
                    id: out.len(),
                    seed_index,
                    seed_u64: s,
                    applied_mutators: vec!["IndirectDispatchOutliner".to_string()],
                    source,
                },
            ));
        }
    }
    out
}

#[test]
fn miri_indirect_mutators_generate_every_construct_class_deterministically() {
    let first = all_miri_template_candidates();
    let second = all_miri_template_candidates();
    assert_eq!(
        first.len(),
        VTABLE_TEMPLATES.len() + CLOSURE_TEMPLATES.len()
    );
    let mut classes: BTreeMap<&str, usize> = BTreeMap::new();
    let mut fn_names = BTreeSet::new();
    for ((template, cand), (_, replay)) in first.iter().zip(&second) {
        assert_eq!(
            cand, replay,
            "template `{}` is not deterministic",
            template.label
        );
        assert!(fn_names.insert(cand.fn_name.clone()));
        assert!(
            syn::parse_file(&cand.source).is_ok(),
            "template `{}` does not parse:\n{}",
            template.label,
            cand.source
        );
        // The entry function gains exactly one statement: the driver call.
        let entry = cand
            .fn_source
            .split_once(&format!("pub fn {}", cand.fn_name))
            .expect("entry function")
            .1;
        assert_eq!(
            entry.matches("__anneal_").count(),
            1,
            "template `{}` must add one driver call to the entry function:\n{}",
            template.label,
            cand.fn_source
        );
        for &class in template.classes {
            *classes.entry(class).or_insert(0) += 1;
        }
    }
    for class in [DYN, FN_PTR, ADDR_EQ, CLOSURE] {
        assert!(
            classes.get(class).is_some_and(|&n| n >= 1),
            "no Miri template exercises `{class}`: {classes:?}"
        );
    }
    // By-value and by-reference (shared and unique) captures are all present.
    for label in [
        "closure_by_value",
        "closure_by_shared_ref",
        "closure_by_unique_ref",
    ] {
        assert!(first.iter().any(|(t, _)| t.label == label));
    }
}

#[test]
fn miri_indirect_candidates_compile_at_opt_levels_0_and_2() {
    let templates = all_miri_template_candidates();
    let mut failures = Vec::new();
    for (template, cand) in &templates {
        for opt_level in ["0", "2"] {
            // `-D warnings`: beyond the lints the corpus crate header allows, a
            // template adds no warning to the seed it mutates.
            if let Err(stderr) = compile_with_lints(template.label, "-D", opt_level, &cand.source) {
                failures.push(format!(
                    "`{}` at -C opt-level={opt_level}:\n{stderr}\n{}",
                    template.label, cand.source
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} template compilations failed:\n{}",
        failures.len(),
        templates.len() * 2,
        failures.join("\n---\n")
    );

    // `miri-difftest --compile-only` compiles a whole run as one crate with a
    // module per candidate, so the items a template adds must also resolve
    // from inside a module and must not clash across candidates.
    let mut combined = String::from(MIRI_CORPUS_CRATE_HEADER);
    for (i, (_, cand)) in templates.iter().enumerate() {
        combined.push_str(&format!(
            "pub mod c{i} {{\n{}\n}}\n",
            cand.module_body_source()
        ));
    }
    for opt_level in ["0", "2"] {
        if let Err(stderr) = compile_at_opt_level("combined", opt_level, &combined) {
            panic!("combined template crate failed at -C opt-level={opt_level}:\n{stderr}");
        }
    }
}

#[test]
fn scheduled_miri_batches_carry_indirect_mutators_replay_and_compile() {
    let seeds = load_miri_diff_corpus_seeds();
    let seed_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut total = 0usize;
    for (count, batch_seed) in [
        (20usize, 0xCAFE_BABE_1234_5678u64),
        (20, 0xDEAD_BEEF_0000_0001),
        (40, 0xE1A0_2026),
    ] {
        let batch = generate_miri_corpus_batch(count, batch_seed, 0);
        assert_eq!(batch, generate_miri_corpus_batch(count, batch_seed, 0));
        total += batch.len();
        for cand in &batch {
            let indirect: Vec<&String> = cand
                .applied_mutators
                .iter()
                .filter(|m| *m == "VTableAndFnPtrMutator" || *m == "ClosureAndAddrEqMutator")
                .collect();
            if indirect.is_empty() {
                continue;
            }
            for name in indirect {
                *seen.entry(name.clone()).or_insert(0) += 1;
            }
            let (base, steps) = reconstruct_miri_mutation_steps(cand, &seed_refs)
                .unwrap_or_else(|| panic!("no recorded passes for `{}`", cand.fn_name));
            assert!(
                miri_candidate_replay_is_faithful(cand, &base, &steps),
                "replay mismatch on `{}`",
                cand.fn_name
            );
            for opt_level in ["0", "2"] {
                if let Err(stderr) = compile_at_opt_level("scheduled", opt_level, &cand.source) {
                    panic!(
                        "`{}` ({:?}) failed at -C opt-level={opt_level}:\n{stderr}\n{}",
                        cand.fn_name, cand.applied_mutators, cand.source
                    );
                }
            }
        }
    }
    assert_eq!(total, 80);
    for name in ["VTableAndFnPtrMutator", "ClosureAndAddrEqMutator"] {
        assert!(
            seen.get(name).is_some_and(|&n| n >= 2),
            "corpus batches must schedule `{name}`: {seen:?}"
        );
    }
    // The schedule stays bounded: most passes still run a base mutator.
    assert!(seen.values().sum::<usize>() <= total / 2, "{seen:?}");
}

#[test]
fn itree_indirect_dispatch_templates_are_deterministic_safe_and_compile() {
    let cands = itree_template_candidates();
    assert_eq!(cands, itree_template_candidates());
    assert_eq!(cands.len(), ITREE_TEMPLATES.len() * ITREE_SAFE_SEEDS.len());
    let mut classes = BTreeSet::new();
    for (label, classes_of, _) in ITREE_TEMPLATES {
        assert!(cands.iter().any(|(l, _)| *l == label));
        classes.extend(classes_of.iter().copied());
    }
    assert_eq!(classes, BTreeSet::from([DYN, FN_PTR, ADDR_EQ, CLOSURE]));

    let mut combined = String::from("#![forbid(unsafe_code)]\n");
    for (i, (label, cand)) in cands.iter().enumerate() {
        assert!(
            !contains_unsafe_token(&cand.source),
            "`{label}` contains `unsafe`:\n{}",
            cand.source
        );
        // The pass adds one top-level item: the boundary helper.
        let seed_items = syn::parse_file(ITREE_SAFE_SEEDS[cand.seed_index])
            .expect("parse ITree seed")
            .items
            .len();
        let file = syn::parse_file(&cand.source).expect("parse candidate");
        assert_eq!(
            file.items.len(),
            seed_items + 1,
            "`{label}`:\n{}",
            cand.source
        );
        let Some(syn::Item::Fn(helper)) = file.items.last() else {
            panic!("`{label}`: the last item is not the helper function");
        };
        let helper_name = helper.sig.ident.to_string();
        assert!(helper_name.starts_with("__anneal_itree_indirect_"));

        // The boundary annotation and the staged copy stay free of `unsafe`.
        let (annotated, callees) = annotate_itree_external_callees(&cand.source, "kernel_step")
            .unwrap_or_else(|e| panic!("`{label}`: annotation failed: {e}"));
        assert!(callees.contains(&helper_name));
        assert!(!contains_unsafe_token(&annotated));
        let staged = stage_itree_candidate_items(&cand.source, "b0_c0__", "kernel_step")
            .unwrap_or_else(|e| panic!("`{label}`: staging failed: {e}"));
        assert!(
            staged
                .ext_callee_names
                .contains(&format!("b0_c0__{helper_name}"))
        );
        assert!(!contains_unsafe_token(&staged.staged_source));

        // The concrete evaluator runs the helper as the root's first boundary
        // call: two `u32` arguments, a nonzero `u32` return, never a panic.
        let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step")
            .unwrap_or_else(|e| panic!("`{label}`: {e}"));
        for (magic, payload_len) in ITREE_CONCOLIC_BASE_INPUTS {
            let run = ev
                .run_kernel_step(magic, payload_len, &EnvSchedule::new(), "")
                .unwrap_or_else(|e| {
                    panic!("`{label}` unsupported on ({magic:#x}, {payload_len:#x}): {e}")
                });
            match run.events.first() {
                Some(ItreeConcreteEvent::ExtCall { callee, args, ret }) => {
                    assert_eq!(*callee, helper_name);
                    assert_eq!(args.len(), 2);
                    assert_ne!(*ret, vec![0u8; 4], "`{label}` returned 0");
                }
                other => panic!("`{label}`: the first event is {other:?}"),
            }
        }
        combined.push_str(&format!("pub mod c{i} {{\n{}\n}}\n", cand.source));
    }
    // `-D warnings` under `#![forbid(unsafe_code)]`, as `itree-difftest` compiles.
    for opt_level in ["0", "2"] {
        assert!(
            compile_rust_strict_opt("indirect_dispatch_templates", opt_level, &combined),
            "ITree indirect-dispatch templates must compile warning-free at \
             -C opt-level={opt_level}:\n{combined}"
        );
    }
}

#[test]
fn scheduled_itree_batches_carry_indirect_dispatch_and_replay_faithfully() {
    let mut scheduled = 0usize;
    let mut total = 0usize;
    let mut combined = String::from("#![forbid(unsafe_code)]\n");
    for (b_idx, batch_seed) in [0x3333_4444u64, 0xABCD_1234, 0x1111_2222]
        .into_iter()
        .enumerate()
    {
        let batch = generate_itree_batch(ITREE_SAFE_SEEDS, 20, batch_seed);
        assert_eq!(
            batch,
            generate_itree_batch(ITREE_SAFE_SEEDS, 20, batch_seed)
        );
        total += batch.len();
        for (c_idx, cand) in batch.iter().enumerate() {
            let passes = cand
                .applied_mutators
                .iter()
                .filter(|m| *m == "IndirectDispatchOutliner")
                .count();
            if passes == 0 {
                continue;
            }
            assert_eq!(
                passes, 1,
                "a candidate runs the indirect-dispatch pass at most once"
            );
            scheduled += 1;
            assert!(!contains_unsafe_token(&cand.source));
            let (base, steps) = reconstruct_itree_mutation_steps(cand, ITREE_SAFE_SEEDS)
                .expect("reconstruct ITree steps");
            assert!(itree_candidate_replay_is_faithful(cand, &base, &steps));
            combined.push_str(&format!(
                "pub mod b{b_idx}_c{c_idx} {{\n{}\n}}\n",
                cand.source
            ));
        }
    }
    assert_eq!(total, 60);
    assert!(
        (4..=total / 2).contains(&scheduled),
        "{scheduled} of {total} candidates carry `IndirectDispatchOutliner`"
    );
    for opt_level in ["0", "2"] {
        assert!(
            compile_rust_strict_opt("indirect_dispatch_scheduled", opt_level, &combined),
            "scheduled ITree indirect-dispatch candidates must compile warning-free at \
             -C opt-level={opt_level}:\n{combined}"
        );
    }
}

/// Live Miri (`-Zmiri-tree-borrows`) + Anneal evaluation of every template.
///
/// No template may end in a harness or extraction error, an `unsupported`
/// outcome, an unmodeled external call, a missed fault, or a value mismatch.
/// The function-pointer, wide-slice, and capturing-closure templates must
/// agree outright; the trait-object and closure-pointer templates may instead
/// be a (kernel-confirmed) conservative false-positive UB at their coercion.
#[test]
fn indirect_call_templates_run_through_live_miri_and_anneal_oracles() {
    let _guard = LIVE_ORACLE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = unique_temp_dir("miri_live");
    let root = repo_root();
    let templates = all_miri_template_candidates();
    let batch: Vec<GeneratedMiriCandidate> = templates.iter().map(|(_, c)| c.clone()).collect();
    let total = batch.len();

    let report = evaluate_miri_batches_with_options(
        "seeded",
        0x1D1C_A110,
        std::slice::from_ref(&batch),
        total,
        &MiriEvalOptions {
            findings_dir: Some(dir.join("findings")),
            anneal_repo_root: Some(root),
            shrink_seeds: None,
        },
    )
    .expect("evaluate indirect-call template batch");

    // One line per template, shown in full if any expectation fails.
    let mut table = Vec::new();
    let mut problems = Vec::new();
    for (template, cand) in &templates {
        let Some(item) = report.item_reports.iter().find(|r| r.name == cand.fn_name) else {
            problems.push(format!("`{}`: no item report", template.label));
            continue;
        };
        table.push(format!(
            "{:<32} {:?}: miri={:?} anneal={:?} verdict={:?} kernel_confirmed={}",
            template.label,
            template.mode,
            item.miri,
            item.anneal,
            item.verdict,
            item.kernel_confirmed
        ));
        let miri_ok = match template.mode {
            MutationMode::Pass | MutationMode::PerturbAst => {
                matches!(item.miri, MiriOutcome::PassScalar { size_bytes: 4, .. })
            }
            MutationMode::Panic => matches!(item.miri, MiriOutcome::Panic { .. }),
            MutationMode::Ub => matches!(item.miri, MiriOutcome::Ub { .. }),
        };
        if !miri_ok {
            problems.push(format!(
                "`{}`: unexpected Miri outcome {:?} for a {:?} template",
                template.label, item.miri, template.mode
            ));
        }
        let verdict_ok = match (&item.verdict, template.expect) {
            (ComparisonVerdict::Agree, _) => true,
            (
                ComparisonVerdict::Diverge(DivergenceKind::FalsePositiveUb { .. }),
                Expect::AgreeOrFalsePositiveUb,
            ) => item.kernel_confirmed,
            _ => false,
        };
        if !verdict_ok {
            problems.push(format!(
                "`{}`: verdict {:?} (kernel_confirmed={}) does not meet {:?}",
                template.label, item.verdict, item.kernel_confirmed, template.expect
            ));
        }
    }
    if report.compiled_candidates != total || report.compared_candidates != total {
        problems.push(format!(
            "compiled {} and compared {} of {total} candidates; not compared: {:?}",
            report.compiled_candidates, report.compared_candidates, report.not_compared_reasons
        ));
    }
    if !report.unmodeled_external_calls.is_empty() {
        problems.push(format!(
            "unmodeled external calls: {:?}",
            report.unmodeled_external_calls
        ));
    }
    for outcome in ["external_call", "unsupported", "out_of_fuel", "error"] {
        let count = report.anneal_outcomes.get(outcome).copied().unwrap_or(0);
        if count != 0 {
            problems.push(format!("{count} Anneal `{outcome}` outcome(s)"));
        }
    }
    for polarity in [
        "harness_or_extraction_error",
        "unsound_missed_fault",
        "value_mismatch",
    ] {
        let count = report
            .witness_polarity_counts
            .get(polarity)
            .copied()
            .unwrap_or(0);
        if count != 0 {
            problems.push(format!("{count} `{polarity}` witness(es)"));
        }
    }
    let conservative = templates
        .iter()
        .filter(|(t, _)| t.expect == Expect::AgreeOrFalsePositiveUb)
        .count();
    if report.agree_count + conservative < total {
        problems.push(format!(
            "only {} of {total} templates agree ({conservative} may be conservative)",
            report.agree_count
        ));
    }
    assert!(
        problems.is_empty(),
        "live Miri + Anneal evaluation of the indirect-call templates:\n{}\n\nproblems:\n{}\n\n\
         divergence classes: {:?}\nfindings: {:#?}",
        table.join("\n"),
        problems.join("\n"),
        report.divergence_classes,
        report.findings
    );
}

/// Live native-trace + Lean `TraceCheck` evaluation of every
/// `IndirectDispatchOutliner` template on every ITree seed: every candidate
/// compiles (plain and instrumented, at both optimization levels), is
/// compared, and agrees on every trace.
#[test]
fn indirect_dispatch_templates_run_through_live_itree_oracle() {
    let _guard = LIVE_ORACLE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let dir = unique_temp_dir("itree_live");
    let root = repo_root();
    let templates = itree_template_candidates();
    let batch: Vec<GeneratedItreeCandidate> = templates.iter().map(|(_, c)| c.clone()).collect();
    let total = batch.len();

    let report = evaluate_itree_batches_with_options(
        "seeded",
        0x1D1C_A111,
        std::slice::from_ref(&batch),
        total,
        &ItreeEvalOptions {
            trials_per_candidate: 6,
            anneal_repo_root: Some(root),
            findings_dir: Some(dir.join("findings")),
            ..ItreeEvalOptions::default()
        },
    )
    .expect("evaluate ITree indirect-dispatch template batch");

    let labels: Vec<String> = templates
        .iter()
        .enumerate()
        .map(|(i, (label, cand))| format!("b0_c{i}: `{label}` on seed {}", cand.seed_index))
        .collect();
    let context = format!(
        "candidates:\n{}\nnot compared: {:?}\nfindings: {:#?}",
        labels.join("\n"),
        report.not_compared_reasons,
        report.findings
    );
    assert_eq!(report.total_candidates, total, "{context}");
    assert_eq!(report.unsafe_token_violations, 0, "{context}");
    assert_eq!(report.opt_level_0_and_2_compiled, total, "{context}");
    assert_eq!(report.instrumented_compiled, total, "{context}");
    assert_eq!(report.not_compared_candidates, 0, "{context}");
    assert_eq!(
        report.not_compared_reasons.values().sum::<usize>(),
        0,
        "{context}"
    );
    assert_eq!(report.compared_candidates, total, "{context}");
    assert_eq!(report.diverge_candidates, 0, "{context}");
    assert_eq!(report.agree_candidates, total, "{context}");
    assert_eq!(report.diverge_traces, 0, "{context}");
    assert_eq!(
        report.agree_traces, report.distinct_traces_checked,
        "{context}"
    );
    assert!(report.distinct_traces_checked >= total, "{context}");
}
