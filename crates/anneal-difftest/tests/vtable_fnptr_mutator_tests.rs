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
use std::sync::{Mutex, OnceLock};
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
    CallBoundaryOutliner, GeneratedItreeCandidate, ITREE_CONCOLIC_BASE_INPUTS,
    IndirectDispatchOutliner, ItreeAstMutator, ItreeConcreteEvaluator, ItreeConcreteEvent,
    annotate_itree_external_callees, contains_unsafe_token, generate_itree_batch,
    itree_candidate_replay_is_faithful, reconstruct_itree_mutation_steps,
    stage_itree_candidate_items,
};
use anneal_difftest::mutators_miri::{
    ClosureAndAddrEqMutator, DetRng, GeneratedMiriCandidate, MIRI_CORPUS_CRATE_HEADER,
    MIRI_CORPUS_MODULE_PREAMBLE, MiriAstMutator, MutationMode, RecordedMutationStep,
    TreeBorrowsRetagInterleaver, VTableAndFnPtrMutator, build_standalone_candidate_source,
    generate_miri_corpus_batch, load_miri_diff_corpus_seeds, miri_candidate_replay_is_faithful,
    reconstruct_miri_mutation_steps, replay_miri_mutation_steps,
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

fn rustc_is_nightly(rustc_bin: &str, repo: &Path) -> bool {
    Command::new(rustc_bin)
        .arg("--version")
        .current_dir(repo)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| {
            let v = String::from_utf8_lossy(&o.stdout);
            v.contains("nightly") || v.contains("-dev")
        })
        .unwrap_or(false)
}

/// Resolve a nightly `rustc` for compiling `#![feature(core_intrinsics)]` Miri
/// candidates. Honors any explicit nightly `RUSTC` override; when `cargo test`
/// was invoked from outside the repo under a stable default `rustup` toolchain
/// (exporting a stable `RUSTC`), asks `rustup which rustc` inside `repo_root()`
/// so the repo's `rust-toolchain.toml` is picked up automatically.
fn test_nightly_rustc_bin() -> &'static str {
    static NIGHTLY_RUSTC: OnceLock<String> = OnceLock::new();
    NIGHTLY_RUSTC.get_or_init(|| {
        let repo = repo_root();
        let candidate = resolve_rustc_bin();
        if rustc_is_nightly(&candidate, &repo) {
            return candidate;
        }
        if let Ok(out) = Command::new("rustup")
            .args(["which", "rustc"])
            .current_dir(&repo)
            .env_remove("RUSTUP_TOOLCHAIN")
            .output()
            && out.status.success()
        {
            let resolved = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !resolved.is_empty() && rustc_is_nightly(&resolved, &repo) {
                return resolved;
            }
        }
        candidate
    })
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
    let mut child = Command::new(test_nightly_rustc_bin())
        .current_dir(repo_root())
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
            // Multi-callee `ReifyFnPointer`, `UnsafeFnPointer`, `FnPtrToPtr`
            // (positive self-equality + negative stack-pointer inequality),
            // `MutToConstPointer`, and indirect calls through all pointers.
            "__anneal_fnptr_callee_",
            "__anneal_fnptr_alt_",
            "__vt_fp: fn(u32) -> u32 = if",
            "__vt_other_fp: fn(u32) -> u32 = if",
            "__vt_ufp: unsafe fn(u32) -> u32 = __vt_fp",
            "__vt_fp as *const ()",
            "__vt_ufp as *const ()",
            "__vt_raw_a == (__vt_const_ptr as *const ())",
            "__vt_const_ptr: *const u32 = __vt_mut_ptr",
            "__vt_fp(__vt_seed)",
            "unsafe { __vt_ufp(",
            "__vt_other_fp(",
        ],
        lacks: "__AnnealVtable",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "dyn_dispatch",
        classes: &[DYN, ADDR_EQ],
        mode: MutationMode::Pass,
        has: &[
            "__AnnealVtableReceiver",
            "__AnnealVtableAltReceiver",
            "__vt_rec_dyn: &dyn __AnnealVtableTrait",
            "as &dyn __AnnealVtableTrait",
            "__vt_dyn_alt: &dyn __AnnealVtableAlt",
            "as &dyn __AnnealVtableAlt",
            "__vt_dyn.eval_vt(__vt_seed)",
            "__vt_dyn.tag_vt()",
            "__vt_dyn_alt.eval_alt()",
            // Positive (one data address, two vtables) and negative (two
            // distinct concrete receivers) wide-pointer `addr_eq`.
            "core::ptr::addr_eq(__vt_rec_dyn, __vt_dyn_alt)",
            "core::ptr::addr_eq(__vt_rec_dyn, __vt_other_dyn)",
        ],
        lacks: "__vt_fp",
        expect: Expect::AgreeOrFalsePositiveUb,
    },
    MiriTemplate {
        label: "closure_fn_ptr",
        classes: &[FN_PTR],
        mode: MutationMode::Pass,
        has: &[
            // `ClosureFnPointer(Safe)`, `ClosureFnPointer(Unsafe)`,
            // `UnsafeFnPointer`, and `FnPtrToPtr`.
            "__vt_cfp: fn(u32) -> u32 = |__vt_z: u32|",
            "__vt_cufp: unsafe fn(u32) -> u32 = __vt_cfp",
            "__vt_cufp_direct: unsafe fn(u32) -> u32 = |__vt_z: u32|",
            "__vt_cfp as *const ()",
            "__vt_cfp(__vt_seed)",
            "unsafe { __vt_cufp_direct(",
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
            // Lengths 3 and 1 at one data address plus length 2 at element 1
            // (positive + negative wide-pointer `addr_eq`).
            "__clos_full: *const [u32; 3] = &raw const __clos_arr",
            "__clos_head: *const [u32; 1] = __clos_full as *const [u32; 1]",
            "__clos_tail_arr: *const [u32; 2] = __clos_tail_elem as *const [u32; 2]",
            "__clos_long: *const [u32] = __clos_full",
            "__clos_short: *const [u32] = __clos_head",
            "__clos_tail: *const [u32] = __clos_tail_arr",
            "size_of_val(__clos_long)",
            "size_of_val(__clos_short)",
            "size_of_val(__clos_tail)",
            "__anneal_wide_slice_addr_eq_",
            "(__clos_p as *const ()) == (__clos_q as *const ())",
            "(__clos_long as *const ()) == (__clos_tail as *const ())",
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
            // A live `AggregateKind::Closure` (`size_of_val` folded into the
            // return value) capturing `&__clos_cap` alongside a direct borrow.
            "__clos_agg = |__clos_u: u32| wrapping_add(__clos_cap, __clos_u)",
            "size_of_val(&raw const __clos_agg)",
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

/// What every candidate of [`stacked_miri_candidates`] must do: both of its
/// passes are templates that agree on their own.
const STACKED_TEMPLATES: &[MiriTemplate] = &[MiriTemplate {
    label: "stacked_indirect_passes",
    classes: &[FN_PTR, ADDR_EQ, CLOSURE],
    mode: MutationMode::Pass,
    has: &[],
    lacks: "",
    expect: Expect::Agree,
}];

/// The `Pass` templates (by label) that [`stacked_miri_candidates`] applies
/// one after the other to one seed: both mutators in either order, one
/// template twice (the second pass draws the tag of the first and must pick
/// fresh item names), and two templates of one mutator.
const STACKED_PAIRS: [(&str, &str); 4] = [
    ("fn_ptr_chain", "closure_by_unique_ref"),
    ("closure_by_shared_ref", "fn_ptr_chain"),
    ("fn_ptr_chain", "fn_ptr_chain"),
    ("wide_slices", "closure_by_value"),
];

/// One candidate per [`STACKED_PAIRS`] entry, named `stack<k>_<first>__<second>`,
/// with ids from `first_id`. Each pass runs from the PRNG seed that produces
/// its template on its own, which also produces it on a seed an earlier pass
/// mutated (a pass draws its template before it reads the file).
fn stacked_miri_candidates(
    first_id: usize,
) -> Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> {
    let singles = all_miri_template_candidates();
    let pass_of = |label: &str| -> (&'static dyn MiriAstMutator, u64) {
        let (_, cand) = singles
            .iter()
            .find(|(t, _)| t.label == label && t.mode == MutationMode::Pass)
            .unwrap_or_else(|| panic!("no `Pass` template `{label}`"));
        let mutator: &'static dyn MiriAstMutator =
            if cand.applied_mutators[0] == "VTableAndFnPtrMutator" {
                &VTableAndFnPtrMutator
            } else {
                &ClosureAndAddrEqMutator
            };
        (mutator, cand.seed_u64)
    };
    let mut out: Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> = Vec::new();
    for (k, &(first, second)) in STACKED_PAIRS.iter().enumerate() {
        let fn_name = format!("stack{k}_{first}__{second}");
        let seed = format!("pub fn {fn_name}() -> u32 {{\n    let x: u32 = 10u32;\n    x ^ 1u32\n}}\n");
        let mut file = syn::parse_file(&seed).expect("parse seed");
        let mut locals = Vec::new();
        let mut applied_mutators = Vec::new();
        for label in [first, second] {
            let (mutator, s) = pass_of(label);
            let mut rng = DetRng::new(s);
            mutator.mutate_with_mode(&mut file, &mut rng, MutationMode::Pass, &mut locals);
            applied_mutators.push(mutator.name().to_string());
        }
        let fn_source = prettyplease::unparse(&file);
        let source = build_standalone_candidate_source(&fn_source);
        out.push((
            &STACKED_TEMPLATES[0],
            GeneratedMiriCandidate {
                id: first_id + out.len(),
                seed_index: 0,
                seed_name: "indirect_call_seed".to_string(),
                fn_name,
                seed_u64: pass_of(first).1,
                applied_mutators,
                tracked_locals: vec![("x".to_string(), "u32".to_string())],
                fn_source,
                source,
            },
        ));
    }
    out
}

/// Expectations for [`tb_stacked_miri_candidates`] (`TreeBorrowsRetagInterleaver`
/// stacked with an indirect-call mutator in either order).
const TB_STACKED_TEMPLATES: &[MiriTemplate] = &[MiriTemplate {
    label: "tb_stacked_indirect_passes",
    classes: &[FN_PTR, CLOSURE],
    mode: MutationMode::Pass,
    has: &[],
    lacks: "",
    expect: Expect::Agree,
}];

/// Expectations for [`perturb_fault_seed_miri_candidates`]: `PerturbAst` prefix
/// probes run ahead of a faulting (`panic_*` / `ub_*`) seed body and must agree
/// with Miri on the seed's own fault without introducing conservative UB first.
const PERTURB_FAULT_TEMPLATES: &[MiriTemplate] = &[
    MiriTemplate {
        label: "perturb_fault_panic",
        classes: &[FN_PTR, CLOSURE],
        mode: MutationMode::Panic,
        has: &[],
        lacks: "",
        expect: Expect::Agree,
    },
    MiriTemplate {
        label: "perturb_fault_ub",
        classes: &[FN_PTR, ADDR_EQ, CLOSURE],
        mode: MutationMode::Ub,
        has: &[],
        lacks: "",
        expect: Expect::Agree,
    },
];

/// First PRNG seed in `0..TEMPLATE_SCAN_SEEDS` on which
/// `TreeBorrowsRetagInterleaver` (`Pass`) selects its self-contained arm 0
/// (Reserved `&mut` coexisting with a parent raw read, marked by
/// `__tb_parent_read`) when applied to `file`.
fn find_tb_arm0_seed(file: &syn::File) -> u64 {
    (0..TEMPLATE_SCAN_SEEDS)
        .find(|&s| {
            let mut probe = file.clone();
            let mut rng = DetRng::new(s);
            let mut locals = Vec::new();
            TreeBorrowsRetagInterleaver.mutate_with_mode(
                &mut probe,
                &mut rng,
                MutationMode::Pass,
                &mut locals,
            );
            prettyplease::unparse(&probe).contains("__tb_parent_read")
        })
        .expect("TreeBorrowsRetagInterleaver must select arm 0 within TEMPLATE_SCAN_SEEDS")
}

/// Candidates stacking `TreeBorrowsRetagInterleaver` with
/// `ClosureAndAddrEqMutator` and `VTableAndFnPtrMutator` in both orders so
/// live Miri (`-Zmiri-tree-borrows`) + Anneal checks their interaction.
fn tb_stacked_miri_candidates(
    first_id: usize,
) -> Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> {
    let singles = all_miri_template_candidates();
    let pass_of = |label: &str| -> (&'static dyn MiriAstMutator, u64) {
        let (_, cand) = singles
            .iter()
            .find(|(t, _)| t.label == label && t.mode == MutationMode::Pass)
            .unwrap_or_else(|| panic!("no `Pass` template `{label}`"));
        let mutator: &'static dyn MiriAstMutator =
            if cand.applied_mutators[0] == "VTableAndFnPtrMutator" {
                &VTableAndFnPtrMutator
            } else {
                &ClosureAndAddrEqMutator
            };
        (mutator, cand.seed_u64)
    };
    let cases: [(&str, Option<&str>, Option<&str>); 4] = [
        (
            "tb_stack0_tb__closure_by_unique_ref",
            None,
            Some("closure_by_unique_ref"),
        ),
        (
            "tb_stack1_closure_by_shared_ref__tb",
            Some("closure_by_shared_ref"),
            None,
        ),
        ("tb_stack2_tb__fn_ptr_chain", None, Some("fn_ptr_chain")),
        ("tb_stack3_fn_ptr_chain__tb", Some("fn_ptr_chain"), None),
    ];
    let mut out: Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> = Vec::new();
    for (fn_name, first_indirect, second_indirect) in cases {
        let seed = format!("pub fn {fn_name}() -> u32 {{\n    let x: u32 = 10u32;\n    x ^ 1u32\n}}\n");
        let mut file = syn::parse_file(&seed).expect("parse seed");
        let mut locals = Vec::new();
        let mut applied_mutators = Vec::new();
        let mut first_seed = 0u64;
        for (step_idx, indirect_opt) in [first_indirect, second_indirect].into_iter().enumerate() {
            let (mutator, s): (&dyn MiriAstMutator, u64) = match indirect_opt {
                Some(label) => pass_of(label),
                None => (&TreeBorrowsRetagInterleaver, find_tb_arm0_seed(&file)),
            };
            if step_idx == 0 {
                first_seed = s;
            }
            let mut rng = DetRng::new(s);
            mutator.mutate_with_mode(&mut file, &mut rng, MutationMode::Pass, &mut locals);
            applied_mutators.push(mutator.name().to_string());
        }
        let fn_source = prettyplease::unparse(&file);
        let source = build_standalone_candidate_source(&fn_source);
        out.push((
            &TB_STACKED_TEMPLATES[0],
            GeneratedMiriCandidate {
                id: first_id + out.len(),
                seed_index: 0,
                seed_name: "indirect_call_tb_stack_seed".to_string(),
                fn_name: fn_name.to_string(),
                seed_u64: first_seed,
                applied_mutators,
                tracked_locals: vec![("x".to_string(), "u32".to_string())],
                fn_source,
                source,
            },
        ));
    }
    out
}

/// Faulting seeds, named `panic_*` / `ub_*` like the corpus seeds on which the
/// scheduler runs pass 0 as `PerturbAst` (the indirect-call mutators recognize
/// an already-faulting seed by that prefix of its entry function's name),
/// mutated under `MutationMode::PerturbAst`.
///
/// The `VTableAndFnPtrMutator` cases deliberately reuse the PRNG seeds of
/// `dyn_dispatch` and `closure_fn_ptr` to prove that `PerturbAst` never emits
/// a conservative-UB template ahead of the seed's own fault, and
/// `ub_perturb_clos_unit` exercises the `()` return-type prefix-sink path.
fn perturb_fault_seed_miri_candidates(
    first_id: usize,
) -> Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> {
    let singles = all_miri_template_candidates();
    let seed_of = |label: &str| -> u64 {
        singles
            .iter()
            .find(|(t, _)| t.label == label && t.mode == MutationMode::Pass)
            .unwrap_or_else(|| panic!("no `Pass` template `{label}`"))
            .1
            .seed_u64
    };
    let cases: [(&str, &str, &dyn MiriAstMutator, u64, &'static MiriTemplate); 5] = [
        (
            "panic_perturb_vt",
            "pub fn panic_perturb_vt() -> u32 {\n    let x: u32 = u32::MAX;\n    let y: u32 = 1;\n    x + y\n}\n",
            &VTableAndFnPtrMutator,
            seed_of("dyn_dispatch"),
            &PERTURB_FAULT_TEMPLATES[0],
        ),
        (
            "panic_perturb_clos",
            "pub fn panic_perturb_clos() -> u32 {\n    let x: u32 = u32::MAX;\n    let y: u32 = 1;\n    x + y\n}\n",
            &ClosureAndAddrEqMutator,
            seed_of("closure_by_unique_ref"),
            &PERTURB_FAULT_TEMPLATES[0],
        ),
        (
            "ub_perturb_vt",
            "pub fn ub_perturb_vt() -> u32 {\n    unsafe { unchecked_add(u32::MAX, 1u32) }\n}\n",
            &VTableAndFnPtrMutator,
            seed_of("closure_fn_ptr"),
            &PERTURB_FAULT_TEMPLATES[1],
        ),
        (
            "ub_perturb_clos",
            "pub fn ub_perturb_clos() -> u32 {\n    unsafe { unchecked_add(u32::MAX, 1u32) }\n}\n",
            &ClosureAndAddrEqMutator,
            seed_of("wide_slices"),
            &PERTURB_FAULT_TEMPLATES[1],
        ),
        (
            "ub_perturb_clos_unit",
            "pub fn ub_perturb_clos_unit() {\n    let p: *mut u32 = 0usize as *mut u32;\n    unsafe {\n        *p = 42;\n    }\n}\n",
            &ClosureAndAddrEqMutator,
            seed_of("closure_by_shared_ref"),
            &PERTURB_FAULT_TEMPLATES[1],
        ),
    ];
    let mut out: Vec<(&'static MiriTemplate, GeneratedMiriCandidate)> = Vec::new();
    for (fn_name, seed, mutator, s, template) in cases {
        let mut file = syn::parse_file(seed).expect("parse faulting seed");
        let mut rng = DetRng::new(s);
        let mut locals = Vec::new();
        mutator.mutate_with_mode(&mut file, &mut rng, MutationMode::PerturbAst, &mut locals);
        let fn_source = prettyplease::unparse(&file);
        let source = build_standalone_candidate_source(&fn_source);
        out.push((
            template,
            GeneratedMiriCandidate {
                id: first_id + out.len(),
                seed_index: 0,
                seed_name: fn_name.to_string(),
                fn_name: fn_name.to_string(),
                seed_u64: s,
                applied_mutators: vec![mutator.name().to_string()],
                tracked_locals: locals,
                fn_source,
                source,
            },
        ));
    }
    out
}

/// The four `IndirectDispatchOutliner` templates: label, construct classes,
/// and the substrings that identify the template.
const ITREE_TEMPLATES: [(&str, &[&str], &[&str]); 4] = [
    (
        "dyn_dispatch",
        &[DYN, ADDR_EQ],
        &[
            "struct AnnealDynHolderA",
            "struct AnnealDynHolderB",
            "&holder as &dyn AnnealDynProbe",
            "&other as &dyn AnnealDynProbe",
            "&holder as &dyn AnnealDynAlt",
            "picked.probe(seed)",
            "picked.stamp()",
            "as_alt.alt()",
            "core::ptr::addr_eq(as_probe, as_alt)",
            "core::ptr::addr_eq(as_probe, other_probe)",
        ],
    ),
    (
        "fn_pointer",
        &[FN_PTR],
        &[
            "op: fn(u32, u32) -> u32 = if",
            "lifted: fn(u32, u32) -> u32 = |a: u32, b: u32|",
            "raw_op: *const () = op as *const ()",
            "raw_lifted: *const () = lifted as *const ()",
            "core::ptr::addr_eq(raw_op, op as *const ())",
            "core::ptr::addr_eq(raw_op, raw_seed)",
            "op(seed, delta)",
            "lifted(first,",
        ],
    ),
    (
        "closures",
        &[CLOSURE],
        &[
            "bias_ref: &u32 = &bias",
            "core::ptr::addr_eq(&bias, bias_ref)",
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

/// On every ITree seed, `IndirectDispatchOutliner` stacked with
/// `CallBoundaryOutliner` in both orders, with ids from `first_id`.
fn stacked_itree_candidates(first_id: usize) -> Vec<(&'static str, GeneratedItreeCandidate)> {
    let mut out: Vec<(&'static str, GeneratedItreeCandidate)> = Vec::new();
    for seed_index in 0..ITREE_SAFE_SEEDS.len() {
        for indirect_first in [true, false] {
            let s = 0x57AC_1000u64 + out.len() as u64;
            let mut file = syn::parse_file(ITREE_SAFE_SEEDS[seed_index]).expect("parse ITree seed");
            let mut rng = DetRng::new(s);
            let (label, applied) = if indirect_first {
                IndirectDispatchOutliner.mutate(&mut file, &mut rng);
                CallBoundaryOutliner.mutate(&mut file, &mut rng);
                (
                    "indirect_then_call_boundary",
                    ["IndirectDispatchOutliner", "CallBoundaryOutliner"],
                )
            } else {
                CallBoundaryOutliner.mutate(&mut file, &mut rng);
                IndirectDispatchOutliner.mutate(&mut file, &mut rng);
                (
                    "call_boundary_then_indirect",
                    ["CallBoundaryOutliner", "IndirectDispatchOutliner"],
                )
            };
            out.push((
                label,
                GeneratedItreeCandidate {
                    id: first_id + out.len(),
                    seed_index,
                    seed_u64: s,
                    applied_mutators: applied.iter().map(|m| m.to_string()).collect(),
                    source: prettyplease::unparse(&file),
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

/// Two indirect-call passes stacked on one seed: generation is deterministic,
/// each pass adds one driver function and one call of it to the entry
/// function (a second pass of one template picks fresh item names), and the
/// candidate compiles without warnings at both optimization levels.
#[test]
fn stacked_miri_indirect_passes_keep_distinct_items_and_compile() {
    let stacked = stacked_miri_candidates(0);
    let again = stacked_miri_candidates(0);
    assert_eq!(stacked.len(), STACKED_PAIRS.len());
    for ((_, cand), (_, replay)) in stacked.iter().zip(&again) {
        assert_eq!(cand, replay, "`{}` is not deterministic", cand.fn_name);
        assert_eq!(cand.applied_mutators.len(), 2);
        let drivers = cand.fn_source.matches("fn __anneal_vt_driver_").count()
            + cand.fn_source.matches("fn __anneal_clos_driver_").count();
        assert_eq!(drivers, 2, "`{}`:\n{}", cand.fn_name, cand.fn_source);
        let entry = cand
            .fn_source
            .split_once(&format!("pub fn {}", cand.fn_name))
            .expect("entry function")
            .1;
        assert_eq!(
            entry.matches("__anneal_").count(),
            2,
            "`{}` must call each driver once from the entry function:\n{}",
            cand.fn_name,
            cand.fn_source
        );
        for opt_level in ["0", "2"] {
            if let Err(stderr) = compile_with_lints(&cand.fn_name, "-D", opt_level, &cand.source) {
                panic!(
                    "`{}` failed at -C opt-level={opt_level}:\n{stderr}\n{}",
                    cand.fn_name, cand.source
                );
            }
        }
    }
}

/// Checks the source layout by which `scripts/run_diff_test_campaign.py`
/// (`_enclosing_miri_mutator_item_owner`) attributes a fault inside an item
/// that one pass of `mutator` puts ahead of the entry function.
///
/// The script finds the enclosing item by indentation. So every such item must
/// be private, its header must start an unindented line with one of the five
/// item keywords and carry a token of `own_tokens` (and none of
/// `foreign_tokens`, which the script tests first), and every other unindented
/// line ahead of the entry function must be an attribute or close an item or a
/// wrapped signature. `expected_kinds` are the item keywords that the scanned
/// PRNG seeds produce between them.
fn assert_campaign_item_attribution_layout(
    mutator: &dyn MiriAstMutator,
    own_tokens: &[&str],
    foreign_tokens: &[&str],
    expected_kinds: &[&str],
) {
    // `MIRI_MUTATOR_ITEM_HEADER_PREFIXES` of the campaign script.
    const ITEM_KEYWORDS: [&str; 5] = ["fn ", "impl ", "trait ", "struct ", "mod "];
    const ENTRY: &str = "pub fn layout_seed(";
    let mut kinds: BTreeSet<&str> = BTreeSet::new();
    for mode in [
        MutationMode::Pass,
        MutationMode::Panic,
        MutationMode::Ub,
        MutationMode::PerturbAst,
    ] {
        for s in 0..TEMPLATE_SCAN_SEEDS {
            let fn_source = miri_mutant_fn_source(mutator, mode, "layout_seed", s);
            assert!(
                fn_source.lines().any(|line| line.starts_with(ENTRY)),
                "`{}` {mode:?} PRNG seed {s} lost the entry function:\n{fn_source}",
                mutator.name()
            );
            let mut headers = 0usize;
            for line in fn_source
                .lines()
                .take_while(|line| !line.starts_with(ENTRY))
            {
                // Blank lines, item bodies, attributes, and the lines that
                // close an item or a wrapped signature.
                if line.is_empty() || line.starts_with([' ', '#', '}', ')']) {
                    continue;
                }
                let kind = ITEM_KEYWORDS
                    .iter()
                    .copied()
                    .find(|keyword| line.starts_with(*keyword));
                let Some(kind) = kind else {
                    panic!(
                        "`{}` {mode:?} PRNG seed {s} put a line that opens no private item \
                         ahead of the entry function: `{line}`\n{fn_source}",
                        mutator.name()
                    );
                };
                assert!(
                    own_tokens.iter().any(|tok| line.contains(*tok))
                        && !foreign_tokens.iter().any(|tok| line.contains(*tok)),
                    "`{}` {mode:?} PRNG seed {s}: the campaign script cannot attribute the \
                     item header `{line}`\n{fn_source}",
                    mutator.name()
                );
                kinds.insert(kind);
                headers += 1;
            }
            assert!(
                headers >= 1,
                "`{}` {mode:?} PRNG seed {s} added no item:\n{fn_source}",
                mutator.name()
            );
        }
    }
    assert_eq!(
        kinds,
        expected_kinds.iter().copied().collect::<BTreeSet<&str>>(),
        "item kinds of `{}`",
        mutator.name()
    );
}

/// Every item of both Miri indirect-call mutators, in every mode, has the
/// layout and the header tokens that the campaign script's fault attribution
/// reads (`VTABLE_FNPTR_MUTATOR_TOKENS` and `CLOSURE_ADDR_EQ_MUTATOR_TOKENS`
/// there).
#[test]
fn indirect_mutator_items_keep_the_campaign_attribution_layout() {
    const VTABLE_TOKENS: [&str; 5] = [
        "__miri_vt_",
        "__anneal_vt_",
        "__anneal_fnptr_",
        "__AnnealVtable",
        "__vt_",
    ];
    const CLOSURE_TOKENS: [&str; 4] = [
        "__miri_clos_",
        "__anneal_clos_",
        "__anneal_wide_",
        "__clos_",
    ];
    assert_campaign_item_attribution_layout(
        &VTableAndFnPtrMutator,
        &VTABLE_TOKENS,
        &[],
        &["fn ", "impl ", "struct ", "trait "],
    );
    assert_campaign_item_attribution_layout(
        &ClosureAndAddrEqMutator,
        &CLOSURE_TOKENS,
        &VTABLE_TOKENS,
        &["fn ", "mod "],
    );
}

/// Whether `mutator` is one of the two Miri indirect-call mutators.
fn is_indirect_miri_mutator(mutator: &str) -> bool {
    mutator == "VTableAndFnPtrMutator" || mutator == "ClosureAndAddrEqMutator"
}

/// Scheduled corpus candidates whose chain stacks both indirect-call mutators,
/// one of them twice, or one of them with `TreeBorrowsRetagInterleaver`: the
/// recorded passes replay the candidate exactly, the candidate compiles at
/// both optimization levels, and every sub-chain (which is what the
/// mutator-chain shrinker replays) is deterministic and parses; a sub-chain of
/// indirect-call passes alone also compiles.
#[test]
fn scheduled_miri_stacks_of_indirect_passes_replay_shrink_and_compile() {
    const SHAPES: [&str; 3] = [
        "both_indirect_mutators",
        "one_indirect_mutator_twice",
        "indirect_mutator_and_tree_borrows",
    ];
    // Candidates of each shape that are checked.
    const PER_SHAPE: usize = 2;
    let seeds = load_miri_diff_corpus_seeds();
    let seed_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
    let mut checked: BTreeMap<&'static str, usize> = BTreeMap::new();
    for batch_idx in 0..64u64 {
        if SHAPES
            .iter()
            .all(|shape| checked.get(shape).copied().unwrap_or(0) >= PER_SHAPE)
        {
            break;
        }
        for cand in generate_miri_corpus_batch(128, 0x57AC_2000 + batch_idx, 0) {
            let names: Vec<&str> = cand.applied_mutators.iter().map(String::as_str).collect();
            let indirect_passes = names
                .iter()
                .filter(|m| is_indirect_miri_mutator(**m))
                .count();
            let shape: &'static str = if names.contains(&"VTableAndFnPtrMutator")
                && names.contains(&"ClosureAndAddrEqMutator")
            {
                SHAPES[0]
            } else if indirect_passes >= 2 {
                SHAPES[1]
            } else if indirect_passes == 1 && names.contains(&"TreeBorrowsRetagInterleaver") {
                SHAPES[2]
            } else {
                continue;
            };
            let seen = checked.entry(shape).or_insert(0);
            if *seen >= PER_SHAPE {
                continue;
            }
            *seen += 1;

            let label = format!("`{}` {:?}", cand.fn_name, cand.applied_mutators);
            let (base, steps) = reconstruct_miri_mutation_steps(&cand, &seed_refs)
                .unwrap_or_else(|| panic!("no recorded passes for {label}"));
            assert_eq!(steps.len(), names.len(), "{label}");
            assert!(
                miri_candidate_replay_is_faithful(&cand, &base, &steps),
                "replay mismatch on {label}"
            );
            for opt_level in ["0", "2"] {
                if let Err(stderr) = compile_at_opt_level("stacked", opt_level, &cand.source) {
                    panic!(
                        "{label} failed at -C opt-level={opt_level}:\n{stderr}\n{}",
                        cand.source
                    );
                }
            }
            // Every non-empty proper sub-chain.
            for mask in 1u32..(1u32 << steps.len()) - 1 {
                let sub: Vec<RecordedMutationStep> = steps
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| (mask >> i) & 1 == 1)
                    .map(|(_, step)| step.clone())
                    .collect();
                let replayed = replay_miri_mutation_steps(&cand, &base, &sub);
                assert_eq!(
                    replayed,
                    replay_miri_mutation_steps(&cand, &base, &sub),
                    "sub-chain {mask:#b} of {label} is not deterministic"
                );
                assert_eq!(replayed.applied_mutators.len(), sub.len(), "{label}");
                assert!(
                    syn::parse_file(&replayed.source).is_ok(),
                    "sub-chain {mask:#b} of {label} does not parse:\n{}",
                    replayed.source
                );
                if sub
                    .iter()
                    .all(|step| is_indirect_miri_mutator(step.mutator_name.as_str()))
                    && let Err(stderr) = compile_at_opt_level("sub_chain", "0", &replayed.source)
                {
                    panic!(
                        "sub-chain {mask:#b} of {label} failed to compile:\n{stderr}\n{}",
                        replayed.source
                    );
                }
            }
        }
    }
    for shape in SHAPES {
        assert!(
            checked.get(shape).copied().unwrap_or(0) >= 1,
            "no scheduled candidate has shape `{shape}`: {checked:?}"
        );
    }
}

/// `IndirectDispatchOutliner` stacked with `CallBoundaryOutliner` in both
/// orders on every ITree seed: generation is deterministic and free of
/// `unsafe`, both helpers are boundary callees of the root, the concrete
/// evaluator supports every base input and sees the indirect-dispatch helper
/// called, and the candidates compile warning-free under
/// `#![forbid(unsafe_code)]` at both optimization levels.
#[test]
fn stacked_itree_indirect_dispatch_candidates_are_safe_supported_and_compile() {
    let cands = stacked_itree_candidates(0);
    assert_eq!(cands, stacked_itree_candidates(0));
    assert_eq!(cands.len(), 2 * ITREE_SAFE_SEEDS.len());
    let mut combined = String::from("#![forbid(unsafe_code)]\n");
    for (i, (label, cand)) in cands.iter().enumerate() {
        assert!(
            !contains_unsafe_token(&cand.source),
            "`{label}` contains `unsafe`:\n{}",
            cand.source
        );
        let (annotated, callees) = annotate_itree_external_callees(&cand.source, "kernel_step")
            .unwrap_or_else(|e| panic!("`{label}`: annotation failed: {e}"));
        assert!(!contains_unsafe_token(&annotated));
        for prefix in ["__anneal_itree_indirect_", "__anneal_itree_outlined_"] {
            assert!(
                callees.iter().any(|callee| callee.starts_with(prefix)),
                "`{label}`: no boundary callee `{prefix}*`:\n{}",
                cand.source
            );
        }
        let ev = ItreeConcreteEvaluator::new(&cand.source, "kernel_step")
            .unwrap_or_else(|e| panic!("`{label}`: {e}"));
        let mut helper_called = false;
        for (magic, payload_len) in ITREE_CONCOLIC_BASE_INPUTS {
            let run = ev
                .run_kernel_step(magic, payload_len, &EnvSchedule::new(), "")
                .unwrap_or_else(|e| {
                    panic!("`{label}` unsupported on ({magic:#x}, {payload_len:#x}): {e}")
                });
            helper_called |= run.events.iter().any(|event| {
                matches!(
                    event,
                    ItreeConcreteEvent::ExtCall { callee, .. }
                        if callee.starts_with("__anneal_itree_indirect_")
                )
            });
        }
        assert!(
            helper_called,
            "`{label}`: no base input calls the indirect-dispatch helper:\n{}",
            cand.source
        );
        combined.push_str(&format!("pub mod c{i} {{\n{}\n}}\n", cand.source));
    }
    for opt_level in ["0", "2"] {
        assert!(
            compile_rust_strict_opt("stacked_indirect_dispatch", opt_level, &combined),
            "stacked ITree indirect-dispatch candidates must compile warning-free at \
             -C opt-level={opt_level}:\n{combined}"
        );
    }
}

/// `TreeBorrowsRetagInterleaver` stacked with the indirect-call mutators in
/// both orders, plus `PerturbAst` prefix probes on real faulting (`panic_*` /
/// `ub_*`) corpus seeds: generation is deterministic, every candidate compiles
/// warning-free at `-O0` and `-O2`, and every `PerturbAst` probe executes
/// strictly ahead of the seed's fault without emitting a conservative-UB arm.
#[test]
fn tb_stacked_and_perturb_fault_miri_candidates_place_probes_and_compile() {
    let tb_cands = tb_stacked_miri_candidates(0);
    let tb_replay = tb_stacked_miri_candidates(0);
    assert_eq!(tb_cands.len(), 4);
    assert_eq!(tb_cands.len(), tb_replay.len());
    for ((_, cand), (_, replay)) in tb_cands.iter().zip(&tb_replay) {
        assert_eq!(cand, replay, "`{}` is not deterministic", cand.fn_name);
        assert!(
            cand.fn_source.contains("__miri_tb_") && cand.fn_source.contains("__tb_parent_read"),
            "`{}` missing TreeBorrows arm 0:\n{}",
            cand.fn_name,
            cand.fn_source
        );
        assert!(
            cand.fn_source.contains("__anneal_vt_driver_")
                || cand.fn_source.contains("__anneal_clos_driver_"),
            "`{}` missing indirect-call driver:\n{}",
            cand.fn_name,
            cand.fn_source
        );
        for opt_level in ["0", "2"] {
            if let Err(stderr) = compile_with_lints(&cand.fn_name, "-D", opt_level, &cand.source) {
                panic!(
                    "`{}` failed at -C opt-level={opt_level}:\n{stderr}\n{}",
                    cand.fn_name, cand.source
                );
            }
        }
    }

    let perturb_cands = perturb_fault_seed_miri_candidates(tb_cands.len());
    let perturb_replay = perturb_fault_seed_miri_candidates(tb_cands.len());
    assert_eq!(perturb_cands.len(), 5);
    assert_eq!(perturb_cands.len(), perturb_replay.len());
    for ((_, cand), (_, replay)) in perturb_cands.iter().zip(&perturb_replay) {
        assert_eq!(cand, replay, "`{}` is not deterministic", cand.fn_name);
        let entry_hdr = format!("pub fn {}()", cand.fn_name);
        let entry_pos = cand
            .fn_source
            .find(&entry_hdr)
            .unwrap_or_else(|| panic!("`{}` missing entry header:\n{}", cand.fn_name, cand.fn_source));
        let entry_body = &cand.fn_source[entry_pos..];
        let driver_marker = if cand.applied_mutators[0] == "VTableAndFnPtrMutator" {
            assert!(
                cand.fn_source.contains("__anneal_fnptr_callee_")
                    && !cand.fn_source.contains("__AnnealVtable")
                    && !cand.fn_source.contains("__vt_cfp"),
                "`{}` PerturbAst must emit the 100%-Agree fn_ptr_chain arm:\n{}",
                cand.fn_name,
                cand.fn_source
            );
            "__anneal_vt_driver_"
        } else {
            "__anneal_clos_driver_"
        };
        let fault_marker = if cand.fn_name.starts_with("panic_") {
            "x + y"
        } else if cand.fn_name.ends_with("_unit") {
            "*p = 42"
        } else {
            "unchecked_add"
        };
        let probe_pos = entry_body.find(driver_marker).unwrap_or_else(|| {
            panic!("`{}` missing `{driver_marker}` in entry:\n{entry_body}", cand.fn_name)
        });
        let fault_pos = entry_body.find(fault_marker).unwrap_or_else(|| {
            panic!("`{}` missing `{fault_marker}` in entry:\n{entry_body}", cand.fn_name)
        });
        assert!(
            probe_pos < fault_pos,
            "`{}` must place PerturbAst driver call before fault:\n{entry_body}",
            cand.fn_name
        );
        if cand.fn_name.ends_with("_unit") {
            let sink_pos = entry_body.find("let mut __miri_sink: u32 =").unwrap_or_else(|| {
                panic!("`{}` missing unit-return sink:\n{entry_body}", cand.fn_name)
            });
            assert!(
                probe_pos < sink_pos && sink_pos < fault_pos,
                "`{}` must bind `__miri_sink` between prefix call and fault:\n{entry_body}",
                cand.fn_name
            );
        }
        for opt_level in ["0", "2"] {
            if let Err(stderr) = compile_with_lints(&cand.fn_name, "-D", opt_level, &cand.source) {
                panic!(
                    "`{}` failed at -C opt-level={opt_level}:\n{stderr}\n{}",
                    cand.fn_name, cand.source
                );
            }
        }
    }
}

/// One `PerturbAst` pass on `base` (whose entry function is `fn_name`) for
/// every `Pass` template of `singles`, run with that template's mutator and
/// PRNG seed. Returns the mutated sources after checking that each one:
/// - is deterministic and parses;
/// - adds exactly one driver call to the entry function;
/// - on an already-faulting (`panic_*` / `ub_*`) seed, runs that call as the
///   entry function's first statement (ahead of the seed's own fault) and
///   carries no conservative-UB (`dyn Trait` / closure-pointer) template;
/// - on any other seed, is byte for byte the `Pass` mutant (every template,
///   appended after the seed body), so `dyn_dispatch` stays reachable there.
fn checked_perturb_ast_sources(
    base: &syn::File,
    fn_name: &str,
    singles: &[(&'static MiriTemplate, GeneratedMiriCandidate)],
) -> Vec<String> {
    let seed_faults = fn_name.starts_with("panic_") || fn_name.starts_with("ub_");
    let entry_header = format!("pub fn {fn_name}(");
    let mut out = Vec::new();
    for (template, single) in singles.iter().filter(|(t, _)| t.mode == MutationMode::Pass) {
        let is_vt = single.applied_mutators[0] == "VTableAndFnPtrMutator";
        let mutator: &dyn MiriAstMutator = if is_vt {
            &VTableAndFnPtrMutator
        } else {
            &ClosureAndAddrEqMutator
        };
        let mutate = |mode: MutationMode| -> String {
            let mut file = base.clone();
            let mut rng = DetRng::new(single.seed_u64);
            let mut locals = Vec::new();
            mutator.mutate_with_mode(&mut file, &mut rng, mode, &mut locals);
            prettyplease::unparse(&file)
        };
        let perturbed = mutate(MutationMode::PerturbAst);
        assert_eq!(
            perturbed,
            mutate(MutationMode::PerturbAst),
            "`{}` PerturbAst is not deterministic on `{fn_name}`",
            mutator.name()
        );
        assert!(
            syn::parse_file(&perturbed).is_ok(),
            "`{}` PerturbAst on `{fn_name}` does not parse:\n{perturbed}",
            mutator.name()
        );
        let entry = perturbed
            .split_once(entry_header.as_str())
            .unwrap_or_else(|| panic!("`{fn_name}` missing entry header:\n{perturbed}"))
            .1;
        let (driver, probe_let) = if is_vt {
            ("__anneal_vt_driver_", "let __miri_vt_")
        } else {
            ("__anneal_clos_driver_", "let __miri_clos_")
        };
        assert_eq!(
            entry.matches(driver).count(),
            1,
            "`{}` PerturbAst must add one driver call to `{fn_name}`:\n{perturbed}",
            mutator.name()
        );
        if seed_faults {
            let body = entry
                .split_once('{')
                .unwrap_or_else(|| panic!("`{fn_name}` missing entry body:\n{perturbed}"))
                .1
                .trim_start();
            assert!(
                body.starts_with(probe_let),
                "`{}` PerturbAst must run its driver ahead of faulting `{fn_name}`:\n{perturbed}",
                mutator.name()
            );
            assert!(
                !perturbed.contains("__AnnealVtable") && !perturbed.contains("__vt_cfp"),
                "`{}` PerturbAst emitted a conservative-UB template ahead of faulting \
                 `{fn_name}` (template seed `{}`):\n{perturbed}",
                mutator.name(),
                template.label
            );
        } else {
            assert_eq!(
                perturbed,
                mutate(MutationMode::Pass),
                "`{}` PerturbAst must equal Pass on non-faulting `{fn_name}` (template `{}`)",
                mutator.name(),
                template.label
            );
        }
        out.push(perturbed);
    }
    out
}

/// `PerturbAst` passes of both indirect-call mutators on EVERY corpus seed
/// (`load_miri_diff_corpus_seeds`), and on the closed, renamed seed ASTs that
/// the scheduler mutates: an already-faulting (`panic_*` / `ub_*`) seed gets a
/// 100%-`Agree` prefix driver ahead of its fault, every other seed keeps the
/// whole `Pass` template set (including `&T as &dyn Trait` dispatch) after its
/// body, and the mutants of the closed seeds compile as one crate.
#[test]
fn perturb_ast_indirect_passes_place_probes_on_every_corpus_seed() {
    let seeds = load_miri_diff_corpus_seeds();
    let seed_refs: Vec<&str> = seeds.iter().map(|s| s.fn_source.as_str()).collect();
    let singles = all_miri_template_candidates();
    let n_pass = singles
        .iter()
        .filter(|(t, _)| t.mode == MutationMode::Pass)
        .count();
    assert!(n_pass >= 2, "expected `Pass` templates of both mutators");

    // 0. Ratchet the naming convention relied on by `entry_fn_is_faulting_seed`
    //    and `collect_non_fault_seed_indices`: every corpus seed in
    //    `tests/miri-diff/manifest.toml` must carry a `panic_` / `ub_` prefix
    //    iff its manifest verdict is non-passing.
    let manifest_path = repo_root().join("tests/miri-diff/manifest.toml");
    let manifest = fs::read_to_string(&manifest_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", manifest_path.display()));
    let mut manifest_verdicts: BTreeMap<String, String> = BTreeMap::new();
    let mut cur_name: Option<String> = None;
    for raw_line in manifest.lines() {
        let line = raw_line.trim();
        if line == "[[tests]]" {
            cur_name = None;
        } else if let Some(rest) = line.strip_prefix("name = \"")
            && let Some(name) = rest.strip_suffix('"')
        {
            cur_name = Some(name.to_string());
        } else if let Some(rest) = line.strip_prefix("miri_verdict = \"")
            && let Some(verdict) = rest.strip_suffix('"')
            && let Some(name) = &cur_name
        {
            manifest_verdicts.insert(name.clone(), verdict.to_string());
        }
    }
    assert_eq!(
        manifest_verdicts.len(),
        seeds.len(),
        "manifest test count ({}) diverged from loaded corpus seeds ({})",
        manifest_verdicts.len(),
        seeds.len()
    );
    for seed in &seeds {
        let verdict = manifest_verdicts
            .get(&seed.name)
            .unwrap_or_else(|| panic!("corpus seed `{}` missing from manifest.toml", seed.name));
        let prefix_faults = seed.name.starts_with("panic_") || seed.name.starts_with("ub_");
        let manifest_faults = !verdict.starts_with("pass:");
        assert_eq!(
            prefix_faults, manifest_faults,
            "corpus seed `{}` has manifest verdict `{verdict}` which disagrees with \
             `entry_fn_is_faulting_seed` (`panic_*` / `ub_*`)",
            seed.name
        );
    }

    // 1. Every corpus seed, exactly as `load_miri_diff_corpus_seeds` returns it.
    let mut faulting = 0usize;
    let mut live = 0usize;
    let mut dyn_on_live = 0usize;
    for seed in &seeds {
        let base = syn::parse_file(&seed.fn_source)
            .unwrap_or_else(|e| panic!("corpus seed `{}` does not parse: {e}", seed.name));
        let sources = checked_perturb_ast_sources(&base, &seed.name, &singles);
        assert_eq!(sources.len(), n_pass);
        if seed.name.starts_with("panic_") || seed.name.starts_with("ub_") {
            faulting += 1;
        } else {
            live += 1;
            dyn_on_live += sources
                .iter()
                .filter(|src| src.contains("as &dyn __AnnealVtableTrait"))
                .count();
        }
    }
    assert!(
        faulting >= 8 && live >= 8,
        "corpus must mix faulting ({faulting}) and non-faulting ({live}) seeds"
    );
    // Every non-faulting seed still reaches `&T as &dyn Trait` dispatch under
    // `PerturbAst` (from the `dyn_dispatch` template's PRNG seed).
    assert!(
        dyn_on_live >= live,
        "`PerturbAst` reached `dyn Trait` dispatch on only {dyn_on_live} of {live} live seeds"
    );

    // 2. The closed, renamed seed ASTs that one scheduled batch mutates (one
    //    per seed it draws): the same checks, and the mutants (one template per
    //    seed, rotating) compile together, one module per candidate.
    let mut closed: BTreeMap<usize, (syn::File, String)> = BTreeMap::new();
    for cand in generate_miri_corpus_batch(1024, 0x00A2_5EED_2026, 0) {
        if closed.contains_key(&cand.seed_index) {
            continue;
        }
        let Some((base, _steps)) = reconstruct_miri_mutation_steps(&cand, &seed_refs) else {
            continue;
        };
        let entry_header = format!("pub fn {}(", cand.fn_name);
        if !cand.fn_name.starts_with(&cand.seed_name)
            || !prettyplease::unparse(&base).contains(&entry_header)
        {
            continue;
        }
        closed.insert(cand.seed_index, (base, cand.fn_name.clone()));
    }
    let mut closed_faulting = 0usize;
    let mut closed_live = 0usize;
    let mut combined = String::from(MIRI_CORPUS_CRATE_HEADER);
    let mut modules = 0usize;
    for (seed_index, (base, fn_name)) in &closed {
        let sources = checked_perturb_ast_sources(base, fn_name, &singles);
        assert_eq!(sources.len(), n_pass);
        if fn_name.starts_with("panic_") || fn_name.starts_with("ub_") {
            closed_faulting += 1;
        } else {
            closed_live += 1;
        }
        let k = seed_index % n_pass;
        combined.push_str(&format!(
            "pub mod s{seed_index}_t{k} {{\n{MIRI_CORPUS_MODULE_PREAMBLE}\n{}\n}}\n",
            sources[k]
        ));
        modules += 1;
    }
    assert!(
        closed_faulting >= 8 && closed_live >= 8,
        "scheduled batch drew only {closed_faulting} faulting and {closed_live} non-faulting seeds"
    );
    if let Err(stderr) = compile_at_opt_level("perturb_all_seeds", "0", &combined) {
        panic!(
            "`PerturbAst` mutants of {modules} closed corpus seeds failed to compile:\n{stderr}"
        );
    }
}

/// Scheduled Miri (`generate_miri_corpus_batch`) and ITree
/// (`generate_itree_batch`) batches must emit all four construct classes
/// (`&T as &dyn Trait` + vtable dispatch, indirect `fn(...)` + `FnPtrToPtr` /
/// `PointerCoercion`, wide-pointer `addr_eq`, and capturing closures) at
/// non-zero, healthy, and bounded rates.
#[test]
fn scheduled_miri_and_itree_batches_emit_all_four_construct_classes_at_healthy_rates() {
    // 1. Scheduled Miri corpus batch.
    const MIRI_N: usize = 1024;
    let miri_batch = generate_miri_corpus_batch(MIRI_N, 0xD157_2026_0004, 0);
    assert_eq!(miri_batch.len(), MIRI_N);

    let mut miri_indirect_cands = 0usize;
    let mut miri_dyn = 0usize;
    let mut miri_fn_ptr_chain = 0usize;
    let mut miri_closure_fn_ptr = 0usize;
    let mut miri_wide_slices = 0usize;
    let mut miri_clos_by_val = 0usize;
    let mut miri_clos_by_shared_ref = 0usize;
    let mut miri_clos_by_unique_ref = 0usize;
    let mut miri_classes: BTreeSet<&'static str> = BTreeSet::new();

    for cand in &miri_batch {
        if !cand
            .applied_mutators
            .iter()
            .any(|m| is_indirect_miri_mutator(m.as_str()))
        {
            continue;
        }
        miri_indirect_cands += 1;
        let src = &cand.fn_source;
        if VTABLE_TEMPLATES[1].has.iter().all(|m| has_marker(src, m)) {
            miri_dyn += 1;
            miri_classes.extend(VTABLE_TEMPLATES[1].classes.iter().copied());
        }
        if VTABLE_TEMPLATES[0].has.iter().all(|m| has_marker(src, m)) {
            miri_fn_ptr_chain += 1;
            miri_classes.extend(VTABLE_TEMPLATES[0].classes.iter().copied());
        }
        if VTABLE_TEMPLATES[2].has.iter().all(|m| has_marker(src, m)) {
            miri_closure_fn_ptr += 1;
            miri_classes.extend(VTABLE_TEMPLATES[2].classes.iter().copied());
        }
        if has_marker(src, "__anneal_wide_slice_addr_eq_") {
            miri_wide_slices += 1;
            miri_classes.insert(ADDR_EQ);
        }
        if has_marker(src, "::__::apply_keep(") {
            miri_clos_by_val += 1;
            miri_classes.insert(CLOSURE);
        }
        if has_marker(src, "__clos_shared: &u32 = &__clos_base") {
            miri_clos_by_shared_ref += 1;
            miri_classes.insert(CLOSURE);
        }
        if has_marker(src, "::__::eval_once(move ||") {
            miri_clos_by_unique_ref += 1;
            miri_classes.insert(CLOSURE);
        }
    }
    assert_eq!(
        miri_classes,
        BTreeSet::from([DYN, FN_PTR, ADDR_EQ, CLOSURE]),
        "scheduled Miri batch missed construct classes"
    );
    assert!(
        (50..=MIRI_N / 4).contains(&miri_indirect_cands),
        "scheduled Miri batch had {miri_indirect_cands}/{MIRI_N} indirect candidates"
    );
    assert!(
        miri_dyn >= 3
            && miri_fn_ptr_chain >= 5
            && miri_closure_fn_ptr >= 3
            && miri_wide_slices >= 10
            && miri_clos_by_val >= 10
            && miri_clos_by_shared_ref >= 4
            && miri_clos_by_unique_ref >= 1,
        "scheduled Miri construct counts too low: dyn={miri_dyn}, fn_ptr={miri_fn_ptr_chain}, \
         closure_fn_ptr={miri_closure_fn_ptr}, wide_slices={miri_wide_slices}, \
         by_val={miri_clos_by_val}, by_shared_ref={miri_clos_by_shared_ref}, \
         by_unique_ref={miri_clos_by_unique_ref}"
    );

    // 2. Scheduled ITree batch.
    const ITREE_N: usize = 512;
    let itree_batch = generate_itree_batch(ITREE_SAFE_SEEDS, ITREE_N, 0xD157_2026_1733);
    assert_eq!(itree_batch.len(), ITREE_N);

    let mut itree_indirect_cands = 0usize;
    let mut itree_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut itree_classes: BTreeSet<&'static str> = BTreeSet::new();

    for cand in &itree_batch {
        assert!(
            !contains_unsafe_token(&cand.source),
            "scheduled ITree candidate {} emitted `unsafe`:\n{}",
            cand.id,
            cand.source
        );
        if !cand
            .applied_mutators
            .iter()
            .any(|m| m == "IndirectDispatchOutliner")
        {
            continue;
        }
        itree_indirect_cands += 1;
        for (label, classes, markers) in ITREE_TEMPLATES {
            if markers.iter().all(|m| has_marker(&cand.source, m)) {
                *itree_counts.entry(label).or_insert(0) += 1;
                itree_classes.extend(classes.iter().copied());
            }
        }
    }
    assert_eq!(
        itree_classes,
        BTreeSet::from([DYN, FN_PTR, ADDR_EQ, CLOSURE]),
        "scheduled ITree batch missed construct classes: {itree_counts:?}"
    );
    assert!(
        (24..=ITREE_N / 4).contains(&itree_indirect_cands),
        "scheduled ITree batch had {itree_indirect_cands}/{ITREE_N} indirect candidates"
    );
    for (label, _, _) in ITREE_TEMPLATES {
        let count = itree_counts.get(label).copied().unwrap_or(0);
        assert!(
            count >= 5,
            "scheduled ITree batch emitted `{label}` only {count} time(s): {itree_counts:?}"
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
    // Every template on its own, pairs of agreeing indirect-call templates,
    // `TreeBorrowsRetagInterleaver` stacked with indirect-call passes in both
    // orders, and `PerturbAst` prefix probes on real faulting corpus seeds.
    let mut templates = all_miri_template_candidates();
    let first_stacked_id = templates.len();
    templates.extend(stacked_miri_candidates(first_stacked_id));
    let first_tb_id = templates.len();
    templates.extend(tb_stacked_miri_candidates(first_tb_id));
    let first_perturb_id = templates.len();
    templates.extend(perturb_fault_seed_miri_candidates(first_perturb_id));
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
    // Every template on its own, then `IndirectDispatchOutliner` stacked with
    // `CallBoundaryOutliner` in both orders.
    let mut templates = itree_template_candidates();
    let first_stacked_id = templates.len();
    templates.extend(stacked_itree_candidates(first_stacked_id));
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

/// Anti-vacuity check: verify that every `IndirectDispatchOutliner` template's
/// multi-impl vtable dispatch, multi-callee function-pointer dispatch, and
/// positive/negative `addr_eq` checks genuinely influence the boundary helper's
/// returned `u32` (even on zero inputs `(0, 0)`).
#[test]
fn indirect_dispatch_outliner_outputs_depend_on_vtable_fnptr_and_addr_eq() {
    let cands: Vec<(&str, GeneratedItreeCandidate)> = itree_template_candidates()
        .into_iter()
        .filter(|(_, c)| c.seed_index == 0)
        .collect();
    assert_eq!(cands.len(), ITREE_TEMPLATES.len());

    let helper_ret = |source: &str, magic: u32, payload_len: u32| -> Vec<u8> {
        let ev = ItreeConcreteEvaluator::new(source, "kernel_step")
            .unwrap_or_else(|e| panic!("evaluator init failed: {e}\n{source}"));
        let run = ev
            .run_kernel_step(magic, payload_len, &EnvSchedule::new(), "")
            .unwrap_or_else(|e| panic!("evaluator run failed: {e}\n{source}"));
        match run.events.first() {
            Some(ItreeConcreteEvent::ExtCall { ret, .. }) => ret.clone(),
            other => panic!("expected first ExtCall event, got {other:?}"),
        }
    };

    for (label, cand) in &cands {
        let base_zero = helper_ret(&cand.source, 0, 0);
        match *label {
            "dyn_dispatch" => {
                // Even vs odd `seed` dispatches `AnnealDynHolderA` vs `AnnealDynHolderB`.
                let base_odd = helper_ret(&cand.source, 1, 0);
                assert_ne!(
                    base_zero, base_odd,
                    "`dyn_dispatch` must distinguish HolderA vs HolderB"
                );
                // Flipping either positive or negative `addr_eq` must change the return.
                for (needle, flipped) in [
                    ("core::ptr::addr_eq(as_probe, as_alt)", "false"),
                    ("core::ptr::addr_eq(as_probe, other_probe)", "true"),
                ] {
                    assert!(
                        cand.source.contains(needle),
                        "missing `{needle}`:\n{}",
                        cand.source
                    );
                    let perturbed = cand.source.replacen(needle, flipped, 1);
                    assert_ne!(
                        base_zero,
                        helper_ret(&perturbed, 0, 0),
                        "`dyn_dispatch` return did not change when flipping `{needle}`"
                    );
                }
            }
            "fn_pointer" => {
                // Even vs odd `seed` dispatches `anneal_fnptr_mix` vs `anneal_fnptr_fold`.
                let even_ret = helper_ret(&cand.source, 0x200, 0x44);
                let odd_ret = helper_ret(&cand.source, 0x201, 0x44);
                assert_ne!(
                    even_ret, odd_ret,
                    "`fn_pointer` must distinguish `anneal_fnptr_mix` vs `anneal_fnptr_fold`"
                );
                for (needle, flipped) in [
                    ("core::ptr::addr_eq(raw_op, op as *const ())", "false"),
                    ("core::ptr::addr_eq(raw_lifted, lifted as *const ())", "false"),
                    ("core::ptr::addr_eq(raw_op, raw_seed)", "true"),
                ] {
                    assert!(
                        cand.source.contains(needle),
                        "missing `{needle}`:\n{}",
                        cand.source
                    );
                    let perturbed = cand.source.replacen(needle, flipped, 1);
                    assert_ne!(
                        base_zero,
                        helper_ret(&perturbed, 0, 0),
                        "`fn_pointer` return did not change when flipping `{needle}`"
                    );
                }
            }
            "closures" => {
                let needle = "core::ptr::addr_eq(&bias, bias_ref)";
                assert!(
                    cand.source.contains(needle),
                    "missing `{needle}`:\n{}",
                    cand.source
                );
                let perturbed = cand.source.replacen(needle, "false", 1);
                assert_ne!(
                    base_zero,
                    helper_ret(&perturbed, 0, 0),
                    "`closures` return did not change when flipping `{needle}`"
                );
            }
            "slice_addr_eq" => {
                for (needle, flipped) in [
                    ("core::ptr::addr_eq(whole, short)", "false"),
                    ("core::ptr::addr_eq(whole, shifted)", "true"),
                ] {
                    assert!(
                        cand.source.contains(needle),
                        "missing `{needle}`:\n{}",
                        cand.source
                    );
                    let perturbed = cand.source.replacen(needle, flipped, 1);
                    assert_ne!(
                        base_zero,
                        helper_ret(&perturbed, 0, 0),
                        "`slice_addr_eq` return did not change when flipping `{needle}`"
                    );
                }
            }
            other => panic!("unexpected ITree template `{other}`"),
        }
    }
}
