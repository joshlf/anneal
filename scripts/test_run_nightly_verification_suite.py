#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `scripts/run_nightly_verification_suite.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_nightly_verification_suite as suite  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parent.parent
UNTESTED_VARIANT_TEST = "tests/mir/MirUntestedVariantCorrespondenceTests.lean"
# Workspace-library imports of `MirUntestedVariantCorrespondenceTests.lean` (its header is
# `import Trusted`, `Anneal.MirFuelFree`, the two `Correspondence.V2026_06_01` layers,
# `MiniRustSpec.Correspondence.Translate` and `Lean.Elab.Command`).
UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS = (
    "Trusted",
    "Anneal.MirFuelFree",
    "Correspondence.V2026_06_01.L3_PlacesAndBasicMem",
    "Correspondence.V2026_06_01.L5_ControlAndCalls",
    "MiniRustSpec.Correspondence.Translate",
)

# Pillar 3 divergences resolved by `*_simulation` theorems (statement-pinned in their
# authority audit module, or in `tests/mir/MirUntestedVariantCorrespondenceTests.lean` itself).
RESOLVED_DIVERGENCE_IDS = frozenset(
    {
        "DIV-MR-CALL-TARGET-LOCAL",
        "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL",
        "DIV-MR-TB-TWOPHASE-DIRECT-WRITE",
        "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
        "DIV-MR-TB-UNSAFECELL-PROTECTED-IM",
        "DIV-LM-RAW-OVERWRITE-CHAR-COPY",
        "DIV-LM-D6-OFFSET-DISABLED-TAG",
        "DIV-LM-ENUM-SET-DISCR-UNINIT",
        # Episode 2: fixed by the frame-depth-aware tail-call teardown (`disableFrameBorrows`
        # before `enterTailCalleeFrame` in `evalTailCallTerminator`).
        "DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL",
    }
)
# Episode 2 divergences that are still live (open actionable Anneal bugs).
OPEN_DIVERGENCE_IDS = frozenset(
    {
        "DIV-LM-TAILCALL-NOUNWIND-UNWIND",
        "DIV-TR-OPAQUECAST-ROOT-DISPATCH",
        "DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW",
    }
)
ACTIONABLE_DIVERGENCE_COUNT = len(RESOLVED_DIVERGENCE_IDS) + len(OPEN_DIVERGENCE_IDS)

# A meaningful, hole-free statement for synthetic resolution theorems and their statement
# pins: the flip-direction witness polarity guard rejects vacuous ones (`True`, `0 = 0`).
SYNTH_STMT = "annealOutcome fooProg = miriOutcome fooProg"
# A synthetic divergence witness statement (distinct from `SYNTH_STMT`).
SYNTH_DIVERGENCE_STMT = "annealOutcome fooProg ≠ miriOutcome fooProg"

# Synthetic Stage-B corpus separating Episode 1's lifted slice wide pointers from unlifted
# unsized DSTs (8 functions; statement counts in comments).
SLICE_VS_DST_CORPUS = """
pub fn slice_only(p: *mut u32, n: usize, k: usize) -> usize {
    let s = unsafe { core::slice::from_raw_parts(p, n) };
    let w = core::ptr::slice_from_raw_parts_mut(p, n);
    let (a, b) = unsafe { (*w).split_at_mut(k) };
    s.len() + a.len() + b.len()
}

pub fn pure_add(a: u32, b: u32) -> u32 {
    let c = a + b;
    c
}

pub fn unsized_body(x: &[u8]) -> usize {
    let n = x.len();
    let bytes = core::mem::size_of_val(x);
    n + bytes
}

pub fn qsized_generic<T: ?Sized>(_t: &T, p: *const u8, n: usize) -> usize {
    let w = core::ptr::slice_from_raw_parts(p, n);
    let m = n + 1;
    m
}

pub fn generic_from_raw_parts(p: *const u8, n: usize) -> usize {
    let m = n * 2;
    let w: *const [u8] = core::ptr::from_raw_parts(p, n);
    m
}

pub fn qsized_without_slice_op<T: ?Sized>(_t: &T) -> usize {
    let m = 3;
    m
}

pub struct W<T: ?Sized>(core::marker::PhantomData<T>);
impl<T: ?Sized> W<T> {
    pub fn impl_qsized(&self, p: *const u8, n: usize) -> usize {
        let w = core::ptr::slice_from_raw_parts(p, n);
        let m = n;
        m
    }
}

pub fn dyn_dispatch(x: &u32) -> u32 {
    let d: &dyn Fooable = x;
    let y = *x;
    y
}
"""


class NightlyVerificationSuiteTests(unittest.TestCase):
    def test_stage_a_syntactic_completeness_on_repo(self) -> None:
        stage_a = suite.compute_stage_a_syntactic_completeness(REPO_ROOT)
        mir = stage_a["anneal_mir_ast"]
        # Exactly the `Trusted.Rustc.V2026_06_01.MirAst` constructors (checked against the Lean
        # inductives by `scripts/audit_mir_coverage_matrix.py`).
        self.assertEqual(mir["total_variants"], 94)
        self.assertGreaterEqual(mir["proved_corresponding"], 73)
        self.assertEqual(mir["supported_untested"], 0)
        self.assertEqual(mir["untested_variants"], [])
        self.assertEqual(
            mir["total_variants"],
            mir["proved_corresponding"]
            + mir["supported_and_tested"]
            + mir["supported_untested"]
            + mir["unsupported_fail_closed"],
        )
        statuses = {
            f"{entry['category']}.{name}": status
            for entry in suite.MIR_AST_CATEGORIES
            for name, status in entry["variants"]
        }
        self.assertEqual(statuses["StatementKind.constEvalCounter"], "proved_corresponding")
        self.assertEqual(statuses["TerminatorKind.tailCall"], "proved_corresponding")
        # Explicit phase boundary (rejected after borrowck by rustc and Miri).
        self.assertEqual(statuses["ProjectionElem.opaqueCast"], "supported_and_tested")
        self.assertGreaterEqual(mir["stage1_lowered_lintrinsic_op_variants"], 30)

        mr = stage_a["minirust_authority"]
        self.assertEqual(mr["spec_files"], 27)
        self.assertEqual(mr["shallow_types_translated"], 100)
        self.assertEqual(mr["interp_anchored_items"], 104)
        self.assertGreater(mr["audited_declarations"], 500)

        lm = stage_a["lean_miri_authority"]
        self.assertEqual(lm["vendored_miri_files"], 608)
        self.assertIn("LM-1.1", lm["milestones_merged"])
        self.assertIn("LM-3.3", lm["milestones_merged"])
        self.assertGreater(lm["audited_declarations"], 500)

    def test_stage_b_blended_completeness_and_marginal_unlock_math(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            sample_rs = tmp_dir / "sample.rs"
            sample_rs.write_text(
                """
                pub fn pure_add(a: u32, b: u32) -> u32 {
                    let c = a.wrapping_add(b);
                    c
                }

                pub fn partially_blocked_float(x: u32) -> u32 {
                    let a = x + 1;
                    let b = a * 2;
                    let c = b - 1;
                    let _f: f64 = 1.0;
                    c
                }

                pub fn multi_blocked(x: u32) -> u32 {
                    let _f: f32 = 0.0;
                    unsafe { core::arch::asm!("nop") };
                    x
                }
                """,
                encoding="utf-8",
            )
            res = suite.analyze_corpus_completeness("synthetic", [sample_rs], alpha=0.5)
            self.assertEqual(res["total_fns"], 3)
            lifter = res["layers"]["anneal_proof_lifters"]
            self.assertEqual(lifter["fully_verifiable_fns"], 1)
            self.assertEqual(lifter["partially_covered_fns"], 2)
            self.assertEqual(lifter["uncovered_fns"], 0)
            self.assertGreater(lifter["within_blocked_fns_stmt_coverage_pct"], 50.0)
            self.assertAlmostEqual(lifter["within_blocked_fns_cfg_prefix_pct"], 37.5)
            self.assertGreater(
                lifter["blended_completeness_score_pct"],
                lifter["fully_verifiable_stmt_pct"],
            )

            # `float_arith_or_cast` is the sole blocker on `partially_blocked_float` (1 fn),
            # whereas `inline_asm` only appears alongside `float_arith_or_cast` (0 sole-blocker fns).
            blockers = {b["construct"]: b for b in res["top_marginal_unlock_blockers"]}
            self.assertEqual(blockers["float_arith_or_cast"]["sole_blocker_fn_count"], 1)
            self.assertEqual(blockers["float_arith_or_cast"]["blocked_fn_count"], 2)
            self.assertEqual(blockers["inline_asm"]["sole_blocker_fn_count"], 0)
            self.assertEqual(blockers["inline_asm"]["blocked_fn_count"], 1)

    def test_stage_b_separates_lifted_slice_wide_ptrs_from_unsized_dsts(self) -> None:
        lifted = suite.LIFTED_SLICE_WIDE_PTR_BLOCKER
        unsized = suite.UNSIZED_DST_BLOCKER
        layers = {name: aff for name, _pat, aff in suite.RUST_CONSTRUCT_BLOCKERS}
        self.assertNotIn("wide_ptr_or_unsized_dst", layers)
        self.assertNotIn("anneal_proof_lifters", layers[lifted])
        self.assertEqual(layers[lifted], {"minirust_correspondence", "lean_miri_correspondence"})
        self.assertEqual(
            layers[unsized],
            {"anneal_proof_lifters", "minirust_correspondence", "lean_miri_correspondence"},
        )
        with tempfile.TemporaryDirectory() as tmp:
            sample_rs = Path(tmp) / "slice_vs_dst.rs"
            sample_rs.write_text(SLICE_VS_DST_CORPUS, encoding="utf-8")
            res = suite.analyze_corpus_completeness("slice_vs_dst", [sample_rs], alpha=0.5)
        self.assertEqual(res["total_fns"], 8)
        self.assertEqual(res["total_stmt_units"], 4 + 2 + 3 + 3 + 3 + 2 + 3 + 3)
        counts = {
            layer: (d["fully_verifiable_fns"], d["partially_covered_fns"], d["uncovered_fns"])
            for layer, d in res["layers"].items()
        }
        # Lifters: `slice_only` (raw slice construction + split_at_mut + len), `pure_add` and
        # `qsized_without_slice_op` (no slice exemption claimed, so body-only scanning as
        # before) verify; size_of_val, generic `ptr::from_raw_parts`, a lifted slice op inside a
        # `T: ?Sized` fn or `impl<T: ?Sized>`, and `dyn` are partial (entry statement blocked
        # for the signature-guarded two).
        self.assertEqual(counts["anneal_proof_lifters"], (3, 5, 0))
        # Raw slice construction still blocks both correspondence layers.
        self.assertEqual(counts["minirust_correspondence"], (2, 6, 0))
        self.assertEqual(counts["lean_miri_correspondence"], (2, 6, 0))
        self.assertEqual(counts["trusted_mir"], (7, 1, 0))
        lifters = res["layers"]["anneal_proof_lifters"]
        # Entry prefixes of the 5 blocked fns (3 stmts each): `unsized_body` 1,
        # `generic_from_raw_parts` 1, and 0 for the signature-guarded `qsized_generic` /
        # `impl_qsized` (blocked at entry) and `dyn_dispatch`.
        self.assertAlmostEqual(lifters["within_blocked_fns_cfg_prefix_pct"], round(100.0 * 2 / 15, 2))
        self.assertAlmostEqual(lifters["within_blocked_fns_stmt_coverage_pct"], round(100.0 * 10 / 15, 2))
        top = {b["construct"]: b for b in res["top_marginal_unlock_blockers"]}
        self.assertEqual(set(top), {unsized, "dyn_trait_dispatch"})
        self.assertNotIn(lifted, top)
        self.assertEqual(top[unsized]["blocked_fn_count"], 4)
        self.assertEqual(top[unsized]["sole_blocker_fn_count"], 4)
        self.assertEqual(top[unsized]["uncovered_stmt_count"], 4)
        self.assertEqual(top["dyn_trait_dispatch"]["sole_blocker_fn_count"], 1)
        self.assertEqual(res["top_marginal_unlock_blockers"][0]["construct"], unsized)

    def test_lifted_slice_and_unsized_dst_patterns_do_not_overlap(self) -> None:
        patterns = {name: pat for name, pat, _aff in suite.RUST_CONSTRUCT_BLOCKERS}
        lifted = patterns[suite.LIFTED_SLICE_WIDE_PTR_BLOCKER]
        unsized = patterns[suite.UNSIZED_DST_BLOCKER]
        lifted_only = (
            "let s = unsafe { core::slice::from_raw_parts(p, n) }",
            "slice::from_raw_parts_mut(p, n)",
            "ptr::slice_from_raw_parts(p, n)",
            "core::ptr::slice_from_raw_parts_mut(p, n)",
            "NonNull::slice_from_raw_parts(nn, n)",
        )
        unsized_only = (
            "fn f<T: ?Sized>(t: &T)",
            "T: ? Sized",
            "core::mem::size_of_val(x)",
            "mem::size_of_val_raw(p)",
            "align_of_val(x)",
            "core::mem::align_of_val_raw(p)",
            "Layout::for_value(x)",
            "Layout::for_value_raw(p)",
            "<T as Pointee>::Metadata",
            "DynMetadata<dyn Foo>",
            "Dst::PointerMetadata::from_elem_count(n)",
            "core::ptr::metadata(p)",
            "core::ptr::from_raw_parts(p, n)",
            "ptr::from_raw_parts_mut(p, n)",
            "NonNull::from_raw_parts(nn, n)",
            "<*const [u8]>::from_raw_parts(p, n)",
            "p.to_raw_parts()",
            "<*const [u8]>::to_raw_parts(p)",
        )
        neither = (
            "v.len()",
            "s.split_at_mut(2)",
            "let (a, b) = s.split_at(k)",
            "Vec::from_raw_parts(p, n, c)",
            "String::from_raw_parts(p, n, c)",
            "std::fs::metadata(path)",
            "myslice::from_raw_parts(p)",
            "from_raw_parts(p, n)",
            "x.as_ptr()",
            "fn g<T: Sized>(t: T)",
        )
        for text in lifted_only:
            self.assertRegex(text, lifted)
            self.assertNotRegex(text, unsized)
        for text in unsized_only:
            self.assertRegex(text, unsized)
            self.assertNotRegex(text, lifted)
        for text in neither:
            self.assertNotRegex(text, lifted)
            self.assertNotRegex(text, unsized)

    def test_rust_fn_units_carry_signature_and_enclosing_headers(self) -> None:
        units = suite._extract_rust_fn_units(SLICE_VS_DST_CORPUS)
        by_name = {name: (stmts, sig) for name, stmts, sig in units}
        self.assertEqual(
            [name for name, _s, _g in units],
            [
                "slice_only",
                "pure_add",
                "unsized_body",
                "qsized_generic",
                "generic_from_raw_parts",
                "qsized_without_slice_op",
                "impl_qsized",
                "dyn_dispatch",
            ],
        )
        self.assertIn("?Sized", by_name["qsized_generic"][1])
        self.assertIn("impl<T: ?Sized> W<T>", by_name["impl_qsized"][1])
        self.assertNotIn("?Sized", by_name["slice_only"][1])
        self.assertEqual(
            suite._extract_rust_functions(SLICE_VS_DST_CORPUS),
            [(name, stmts) for name, stmts, _sig in units],
        )
        commented = """
        /* Nested /* block comment with { and impl<T: ?Sized> W<T> { fn ghost() {} } */ end */
        pub fn real_fn(p: *const u8, n: usize) -> usize {
            let _url = "http://example.com // not a comment { size_of_val ?Sized";
            let s = unsafe { core::slice::from_raw_parts(p, n) };
            s.len()
        }
        """
        c_units = suite._extract_rust_fn_units(commented)
        self.assertEqual([u[0] for u in c_units], ["real_fn"])
        self.assertNotIn("?Sized", c_units[0][2])
        self.assertFalse(any("size_of_val" in stmt for stmt in c_units[0][1]))
        # A byte char literal `b'"'` (and `b'{'`) must not open a string literal or a block,
        # while lifetimes (`'a`) and identifiers ending in `b` stay untouched.
        byte_chars = """
        pub fn scan<'a>(s: &'a [u8], ab: u8) -> usize {
            let q = s.iter().filter(|&&c| c == b'"' || c == b'{' || c == ab).count();
            let n = unsafe { core::slice::from_raw_parts(s.as_ptr(), q) };
            n.len()
        }
        pub fn after<T: ?Sized>(t: &T) -> usize { core::mem::size_of_val(t) }
        """
        stripped = suite._strip_rust_comments_and_strings(byte_chars)
        self.assertIn("size_of_val", stripped)
        self.assertIn("&'a [u8]", stripped)
        b_units = suite._extract_rust_fn_units(byte_chars)
        self.assertEqual([u[0] for u in b_units], ["scan", "after"])
        self.assertTrue(any("size_of_val" in stmt for stmt in b_units[1][1]))
        self.assertIn("?Sized", b_units[1][2])
        # Array `[T; N]` return/where types must not be mistaken for `;`-terminated trait method
        # declarations, and raw C-string literals `cr#"..."#` must not open unbalanced strings.
        arr_and_cr = """
        pub fn ret_array<T: ?Sized>(_t: &T, p: *const u8, n: usize) -> [usize; 2] {
            let _cs = cr#"raw C string with " quote and size_of_val"#;
            let _w = core::ptr::slice_from_raw_parts(p, n);
            [n, 0]
        }
        pub fn after_arr(p: *const u8, n: usize) -> [u8; 4] {
            let _s = unsafe { core::slice::from_raw_parts(p, n) };
            [0; 4]
        }
        """
        a_units = suite._extract_rust_fn_units(arr_and_cr)
        self.assertEqual([u[0] for u in a_units], ["ret_array", "after_arr"])
        self.assertIn("?Sized", a_units[0][2])
        self.assertFalse(any("size_of_val" in stmt for stmt in a_units[0][1]))

    def test_correspondence_divergence_switch_to_pass_detection(self) -> None:
        divs = suite.discover_correspondence_divergences(REPO_ROOT)
        self.assertEqual(divs["actionable_anneal_bugs_count"], len(OPEN_DIVERGENCE_IDS))
        self.assertEqual(
            sorted((d["id"], d["status"]) for d in divs["actionable_anneal_bugs"]),
            sorted((div_id, "open") for div_id in OPEN_DIVERGENCE_IDS),
        )
        for d in divs["actionable_anneal_bugs"]:
            self.assertTrue(d["live_in_source"], d["id"])
            self.assertEqual(d["file"], suite.UNTESTED_VARIANT_TEST_FILE)
        self.assertEqual(len(divs["resolved_correspondence_divergences"]), len(RESOLVED_DIVERGENCE_IDS))
        resolved_ids = {d["id"] for d in divs["resolved_correspondence_divergences"]}
        self.assertEqual(resolved_ids, RESOLVED_DIVERGENCE_IDS)
        self.assertEqual(divs["known_miri_diff_manifest_bugs"], [])
        for d in divs["resolved_correspondence_divergences"]:
            self.assertEqual(d["status"], "resolved")
            self.assertFalse(d["live_in_source"])
            self.assertTrue(d["resolution_live_in_source"], d["id"])
            self.assertTrue(d["resolution_statement_pinned"], d["id"])

        actionable_items = [
            item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["category"] != "intentional_modeling_choice"
        ]
        self.assertEqual(len(actionable_items), ACTIONABLE_DIVERGENCE_COUNT)
        for item in actionable_items:
            self.assertTrue(item.get("resolution_symbol"), item["id"])
            self.assertTrue(item["resolution_symbol"].endswith("_simulation"), item["id"])
        n_actionable = len(actionable_items)

        def write_synthetic_checkout(
            root: Path,
            *,
            live_ids: set[str] = frozenset(),
            missing_ids: set[str] = frozenset(),
            unpinned_ids: set[str] = frozenset(),
        ) -> None:
            for item in actionable_items:
                # Statement pins live in the entry's pin module (its `resolution_pin_file`,
                # else its authority audit module), written even for `missing_ids`, whose
                # resolution theorem itself is absent.
                if item["id"] not in unpinned_ids:
                    audit = root / item.get(
                        "resolution_pin_file", suite.AUTHORITY_AUDIT_FILES[item["authority"]]
                    )
                    audit.parent.mkdir(parents=True, exist_ok=True)
                    with audit.open("a", encoding="utf-8") as fh:
                        fh.write(f"example : {SYNTH_STMT} :=\n  {item['resolution_symbol']}\n")
                if item["id"] in missing_ids:
                    continue
                path = root / item.get("resolution_file", item["file"])
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("a", encoding="utf-8") as fh:
                    fh.write(f"theorem {item['resolution_symbol']} : {SYNTH_STMT} := rfl\n")
                    if item["id"] in live_ids:
                        fh.write(f"theorem {item['witness_symbol']} : {SYNTH_DIVERGENCE_STMT} := rfl\n")

        # Fail-closed statement-pin linkage: a resolution theorem whose statement is not
        # locked by a non-trivial typed audit `example : <Prop> := <theorem>` pin (e.g.
        # only listed, commented out, applied mid-term, untyped `let _ :=` / `example :=`,
        # vacuous `: True` / wildcard `: _`, field-projected `.1`, or decoy-qualified
        # `Scratch.<thm>`) stays actionable as `resolution_unpinned`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, unpinned_ids={"DIV-MR-CALL-TARGET-LOCAL"})
            mr_audit = tmp_root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
            with mr_audit.open("a", encoding="utf-8") as fh:
                fh.write(
                    "#assert_standard_axioms\n  callerRefMutSilentWrongLocal_simulation\n"
                    f"-- example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : {SYNTH_STMT} := id callerRefMutSilentWrongLocal_simulation\n"
                    "let _ := @callerRefMutSilentWrongLocal_simulation\n"
                    "example := callerRefMutSilentWrongLocal_simulation\n"
                    "example : _ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : True := callerRefMutSilentWrongLocal_simulation\n"
                    "example : (True) := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation.1\n"
                    f"example : {SYNTH_STMT} := Scratch.callerRefMutSilentWrongLocal_simulation\n"
                    f"unsafe example : {SYNTH_STMT} := callerRefMutSilentWrongLocal_simulation\n"
                    # Self-typed pins lock nothing: the type is computed from the RHS.
                    "example : type_of% callerRefMutSilentWrongLocal_simulation :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                    "example : (by exact type_of% @callerRefMutSilentWrongLocal_simulation) :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                    "example : _ ∧ _ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?_ := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?m := callerRefMutSilentWrongLocal_simulation\n"
                    "example : ?m ∧ ?n := callerRefMutSilentWrongLocal_simulation\n"
                    f"example : id ({SYNTH_STMT}) ∧ callerRefMutSilentWrongLocal_simulation = "
                    "callerRefMutSilentWrongLocal_simulation :=\n"
                    "  callerRefMutSilentWrongLocal_simulation\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-MR-CALL-TARGET-LOCAL", "resolution_unpinned")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)
            with mr_audit.open("a", encoding="utf-8") as fh:
                fh.write(f"example : {SYNTH_STMT} :=\n  @callerRefMutSilentWrongLocal_simulation\n")
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 0)
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable)

        # A `private` (or `unsafe` / `partial`) modifier on its own line(s) before the
        # resolution theorem still makes it module-private, so it must not count.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, missing_ids={"DIV-LM-ENUM-SET-DISCR-UNINIT"})
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "@[simp]\nprivate\n\ntheorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing")],
            )

        # Regression check: reintroducing a live `*_divergence` witness symbol in a
        # synthetic checkout must immediately flip `actionable_anneal_bugs_count` back > 0.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, live_ids={"DIV-LM-RAW-OVERWRITE-CHAR-COPY"})
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 1)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

        # Fail-closed check: a witness that vanished WITHOUT its positive replacement
        # theorem (bare rename / deletion) is not counted as resolved.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(tmp_root, missing_ids={"DIV-LM-D6-OFFSET-DISABLED-TAG"})
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], 1)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

        # An empty checkout (all witness files missing) must not report any resolution.
        with tempfile.TemporaryDirectory() as tmp:
            synth_divs = suite.discover_correspondence_divergences(Path(tmp))
            self.assertEqual(synth_divs["actionable_anneal_bugs_count"], n_actionable)
            self.assertEqual(synth_divs["resolved_correspondence_divergences"], [])
            self.assertEqual(
                {d["status"] for d in synth_divs["actionable_anneal_bugs"]},
                {"resolution_missing"},
            )

        # Comment, nested block-comment, string-literal, and non-theorem (`def`) spoofing
        # must fail closed (`resolution_missing`), while `abbrev` witness aliases and
        # character literals (`'"'`) must be handled accurately.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={"DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-LM-ENUM-SET-DISCR-UNINIT"},
            )
            d6_file = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with d6_file.open("a", encoding="utf-8") as fh:
                fh.write(
                    "-- theorem step_binOp_offset_disabled_simulation : True := trivial\n"
                    "/- outer /- theorem step_binOp_offset_disabled_simulation : True := trivial -/ -/\n"
                    'def docStr : String := "theorem step_binOp_offset_disabled_simulation"\n'
                    "def step_binOp_offset_disabled_simulation : Unit := ()\n"
                )
            lm23_file = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23_file.parent.mkdir(parents=True, exist_ok=True)
            lm23_file.write_text(
                "def quoteChar : Char := '\"'\n"
                "-- Replaces theorem step_setDiscriminant_uninit_divergence\n"
                f"@[simp] theorem step_setDiscriminant_uninit_simulation : {SYNTH_STMT} := rfl\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                [(d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]],
                [("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing")],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 1)

            # Reintroducing a witness via `abbrev` must also be caught as `open`.
            with lm23_file.open("a", encoding="utf-8") as fh:
                fh.write("abbrev step_setDiscriminant_uninit_divergence := True\n")
            synth_divs2 = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs2["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "open"),
                ],
            )
            state_dir = tmp_root / "state_render"
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=tmp_root, profile="census-only", state_dir=state_dir
            )
            self.assertIn(
                "**missing resolution** `step_binOp_offset_disabled_simulation`", md
            )

        # Scanner robustness: namespace-qualified, same-line `... in`-prefixed, and
        # `nonrec` / attributed witnesses are live (`open`), while a resolution that
        # only appears after `#exit` or only under a primed name does not count.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={"DIV-LM-ENUM-SET-DISCR-UNINIT", "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC"},
            )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    "theorem ProvenanceWitness.callerRefMutSilentWrongLocal_divergence : "
                    "True := trivial\n"
                    "set_option maxHeartbeats 400000 in theorem "
                    "callerBorrowAcrossScalarCall_divergence : True := trivial\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "open Foo in\n@[reducible] nonrec def twoPhaseDirectWriteTreeBorrowsGap : "
                    "Nat := 0\n"
                    "theorem retagFnEntryLocalDealloc_simulation' : True := trivial\n"
                )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "#exit\ntheorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-MR-CALL-TARGET-LOCAL", "open"),
                    ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 5)

        # Asymmetric resolution vs. witness enforcement: `private`/`unsafe`/wrong-namespace
        # `resolution_symbol` declarations must be rejected (`resolution_missing`), whereas
        # `local attribute [...] in`, `axiom`/`opaque`, guillemet-quoted `«...»`, and
        # multi-line `private\ntheorem` witnesses must still be detected as `open`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={
                    "DIV-LM-ENUM-SET-DISCR-UNINIT",
                    "DIV-LM-D6-OFFSET-DISABLED-TAG",
                    "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
                },
            )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "private theorem step_setDiscriminant_uninit_simulation : True := trivial\n"
                "unsafe theorem step_setDiscriminant_uninit_simulation : True := trivial\n",
                encoding="utf-8",
            )
            lm31 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with lm31.open("a", encoding="utf-8") as fh:
                fh.write(
                    "theorem BogusNs.step_binOp_offset_disabled_simulation : True := trivial\n"
                    "private\ntheorem step_raw_overwritten_direct_copy_invalid_char_divergence : "
                    "True := trivial\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "namespace Scratch\n"
                    "theorem retagFnEntryLocalDealloc_simulation : True := trivial\n"
                    "end Scratch\n"
                    "axiom «twoPhaseDirectWriteTreeBorrowsGap» : True\n"
                )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    "local attribute [simp] id in theorem "
                    "callerBorrowAcrossScalarCall_divergence : True := trivial\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open"),
                    ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 6)

        # Token-level Lean 4 grammar edge cases: `open Foo in private\ntheorem`,
        # `private @[simp,\n  reducible]\ntheorem`, `section private theorem ... end`,
        # and `section #exit\ntheorem` must NOT satisfy `resolution_symbol`, whereas
        # same-line `namespace Foo theorem <witness> ... end Foo`, `mutual def <witness> ... end`,
        # `#exit'` non-truncation, and `r#"\"#` raw strings must still detect witnesses as `open`.
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = Path(tmp)
            write_synthetic_checkout(
                tmp_root,
                missing_ids={
                    "DIV-LM-ENUM-SET-DISCR-UNINIT",
                    "DIV-LM-D6-OFFSET-DISABLED-TAG",
                    "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC",
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM",
                },
            )
            lm23 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            lm23.parent.mkdir(parents=True, exist_ok=True)
            lm23.write_text(
                "open Foo in private\n"
                "theorem step_setDiscriminant_uninit_simulation : 0 = 0 := rfl\n"
                "private @[simp,\n  reducible]\n"
                "theorem step_setDiscriminant_uninit_simulation : 0 = 0 := rfl\n",
                encoding="utf-8",
            )
            lm31 = tmp_root / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            with lm31.open("a", encoding="utf-8") as fh:
                fh.write(
                    "section private theorem step_binOp_offset_disabled_simulation : "
                    "0 = 0 := rfl end\n"
                    "#exit'\n"
                    "theorem step_raw_overwritten_direct_copy_invalid_char_divergence : "
                    "0 = 0 := rfl\n"
                )
            ref = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/RefWitness.lean"
            with ref.open("a", encoding="utf-8") as fh:
                fh.write(
                    "section #exit\n"
                    "theorem retagFnEntryLocalDealloc_simulation : 0 = 0 := rfl\n"
                )
            tb = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/TbWitness.lean"
            tb.parent.mkdir(parents=True, exist_ok=True)
            tb.write_text(
                "mutual def unsafeCellProtectedInteriorMut : Nat := 0 end\n",
                encoding="utf-8",
            )
            prov = tmp_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with prov.open("a", encoding="utf-8") as fh:
                fh.write(
                    'def rawBackslash := r#"\\"#\n'
                    "namespace Foo theorem callerRefMutSilentWrongLocal_divergence : "
                    "0 = 0 := rfl end Foo\n"
                )
            synth_divs = suite.discover_correspondence_divergences(tmp_root)
            self.assertEqual(
                sorted((d["id"], d["status"]) for d in synth_divs["actionable_anneal_bugs"]),
                [
                    ("DIV-LM-D6-OFFSET-DISABLED-TAG", "resolution_missing"),
                    ("DIV-LM-ENUM-SET-DISCR-UNINIT", "resolution_missing"),
                    ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open"),
                    ("DIV-MR-CALL-TARGET-LOCAL", "open"),
                    ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolution_missing"),
                    ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "open"),
                ],
            )
            self.assertEqual(len(synth_divs["resolved_correspondence_divergences"]), n_actionable - 6)

    def test_episode2_divergences_tracked_with_live_witnesses(self) -> None:
        divs = suite.discover_correspondence_divergences(REPO_ROOT)
        actionable = {d["id"]: d for d in divs["actionable_anneal_bugs"]}
        resolved = {d["id"]: d for d in divs["resolved_correspondence_divergences"]}
        modeling = {d["id"]: d for d in divs["intentional_modeling_choices"]}
        episode2 = {
            item["id"]: item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["file"] == suite.UNTESTED_VARIANT_TEST_FILE
        }
        self.assertEqual(
            {i for i, item in episode2.items() if item["category"] == "actionable_anneal_bug"},
            {
                "DIV-LM-TAILCALL-NOUNWIND-UNWIND",
                "DIV-TR-OPAQUECAST-ROOT-DISPATCH",
                "DIV-TR-TAILCALL-DANGLING-CALLER-LOCAL",
                "DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW",
            },
        )
        for div_id, item in episode2.items():
            if item["category"] != "actionable_anneal_bug":
                continue
            # Resolved in the file itself, in its namespace, and statement-pinned there.
            self.assertEqual(item["resolution_namespace"], suite.UNTESTED_VARIANT_NAMESPACE)
            self.assertEqual(item["resolution_pin_file"], suite.UNTESTED_VARIANT_TEST_FILE)
            if div_id in OPEN_DIVERGENCE_IDS:
                self.assertEqual(actionable[div_id]["status"], "open")
                self.assertTrue(actionable[div_id]["live_in_source"])
            else:
                self.assertIn(div_id, RESOLVED_DIVERGENCE_IDS)
                self.assertEqual(resolved[div_id]["status"], "resolved")
                self.assertTrue(resolved[div_id]["resolution_statement_pinned"])
        for div_id in ("MODEL-LM-TAILCALL-MODULAR-ROOT", "MODEL-LM-TAILCALL-DIRECT-ARITY-STEP"):
            self.assertIn(div_id, modeling)
            self.assertTrue(modeling[div_id]["live_in_source"])

        # Switch-to-pass is fail-closed: once Trusted is fixed, the witness theorem must be
        # replaced by the registered `resolution_symbol`, declared in the file's namespace and
        # statement-pinned there; a bare rename, a decoy namespace, or a missing pin does not
        # resolve the entry.
        text = (REPO_ROOT / suite.UNTESTED_VARIANT_TEST_FILE).read_text(encoding="utf-8")
        ns_end = f"end {suite.UNTESTED_VARIANT_NAMESPACE}"
        self.assertEqual(text.count(ns_end), 1)
        witness = "theorem opaqueCast_trusted_root_dispatch_divergence"
        self.assertEqual(text.count(witness), 1)

        def status_after(new_text: str) -> str:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                target = root / suite.UNTESTED_VARIANT_TEST_FILE
                target.parent.mkdir(parents=True)
                target.write_text(new_text, encoding="utf-8")
                fixed = suite.discover_correspondence_divergences(root)
                by_id = {
                    d["id"]: d
                    for d in fixed["actionable_anneal_bugs"] + fixed["resolved_correspondence_divergences"]
                }
                for div_id in OPEN_DIVERGENCE_IDS - {"DIV-TR-OPAQUECAST-ROOT-DISPATCH"}:
                    self.assertEqual(by_id[div_id]["status"], "open")
                return by_id["DIV-TR-OPAQUECAST-ROOT-DISPATCH"]["status"]

        renamed = text.replace(witness, "theorem opaqueCast_trusted_root_dispatch_simulation")
        pin = f"example : {SYNTH_STMT} := opaqueCast_trusted_root_dispatch_simulation\n"
        self.assertEqual(
            status_after(text.replace(witness, "theorem opaqueCast_trusted_root_dispatch_erasure_commutes")),
            "resolution_missing",
        )
        self.assertEqual(status_after(renamed), "resolution_unpinned")
        self.assertEqual(
            status_after(renamed.replace(ns_end, f"namespace Scratch\n{pin}end Scratch\n{ns_end}")),
            "resolution_unpinned",
        )
        self.assertEqual(status_after(renamed.replace(ns_end, f"{pin}{ns_end}")), "resolved")
        # The single-tree scan cannot tell that bare rename from a fix, but the
        # flip-direction audit against the unrenamed baseline can: the "simulation"
        # theorem restates the divergence witness (`polarity_not_flipped`).
        with tempfile.TemporaryDirectory() as base_tmp, tempfile.TemporaryDirectory() as cur_tmp:
            base_root, cur_root = Path(base_tmp), Path(cur_tmp)
            for root, body in (
                (base_root, text),
                (cur_root, renamed.replace(ns_end, f"{pin}{ns_end}")),
            ):
                target = root / suite.UNTESTED_VARIANT_TEST_FILE
                target.parent.mkdir(parents=True)
                target.write_text(body, encoding="utf-8")
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                audit["transitions"],
                [{"id": "DIV-TR-OPAQUECAST-ROOT-DISPATCH", "from": "open", "to": "resolved"}],
            )
            self.assertEqual(
                [(v["id"], v["reason"]) for v in audit["violations"]],
                [("DIV-TR-OPAQUECAST-ROOT-DISPATCH", "polarity_not_flipped")],
            )
        decoy = (
            "namespace Scratch\n"
            "theorem opaqueCast_trusted_root_dispatch_simulation : 0 = 0 := rfl\n"
            "end Scratch\n"
            "theorem opaqueCast_trusted_root_dispatch_erasure_commutes"
        )
        self.assertEqual(
            status_after(text.replace(witness, decoy).replace(ns_end, f"{pin}{ns_end}")),
            "resolution_missing",
        )

    def _actionable_items(self) -> list[dict[str, str]]:
        return [
            item
            for item in suite.TRACKED_CORRESPONDENCE_DIVERGENCES
            if item["category"] != "intentional_modeling_choice"
        ]

    def _write_flip_tree(
        self,
        root: Path,
        overrides: dict[str, tuple[str | None, str | None, str | None]] | None = None,
    ) -> None:
        """Write a synthetic checkout in which every actionable divergence is resolved
        (`theorem <resolution> : SYNTH_STMT := rfl` plus a `SYNTH_STMT` statement pin),
        except for each `overrides[id] = (witness_decl_tail, resolution_decl_tail,
        pin_type)`, whose non-`None` parts are written instead (`<symbol> <tail>`)."""
        for item in self._actionable_items():
            witness, resolution, pin = (overrides or {}).get(
                item["id"], (None, f": {SYNTH_STMT} := rfl", SYNTH_STMT)
            )
            src = root / item["file"]
            res = root / item.get("resolution_file", item["file"])
            audit = root / item.get(
                "resolution_pin_file", suite.AUTHORITY_AUDIT_FILES[item["authority"]]
            )
            for path, text in (
                (src, witness and f"theorem {item['witness_symbol']} {witness}\n"),
                (res, resolution and f"theorem {item['resolution_symbol']} {resolution}\n"),
                (audit, pin and f"example : {pin} :=\n  {item['resolution_symbol']}\n"),
            ):
                if text:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    with path.open("a", encoding="utf-8") as fh:
                        fh.write(text)

    def _flip_status(self, root: Path, div_id: str) -> dict[str, object]:
        divs = suite.discover_correspondence_divergences(root)
        by_id = {
            d["id"]: d
            for d in divs["actionable_anneal_bugs"] + divs["resolved_correspondence_divergences"]
        }
        return by_id[div_id]

    def test_flip_direction_guard_rejects_vacuous_and_hole_riddled_resolution_theorems(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        stmt = SYNTH_STMT
        # A resolution theorem that states or proves nothing is `resolution_invalid`
        # (fail closed), even with a meaningful statement pin.
        invalid_cases: list[tuple[str, set[str]]] = [
            (": True := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": (True) := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": ¬False := id", {"vacuous_statement", "closed_trivial_statement"}),
            (": True ∧ ¬False := ⟨trivial, id⟩", {"vacuous_statement", "closed_trivial_statement"}),
            (": 0 = 0 := rfl", {"vacuous_statement", "closed_trivial_statement"}),
            (": annealOutcome fooProg = annealOutcome fooProg := rfl", {"vacuous_statement"}),
            (": annealOutcome fooProg ↔ annealOutcome fooProg := Iff.rfl", {"vacuous_statement"}),
            (f": True ∨ {stmt} := Or.inl trivial", {"vacuous_statement"}),
            (": _ := foo", {"wildcard_statement"}),
            (": ?m := foo", {"metavariable_hole", "closed_trivial_statement"}),
            (f": {stmt} ∧ ?_ := foo", {"metavariable_hole"}),
            (f"(h : ?m) : {stmt} := foo", {"metavariable_hole"}),
            (f"{{x : ?t}} : {stmt} := foo", {"metavariable_hole"}),
            # Vacuous antecedents, also nested under binders and in Pi binders.
            (f": False → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": False -> {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": (False) → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": ¬True → {stmt} := fun h => absurd trivial h", {"vacuous_statement"}),
            (f": (h : False) → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": ∀ x : Nat, False → {stmt} := fun _ h => h.elim", {"vacuous_statement"}),
            (f": ∀ (x : Nat) (h : False), {stmt} := nofun", {"vacuous_statement"}),
            (f": ∀ x, ∀ h : False, {stmt} := nofun", {"vacuous_statement"}),
            (f": (∀ x, annealOutcome x = 1 → False → {stmt}) := nofun", {"vacuous_statement"}),
            (f": annealOutcome fooProg = 1 → ∀ y, False → {stmt} := nofun", {"vacuous_statement"}),
            (f"(h : False) : {stmt} := h.elim", {"vacuous_statement"}),
            (f"⦃h : False⦄ : {stmt} := h.elim", {"vacuous_statement"}),
            (f"[inst : False] : {stmt} := inst.elim", {"vacuous_statement"}),
            (
                f"\n    {{body : CapturedMir}}\n    (hstate : stateRel body)\n    (hfalse : False) :\n"
                f"    {stmt} := by\n  exact hfalse.elim\n",
                {"vacuous_statement"},
            ),
            # Self-typed statements.
            (": type_of% fooLemma := fooLemma", {"self_typed_statement"}),
            (f": (by exact {stmt}) := rfl", {"self_typed_statement"}),
            # `sorry` / `admit` anywhere in the signature or the proof.
            (f": {stmt} := sorry", {"sorry_or_admit"}),
            (f": {stmt} := by sorry", {"sorry_or_admit"}),
            (f": {stmt} := by admit", {"sorry_or_admit"}),
            (f": {stmt} := sorryAx _ false", {"sorry_or_admit"}),
            (f": {stmt} := by\n  simp only [annealOutcome]\n  sorry\n", {"sorry_or_admit"}),
            (
                f": {stmt} := by\n  set_option maxHeartbeats 400000 in\n  sorry\n",
                {"sorry_or_admit"},
            ),
            (f": {stmt} := aux\nwhere\n  aux : {stmt} := sorry\n", {"sorry_or_admit"}),
            (
                ": ∀ n : Nat, annealOutcome n = miriOutcome n\n  | 0 => rfl\n  | _ + 1 => sorry\n",
                {"sorry_or_admit"},
            ),
            (": annealOutcome sorry = miriOutcome fooProg := rfl", {"sorry_or_admit"}),
            (f": {stmt} := by\n  decreasing_by admit\n", {"sorry_or_admit"}),
        ]
        for tail, expected in invalid_cases:
            with self.subTest(tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_invalid")
                self.assertTrue(rec["resolution_live_in_source"])
                self.assertFalse(rec["resolution_valid"])
                self.assertEqual(set(rec["resolution_problems"]), expected)
        # Meaningful, hole-free resolution theorems (multi-line headers, binders,
        # `let`, equation compilers, `where` helpers, `match` / `set_option ... in` in
        # tactic proofs, and a vacuous conjunct beside a meaningful one) resolve.
        valid_cases = [
            f": {stmt} := rfl",
            "(h : annealOutcome fooProg = 3) : miriOutcome fooProg = 3 := by simp [h]",
            (
                f"\n    {{body : CapturedMir}} {{s : MachineState}}\n    (hstate : stateRel body s) :\n"
                f"    stepMirFn body s = .step s ∧\n      {stmt} := by\n  constructor <;> simp [hstate]\n"
            ),
            ": let s := annealOutcome fooProg; s = miriOutcome fooProg := rfl",
            ": ∀ n : Nat, annealOutcome n = miriOutcome n\n  | 0 => rfl\n  | _ + 1 => rfl\n",
            f": {stmt} := aux\nwhere\n  aux : {stmt} := rfl\n",
            f": {stmt} := by\n  match fooProg with\n  | _ => rfl\n",
            f": {stmt} := by\n  set_option maxHeartbeats 400000 in\n  simp\n",
            f": {stmt} ∧ (False → annealOutcome barProg = 0) := ⟨rfl, nofun⟩",
            f": ∀ x, annealOutcome x = miriOutcome x <| fooProg := fun _ => rfl",
        ]
        for tail in valid_cases:
            with self.subTest(tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_problems"]), ("resolved", []))
                self.assertTrue(rec["resolution_valid"])
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        # Fail closed across namespaces: a vacuous candidate in the expected namespace
        # invalidates a meaningful one (a decoy namespace's vacuous theorem does not).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(root, {div_id: (None, None, stmt)})
            target = root / lm23
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n"
                f"namespace LeanMiriSpec\ntheorem {sym} : True := trivial\nend LeanMiriSpec\n",
                encoding="utf-8",
            )
            rec = self._flip_status(root, div_id)
            self.assertEqual(rec["status"], "resolution_invalid")
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n"
                f"namespace Scratch\ntheorem {sym} : True := trivial\nend Scratch\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")
            # A `sorry` in an unrelated later declaration does not leak into the
            # resolution theorem, while a `sorry` before the next declaration does.
            target.write_text(
                f"theorem {sym} : {stmt} := rfl\n\ntheorem unrelated : {stmt} := sorry\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")
            target.write_text(
                f"theorem {sym} : {stmt} := by\n  first\n  | rfl\n  | sorry\n\n#print axioms {sym}\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolution_invalid")
            # The dashboard reports the invalid resolution with its reasons.
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=root, profile="census-only", state_dir=root / "state_render"
            )
            self.assertIn(f"**invalid resolution** `{sym}` (`{lm23}`: sorry_or_admit)", md)

    def test_flip_direction_guard_rejects_vacuous_self_typed_and_hole_statement_pins(self) -> None:
        div_id = "DIV-MR-CALL-TARGET-LOCAL"
        sym = "callerRefMutSilentWrongLocal_simulation"
        stmt = SYNTH_STMT
        rejected_pins: list[tuple[str, list[str]]] = [
            # Filtered by the declaration scanner itself (no candidate pin remains).
            ("example : True := {sym}", []),
            ("example : _ := {sym}", []),
            ("example : ?m := {sym}", []),
            # Self-typed, tactic-synthesized, wildcard, or metavariable types.
            ("example : type_of% {sym} := {sym}", ["self_typed_or_hole_pin"]),
            (f"example : (by exact {stmt}) := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ _ := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ ?m := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example : {stmt} ∧ ?_ := {{sym}}", ["self_typed_or_hole_pin"]),
            # Vacuous statements and antecedents, also under binders.
            ("example : True ∧ True := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            ("example : 0 = 0 := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            (
                "example : annealOutcome fooProg = annealOutcome fooProg := {sym}",
                ["pin_vacuous_statement"],
            ),
            (f"example : False → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ¬True -> {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : (h : False) → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ∀ x : Nat, False → {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example : ∀ {{x : Nat}} (h : False), {stmt} := {{sym}}", ["pin_vacuous_statement"]),
            (f"example (h : False) : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
            (f"example :\n    ∀ (h : False),\n      {stmt} :=\n  @{{sym}}", ["pin_vacuous_statement"]),
            # Holes that the coarse token scan cannot see.
            (f"example : {stmt} ∧ sorry := {{sym}}", ["pin_sorry_or_admit"]),
        ]
        for pin_text, reasons in rejected_pins:
            with self.subTest(pin=pin_text), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, f": {stmt} := rfl", None)})
                audit = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                with audit.open("a", encoding="utf-8") as fh:
                    fh.write(pin_text.replace("{sym}", sym) + "\n")
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_unpinned")
                self.assertEqual(rec["resolution_pin_problems"], reasons)
                # A meaningful pin beside the rejected one resolves the entry.
                with audit.open("a", encoding="utf-8") as fh:
                    fh.write(f"example : {stmt} :=\n  @{sym}\n")
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_pin_problems"]), ("resolved", []))
        # The dashboard reports why a pin was rejected.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(
                root, {div_id: (None, f": {stmt} := rfl", f"∀ (h : False), {stmt}")}
            )
            _, _, md = suite.run_suite_and_generate_dashboard(
                repo_root=root, profile="census-only", state_dir=root / "state_render"
            )
            self.assertIn(f"**unpinned resolution** `{sym}`", md)
            self.assertIn("rejected pins: pin_vacuous_statement", md)

    def test_flip_direction_transition_audit_against_a_baseline_tree(self) -> None:
        stmt = SYNTH_STMT
        changed_stmt = "annealOutcome fooProg = miriOutcome fooProg ∧ annealTrace fooProg = miriTrace fooProg"
        baseline_overrides = {
            # Proper flip: witness only in the baseline.
            "DIV-LM-D6-OFFSET-DISABLED-TAG": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
            # Bare rename: the baseline witness statement becomes the "simulation".
            "DIV-LM-ENUM-SET-DISCR-UNINIT": (": annealStep s ≠ miriStep s := by decide", None, None),
            # The simulation theorem already held, unchanged, next to the live witness.
            "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                f": {stmt} := rfl",
                stmt,
            ),
            # The same, but the flip changes the simulation statement.
            "DIV-MR-TB-TWOPHASE-DIRECT-WRITE": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                f": {stmt} := rfl",
                stmt,
            ),
            # Incomplete flips: vacuous simulation / vacuous pin.
            "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
            "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL": (
                f": {SYNTH_DIVERGENCE_STMT} := rfl",
                None,
                None,
            ),
        }
        current_overrides = {
            "DIV-LM-D6-OFFSET-DISABLED-TAG": (None, f": {stmt} := rfl", stmt),
            "DIV-LM-ENUM-SET-DISCR-UNINIT": (None, ": annealStep s ≠ miriStep s := by decide", "annealStep s ≠ miriStep s"),
            "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (None, f": {stmt} := rfl", stmt),
            "DIV-MR-TB-TWOPHASE-DIRECT-WRITE": (None, f": {changed_stmt} := ⟨rfl, rfl⟩", changed_stmt),
            "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, ": True := trivial", stmt),
            "DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL": (None, f": {stmt} := rfl", "True ∧ True"),
            # Regressions of resolved entries: the witness is back / the simulation
            # became vacuous.
            "DIV-MR-CALL-TARGET-LOCAL": (f": {SYNTH_DIVERGENCE_STMT} := rfl", f": {stmt} := rfl", stmt),
            "DIV-MR-TB-FNENTRY-LOCAL-DEALLOC": (None, ": 0 = 0 := rfl", stmt),
        }
        with tempfile.TemporaryDirectory() as base_tmp, tempfile.TemporaryDirectory() as cur_tmp:
            base_root, cur_root = Path(base_tmp), Path(cur_tmp)
            self._write_flip_tree(base_root, baseline_overrides)
            self._write_flip_tree(cur_root, current_overrides)
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                sorted((t["id"], t["from"], t["to"]) for t in audit["transitions"]),
                sorted(
                    [
                        ("DIV-LM-D6-OFFSET-DISABLED-TAG", "open", "resolved"),
                        ("DIV-LM-ENUM-SET-DISCR-UNINIT", "open", "resolved"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "open", "resolved"),
                        ("DIV-MR-TB-TWOPHASE-DIRECT-WRITE", "open", "resolved"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "open", "resolution_invalid"),
                        ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "open", "resolution_unpinned"),
                        ("DIV-MR-CALL-TARGET-LOCAL", "resolved", "open"),
                        ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "resolved", "resolution_invalid"),
                    ]
                ),
            )
            self.assertEqual(
                sorted((v["id"], v["reason"]) for v in audit["violations"]),
                sorted(
                    [
                        ("DIV-LM-ENUM-SET-DISCR-UNINIT", "polarity_not_flipped"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "resolution_predates_flip"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "incomplete_flip"),
                        ("DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL", "incomplete_flip"),
                        ("DIV-MR-CALL-TARGET-LOCAL", "flip_regressed"),
                        ("DIV-MR-TB-FNENTRY-LOCAL-DEALLOC", "flip_regressed"),
                    ]
                ),
            )
            details = {v["id"]: v["detail"] for v in audit["violations"]}
            self.assertIn("vacuous_statement", details["DIV-LM-RAW-OVERWRITE-CHAR-COPY"])
            self.assertIn("pin_vacuous_statement", details["DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL"])
            self.assertIn("annealStep s ≠ miriStep s", details["DIV-LM-ENUM-SET-DISCR-UNINIT"])
            # An unchanged tree has no transitions.
            same = suite.audit_flip_direction_transitions(cur_root, cur_root)
            self.assertEqual((same["passed"], same["transitions"], same["violations"]), (True, [], []))
            # Only the proper flips remain once the violating entries are fixed.
            fixed_overrides = {
                k: v
                for k, v in current_overrides.items()
                if k in ("DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE")
            }
            fixed_root = Path(cur_tmp) / "fixed"
            self._write_flip_tree(fixed_root, fixed_overrides)
            base_fixed = Path(base_tmp) / "fixed"
            self._write_flip_tree(
                base_fixed,
                {
                    k: v
                    for k, v in baseline_overrides.items()
                    if k in ("DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE")
                },
            )
            ok = suite.audit_flip_direction_transitions(base_fixed, fixed_root)
            self.assertTrue(ok["passed"], ok["violations"])
            self.assertEqual(
                sorted(t["id"] for t in ok["transitions"]),
                ["DIV-LM-D6-OFFSET-DISABLED-TAG", "DIV-MR-TB-TWOPHASE-DIRECT-WRITE"],
            )

    def test_flip_direction_audit_fails_the_dashboard_run_and_cli_on_violations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            base = tmp_dir / "baseline"
            for rel in suite.flip_direction_tracked_files():
                src = REPO_ROOT / rel
                if src.is_file():
                    dst = base / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(src, dst)
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=tmp_dir / "state_same",
                flip_baseline_root=base,
            )
            flip = dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]
            self.assertEqual((code, flip["passed"], flip["transitions"]), (0, True, []))
            self.assertIn("### 3C. Flip-Direction Witness Polarity Audit", md)
            # A baseline in which the resolved `step_setDiscriminant_uninit_simulation`
            # was still its `_divergence` witness, with the same statement: the current
            # "simulation" theorem is a rename, not a flip.
            lm23 = base / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
            renamed_text, renames = re.subn(
                r"\btheorem step_setDiscriminant_uninit_simulation\b",
                "theorem step_setDiscriminant_uninit_divergence",
                lm23.read_text(encoding="utf-8"),
            )
            self.assertEqual(renames, 1)
            lm23.write_text(renamed_text, encoding="utf-8")
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=tmp_dir / "state_renamed",
                flip_baseline_root=base,
            )
            self.assertEqual(code, suite.EXIT_SUITE_REGRESSION)
            flip = dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]
            self.assertEqual(
                [(v["id"], v["reason"]) for v in flip["violations"]],
                [("DIV-LM-ENUM-SET-DISCR-UNINIT", "polarity_not_flipped")],
            )
            self.assertIn(
                "**VIOLATION** `DIV-LM-ENUM-SET-DISCR-UNINIT` (`polarity_not_flipped`)", md
            )
            saved = json.loads(
                (tmp_dir / "state_renamed/reports/LATEST_DASHBOARD_STATE.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertFalse(
                saved["pillar_3_known_issues_and_regressions"]["flip_direction_audit"]["passed"]
            )
            out = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "scripts/run_nightly_verification_suite.py"),
                    "--profile",
                    "census-only",
                    "--state-dir",
                    str(tmp_dir / "state_cli"),
                    "--flip-baseline-root",
                    str(base),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(out.returncode, suite.EXIT_SUITE_REGRESSION, out.stderr)
            self.assertIn("(`polarity_not_flipped`)", out.stdout)
            # Without a baseline, the audit does not run.
            code, dashboard, md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT, profile="census-only", state_dir=tmp_dir / "state_none"
            )
            self.assertEqual(code, 0)
            self.assertIsNone(dashboard["pillar_3_known_issues_and_regressions"]["flip_direction_audit"])
            self.assertNotIn("3C. Flip-Direction", md)
            # An unknown baseline revision or a missing baseline directory is an error.
            for flag, value in (
                ("--flip-baseline-ref", "refs/heads/no-such-flip-baseline-ref"),
                ("--flip-baseline-root", str(tmp_dir / "missing")),
            ):
                with self.subTest(flag=flag):
                    out = subprocess.run(
                        [
                            sys.executable,
                            str(REPO_ROOT / "scripts/run_nightly_verification_suite.py"),
                            "--profile",
                            "census-only",
                            "--state-dir",
                            str(tmp_dir / "state_err"),
                            flag,
                            value,
                        ],
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(out.returncode, suite.EXIT_INTERNAL_ERROR, out.stderr)

    def test_materialize_flip_baseline_tree_reads_tracked_files_at_a_git_revision(self) -> None:
        git = shutil.which("git")
        if git is None:
            self.skipTest("git is not installed")
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            repo.mkdir()

            def run_git(*args: str) -> None:
                subprocess.run(
                    [
                        git,
                        "-c",
                        "user.name=Flip Audit Test",
                        "-c",
                        "user.email=flip-audit@example.com",
                        "-c",
                        "commit.gpgsign=false",
                        *args,
                    ],
                    cwd=repo,
                    check=True,
                    capture_output=True,
                )

            run_git("init", "-q")
            self._write_flip_tree(
                repo, {"DIV-LM-D6-OFFSET-DISABLED-TAG": (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None)}
            )
            run_git("add", "-A")
            run_git("commit", "-q", "-m", "baseline")
            d6 = repo / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
            witness_line = (
                f"theorem step_binOp_offset_disabled_divergence : {SYNTH_DIVERGENCE_STMT} := rfl\n"
            )
            d6_text = d6.read_text(encoding="utf-8")
            self.assertEqual(d6_text.count(witness_line), 1)
            d6.write_text(
                d6_text.replace(
                    witness_line,
                    f"theorem step_binOp_offset_disabled_simulation : {SYNTH_STMT} := rfl\n",
                ),
                encoding="utf-8",
            )
            with (repo / suite.AUTHORITY_AUDIT_FILES["LeanMiriSpec"]).open("a", encoding="utf-8") as fh:
                fh.write(f"example : {SYNTH_STMT} :=\n  step_binOp_offset_disabled_simulation\n")
            (repo / "unrelated.txt").write_text("not a tracked file\n", encoding="utf-8")
            run_git("add", "-A")
            run_git("commit", "-q", "-m", "flip")
            dest = Path(tmp) / "baseline_tree"
            self.assertEqual(suite.materialize_flip_baseline_tree(repo, "HEAD~1", dest), dest)
            self.assertFalse((dest / "unrelated.txt").exists())
            self.assertTrue((dest / "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean").is_file())
            audit = suite.audit_flip_direction_transitions(dest, repo)
            self.assertTrue(audit["passed"], audit["violations"])
            self.assertEqual(
                audit["transitions"],
                [{"id": "DIV-LM-D6-OFFSET-DISABLED-TAG", "from": "open", "to": "resolved"}],
            )
            with self.assertRaises(ValueError):
                suite.materialize_flip_baseline_tree(repo, "no-such-ref", Path(tmp) / "x")

    def test_flip_direction_audit_rejects_proof_holes_hidden_behind_macros_and_axioms(self) -> None:
        # A hole that the theorem's own text does not spell (a tactic macro expanding
        # to `sorry`, an `axiom` proving `False`) passes the single-tree scan, but the
        # flip audit sees the flip add it to the resolution file.
        d6 = "DIV-LM-D6-OFFSET-DISABLED-TAG"
        sym = "step_binOp_offset_disabled_simulation"
        sim31 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
        hidden = {
            "macro_sorry": (
                'macro "close_goal" : tactic => `(tactic| sorry)\n'
                f"theorem {sym} : {SYNTH_STMT} := by close_goal\n",
                {"sorry": 1},
            ),
            "macro_admit": (
                'macro "close_goal" : tactic => `(tactic| admit)\n'
                f"theorem {sym} : {SYNTH_STMT} := by close_goal\n",
                {"admit": 1},
            ),
            "axiom": (
                "axiom flipCheat : False\n"
                f"theorem {sym} : {SYNTH_STMT} := flipCheat.elim\n",
                {"axiom": 1},
            ),
        }
        for label, (decls, added) in hidden.items():
            with self.subTest(hole=label), tempfile.TemporaryDirectory() as tmp:
                base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
                self._write_flip_tree(
                    base_root, {d6: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None)}
                )
                self._write_flip_tree(cur_root, {d6: (None, None, SYNTH_STMT)})
                with (cur_root / sim31).open("a", encoding="utf-8") as fh:
                    fh.write(decls)
                self.assertEqual(self._flip_status(cur_root, d6)["status"], "resolved")
                audit = suite.audit_flip_direction_transitions(base_root, cur_root)
                self.assertEqual(
                    [(v["id"], v["reason"]) for v in audit["violations"]],
                    [(d6, "proof_hole_introduced")],
                )
                self.assertIn(f"`{sim31}` gained proof-hole tokens {added}", audit["violations"][0]["detail"])
                # A hole that the baseline already had is not attributed to the flip,
                # and `.axiom` / `.sorry` field accesses are not holes.
                with (base_root / sim31).open("a", encoding="utf-8") as fh:
                    fh.write(decls.split("\n", 1)[0] + "\n")
                    fh.write("def fieldUses : Nat := Config.axiom + Tactic.sorry\n")
                self.assertTrue(suite.audit_flip_direction_transitions(base_root, cur_root)["passed"])

    def test_census_only_end_to_end_dashboard_and_ratchet(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state_dir = Path(tmp) / "state_out"
            code, dashboard, report_md = suite.run_suite_and_generate_dashboard(
                repo_root=REPO_ROOT,
                profile="census-only",
                state_dir=state_dir,
            )
            self.assertEqual(code, 0)
            self.assertEqual(
                dashboard["pillar_2_correctness_and_correspondence"]["overall_status"],
                "PASS",
            )
            self.assertIn("Pillar 1: 10,000-Foot Project Completeness", report_md)
            self.assertTrue((state_dir / "reports/LATEST_DASHBOARD_STATE.json").is_file())
            self.assertTrue((state_dir / "reports/LATEST_SUITE_REPORT.md").is_file())
            self.assertTrue((state_dir / "state/correspondence_ratchet.json").is_file())
            self.assertTrue((state_dir / "state/completeness_history.jsonl").is_file())

            loaded = json.loads(
                (state_dir / "reports/LATEST_DASHBOARD_STATE.json").read_text(encoding="utf-8")
            )
            self.assertEqual(loaded["schema_version"], 1)

    def test_build_suite_steps_ordering_core_theory_and_profile_isolation(self) -> None:
        census_steps = suite.build_suite_steps(REPO_ROOT, "census-only")
        census_names = [s[0] for s in census_steps]
        self.assertEqual(
            census_names,
            ["lean_miri_semantic_source_lint", "ci_check_non_stable_version"],
        )
        for _name, _cat, cmd, _timeout in census_steps:
            self.assertNotIn("lake", cmd)
            self.assertNotIn("cargo", cmd)

        quick_steps = suite.build_suite_steps(REPO_ROOT, "quick")
        quick_names = [s[0] for s in quick_steps]
        self.assertIn("lake_build_core_theory", quick_names)
        self.assertIn("check_trusted_fast", quick_names)
        self.assertLess(
            quick_names.index("lake_build_core_theory"),
            quick_names.index("check_trusted_fast"),
        )
        self.assertNotIn("check_trusted_self_test", quick_names)
        self.assertNotIn("lake_build_minirust_spec", quick_names)

        nightly_steps = suite.build_suite_steps(REPO_ROOT, "nightly")
        nightly_names = [s[0] for s in nightly_steps]
        core_idx = nightly_names.index("lake_build_core_theory")
        for dependent in (
            "check_trusted_fast",
            "check_trusted_self_test",
            "tests_mir_bit_validity_stage1",
            "tests_mir_byte_codec",
            "tests_mir_cast_stage1",
            "tests_mir_adt_and_control",
            "tests_mir_slice_wide_ptr_lens",
            "tests_mir_untested_variant_correspondence",
            "lake_build_correspondence",
            "lake_build_minirust_spec",
            "lake_build_lean_miri_spec",
        ):
            self.assertIn(dependent, nightly_names)
            self.assertLess(
                core_idx,
                nightly_names.index(dependent),
                f"lake_build_core_theory must precede {dependent}",
            )

        core_step = dict((s[0], s) for s in nightly_steps)["lake_build_core_theory"]
        self.assertEqual(core_step[1], "cat1_trusted_boundary")
        self.assertEqual(
            core_step[2][-5:],
            ["lake", "build", "Trusted", "Anneal", "MiniRust"],
        )

        # `lake env lean` never builds imports: every `tests_mir_*` file's workspace
        # imports must be built (`lake build +<Module>`) before it runs. `Anneal.ByteCodec`
        # and `Anneal.Mir.Cast` are outside the `Trusted`/`Anneal`/`MiniRust` closure, so
        # on a cold checkout `lake_build_core_theory` alone leaves them without `.olean`s.
        self.assertNotIn("lake_build_mir_test_modules", quick_names)
        self.assertNotIn("lake_build_mir_test_modules", census_names)
        by_name = dict((s[0], s) for s in nightly_steps)
        mods_step = by_name["lake_build_mir_test_modules"]
        sep = mods_step[2].index("--") if "--" in mods_step[2] else -1
        inner = mods_step[2][sep + 1 :]
        self.assertEqual(inner[:2], ["lake", "build"])
        built = {t[1:] for t in inner[2:] if t.startswith("+")}
        mods_idx = nightly_names.index("lake_build_mir_test_modules")
        self.assertLess(core_idx, mods_idx)
        import_re = re.compile(r"^import\s+(\S+)", re.MULTILINE)
        workspace_libs = suite.CORE_THEORY_LIBS + ("Correspondence", "MiniRustSpec")
        for step_name, rel in suite.MIR_STANDALONE_LEAN_TESTS:
            self.assertLess(mods_idx, nightly_names.index(step_name))
            self.assertEqual(by_name[step_name][2][-4:], ["lake", "env", "lean", rel])
            path = REPO_ROOT / rel
            if not path.is_file():
                # Only the Episode 2 correspondence suite may be absent (written concurrently);
                # its declared header is then covered by `_MIR_TEST_MODULE_FALLBACK`.
                self.assertEqual(rel, UNTESTED_VARIANT_TEST)
                imports = list(UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS)
            else:
                imports = import_re.findall(path.read_text(encoding="utf-8"))
            self.assertTrue(imports, rel)
            for mod in imports:
                if mod.split(".")[0] in workspace_libs:
                    self.assertIn(mod, built, f"{rel} imports {mod}, which must be pre-built")
        self.assertTrue({"Anneal.ByteCodec", "Anneal.Mir.Cast", "Anneal.Mir.AdtAndControl"} <= built)
        self.assertTrue(set(UNTESTED_VARIANT_TEST_WORKSPACE_IMPORTS) <= built)
        self.assertEqual(sorted(built), sorted(suite._MIR_TEST_MODULE_FALLBACK))
        self.assertEqual(len(suite._MIR_TEST_MODULE_FALLBACK), len(set(suite._MIR_TEST_MODULE_FALLBACK)))
        # The exact standalone `tests/mir` suites the nightly runs, including the
        # `Anneal.Mir.AdtAndControl` kernel-regression / axiom-pin suite, Episode 1's slice-lens
        # witnesses and Episode 2's untested-variant correspondence suite.
        self.assertEqual(
            sorted(rel for _step, rel in suite.MIR_STANDALONE_LEAN_TESTS),
            sorted(
                f"tests/mir/{name}.lean"
                for name in (
                    "BitValidityStage1Tests",
                    "ByteCodecTests",
                    "CastStage1Tests",
                    "AdtAndControlTests",
                    "MirSliceWidePtrLensTests",
                    "MirUntestedVariantCorrespondenceTests",
                )
            ),
        )

    def test_mir_test_prebuild_modules_fallback_when_a_header_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copy2(REPO_ROOT / "lakefile.toml", root / "lakefile.toml")
            (root / "tests/mir").mkdir(parents=True)
            for _step, rel in suite.MIR_STANDALONE_LEAN_TESTS:
                if rel != UNTESTED_VARIANT_TEST:
                    shutil.copy2(REPO_ROOT / rel, root / rel)
            # The correspondence suite is absent: the fallback fills in its imports, keeping
            # the first-seen order of the full union.
            self.assertEqual(suite.mir_test_prebuild_modules(root), list(suite._MIR_TEST_MODULE_FALLBACK))
            (root / UNTESTED_VARIANT_TEST).write_text(
                "import Trusted\nimport Anneal.MirFuelFree\n"
                "import Correspondence.V2026_06_01.L3_PlacesAndBasicMem\n"
                "import Correspondence.V2026_06_01.L5_ControlAndCalls\n"
                "import MiniRustSpec.Correspondence.Translate\nimport Lean.Elab.Command\n",
                encoding="utf-8",
            )
            self.assertEqual(suite.mir_test_prebuild_modules(root), list(suite._MIR_TEST_MODULE_FALLBACK))
        if (REPO_ROOT / UNTESTED_VARIANT_TEST).is_file():
            self.assertEqual(suite.mir_test_prebuild_modules(REPO_ROOT), list(suite._MIR_TEST_MODULE_FALLBACK))

    def test_timeout_propagation_and_calibrated_step_timeouts(self) -> None:
        nightly_by_name = {
            name: (cat, cmd, timeout_sec)
            for name, cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, "nightly")
        }
        expected_timeouts = {
            "lake_build_core_theory": 900,
            "check_trusted_fast": 600,
            "rust_workspace_unit_tests": 600,
            "check_trusted_self_test": 1500,
            "tests_mir_bit_validity_stage1": 300,
            "tests_mir_byte_codec": 300,
            "tests_mir_cast_stage1": 300,
            "tests_mir_adt_and_control": 300,
            "tests_mir_slice_wide_ptr_lens": 300,
            "tests_mir_untested_variant_correspondence": 300,
            "lake_build_correspondence": 900,
            "lake_build_minirust_spec": 1200,
            "lake_build_lean_miri_spec": 1800,
            "domain_integration_tests_anneal_difftest": 900,
            "cargo_anneal_e2e_minirust_correspondence": 600,
            "cargo_anneal_e2e_pipeline_and_adoption": 900,
        }
        # Raised from 900 s: also pre-builds the `Correspondence` L3/L5 and
        # `MiniRustSpec.Correspondence.Translate` closure of the correspondence suite.
        expected_timeouts["lake_build_mir_test_modules"] = 1500
        for step_name, exp_timeout in expected_timeouts.items():
            self.assertIn(step_name, nightly_by_name)
            _cat, cmd, timeout_sec = nightly_by_name[step_name]
            self.assertEqual(timeout_sec, exp_timeout, f"Unexpected timeout for {step_name}")
            self.assertEqual(Path(cmd[0]).name, "anneal-lean-run", f"{step_name} must be wrapped")
            self.assertIn("--timeout", cmd)
            t_idx = cmd.index("--timeout")
            self.assertEqual(int(cmd[t_idx + 1]), timeout_sec)

        # Every wrapped step in every profile hands its exact step budget to the wrapper.
        for profile in ("census-only", "quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                if not suite._is_lean_run_wrapped(cmd):
                    continue
                mode, inner_timeout, slot_lock = suite._lean_run_wrapper_flags(cmd)
                self.assertEqual(inner_timeout, timeout_sec, f"{profile}/{name}")
                self.assertTrue(slot_lock, f"{profile}/{name}")
                expected_mode = "file" if name.startswith("tests_mir_") else "build"
                self.assertEqual(mode, expected_mode, f"{profile}/{name}")

    def test_run_step_wrapper_timeout_grace_and_exit_124_classification(self) -> None:
        # When a wrapped command exits with 124 (inner anneal-lean-run timeout),
        # `_run_step` classifies status as TIMEOUT and preserves diagnostic stderr.
        res = suite._run_step(
            name="simulated_inner_timeout",
            category="cat2_correspondence_suites",
            cmd=[
                sys.executable,
                "-c",
                "import sys; sys.stderr.write('[anneal-lean-run] ERROR: Command timed out\\n'); sys.exit(124)",
            ],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(res["status"], "TIMEOUT")
        self.assertEqual(res["exit_code"], 124)
        self.assertIn("[anneal-lean-run] ERROR: Command timed out", res["failure_excerpt"])

        # Verify `_ensure_toolchain_path` populates existing user toolchain dirs into minimal PATH.
        minimal_env = {"PATH": "/usr/bin:/bin"}
        suite._ensure_toolchain_path(minimal_env)
        for rel in (".elan/bin", ".cargo/bin", ".local/bin"):
            cand = Path.home() / rel
            if cand.is_dir():
                self.assertIn(str(cand), minimal_env["PATH"].split(":"))

    def test_outer_timeout_covers_wrapper_slot_wait_and_grace(self) -> None:
        lr = str(REPO_ROOT / "scripts/anneal-lean-run")
        grace = suite.WRAPPER_TIMEOUT_GRACE_SEC
        # Direct commands: the step budget is the only deadline.
        self.assertEqual(suite._outer_timeout_sec(["cargo", "test"], 600), 600)
        # `--mode build` may queue up to `max(30, T)` s for a build slot before its own
        # `T`-second clock starts, so the outer deadline must exceed `T + max(30, T)`.
        build = [lr, "--mode", "build", "--concurrency", "1", "--timeout", "1200", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(build, 1200), 1200 + 1200 + grace)
        short = [lr, "--mode", "build", "--timeout", "10", "--", "lake", "build"]
        self.assertEqual(suite._outer_timeout_sec(short, 10), 10 + 30 + grace)
        # `file` mode and `--no-slot-lock` never queue.
        file_cmd = [lr, "--mode", "file", "--timeout", "300", "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._outer_timeout_sec(file_cmd, 300), 300 + grace)
        nolock = [lr, "--mode", "build", "--no-slot-lock", "--timeout=900", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(nolock), ("build", 900, False))
        self.assertEqual(suite._outer_timeout_sec(nolock, 900), 900 + grace)
        # `auto` resolves like the wrapper; without `--timeout` the wrapper defaults apply.
        auto_file = [lr, "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file, 60), 180 + grace)
        auto_file_nosep = [lr, "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_file_nosep), ("file", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_file_nosep, 60), 180 + grace)
        auto_build = [lr, "--", "lake", "build", "Anneal"]
        self.assertEqual(suite._lean_run_wrapper_flags(auto_build), ("build", None, True))
        self.assertEqual(suite._outer_timeout_sec(auto_build, 60), 900 + 900 + grace)
        # Inner command `--` and inner flags (e.g. `cargo test -- --no-slot-lock --timeout 5`)
        # must never be mistaken for wrapper flags.
        inner_sep = [
            lr,
            "--mode",
            "build",
            "--timeout",
            "600",
            "cargo",
            "test",
            "--",
            "--no-slot-lock",
            "--mode",
            "file",
            "--timeout",
            "5",
        ]
        self.assertEqual(suite._lean_run_wrapper_flags(inner_sep), ("build", 600, True))
        self.assertEqual(suite._outer_timeout_sec(inner_sep, 600), 600 + 600 + grace)
        # `argparse` long-option prefix abbreviations (`--time`, `--no-slot`, `--conc`) and
        # `ANNEAL_LEAN_TIMEOUT_SEC` env fallback when `--timeout` is omitted.
        abbrev = [lr, "--mo", "build", "--no-slot", "--conc=1", "--time", "450", "--", "lake", "build"]
        self.assertEqual(suite._lean_run_wrapper_flags(abbrev), ("build", 450, False))
        self.assertEqual(suite._outer_timeout_sec(abbrev, 300), 450 + grace)
        self.assertEqual(
            suite._outer_timeout_sec(auto_build, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "1500"}),
            1500 + 1500 + grace,
        )
        self.assertEqual(
            suite._outer_timeout_sec(auto_file, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "240"}),
            240 + grace,
        )
        # Explicit `--timeout 0` on the command line overrides `ANNEAL_LEAN_TIMEOUT_SEC`
        # (falling back to the mode default 900s/180s), and `-- --` leaves the second
        # `--` in `inner` (so `detect_mode` resolves to `"build"`, matching `anneal-lean-run`).
        explicit_zero = [lr, "--timeout", "0", "--", "lake", "build", "Anneal"]
        self.assertEqual(
            suite._outer_timeout_sec(explicit_zero, 60, env={"ANNEAL_LEAN_TIMEOUT_SEC": "1500"}),
            900 + 900 + grace,
        )
        double_sep = [lr, "--", "--", "lake", "env", "lean", "X.lean"]
        self.assertEqual(suite._lean_run_wrapper_flags(double_sep), ("build", None, True))
        # A wrapped step never gets a shorter outer deadline than its own budget.
        for profile in ("quick", "nightly"):
            for name, _cat, cmd, timeout_sec in suite.build_suite_steps(REPO_ROOT, profile):
                outer = suite._outer_timeout_sec(cmd, timeout_sec)
                if suite._is_lean_run_wrapped(cmd):
                    mode, _t, _lock = suite._lean_run_wrapper_flags(cmd)
                    slot = max(30, timeout_sec) if mode == "build" else 0
                    self.assertEqual(outer, timeout_sec + slot + grace, f"{profile}/{name}")
                else:
                    self.assertEqual(outer, timeout_sec, f"{profile}/{name}")

    def _assert_pid_gone(self, pid: int, what: str) -> None:
        deadline = time.monotonic() + 10.0
        while time.monotonic() < deadline:
            try:
                state = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0]
            except (OSError, IndexError):
                return
            if state == "Z":
                return
            time.sleep(0.05)
        try:
            os.kill(pid, 9)
        except OSError:
            pass
        self.fail(f"{what} (pid {pid}) survived the step timeout")

    def test_run_step_timeout_terminates_whole_step_process_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            # A same-group grandchild (as `cargo` children are) must not outlive the step.
            script = (
                "import subprocess, sys, time\n"
                f"child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "print('partial-output-before-timeout', flush=True)\n"
                "time.sleep(60)\n"
            )
            t0 = time.monotonic()
            res = suite._run_step(
                name="hung_step",
                category="cat7_python_and_ci_tests",
                cmd=[sys.executable, "-c", script],
                cwd=REPO_ROOT,
                timeout_sec=3,  # ample slack for two interpreter start-ups under load
            )
            self.assertLess(time.monotonic() - t0, 30.0)
            self.assertEqual(res["status"], "TIMEOUT")
            self.assertEqual(res["exit_code"], 124)
            self.assertIn("partial-output-before-timeout", res["failure_excerpt"])
            self.assertIn("Timed out after", res["failure_excerpt"])
            self.assertTrue(pid_file.is_file(), "step was killed before it spawned its child")
            self._assert_pid_gone(int(pid_file.read_text()), "same-group grandchild")

    def _spawn_ready_step(self, script: str, ready: Path) -> subprocess.Popen[bytes]:
        """Start `script` exactly as `_run_step` does (own session) and wait until it
        creates `ready`, so signal tests never race interpreter start-up."""
        proc = subprocess.Popen(
            [sys.executable, "-c", script],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        deadline = time.monotonic() + 60.0
        while not ready.exists():
            if proc.poll() is not None or time.monotonic() > deadline:
                suite._terminate_step(proc)
                self.fail(f"step never became ready (exit {proc.returncode})")
            time.sleep(0.02)
        return proc

    def test_terminate_step_lets_wrapper_reap_its_separate_session_scope(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            pid_file = Path(tmp) / "pids"
            ready = Path(tmp) / "ready"
            # Mirrors `anneal-lean-run`: the build runs in its own session and is only
            # reaped by the wrapper's SIGTERM handler, so a bare SIGKILL of the wrapper
            # (what `subprocess.run(timeout=...)` does) would orphan it.
            script = (
                "import os, signal, subprocess, sys, time\n"
                "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],\n"
                "                         start_new_session=True)\n"
                f"open({str(pid_file)!r}, 'w').write(str(child.pid))\n"
                "def on_term(signum, frame):\n"
                "    os.killpg(child.pid, signal.SIGKILL)\n"
                "    child.wait()\n"
                "    sys.exit(128 + signum)\n"
                "signal.signal(signal.SIGTERM, on_term)\n"
                f"open({str(ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            proc = self._spawn_ready_step(script, ready)
            suite._terminate_step(proc)
            self.assertEqual(proc.returncode, 128 + 15)  # exited through its handler
            self._assert_pid_gone(int(pid_file.read_text()), "separate-session build scope")

        # End to end: a hung wrapper is still reported as a TIMEOUT through `_run_step`.
        res = suite._run_step(
            name="hung_wrapper",
            category="cat2_correspondence_suites",
            cmd=[sys.executable, "-c", "import time; time.sleep(60)"],
            cwd=REPO_ROOT,
            timeout_sec=1,
        )
        self.assertEqual((res["status"], res["exit_code"]), ("TIMEOUT", 124))

    def test_run_step_reports_launch_failure_and_undecodable_output(self) -> None:
        missing = suite._run_step(
            name="missing_tool",
            category="cat7_python_and_ci_tests",
            cmd=[str(REPO_ROOT / "scripts" / "no-such-tool-ep2")],
            cwd=REPO_ROOT,
            timeout_sec=5,
        )
        self.assertEqual(missing["status"], "FAIL")
        self.assertEqual(missing["exit_code"], 127)
        garbage = suite._run_step(
            name="binary_output",
            category="cat7_python_and_ci_tests",
            cmd=[sys.executable, "-c", "import sys; sys.stdout.buffer.write(b'\\xff\\xfe bad'); sys.exit(3)"],
            cwd=REPO_ROOT,
            timeout_sec=10,
        )
        self.assertEqual(garbage["status"], "FAIL")
        self.assertEqual(garbage["exit_code"], 3)
        self.assertIn("bad", garbage["failure_excerpt"])

    def test_lean_header_imports_parses_module_system_and_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "T.lean"
            f.write_text(
                "\ufeff/- header /- nested -/ comment -/\n"
                "module\n"
                "-- line comment import Fake.Module\n"
                "public import Anneal.ByteCodec\n"
                "meta import all Anneal.Mir.Cast  -- trailing\n"
                "import «Anneal».BitValidity import Foo.«a b».c\n"
                "import Bar.«x--y».«z/-w» -- comment after guillemets\n"
                "\n"
                "theorem t : True := by\n"
                "  trivial\n"
                "import Not.A.Header.Import\n",
                encoding="utf-8",
            )
            self.assertEqual(
                suite._lean_header_imports(f),
                [
                    "Anneal.ByteCodec",
                    "Anneal.Mir.Cast",
                    "Anneal.BitValidity",
                    "Foo.a b.c",
                    "Bar.x--y.z/-w",
                ],
            )
            self.assertIsNone(suite._lean_header_imports(Path(tmp) / "missing.lean"))

    def test_discover_correspondence_divergences_ignores_commented_out_witness(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / UNTESTED_VARIANT_TEST
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                "-- theorem tailCall_leanMiri_nounwind_callee : True := trivial\n"
                "/- theorem opaqueCast_trusted_root_dispatch_divergence : True := trivial -/\n"
                "theorem tailCall_leanMiri_root_stop_diverges : True := trivial\n",
                encoding="utf-8",
            )
            divs = suite.discover_correspondence_divergences(root)
            open_by_id = {d["id"]: d for d in divs["actionable_anneal_bugs"]}
            # Commented-out witnesses are not live, and without their pinned `*_simulation`
            # replacements the entries fail closed as `resolution_missing` (not `resolved`).
            for div_id in ("DIV-LM-TAILCALL-NOUNWIND-UNWIND", "DIV-TR-OPAQUECAST-ROOT-DISPATCH"):
                self.assertFalse(open_by_id[div_id]["live_in_source"])
                self.assertEqual(open_by_id[div_id]["status"], "resolution_missing")
            self.assertEqual(divs["resolved_correspondence_divergences"], [])
            by_id = {d["id"]: d for d in divs["intentional_modeling_choices"]}
            self.assertTrue(by_id["MODEL-LM-TAILCALL-MODULAR-ROOT"]["live_in_source"])
            self.assertFalse(by_id["MODEL-LM-TAILCALL-DIRECT-ARITY-STEP"]["live_in_source"])

    def test_terminate_step_grants_grace_window_to_same_group_descendants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / "cleaned"
            child_ready = Path(tmp) / "child_ready"
            ready = Path(tmp) / "ready"
            # The leader exits immediately on SIGTERM while its same-group child takes
            # 0.25 s to write `marker` before exiting cleanly: escalating to SIGKILL as
            # soon as the leader is gone would kill the child mid-cleanup.
            child_code = (
                "import pathlib, signal, sys, time\n"
                "def handler(s, f):\n"
                "    time.sleep(0.25)\n"
                f"    pathlib.Path({str(marker)!r}).write_text('grace-ok')\n"
                "    sys.exit(0)\n"
                "signal.signal(signal.SIGTERM, handler)\n"
                f"open({str(child_ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            leader_code = (
                "import os, signal, subprocess, sys, time\n"
                "signal.signal(signal.SIGTERM, lambda s, f: sys.exit(0))\n"
                f"subprocess.Popen([sys.executable, '-c', {child_code!r}])\n"
                f"while not os.path.exists({str(child_ready)!r}):\n"
                "    time.sleep(0.01)\n"
                f"open({str(ready)!r}, 'w').close()\n"
                "time.sleep(60)\n"
            )
            proc = self._spawn_ready_step(leader_code, ready)
            suite._terminate_step(proc)
            self.assertEqual(proc.returncode, 0)
            self.assertTrue(marker.is_file(), "same-group child was SIGKILLed before grace window")
            self.assertEqual(marker.read_text(), "grace-ok")

    def test_flip_direction_guard_hardens_parser_tautology_pin_and_transition_bypasses(self) -> None:
        div_id = "DIV-LM-ENUM-SET-DISCR-UNINIT"
        sym = "step_setDiscriminant_uninit_simulation"
        lm23 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM2_3.lean"
        pin_div = "DIV-MR-CALL-TARGET-LOCAL"
        pin_sym = "callerRefMutSilentWrongLocal_simulation"
        stmt = SYNTH_STMT

        # 1. Guillemet-escaped / `_root_`-qualified logicals, tautological self-implications,
        #    contradictory hypotheses, prefix connectives, vacuous existentials, literal
        #    contradictions, nested holes, tactic-typed binders, `where` modifier/attribute
        #    helpers, `in`-scoped tactic commands, and `mutual` sibling holes are all rejected.
        bypass_theorems: list[tuple[str, set[str]]] = [
            (": «True» := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (": _root_.True := trivial", {"vacuous_statement", "closed_trivial_statement"}),
            (f": «False» → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": _root_.False → {stmt} := fun h => h.elim", {"vacuous_statement"}),
            (f": {stmt} := «sorryAx» _ false", {"sorry_or_admit"}),
            (f": {stmt} := by native_decide", {"sorry_or_admit"}),
            # Circular / tautological hypotheses and excluded middle.
            (f"(h : {stmt}) : {stmt} := h", {"vacuous_statement"}),
            (f": {stmt} → {stmt} := id", {"vacuous_statement"}),
            (
                ": ∀ x, annealOutcome x = miriOutcome x → stepMirFn x = .ub → "
                "annealOutcome x = miriOutcome x := fun _ h _ => h",
                {"vacuous_statement"},
            ),
            (
                f": ({stmt} ∧ stepMirFn fooProg = .ub) → {stmt} := And.left",
                {"vacuous_statement"},
            ),
            (
                f"(h : {stmt}) : {stmt} ∨ stepMirFn fooProg = .ub := Or.inl h",
                {"vacuous_statement"},
            ),
            (
                ": annealOutcome fooProg = miriOutcome fooProg ∨ "
                "annealOutcome fooProg ≠ miriOutcome fooProg := Classical.em _",
                {"vacuous_statement"},
            ),
            (
                f"(h1 : stepMirFn fooProg = .ub) (h2 : stepMirFn fooProg ≠ .ub) : {stmt} := "
                "absurd h1 h2",
                {"vacuous_statement"},
            ),
            (
                f"(h : stepMirFn fooProg = .ub ∧ ¬(stepMirFn fooProg = .ub)) : {stmt} := "
                "absurd h.1 h.2",
                {"vacuous_statement"},
            ),
            # Prefix logicals, uninhabited/trivial types, and distinct literal contradictions.
            (": Eq (annealOutcome fooProg) (annealOutcome fooProg) := rfl", {"vacuous_statement"}),
            (": @Eq Nat (annealOutcome fooProg) (annealOutcome fooProg) := rfl", {"vacuous_statement"}),
            (f": Iff ({stmt}) ({stmt}) := Iff.rfl", {"vacuous_statement"}),
            (f": Or True ({stmt}) := Or.inl trivial", {"vacuous_statement"}),
            (f": And False ({stmt}) → {stmt} := fun h => h.1.elim", {"vacuous_statement"}),
            (f"(h : Fin 0) : {stmt} := h.elim0", {"vacuous_statement"}),
            (f"(h : ULift False) : {stmt} := h.down.elim", {"vacuous_statement"}),
            (": PLift True := ⟨trivial⟩", {"vacuous_statement", "closed_trivial_statement"}),
            (f": (0 = 1) → {stmt} := nofun", {"vacuous_statement"}),
            (f": (true = false) → {stmt} := nofun", {"vacuous_statement"}),
            (f": (Bool.true = Bool.false) → {stmt} := nofun", {"vacuous_statement"}),
            (": 0 ≠ 1 := by decide", {"vacuous_statement", "closed_trivial_statement"}),
            # Auto-param default on a vacuous binder.
            (f"(h : False := nomatch) : {stmt} := h.elim", {"vacuous_statement"}),
            # Vacuous existentials.
            (": ∃ (_ : CapturedMir), True := ⟨fooProg, trivial⟩", {"vacuous_statement"}),
            (": ∃ out, annealOutcome fooProg = out := ⟨_, rfl⟩", {"vacuous_statement"}),
            (": ∃ (out : Value), out = annealOutcome fooProg := ⟨_, rfl⟩", {"vacuous_statement"}),
            # Nested wildcard holes and tactic-synthesized binder types.
            ("(_ : CapturedMir) : id _ := trivial", {"wildcard_statement"}),
            (": annealOutcome fooProg = _ := rfl", {"wildcard_statement"}),
            (f"(h : _) : {stmt} := h", {"wildcard_statement"}),
            (f"(h : by exact False) : {stmt} := h.elim", {"self_typed_statement"}),
            (f"(h : type_of% fooLemma) : {stmt} := h", {"self_typed_statement"}),
            # `where` helpers with attributes/modifiers and `in`-scoped tactic commands.
            (
                f": {stmt} := aux\nwhere\n  @[simp] aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := aux\nwhere\n  private aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := aux\nwhere\n  noncomputable aux : {stmt} := sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f"(h : CapturedMir) : {stmt} := by\n  omit h in\n  sorry\n",
                {"sorry_or_admit"},
            ),
            (
                f": {stmt} := by\n  attribute [local simp] fooLemma in\n  sorry\n",
                {"sorry_or_admit"},
            ),
        ]
        for tail, expected in bypass_theorems:
            with self.subTest(theorem_tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual(rec["status"], "resolution_invalid")
                self.assertEqual(set(rec["resolution_problems"]), expected)

        # Positive controls: auto-param tactic defaults, `match` wildcard arms, dependent
        # proof-term arguments `(by ...)`, non-trivial existentials, and `⦃...⦄` binders pass.
        valid_controls = [
            f"⦃body : CapturedMir⦄ (_hlive : body ≠ deadBody := by rintro ⟨⟩) : "
            f"annealOutcome body = miriOutcome body := rfl",
            f"(k : TyKind) (hk : sizeOf k = match k with | .bool => 1 | _ => 4) : {stmt} := rfl",
            f"(idx : Nat) (hlt : idx < 4) : getElem fooArr idx (by exact hlt) = miriElem idx := rfl",
            ": ∃ s', stepMirFn fooProg s = .step s' ∧ mirStateRel s' m' := ⟨s, rfl, hrel⟩",
        ]
        for tail in valid_controls:
            with self.subTest(valid_tail=tail), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {div_id: (None, tail, stmt)})
                rec = self._flip_status(root, div_id)
                self.assertEqual((rec["status"], rec["resolution_problems"]), ("resolved", []))

        # `mutual ... end` sibling `sorry` invalidates a resolution theorem in the same block,
        # while a hole-free `mutual` block resolves.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write_flip_tree(root, {div_id: (None, None, stmt)})
            target = root / lm23
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(
                f"mutual\n"
                f"  theorem {sym} : {stmt} := mutualHelper\n"
                f"  theorem mutualHelper : {stmt} := sorry\n"
                f"end\n",
                encoding="utf-8",
            )
            rec = self._flip_status(root, div_id)
            self.assertEqual(rec["status"], "resolution_invalid")
            self.assertEqual(rec["resolution_problems"], ["sorry_or_admit"])
            target.write_text(
                f"mutual\n"
                f"  theorem {sym} : {stmt} := mutualHelper\n"
                f"  theorem mutualHelper : {stmt} := rfl\n"
                f"end\n",
                encoding="utf-8",
            )
            self.assertEqual(self._flip_status(root, div_id)["status"], "resolved")

        # 2. Statement-pin RHS operators (`|>`, `▸`, `<|`, `$`), binder holes (`(h : _)`),
        #    binder self-references, `⦃h : False⦄` strict-implicit binders, and `_root_.True`
        #    are all rejected; a legitimate `⦃...⦄` statement pin is accepted.
        bypass_pins: list[tuple[str, list[str]]] = [
            (f"example : {stmt} := {{sym}} |> ignoreFirst realProof", []),
            (f"example : {stmt} := {{sym}} ▸ realProof", []),
            (f"example : {stmt} := {{sym}} <| argA", []),
            (f"example : {stmt} := {{sym}} $ argA", []),
            ("example : «True» := {sym}", []),
            ("example : _root_.True := {sym}", ["pin_closed_trivial_statement", "pin_vacuous_statement"]),
            (f"example (h : _) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example [_] : {stmt} := {{sym}}", ["self_typed_or_hole_pin"]),
            (f"example (h : type_of% {{sym}}) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example (h : by exact False) : {stmt} := {{sym}} h", ["self_typed_or_hole_pin"]),
            (f"example ⦃h : False⦄ : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
            (f"example (h : {stmt}) : {stmt} := {{sym}} h", ["pin_vacuous_statement"]),
        ]
        for pin_text, expected_reasons in bypass_pins:
            with self.subTest(pin=pin_text), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                self._write_flip_tree(root, {pin_div: (None, f": {stmt} := rfl", None)})
                audit_file = root / suite.AUTHORITY_AUDIT_FILES["MiniRustSpec"]
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(pin_text.replace("{sym}", pin_sym) + "\n")
                rec = self._flip_status(root, pin_div)
                self.assertEqual(rec["status"], "resolution_unpinned")
                self.assertEqual(rec["resolution_pin_problems"], expected_reasons)
                with audit_file.open("a", encoding="utf-8") as fh:
                    fh.write(
                        f"example ⦃body : CapturedMir⦄ : annealOutcome body = miriOutcome body :=\n"
                        f"  @{pin_sym}\n"
                    )
                self.assertEqual(self._flip_status(root, pin_div)["status"], "resolved")

        # 3. Baseline-to-current transition audit catches cosmetically rewritten witness
        #    statements (`polarity_not_flipped`), cosmetically rewritten pre-existing
        #    resolutions (`resolution_predates_flip`), non-`open` incomplete flips,
        #    `native_decide` / `implemented_by` / `«sorryAx»` holes, witness-file holes,
        #    and `resolved -> resolved` statement rewrites backed by a new proof hole.
        d6 = "DIV-LM-D6-OFFSET-DISABLED-TAG"
        sim31 = "lean-miri/lean/LeanMiriSpec/Correspondence/SimLM3_1.lean"
        with tempfile.TemporaryDirectory() as tmp:
            base_root, cur_root = Path(tmp) / "base", Path(tmp) / "cur"
            self._write_flip_tree(
                base_root,
                {
                    # Witness uses binder `(s : MachineState)` and `≠`.
                    div_id: ("(s : MachineState) : annealStep s ≠ miriStep s := by decide", None, None),
                    # Pre-existing simulation uses `(s : MachineState)`.
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                        f": {SYNTH_DIVERGENCE_STMT} := rfl",
                        "(s : MachineState) : annealOutcome s = miriOutcome s := rfl",
                        "∀ s : MachineState, annealOutcome s = miriOutcome s",
                    ),
                    # Baseline is `resolution_missing` (neither witness nor resolution).
                    "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, None, None),
                    # Proper flip in `SimLM3_1` whose witness file `WitLM3_1` gains a hole.
                    d6: (f": {SYNTH_DIVERGENCE_STMT} := rfl", None, None),
                },
            )
            self._write_flip_tree(
                cur_root,
                {
                    # Cosmetically alpha-renamed + `∀`-wrapped + `True ∧`-padded witness!
                    div_id: (
                        None,
                        ": ∀ {st : MachineState}, True ∧ (id (annealStep st ≠ miriStep st)) := by decide",
                        "∀ {st : MachineState}, annealStep st ≠ miriStep st",
                    ),
                    # Cosmetically `∀`-wrapped pre-existing simulation!
                    "DIV-MR-TB-UNSAFECELL-PROTECTED-IM": (
                        None,
                        ": ∀ (st : MachineState), (annealOutcome st = miriOutcome st) := rfl",
                        "∀ (st : MachineState), annealOutcome st = miriOutcome st",
                    ),
                    # `resolution_missing -> resolution_unpinned` (non-`open` incomplete flip).
                    "DIV-LM-RAW-OVERWRITE-CHAR-COPY": (None, f": {stmt} := rfl", None),
                    # Proper flip on `SimLM3_1`, but `WitLM3_1` gains `«sorryAx»` and
                    # an already-resolved entry (`DIV-MR-CALL-TARGET-LOCAL`) rewrites its
                    # statement with a new `axiom` in its module.
                    d6: (None, f": {stmt} := rfl", stmt),
                    pin_div: (
                        None,
                        ": annealOutcome barProg = miriOutcome barProg := cheatAx",
                        "annealOutcome barProg = miriOutcome barProg",
                    ),
                },
            )
            with (cur_root / sim31).open("a", encoding="utf-8") as fh:
                fh.write("def hiddenHole : False := «sorryAx» False false\n")
            mr_wit = cur_root / "minirust/lean/MiniRustSpec/Correspondence/ProvenanceWitness.lean"
            with mr_wit.open("a", encoding="utf-8") as fh:
                fh.write("axiom cheatAx : annealOutcome barProg = miriOutcome barProg\n")
            audit = suite.audit_flip_direction_transitions(base_root, cur_root)
            self.assertFalse(audit["passed"])
            self.assertEqual(
                sorted((v["id"], v["reason"]) for v in audit["violations"]),
                sorted(
                    [
                        (div_id, "polarity_not_flipped"),
                        ("DIV-MR-TB-UNSAFECELL-PROTECTED-IM", "resolution_predates_flip"),
                        ("DIV-LM-RAW-OVERWRITE-CHAR-COPY", "incomplete_flip"),
                        (d6, "proof_hole_introduced"),
                        (pin_div, "proof_hole_introduced"),
                    ]
                ),
            )


if __name__ == "__main__":
    unittest.main()
