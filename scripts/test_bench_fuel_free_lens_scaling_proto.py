#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit, negative/edge-case, proof-health, axiom-guard, hygiene, and report tests
for `bench_fuel_free_lens_scaling_proto.py` and the Track P prototype."""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import importlib.util  # noqa: E402
import json  # noqa: E402
import os  # noqa: E402
import pathlib  # noqa: E402
import re  # noqa: E402
import subprocess  # noqa: E402
import time  # noqa: E402
import unittest  # noqa: E402

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parent
SPEC = importlib.util.spec_from_file_location("bench_proto", HERE / "bench_fuel_free_lens_scaling_proto.py")
bench = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules["bench_proto"] = bench
SPEC.loader.exec_module(bench)

PROTO = REPO / bench.PROTO_REL
REPORT = REPO / "PROTOTYPE_REPORT.md"
TRACK_P_FILES = {
    bench.PROTO_REL,
    "scripts/bench_fuel_free_lens_scaling_proto.py",
    "scripts/test_bench_fuel_free_lens_scaling_proto.py",
    "PROTOTYPE_REPORT.md",
}
BASE_SHA = "2167b83c9bf782c337d7cec99d54249c52f865c9"
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def strip_lean_comments(text: str) -> str:
    """Blank out nested block comments, line comments, and string literals."""
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(" " * (j + 1 - i))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


class GeneratorTests(unittest.TestCase):
    def test_variants_share_identical_statements(self):
        for family, variants in bench.FAMILIES.items():
            for k in bench.KS:
                stmts = {bench.statement_of(bench.theorem_source(family, v, k, f"K{k}"))[0] for v in variants}
                self.assertEqual(len(stmts), 1, f"{family}/K={k} statements differ across variants")

    def test_statements_are_symbolic(self):
        for family in bench.FAMILIES:
            for k in bench.KS:
                binders, stmt = bench.obligation(family, k)
                self.assertRegex(binders, r"^\(.+ : (Nat|UInt8)\)$")
                names = binders[1:].split(":")[0].split()
                self.assertTrue(any(re.search(rf"\b{n}\b", stmt) for n in names))

    def test_obligation_scales_with_k(self):
        for k in bench.KS:
            _, stmt = bench.obligation("local_slots", k)
            self.assertEqual(len(re.findall(r"\(\d+, x\d+\)", stmt)), k)
            _, fstmt = bench.obligation("struct_fields", k)
            self.assertEqual(len(re.findall(r"\.in[lr] x\d+", fstmt)), 2 * k)
            _, lstmt = bench.obligation("loop_trip", k)
            self.assertIn(f"countUpInit {k} x junk", lstmt)

    def test_slot_final_state_is_last_write(self):
        _, stmt = bench.obligation("local_slots", 10)
        ups = re.findall(r"\((\d+), (x\d+)\)", stmt)
        final = stmt.rsplit("= [", 1)[1].rstrip("]").split(", ")
        expect = [f"a{i}" for i in range(8)]
        for i, x in ups:
            expect[int(i)] = x
        self.assertEqual(final, expect)

    def test_field_final_values_are_last_writes(self):
        _, stmt = bench.obligation("struct_fields", 7)
        writes = re.findall(r"\.(inl|inr) (x\d+)", stmt.split("\n")[0])
        last_l = [x for side, x in writes if side == "inl"][-1]
        last_r = [x for side, x in writes if side == "inr"][-1]
        self.assertTrue(stmt.split("\n")[0].endswith(f"= {last_l} ∧"))
        self.assertTrue(stmt.strip().endswith(f"= {last_r}"))

    def test_bench_file_has_warmup_and_all_k(self):
        src = bench.bench_file("loop_trip", "optimized_runCfgToBlock_forRangeUp", bench.KS)
        labels = re.findall(r'#measure "(\w+)"', src)
        self.assertEqual(labels, ["warmup"] + [f"K{k}" for k in bench.KS])
        self.assertIn("set_option Elab.async false", src)
        self.assertIn(f"set_option maxHeartbeats {bench.HEARTBEAT_BUDGET}", src)
        self.assertIn(f"import {bench.BENCH_MODULE}", src)

    def test_no_forbidden_tokens_in_generated_sources(self):
        for family, variants in bench.FAMILIES.items():
            for v in variants:
                src = bench.bench_file(family, v, bench.KS)
                for tok in ("sorry", "admit", "native_decide", "ofReduceBool", "axiom "):
                    self.assertNotIn(tok, src)

    def test_unknown_variant_rejected(self):
        with self.assertRaises(ValueError):
            bench.proof("loop_trip", "magic", 5)

    def test_validate_generated(self):
        info = bench.validate_generated()
        self.assertEqual(info["files"], sum(len(v) for v in bench.FAMILIES.values()))


class MeasurementParsingTests(unittest.TestCase):
    SAMPLE = (
        "MEASURE label=warmup status=ok ms=12 hb=34000\n"
        "MEASURE label=K5 status=ok ms=10 hb=33000\n"
        "f.lean:9:2: error: (deterministic) timeout at `whnf`\n"
        "MEASURE label=K10 status=error ms=15000 hb=200000123\n"
        "MEASURE label=K20 status=skipped ms=0 hb=0\n"
    )

    def test_parse(self):
        m = bench.parse_measure_output(self.SAMPLE)
        self.assertEqual(m["K5"], {"status": "ok", "ms": 10, "hb": 33000})
        self.assertEqual(m["K10"]["status"], "error")
        self.assertEqual(m["K20"]["status"], "skipped")

    def test_aggregate_ok_median(self):
        agg = bench.aggregate([{"status": "ok", "ms": m, "hb": 5000} for m in (30, 10, 20)])
        self.assertEqual(agg["status"], "ok")
        self.assertEqual(agg["median_ms"], 20)
        self.assertEqual(agg["kilo_heartbeats"], 5)

    def test_aggregate_timeout_and_skip(self):
        self.assertEqual(bench.aggregate([{"status": "error", "ms": 0, "hb": 0}])["status"], "timeout")
        self.assertEqual(bench.aggregate([{"status": "skipped", "ms": 0, "hb": 0}])["status"], "skipped")
        mixed = bench.aggregate([{"status": "ok", "ms": 5, "hb": 1000}, {"status": "error", "ms": 9, "hb": 9}])
        self.assertEqual(mixed["status"], "timeout")


class EnvironmentTests(unittest.TestCase):
    def test_tool_env_prepends_toolchain_dirs(self):
        env = bench.tool_env()
        parts = env["PATH"].split(os.pathsep)
        home = pathlib.Path.home()
        self.assertEqual(parts[0], str(home / ".elan" / "bin"))
        self.assertIn(str(home / ".local" / "bin"), parts[:3])

    def test_lean_commands_are_wrapped(self):
        cmd = bench.lean_command(["x.lean"], 60)
        self.assertEqual(cmd[:5], ["anneal-lean-run", "--mode", "file", "--concurrency", "1"])
        self.assertEqual(cmd[-4:], ["lake", "env", "lean", "x.lean"])

    def test_receipts_go_to_tmp(self):
        self.assertTrue(str(bench.RECEIPT_DIR).startswith("/tmp/"))


class DryRunCliTests(unittest.TestCase):
    def test_dry_run_is_fast_and_clean(self):
        before = set(p.name for p in REPO.iterdir())
        t0 = time.perf_counter()
        res = subprocess.run([sys.executable, "-B", str(HERE / "bench_fuel_free_lens_scaling_proto.py"),
                              "--dry-run"], capture_output=True, text=True, cwd=REPO)
        elapsed = time.perf_counter() - t0
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("dry-run OK", res.stdout)
        self.assertLess(elapsed, 3.0)
        self.assertEqual(before, set(p.name for p in REPO.iterdir()), "dry-run wrote into the worktree")


class LeanSourceAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = PROTO.read_text()
        cls.code = strip_lean_comments(cls.text)

    def test_no_sorry_admit_axiom_unsafe(self):
        for pat in (r"\bsorry\b", r"\badmit\b", r"^\s*axiom\b", r"\bpartial\s+def\b", r"\bunsafe\b",
                    r"native_decide", r"ofReduceBool", r"implemented_by", r"@\[extern",
                    r"Classical\.", r"set_option\s+linter", r"\bopaque\b"):
            self.assertIsNone(re.search(pat, self.code, re.M), f"forbidden pattern {pat}")

    def test_every_theorem_has_axiom_guard(self):
        self.assertIsNone(
            re.search(
                r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)+theorem\b"
                r"|^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*lemma\b"
                r"|^\s*@\[[^\]]*\]\s*theorem\b",
                self.code,
                re.M,
            ),
            "all theorems must be plain top-level `theorem` declarations audited by `#print axioms`",
        )
        theorems = re.findall(r"^theorem\s+([A-Za-z_0-9.'?]+)", self.code, re.M)
        self.assertGreater(len(theorems), 150)
        self.assertEqual(len(theorems), len(set(theorems)))
        triples = re.findall(
            r"/-- info: '" + re.escape(bench.NAMESPACE) + r"\.([^']+)' ([^\n]*?) -/\n"
            r"#guard_msgs \(whitespace := lax\) in\n#print axioms (\S+)", self.text)
        guards = {}
        for name, msg, target in triples:
            self.assertEqual(name, target, "guard docstring and #print axioms target disagree")
            self.assertNotIn(name, guards, f"duplicate guard for {name}")
            guards[name] = msg
        self.assertEqual(sorted(theorems), sorted(guards), "theorems without guards (or stale guards)")
        for name, msg in guards.items():
            if msg == "does not depend on any axioms":
                continue
            m = re.fullmatch(r"depends on axioms: \[([^\]]*)\]", msg)
            self.assertIsNotNone(m, msg)
            axioms = {a.strip() for a in m.group(1).split(",")}
            self.assertTrue(axioms <= ALLOWED_AXIOMS, f"{name}: {axioms}")

    def test_required_theorems_present(self):
        required = [
            "evalFuel_mono", "StepsTo.bind_wp", "runToTarget_mono_bound", "stepsTo_of_runCfgToBlock_reached",
            "wpConverges_of_runCfgToBlock_halted", "runCfgToBlock_selfLoop_no_overshoot",
            "firstHitIn_of_runToTarget_reached", "forRangeUp_induction", "wpConverges_forRangeUp",
            "forRangeUp_eq_live", "no_uniform_fuel_countUp", "countUp_wpConverges_all_n",
            "evalFuel_infiniteLoop_outOfFuel", "not_wpConverges_infiniteLoop",
            "runToTarget_infiniteLoop_outOfFuel",
            "mirWpConverges_of_wpConverges", "mirStepsConverges_of_stepsTo",
            "runMirToBlock_countToN_entry", "runMirToBlock_countToN_iter", "runMirToBlock_countToN_exit",
            "live_countToN_mirWpConverges_all_n", "inferMinFragment_toMirShape",
            "forcePureEnv_eq_self", "forcePureEnvD_eq_take_append_replicate",
            "forcePureEnv_ne_self_of_length_ne", "forcePureEnv_eq_self_iff",
            "getElem?_forcePureEnv", "forcePureEnv_set_comm", "chained_sets_collapse_rfl",
            "forceSpine?_eq_live", "setSpine?_eq_some_set", "setSpine?_eq_forceSpine?_set",
            "TypedAt.read_write_same", "TypedAt.frame_write", "writeTyped_eq_none_of_oob",
            "writeTyped_zero_width", "typedAt_zero_width_iff", "TypedAt.frame_write_adjacent",
            "typedAt_laidOutPair_iff", "typedAt_laidOutPair_padding_write",
            "typedAt_of_canonicalAt", "typedAt_laidOutPair_of_fieldsValid",
            "subplaceFieldLens_disjoint", "subplaceFieldLens_of_borrowSubplace_disjointOn",
            "reborrow_return_unique_write_perm", "reborrow_return_after_callee_write_unique_write_perm",
            "reborrow_return_after_parent_write_unique_write_perm",
            "callee_parent_write_after_reborrow_disables_child",
            "split_at_mut_unique_write_perm", "split_at_mut_mid_zero", "split_at_mut_mid_len",
            "trustedSpec_reborrow_equivalence", "same_tag_split_unsound_control",
            "overlapping_reborrowFootprint_write_disables_sibling",
            "ofLiveTreeBorrowPerm?_toLiveTreeBorrowPerm", "toLiveTreeBorrowPerm_ofLiveTreeBorrowPerm?",
            "liveBorrowEntryRange_contains_iff", "split_at_mut_rootTree_nonvacuous",
            "setSpine?_eq_some_forcePureEnv_set", "applySlotUpdatesForced_eq_forcePureEnv",
            "liveSet?_eq_setSpine?", "applySlotUpdatesLive?_eq_forced", "applySlotUpdatesLive?_oob",
            "subplaceFieldLens_of_borrowSubplace_disjointOn_nonvacuous",
            "performTransition_accessed_eq_live", "performTransition_unaccessed_eq_live",
            "performTransition_accessed_isSome_eq_live", "isTagProtected_eq_live",
            "performTransition_entry_eq_live", "foreign_write_disabled_protected_noop",
            "protected_reservedIM_foreign_fails_closed",
            "mirStepsConverges_of_mirStep_cont", "mirWpConverges_of_mirStep_cont",
            "live_runMirToBlock_stationary_at_target", "runUntilTarget_reached_iff_live_runMirToBlock",
            "runMirToBlock_reached_iff_step_and_live",
            "setPureEnvSlot?_eq_set?", "setPureEnvSlot?_eq_live_bind_forcePureEnv?",
            "evalPureStmtNorm_eq_bind_forceSpine?",
            "typedAt_laidOutPair_write_fst", "typedAt_laidOutPair_applyFieldWrites",
            "hasUniqueWritePerm_remove_callId", "split_at_mut_stage2Only_unique_write_perm",
            "stage1_vs_stage2Only_two_arg_release_differs", "shared_reborrowFootprint_read_ok_write_ub",
            "isBorrowDescendantOrSelf_refl", "nodeAccessRelatedness_visit_eq_live_writer",
            "borrowEntryWriteConflicts_eq_live", "restoreCallerProtectors_eq_live",
            "applySlotUpdatesTwoPass_eq_live?", "applySlotUpdates_eq_of_twoPass",
            "performTransition_unprotected_eraseLatch", "LatchEquiv.noUB_iff", "LatchEquiv.access",
            "LatchEquiv.insert", "LatchEquiv.retag", "LatchEquiv.release", "LatchEquiv.releaseNoUB_iff",
            "LatchEquiv.of_active", "applyReleaseProtector_read_eraseLatch",
            "stage1_vs_stage2Only_two_arg_release_unobservable",
            "stage1_vs_stage2Only_two_arg_release_same_verdicts",
        ]
        theorems = set(re.findall(r"^theorem\s+([A-Za-z_0-9.'?]+)", self.code, re.M))
        for name in required:
            self.assertIn(name, theorems)

    def test_live_two_pass_variant_mirrors_live_normalizer(self):
        """`local_slots/live_two_pass_rfl` must measure the live `evalPureStmtNorm` structure:
        bounds-checked `Trusted.Sequence.set?` followed by a full `forceSpine?` pass."""
        self.assertIn("live_two_pass_rfl", bench.FAMILIES["local_slots"])
        self.assertEqual(bench.FAMILIES["local_slots"][-1], "optimized_forcePureEnv")
        m = re.search(r"def applySlotUpdatesTwoPass .*?:=?\n(.*?)\n\n", self.code, re.S)
        self.assertIsNotNone(m)
        self.assertIn("(Trusted.Sequence.set? env u.1 u.2).bind forceSpine?", m.group(0))
        self.assertIn("applySlotUpdates_eq_of_twoPass", bench.proof("local_slots", "live_two_pass_rfl", 5))

    def test_live_hierarchy_and_return_bridges_present(self):
        for sym in (
            "Anneal.FunctionalTranslation.runMirToBlock",
            "Anneal.MirLiftCore.evalPureStmtNorm",
            "Trusted.Rustc.V2026_06_01.MirSemantics.isBorrowDescendantOrSelf",
            "Trusted.Rustc.V2026_06_01.MirSemantics.resolveTreeBorrowWriterTag",
            "Trusted.Rustc.V2026_06_01.MirSemantics.borrowEntryWriteConflicts",
            "Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors",
        ):
            self.assertIn(sym, self.code)

    def test_tree_borrows_bridge_is_semantic(self):
        """The Tree Borrows bridge must relate *transitions*, not only rename permissions."""
        live = "Trusted.Rustc.V2026_06_01.MirSemantics."
        for name in ("treeBorrowNodeAccess", "treeBorrowPermTransition", "treeBorrowTransitionIsUB",
                     "isBorrowProtected", "natListContainsBool"):
            self.assertIn(live + name, self.code)
        m = re.search(r"theorem performTransition_accessed_eq_live (.*?) :=", self.code, re.S)
        self.assertIsNotNone(m)
        # Universally quantified over every kind / relatedness / protector bit / permission.
        self.assertRegex(m.group(1), r"\(kind : AccessKind\) \(rel : AccessRelatedness\)\s+\(isProt : Bool\) \(p : Permission\)")

    def test_mirStep_handles_emit_observations(self):
        m = re.search(r"def mirStep .*? :=.*?\n\n", self.code, re.S)
        self.assertIsNotNone(m)
        self.assertIn(".vis (.inr (.inl (.emit", m.group(0))

    def test_live_bridges_present(self):
        self.assertIn("Anneal.SepLogicLenses.BorrowSubplace.disjointOn", self.code)
        self.assertIn("Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm", self.code)
        self.assertIn("Trusted.Rustc.V2026_06_01.MirSemantics.BorrowEntry", self.code)
        self.assertIn("Anneal.MirLoops.countToNBody", self.code)

    def test_countUp_statement_has_no_fuel_numeral(self):
        m = re.search(r"theorem countUp_wpConverges_all_n (.*?) :=", self.code, re.S)
        self.assertIsNotNone(m)
        self.assertNotRegex(m.group(1), r"evalFuel|\b\d{2,}\b")

    def test_reborrow_footprint_type(self):
        self.assertRegex(self.code, r"reborrowFootprint : List \(ByteRange × Mutability\)")

    def test_target_outcome_distinguishes_four_cases(self):
        m = re.search(r"inductive TargetOutcome.*?where(.*?)\n\n", self.code, re.S)
        ctors = re.findall(r"\|\s*(\w+)", m.group(1))
        self.assertEqual(ctors, ["reached", "halted", "stuck", "outOfFuel"])

    def test_live_modules_imported(self):
        for mod in ("PureMirExec", "MirLiftCore", "MirFuelFree", "MirLoops", "SepLogicLenses", "ByteCodec"):
            self.assertRegex(self.text, rf"^import Anneal\.{mod}$" if False else rf"(?m)^import Anneal\.{mod}$")

    def test_proof_health_clean(self):
        sys.path.insert(0, str(REPO / "tools" / "anneal-lsp" / "server"))
        try:
            import proof_health  # type: ignore
        finally:
            sys.path.pop(0)
        findings = proof_health.scan_lean_file(PROTO)
        self.assertEqual([f.to_dict() for f in findings], [])


class HygieneTests(unittest.TestCase):
    def test_no_internal_strings_in_track_p_files(self):
        for rel in TRACK_P_FILES:
            path = REPO / rel
            if not path.exists():
                continue
            text = path.read_text()
            for pat in bench.INTERNAL_PATTERNS:
                self.assertIsNone(re.search(pat, text), f"{rel} matches internal pattern {pat}")

    def test_hygiene_patterns_catch_examples(self):
        bad = ["host " + "cp" + "l-abc", "x.google" + "rs.com", "/home/" + "groupagent-x", "/x" + "20/teams",
               "/goo" + "gle/src", "see c" + "l/123", "bug b" + "/456", "opus" + "-5.5-max", "gem" + "ini-flash"]
        for s in bad:
            self.assertTrue(any(re.search(p, s) for p in bench.INTERNAL_PATTERNS), s)

    def test_track_p_isolation(self):
        try:
            res = subprocess.run(["git", "diff", "--name-only", f"{BASE_SHA}..HEAD"], cwd=REPO,
                                 capture_output=True, text=True, check=True)
        except (OSError, subprocess.CalledProcessError):
            self.skipTest("git history unavailable")
        changed = {line for line in res.stdout.splitlines() if line}
        self.assertTrue(changed <= TRACK_P_FILES, f"files outside Track P scope: {changed - TRACK_P_FILES}")


class ReportTests(unittest.TestCase):
    def fake_receipt(self) -> dict:
        results = []
        for family, variants in bench.FAMILIES.items():
            for v in variants:
                for k in bench.KS:
                    results.append({"family": family, "variant": v, "k": k, "status": "ok",
                                    "median_ms": 10.0 + k, "kilo_heartbeats": 100 + k,
                                    "ms_samples": [10 + k], "hb_samples": [(100 + k) * 1000]})
        return {"schema": bench.SCHEMA, "prototype_sha256": "0" * 64, "ks": list(bench.KS),
                "repetitions": 1, "heartbeat_budget": bench.HEARTBEAT_BUDGET, "results": results}

    def fake_report(self, receipt: dict) -> str:
        claims = "\n".join(f"- {c}" for c in bench.derive_claims(receipt))
        return (
            "# Report\n\n**Decision: CONDITIONAL GO**\n\n"
            "PureMirExec.lean MirLiftCore.lean MirLoops.lean SepLogicLenses.lean ByteCodec.lean MirFuelFree.lean\n\n"
            f"{claims}\n\n" + bench.render_bench_section(receipt) + "\n\n### Round A0\n"
        )

    def test_render_roundtrip_verifies(self):
        r = self.fake_receipt()
        self.assertEqual(bench.verify_report_text(self.fake_report(r), "0" * 64), [])

    def test_detects_table_drift(self):
        r = self.fake_receipt()
        text = self.fake_report(r).replace("15 ms / 105 k", "14 ms / 105 k", 1)
        self.assertTrue(any("drifted" in p for p in bench.verify_report_text(text, "0" * 64)))

    def test_detects_stale_prototype_hash(self):
        r = self.fake_receipt()
        problems = bench.verify_report_text(self.fake_report(r), "1" * 64)
        self.assertTrue(any("sha256" in p for p in problems))

    def test_detects_missing_decision_and_claims(self):
        r = self.fake_receipt()
        text = self.fake_report(r).replace("**Decision: CONDITIONAL GO**", "")
        text = text.replace(bench.derive_claims(r)[0], "")
        problems = bench.verify_report_text(text, "0" * 64)
        self.assertTrue(any("Decision" in p for p in problems))
        self.assertTrue(any("measured claim" in p for p in problems))

    def test_detects_incomplete_receipt(self):
        r = self.fake_receipt()
        r["results"] = r["results"][:-1]
        problems = bench.verify_report_text(self.fake_report(self.fake_receipt()).replace(
            json.dumps(self.fake_receipt(), indent=1, sort_keys=True), json.dumps(r, indent=1, sort_keys=True)),
            "0" * 64)
        self.assertTrue(any("cover" in p for p in problems))

    def test_real_report_verifies(self):
        res = subprocess.run([sys.executable, "-B", str(HERE / "bench_fuel_free_lens_scaling_proto.py"),
                              "--verify-report"], capture_output=True, text=True, cwd=REPO)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_real_report_receipt_is_sane(self):
        receipt = bench.extract_receipt(REPORT.read_text())
        self.assertEqual(receipt["ks"], list(bench.KS))
        self.assertGreaterEqual(receipt["repetitions"], 2)
        by = {(r["family"], r["variant"], r["k"]): r for r in receipt["results"]}
        for family, variants in bench.FAMILIES.items():
            for k in bench.KS:
                self.assertEqual(by[(family, variants[-1], k)]["status"], "ok",
                                 f"optimized {family} must succeed at K={k}")
        for row in receipt["results"]:
            for key in ("generated_at_utc",):
                self.assertNotIn(key, row)
        text = json.dumps(receipt)
        for pat in bench.INTERNAL_PATTERNS:
            self.assertIsNone(re.search(pat, text))

    def test_report_theorem_counts_match_source(self):
        code = strip_lean_comments(PROTO.read_text())
        n = len(re.findall(r"^theorem\s", code, re.M))
        counts = [int(c) for c in re.findall(r"\b(\d+) (?:kernel-checked theorems|axiom guards)\b",
                                             REPORT.read_text())]
        self.assertTrue(counts, "report must state the kernel-checked theorem / axiom guard count")
        self.assertEqual(set(counts), {n}, f"report counts {counts} drifted from the {n} theorems")

    # Report identifiers that are not Lean declarations (benchmark labels, receipt keys,
    # Rust/Miri names, binder names, Lean keywords/core lemmas, workstream status).
    NON_LEAN_NAMES = {
        "split_at_mut", "get_mut", "t_arg", "t_ret", "termination_by", "List.drop_take",
        "PROPOSED_HOLD", "skip_if_known_noop", "perform_access", "protector_end_access",
        "maxHeartbeats", "maxRecDepth", "SkipChildrenOfAccessed", "GlobalState.endCall",
        "hasFVar", "propext", "Quot.sound", "UInt8", "PUnit",
        "blockIdx", "stmtIdx", "parentTag", "t_sib", "t_arg_x", "t_arg_y",
        "Classical.byContradiction", "FuelFreeProtoBench.Prototype", "MirSemantics",
        "ProtectedDisabled", "ReservedFrz", "ReservedIM", "_", "countUp", "endCall",
        "headD", "subRange", "addDecl", "debug.skipKernelTC",
    }

    @staticmethod
    def _decls(text: str) -> set[str]:
        clean = strip_lean_comments(text)
        top = re.findall(
            r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
            r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([A-Za-z_][A-Za-z0-9_.'?!\u2080-\u2089]*)",
            clean, re.M)
        ctors = re.findall(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_.'?!\u2080-\u2089]*)(?:\s|:|$)", clean, re.M)
        fields = re.findall(r"^\s*([a-z][A-Za-z0-9_?!\u2080-\u2089]*)\s*:", clean, re.M)
        return set(top) | set(ctors) | set(fields)

    @classmethod
    def _declaration_index(cls) -> dict:
        """Declared names of the prototype, of each live `theory/Anneal` module, and of the
        trusted Lean tree (plus namespaces), cached across tests."""
        if getattr(cls, "_index", None) is None:
            live_files = [p for p in (REPO / "theory" / "Anneal").glob("*.lean") if p != PROTO]
            namespaces = {f"Anneal.{p.stem}" for p in live_files}
            trusted: set[str] = set()
            for p in (REPO / "trusted" / "lean").rglob("*.lean"):
                text = p.read_text()
                trusted |= cls._decls(text)
                namespaces |= set(re.findall(r"^namespace\s+(\S+)", text, re.M))

            def with_suffixes(names: set[str]) -> set[str]:
                return names | {n.rsplit(".", 1)[-1] for n in names}

            by_module = {p.stem: with_suffixes(cls._decls(p.read_text())) for p in live_files}
            trusted = with_suffixes(trusted)
            cls._index = {
                "proto": cls._decls(strip_lean_comments(PROTO.read_text())),
                "by_module": by_module,
                "trusted": trusted,
                "live_all": trusted.union(*by_module.values()),
                "namespaces": namespaces,
            }
        return cls._index

    def unresolved_names(self, report: str) -> list[str]:
        idx = self._declaration_index()
        try:
            receipt_keys = set(bench.extract_receipt(report))
        except ValueError:
            receipt_keys = set()
        labels = set(bench.FAMILIES) | {v for vs in bench.FAMILIES.values() for v in vs}
        unresolved = []
        for tok in sorted(set(re.findall(r"`([^`\n]+)`", report))):
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'?\u2080-\u2089]*", tok):
                continue
            if tok.endswith((".lean", ".md", ".py", ".json")):
                continue
            qualified = tok.startswith(("Anneal.", "Trusted."))
            has_camel = bool(re.search(r"[a-z][A-Z]", tok))
            if not qualified and "_" not in tok and not has_camel:
                continue
            last = tok.rsplit(".", 1)[-1]
            parts = tok.split(".")
            if (tok in idx["proto"] or labels.__contains__(tok) or tok in receipt_keys
                    or tok in self.NON_LEAN_NAMES or tok in idx["namespaces"]
                    or (len(parts) == 2 and parts[0] in idx["proto"] and last in idx["proto"])):
                continue
            if not qualified and hasattr(bench, tok):
                continue  # harness function named in the methodology section
            if not qualified and re.search(rf"^\s*def {re.escape(tok)}\(", pathlib.Path(__file__).read_text(), re.M):
                continue  # unit test named in the round log
            if tok.startswith("Anneal.") and len(parts) > 2 and parts[1] in idx["by_module"]:
                decls = idx["by_module"][parts[1]]
                ok = ".".join(parts[2:]) in decls or last in decls
            elif tok.startswith("Trusted."):
                ok = last in idx["trusted"]
            else:
                ok = tok in idx["live_all"] or last in idx["live_all"]
            if not ok:
                unresolved.append(tok)
        return unresolved

    def test_report_names_resolve(self):
        """Every Lean identifier cited in the report resolves to a prototype declaration or to a
        declaration of the live module it names (catches report drift and invented live APIs)."""
        self.assertEqual(self.unresolved_names(REPORT.read_text()), [],
                         "report cites identifiers with no matching declaration")

    def test_report_name_check_detects_invented_names(self):
        fake = ("`Anneal.MirLoops.forRangeUp` `Anneal.MirLoops.forRangeUpMagic` `no_such_theorem_xyz` "
                "`evalPureStmtNorm` `evalPureStmtMagic` "
                "`Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowNodeAccess` "
                "`Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowTeleport` `performTransition_accessed_eq_live`")
        self.assertEqual(self.unresolved_names(fake),
                         ["Anneal.MirLoops.forRangeUpMagic",
                          "Trusted.Rustc.V2026_06_01.MirSemantics.treeBorrowTeleport",
                          "evalPureStmtMagic", "no_such_theorem_xyz"])

if __name__ == "__main__":
    unittest.main()
