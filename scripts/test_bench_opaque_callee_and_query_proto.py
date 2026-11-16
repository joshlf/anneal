#!/usr/bin/env python3
"""Unit tests for `scripts/bench_opaque_callee_and_query_proto.py`.

Run: `python3 -B -m unittest -v scripts/test_bench_opaque_callee_and_query_proto.py`

* `RealLeanBenchmarkTest` runs the real Lean benchmark (`--sizes 4,16`) once and
  checks flat heartbeats for `opaque_o1` / `opaque_pruned` against linear growth
  for `linear_list`.
* `AuditScannerTest` pins the exactness of the lexer-aware
  `audit_redundant_beq_decidable_eq` scanner on edge cases.
* `RepoConsistencyTest` checks the repository-wide audit, the prototype file's
  `proof_health.py` result, and the prototype's `DecidableEq`-without-`BEq`
  discipline.
* `WorktreePollutionTest` checks that nothing is written into the worktree.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent
BENCH_PATH = HERE / "bench_opaque_callee_and_query_proto.py"
PROTOTYPE = REPO_ROOT / "theory" / "Anneal" / "DemandCompilerQueryAndOpaqueCalleePrototype.lean"
BASE_SHA = "86255c4698c28ce695b37e82f5a151896f7f736a"
DELIVERABLES = {
    "theory/Anneal/DemandCompilerQueryAndOpaqueCalleePrototype.lean",
    "scripts/bench_opaque_callee_and_query_proto.py",
    "scripts/test_bench_opaque_callee_and_query_proto.py",
    "PROTOTYPE_REPORT.md",
}


def load_bench():
    spec = importlib.util.spec_from_file_location("bench_opaque_callee_and_query_proto", BENCH_PATH)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


bench = load_bench()


def git_status() -> str:
    return subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=REPO_ROOT,
                          capture_output=True, text=True, check=True).stdout


def find_pycache() -> list[str]:
    return sorted(str(p.relative_to(REPO_ROOT)) for p in (REPO_ROOT / "scripts").rglob("__pycache__"))


class AuditScannerTest(unittest.TestCase):
    def audit(self, text: str) -> list[dict]:
        return bench.audit_redundant_beq_decidable_eq_text(text, "T.lean")

    def test_inline_deriving_both(self) -> None:
        f = self.audit("inductive A where\n  | a\n  deriving BEq, DecidableEq\n")
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["kind"], "deriving")
        self.assertEqual(f[0]["line"], 3)
        self.assertEqual(f[0]["classes"], ["BEq", "DecidableEq"])

    def test_multiline_deriving(self) -> None:
        f = self.audit("structure S where\n  x : Nat\n  deriving Repr,\n    DecidableEq,\n    BEq, Hashable\n")
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["classes"], ["Repr", "DecidableEq", "BEq", "Hashable"])

    def test_deriving_instance(self) -> None:
        f = self.audit("deriving instance BEq, DecidableEq for Foo, Bar\n")
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["kind"], "deriving_instance")
        self.assertEqual(f[0]["targets"], ["Foo", "Bar"])

    def test_qualified_and_guillemet_classes(self) -> None:
        self.assertEqual(len(self.audit("deriving instance «BEq», _root_.DecidableEq for Foo\n")), 1)

    def test_beq_without_decidable_eq(self) -> None:
        self.assertEqual(self.audit("inductive A where | a\n  deriving BEq, Hashable, Repr\n"), [])

    def test_decidable_eq_without_beq(self) -> None:
        self.assertEqual(self.audit("inductive A where | a\n  deriving DecidableEq, Repr\n"), [])

    def test_separate_clauses_do_not_combine(self) -> None:
        text = "inductive A where | a\n  deriving DecidableEq\ninductive B where | b\n  deriving BEq\n"
        self.assertEqual(self.audit(text), [])

    def test_line_comment(self) -> None:
        self.assertEqual(self.audit("-- deriving BEq, DecidableEq\ninductive A where | a\n"), [])

    def test_nested_block_comment(self) -> None:
        text = "/- outer /- inner -/ deriving BEq, DecidableEq -/\ninductive A where | a\n"
        self.assertEqual(self.audit(text), [])
        text2 = "/-- doc /- nested -/ still doc deriving BEq, DecidableEq -/\ndef x := 1\n"
        self.assertEqual(self.audit(text2), [])

    def test_block_comment_then_real(self) -> None:
        text = "/- a /- b -/ c -/\ninductive A where | a\n  deriving BEq, DecidableEq\n"
        f = self.audit(text)
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["line"], 3)

    def test_string_literal(self) -> None:
        text = 'def s := "deriving BEq, DecidableEq -- /- not a comment"\ndef t := 1\n'
        self.assertEqual(self.audit(text), [])

    def test_string_with_escaped_quote(self) -> None:
        text = 'def s := "a \\" deriving BEq, DecidableEq"\ninductive A where | a\n  deriving BEq, DecidableEq\n'
        f = self.audit(text)
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["line"], 3)

    def test_raw_string(self) -> None:
        text = 'def s := r#"deriving BEq, DecidableEq " still raw"#\ndef t := r"x"\n'
        self.assertEqual(self.audit(text), [])

    def test_interpolated_string(self) -> None:
        text = 'def s := s!"deriving {"BEq"}, DecidableEq {1 + 1}"\n'
        self.assertEqual(self.audit(text), [])

    def test_interpolated_string_nested_braces_in_chars_raw_guillemets(self) -> None:
        text = (
            'def s1 := s!"prefix {\'{\'} {\'\\\'\'} {r#"{"#} {«{»} {s!"inner {\'}\'}"} deriving BEq, DecidableEq"\n'
            'inductive RealAfterInterp where | a\n'
            '  deriving BEq, DecidableEq\n'
        )
        f = self.audit(text)
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["line"], 3)

    def test_escaped_single_quote_char_literal(self) -> None:
        text = "def q := '\\''\ninductive A where | a\n  deriving BEq, DecidableEq\n"
        f = self.audit(text)
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["line"], 3)

    def test_parenthesized_deriving_classes_and_args(self) -> None:
        text = (
            "inductive A where | a\n"
            "  deriving (BEq), (DecidableEq)\n"
            "structure B where\n"
            "  x : Nat\n"
            "  deriving CustomHandler (opt1 opt2), BEq, DecidableEq\n"
            "deriving instance (BEq), _root_.DecidableEq for (Foo), Bar\n"
        )
        f = self.audit(text)
        self.assertEqual([x["line"] for x in f], [2, 5, 6])
        self.assertEqual(f[2]["targets"], ["Foo", "Bar"])

    def test_guillemet_identifier(self) -> None:
        text = 'def «deriving BEq, DecidableEq» := 1\ndef «a -- b» := 2\ninductive A where | a\n  deriving DecidableEq\n'
        self.assertEqual(self.audit(text), [])

    def test_char_literal_and_primes(self) -> None:
        text = "def c := '\"'\ndef x' := 1\ninductive A where | a\n  deriving BEq, DecidableEq\n"
        f = self.audit(text)
        self.assertEqual(len(f), 1)
        self.assertEqual(f[0]["line"], 4)

    def test_identifier_containing_deriving(self) -> None:
        self.assertEqual(self.audit("def derivingBEq := 1\ndef notderiving := BEq\n"), [])

    def test_rust_codegen_literals(self) -> None:
        rust = ('fn emit(out: &mut String) {\n'
                '    // out.push_str("  deriving BEq, DecidableEq\\n");\n'
                '    let q = \'"\';\n'
                '    out.push_str("  deriving BEq, DecidableEq\\n");\n'
                '    out.push_str(r#"deriving instance DecidableEq, BEq for T"#);\n'
                '    out.push_str("  deriving DecidableEq, Repr\\n");\n'
                '    /* nested /* "deriving BEq, DecidableEq" */ */\n'
                '}\n')
        f = bench.audit_rust_codegen_text(rust, "x.rs")
        self.assertEqual([(x["line"], x["kind"]) for x in f], [(4, "deriving_codegen"), (5, "deriving_instance_codegen")])

    def test_rust_lifetimes_do_not_open_chars(self) -> None:
        rust = "fn f<'a>(x: &'a str) -> &'a str { x }\nconst S: &str = \"deriving BEq, DecidableEq\";\n"
        f = bench.audit_rust_codegen_text(rust, "y.rs")
        self.assertEqual([x["line"] for x in f], [2])

    def test_multiple_occurrences(self) -> None:
        text = ("inductive A where | a\n  deriving BEq, DecidableEq\n"
                "structure B where\n  x : Nat\n  deriving DecidableEq, BEq\n"
                "deriving instance DecidableEq, BEq for C\n")
        self.assertEqual([x["line"] for x in self.audit(text)], [2, 5, 6])


class RepoConsistencyTest(unittest.TestCase):
    def test_repo_audit_structure(self) -> None:
        audit = bench.audit_redundant_beq_decidable_eq()
        self.assertGreater(audit["lean_files_scanned"], 0)
        self.assertGreater(audit["rust_files_scanned"], 0)
        self.assertEqual(audit["occurrences"], len(audit["findings"]))
        self.assertEqual(audit["occurrences"], sum(r["occurrences"] for r in audit["by_root"].values()))
        self.assertEqual(set(audit["by_root"]), {"theory", "crates"})
        for f in audit["findings"]:
            self.assertTrue((REPO_ROOT / f["path"]).is_file())
            last = {c.rsplit(".", 1)[-1] for c in f["classes"]}
            self.assertTrue({"BEq", "DecidableEq"} <= last)

    def test_repo_audit_matches_per_file_scan(self) -> None:
        audit = bench.audit_redundant_beq_decidable_eq()
        recount = 0
        for root in ("theory", "crates"):
            for f in sorted((REPO_ROOT / root).rglob("*")):
                if any(part in (".lake", "build", "target", "node_modules") for part in f.relative_to(REPO_ROOT / root).parts):
                    continue
                if f.suffix == ".lean" and f.is_file():
                    recount += len(bench.audit_redundant_beq_decidable_eq_text(f.read_text(encoding="utf-8")))
                elif f.suffix == ".rs" and f.is_file():
                    recount += len(bench.audit_rust_codegen_text(f.read_text(encoding="utf-8")))
        self.assertEqual(recount, audit["occurrences"])

    def test_prototype_has_no_beq(self) -> None:
        findings = bench.audit_redundant_beq_decidable_eq_text(PROTOTYPE.read_text(encoding="utf-8"))
        self.assertEqual(findings, [])
        toks = bench.tokenize_lean(PROTOTYPE.read_text(encoding="utf-8"))
        for i, (kind, val, _line) in enumerate(toks):
            if kind == "ident" and val == "deriving":
                j = i + 1
                if j < len(toks) and toks[j][1] == "instance":
                    j += 1
                self.assertNotEqual(toks[j][1], "BEq", f"prototype derives BEq at token {i}")

    def test_proof_health_zero_findings(self) -> None:
        proc = subprocess.run([sys.executable, "-B", str(REPO_ROOT / "tools/anneal-lsp/server/proof_health.py"),
                               str(PROTOTYPE.relative_to(REPO_ROOT))], cwd=REPO_ROOT, capture_output=True,
                              text=True, check=False, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)

    def test_prototype_forbidden_tokens(self) -> None:
        text = PROTOTYPE.read_text(encoding="utf-8")
        marker = "/-! ## Bottom-of-file axiom audit"
        self.assertIn(marker, text)
        body, audit = text.split(marker, 1)
        audit = marker + audit
        body_toks = {v for k, v, _ in bench.tokenize_lean(body) if k == "ident"}
        for bad in ("sorry", "admit", "native_decide", "axiom", "partial", "unsafe", "private",
                    "implemented_by", "extern", "Classical.choice", "Classical.em", "Lean.ofReduceBool",
                    "sorryAx"):
            self.assertNotIn(bad, body_toks, bad)
        # The forbidden axioms are named only by the audit's own self-test.
        audit_toks = [v for k, v, _ in bench.tokenize_lean(audit) if k == "ident"]
        for bad in ("sorry", "admit", "native_decide", "axiom", "partial", "unsafe", "private"):
            self.assertNotIn(bad, audit_toks, bad)

    def test_audit_cli_json(self) -> None:
        proc = subprocess.run([sys.executable, "-B", str(BENCH_PATH), "--audit-only", "--json"], cwd=REPO_ROOT,
                              capture_output=True, text=True, check=False)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertIn("repo_audit", payload)
        self.assertNotIn("benchmark", payload)

    def test_a1_headline_theorems_present(self) -> None:
        text = PROTOTYPE.read_text(encoding="utf-8")
        ident_toks = {v for k, v, _ in bench.tokenize_lean(text) if k == "ident"}
        for name in (
            "decEqOfCtorIdxProto",
            "instDecidableEqBinOpProto",
            "instDecidableEqRetagKindProto",
            "collectMatchingTraitImpls_of_no_impl",
            "lookupCallee_hit_free_poly",
            "canary_free_poly_param_and_concrete",
            "dyn_vtablePtr_atCall",
            "dyn_step_missing_receiver_ub",
            "stepBranchPruned_redirect_of_not_demanded",
            "dynDemandStep_eq_dynDispatchStep_of_resolved",
            "dynDemandStep_eq_trusted_of_not_demanded",
            "DynStepPreserved",
            "evalDynWithOpaqueCallees_preserved",
            "dynStepPreservedB",
            "dynStepPreserved_of_check",
            "evalDynWithOpaqueCallees_preserved_of_check",
            "canary_dyn_two_receivers",
            "canary_dyn_two_receivers_preserved",
        ):
            self.assertIn(name, ident_toks, f"missing A1 theorem: {name}")

    def test_no_enum_deriving_for_trusted_types(self) -> None:
        # Lean's enumeration `deriving instance DecidableEq` handler emits global
        # `T.ofNat` / `T.ofNat_ctorIdx` constants in the *Trusted* type's namespace,
        # which collide with `Anneal.Rustc.V2026_06_01.TraceCheck` (imported by the
        # `Anneal` root). The nine enumeration types must use the prototype-local
        # `decEqOfCtorIdxProto` instances instead.
        text = PROTOTYPE.read_text(encoding="utf-8")
        enums = ("AbiPassMode", "UintTy", "IntTy", "FloatTy", "Mutability", "Safety", "UnOp",
                 "BinOp", "RetagKind")
        toks = bench.tokenize_lean(text)
        derived: list[str] = []
        for i, (kind, val, _) in enumerate(toks):
            if kind == "ident" and val == "deriving" and i + 1 < len(toks) and toks[i + 1][1] == "instance":
                j = i + 2
                while j < len(toks) and toks[j][1] != "for":
                    j += 1
                if j + 1 < len(toks):
                    derived.append(toks[j + 1][1])
        self.assertGreater(len(derived), 50)
        for target in derived:
            self.assertNotIn(target.rsplit(".", 1)[-1], enums, target)
        for e in enums:
            self.assertIn(f"instDecidableEq{e}Proto", {v for k, v, _ in toks if k == "ident"}, e)

    def test_b1_headline_theorems_present(self) -> None:
        text = PROTOTYPE.read_text(encoding="utf-8")
        ident_toks = {v for k, v, _ in bench.tokenize_lean(text) if k == "ident"}
        for name in (
            "valueStructEq_iff",
            "capturedMir_beq_iff_eq",
            "machineState_beq_iff_eq",
            "lookupCallee_hit_poly",
            "lookupCallee_trait_hit_poly",
            "lookupCallee_trait_default_hit",
            "canary_trait_specificity_and_default_inheritance",
            "canary_evalWithOpaqueCallees_eq_trusted",
            "computeLayout_bridge_commutes",
            "computeLayoutV08Bridged_eq_computeLayoutV06_bridge",
            "evalLayoutOf_v08_eq_v06",
            "fnAbiMismatch?_eq_none_iff",
            "abiCore_ok_iff",
            "syncStorageRegion_blocks_zero_size",
            "envExtends_schema12_ignored_fields_canary",
            "dynDemandStep_preserved",
            "canary_dyn_e2e_full_run_schema13",
            "canary_dyn_deadBranch_schema12_succeeds",
        ):
            self.assertIn(name, ident_toks, f"missing B1 theorem: {name}")


class RealLeanBenchmarkTest(unittest.TestCase):
    result: dict

    @classmethod
    def setUpClass(cls) -> None:
        cls.before = git_status()
        cls.result = bench.run_benchmark([4, 16], reps=1)
        cls.after = git_status()

    def hb(self, m: int, v: str) -> float:
        return self.result["results"][str(m)][v]["heartbeats"]

    def test_all_variants_measured(self) -> None:
        for m in (4, 16):
            for v in bench.VARIANTS + bench.CERT_LABELS:
                self.assertGreater(self.hb(m, v), 0, (m, v))

    def test_linear_list_grows(self) -> None:
        self.assertGreater(self.hb(16, "linear_list"), 2.0 * self.hb(4, "linear_list"))

    def test_opaque_flat(self) -> None:
        for v in ("opaque_o1", "opaque_pruned"):
            self.assertLess(self.hb(16, v), 1.5 * self.hb(4, v), v)
            self.assertLess(self.result["scaling"][v]["heartbeats_loglog_slope"], 0.25, v)

    def test_opaque_beats_linear(self) -> None:
        self.assertLess(self.hb(16, "opaque_o1"), self.hb(16, "linear_list"))
        self.assertLess(self.hb(16, "opaque_pruned"), self.hb(16, "opaque_o1") * 1.05)

    def test_certificate_generation_is_linear_and_amortized(self) -> None:
        self.assertGreater(self.hb(16, "cert_gen_live"), 2.0 * self.hb(4, "cert_gen_live"))

    def test_worktree_untouched_by_benchmark(self) -> None:
        self.assertEqual(self.before, self.after)

    def test_prototype_coimports_with_anneal_root(self) -> None:
        # The compiled prototype must be importable alongside the `Anneal` root
        # (whose `Anneal.Rustc.V2026_06_01.TraceCheck` derives `DecidableEq` for the
        # same `Trusted` enumeration types): no duplicate global constants.
        co = self.result["coimport"]
        self.assertEqual(co["imports"][0], "Anneal")
        self.assertTrue(co["ok"], co)
        self.assertEqual(co["exit"], 0)
        self.assertEqual(co["errors"], [])
        for probe in ("import_probe", "reelaborate_probe"):
            self.assertTrue(co[probe]["ok"], (probe, co[probe]))
        self.assertIn("Co-import check", bench.render_markdown(self.result, None))

    def test_json_roundtrip(self) -> None:
        text = json.dumps(self.result)
        self.assertEqual(json.loads(text)["sizes"], [4, 16])
        md = bench.render_markdown(self.result, None)
        self.assertIn("linear_list", md)


class WorktreePollutionTest(unittest.TestCase):
    def test_no_pycache_in_scripts(self) -> None:
        self.assertEqual(find_pycache(), [])

    def test_probe_generation_is_pure(self) -> None:
        before = git_status()
        text = bench.generate_probe(4, 1)
        self.assertIn("bench_crate::module_0003::callee_0003", text)
        self.assertIn("#bench_hb \"opaque_pruned\"", text)
        with tempfile.TemporaryDirectory(dir="/tmp") as tmp:
            (Path(tmp) / "Probe.lean").write_text(text, encoding="utf-8")
        self.assertEqual(before, git_status())

    def test_only_deliverables_differ(self) -> None:
        """Only the four prototype deliverables may be new / modified (before or
        after committing), and the branch diff vs. the base contains only `A`
        entries for them."""
        for line in git_status().splitlines():
            path = line[3:].strip()
            self.assertIn(path, DELIVERABLES, f"unexpected worktree change: {line}")
        diff = subprocess.run(["git", "diff", "--name-status", f"{BASE_SHA}..HEAD"], cwd=REPO_ROOT,
                              capture_output=True, text=True, check=True).stdout
        for line in diff.splitlines():
            status, path = line.split("\t", 1)
            self.assertEqual(status, "A", line)
            self.assertIn(path, DELIVERABLES, line)


if __name__ == "__main__":
    unittest.main()
