#!/usr/bin/env python3
"""Comprehensive positive & red-team unit test suite for Track P prototype:
- Cross-language wire schema parity & TrustedBoundary / check_trusted hygiene
- Pillar 1: lean4#16717 forged-inductive replay integrity + live .olean check
- Pillar 2: grmf cl/1029226310 sharded audit + <0.25s --orphan-only + cross-shard chains
- Pillar 3: 4 peer-verifier spec guards (creusot#2388, creusot#2389, verus#3514, Verifrag + Samite)
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
TRUSTED_AUDIT_DIR = REPO_ROOT / "trusted" / "audit"

if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))
if str(TRUSTED_AUDIT_DIR) not in sys.path:
    sys.path.insert(0, str(TRUSTED_AUDIT_DIR))

import check_trusted  # noqa: E402
import proto_sharded_audit_and_inductive_replay as proto  # noqa: E402

PROTO_LEAN_FILE = (
    REPO_ROOT
    / "theory"
    / "Anneal"
    / "Proto"
    / "InductiveReplayAndPeerSpecGuardsProto.lean"
)


def _make_valid_unit_and_nat_fixture() -> tuple[
    dict[str, dict], dict[str, dict], dict[str, dict]
]:
    unit_ind = {
        "name": "Unit",
        "kind": "inductive",
        "level_params": [],
        "type": "Type",
        "num_params": 0,
        "num_indices": 0,
        "all": ["Unit"],
        "ctors": ["Unit.unit"],
        "is_rec": False,
        "is_reflexive": False,
        "is_unsafe": False,
    }
    unit_ctor = {
        "name": "Unit.unit",
        "kind": "constructor",
        "level_params": [],
        "type": "Unit",
        "induct": "Unit",
        "cidx": 0,
        "num_params": 0,
        "num_fields": 0,
    }
    nat_ind = {
        "name": "Nat",
        "kind": "inductive",
        "level_params": [],
        "type": "Type",
        "num_params": 0,
        "num_indices": 0,
        "all": ["Nat"],
        "ctors": ["Nat.zero", "Nat.succ"],
        "is_rec": True,
        "is_reflexive": False,
        "is_unsafe": False,
    }
    nat_zero = {
        "name": "Nat.zero",
        "kind": "constructor",
        "level_params": [],
        "type": "Nat",
        "induct": "Nat",
        "cidx": 0,
        "num_params": 0,
        "num_fields": 0,
    }
    nat_succ = {
        "name": "Nat.succ",
        "kind": "constructor",
        "level_params": [],
        "type": "Nat -> Nat",
        "induct": "Nat",
        "cidx": 1,
        "num_params": 0,
        "num_fields": 1,
    }
    consts = {
        "Unit": unit_ind,
        "Unit.unit": unit_ctor,
        "Nat": nat_ind,
        "Nat.zero": nat_zero,
        "Nat.succ": nat_succ,
    }
    k_ind = {"Unit": dict(unit_ind), "Nat": dict(nat_ind)}
    k_ctor = {
        "Unit.unit": dict(unit_ctor),
        "Nat.zero": dict(nat_zero),
        "Nat.succ": dict(nat_succ),
    }
    return consts, k_ind, k_ctor


class TestCrossLanguageParityAndHygiene(unittest.TestCase):
    def test_01_wire_schema_parity_with_lean_file(self) -> None:
        lean_text = PROTO_LEAN_FILE.read_text(encoding="utf-8")
        # Every rank, guard_id, canonical_name, vacuity_class appears verbatim in PeerSpecGuardClass.wire_table
        for g in proto.PEER_SPEC_GUARDS:
            self.assertIn(f'"{g["guard_id"]}"', lean_text)
            self.assertIn(f'"{g["canonical_name"]}"', lean_text)
            self.assertIn(f'"{g["vacuity_class"]}"', lean_text)
        # All 12 + 9 + 6 violation codes match Lean 1-for-1
        for code in proto.INDUCTIVE_REPLAY_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        for code in proto.SHARD_AUDIT_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        for code in proto.PEER_GUARD_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        self.assertEqual(len(proto.INDUCTIVE_REPLAY_VIOLATION_CODES), 12)
        self.assertEqual(len(proto.SHARD_AUDIT_VIOLATION_CODES), 9)
        self.assertEqual(len(proto.PEER_GUARD_VIOLATION_CODES), 6)

    def test_02_ranks_and_ids_disjoint_from_baseline_spec_boundary_guards(self) -> None:
        base_ranks = {g["rank"] for g in proto.SPEC_BOUNDARY_GUARDS}
        peer_ranks = {g["rank"] for g in proto.PEER_SPEC_GUARDS}
        self.assertEqual(base_ranks, {0, 1, 2})
        self.assertEqual(peer_ranks, {3, 4, 5, 6})
        self.assertTrue(base_ranks.isdisjoint(peer_ranks))
        base_ids = {g["guard_id"] for g in proto.SPEC_BOUNDARY_GUARDS}
        peer_ids = {g["guard_id"] for g in proto.PEER_SPEC_GUARDS}
        self.assertTrue(base_ids.isdisjoint(peer_ids))
        base_names = {g["canonical_name"] for g in proto.SPEC_BOUNDARY_GUARDS}
        peer_names = {g["canonical_name"] for g in proto.PEER_SPEC_GUARDS}
        self.assertTrue(base_names.isdisjoint(peer_names))

    def test_03_lean_proto_passes_check_trusted_audit_file_zero_findings(self) -> None:
        findings = check_trusted.audit_file(
            PROTO_LEAN_FILE, check_3axis=True, vacuity_scope="all"
        )
        self.assertEqual(findings, [], f"Unexpected check_trusted findings: {findings}")

    def test_04_lean_proto_passes_trusted_boundary_inspect_source(self) -> None:
        res = proto.run_trusted_boundary_inspect_source(
            REPO_ROOT,
            "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto",
            PROTO_LEAN_FILE,
        )
        self.assertTrue(res.get("ok"), f"TrustedBoundary.inspectSource failed: {res}")
        self.assertEqual(res.get("returncode"), 0)

    def test_05_no_bare_mkdtemp_in_prototype_python_files(self) -> None:
        for path in (
            SCRIPTS_DIR / "proto_sharded_audit_and_inductive_replay.py",
            SCRIPTS_DIR / "test_proto_sharded_audit_and_inductive_replay.py",
        ):
            src = path.read_text(encoding="utf-8")
            self.assertNotIn("tempfile." + "mkdtemp(", src)


class TestPillar1InductiveReplay(unittest.TestCase):
    def test_06_fake_false_passes_vulnerable_replay_but_caught_by_hardened_check(self) -> None:
        consts, k_ind, k_ctor = _make_valid_unit_and_nat_fixture()
        consts["FakeFalse"] = {
            "name": "FakeFalse",
            "kind": "inductive",
            "level_params": [],
            "type": "Prop",
            "num_params": 0,
            "num_indices": 0,
            "all": ["Unit"],
            "ctors": [],
            "is_rec": False,
            "is_reflexive": False,
            "is_unsafe": False,
        }
        vuln = proto.simulate_vulnerable_replay(consts, k_ind, k_ctor)
        self.assertTrue(vuln["accepted"])
        self.assertNotIn("FakeFalse", vuln["replayed_inductives"])

        viols = proto.check_inductive_replay_integrity(consts, k_ind, k_ctor)
        codes = {v["code"] for v in viols}
        self.assertIn("self_not_in_all", codes)

    def test_07_forged_indices_and_is_rec_passes_vulnerable_but_caught_by_postponed_check(self) -> None:
        consts, k_ind, k_ctor = _make_valid_unit_and_nat_fixture()
        consts["Nat"]["num_indices"] = 1
        consts["Nat"]["is_rec"] = False
        vuln = proto.simulate_vulnerable_replay(consts, k_ind, k_ctor)
        self.assertTrue(vuln["accepted"])

        viols = proto.check_inductive_replay_integrity(consts, k_ind, k_ctor)
        codes = {v["code"] for v in viols}
        self.assertIn("indices_mismatch", codes)
        self.assertIn("is_rec_mismatch", codes)

    def test_08_all_twelve_inductive_violation_codes_caught(self) -> None:
        # 1. key_mismatch
        c, ki, kc = _make_valid_unit_and_nat_fixture()
        c["WrongKey"] = c.pop("Unit")
        self.assertIn("key_mismatch", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 2. self_not_in_all
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit"]["all"] = ["Nat"]
        self.assertIn("self_not_in_all", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 3. duplicate_in_all
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit"]["all"] = ["Unit", "Unit"]
        self.assertIn("duplicate_in_all", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 4. non_induct_in_all
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit"]["all"] = ["Unit", "NotInd"]
        c["NotInd"] = {"name": "NotInd", "kind": "definition"}
        self.assertIn("non_induct_in_all", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 5. mutual_metadata_mismatch
        mut_a = {
            "name": "MutA", "kind": "inductive", "level_params": ["u"], "type": "Type",
            "num_params": 1, "num_indices": 0, "all": ["MutA", "MutB"], "ctors": [],
            "is_rec": False, "is_reflexive": False, "is_unsafe": False,
        }
        mut_b = dict(mut_a, name="MutB", num_params=2)
        self.assertIn(
            "mutual_metadata_mismatch",
            {v["code"] for v in proto.check_inductive_replay_integrity({"MutA": mut_a, "MutB": mut_b})},
        )

        # 6. duplicate_in_ctors
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit"]["ctors"] = ["Unit.unit", "Unit.unit"]
        self.assertIn("duplicate_in_ctors", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 7. non_ctor_in_ctors
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit"]["ctors"] = ["FakeCtor"]
        c["FakeCtor"] = {"name": "FakeCtor", "kind": "definition"}
        self.assertIn("non_ctor_in_ctors", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 8. ctor_induct_mismatch
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit.unit"]["induct"] = "Nat"
        self.assertIn("ctor_induct_mismatch", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 9. ctor_cidx_mismatch
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit.unit"]["cidx"] = 7
        self.assertIn("ctor_cidx_mismatch", {v["code"] for v in proto.check_inductive_replay_integrity(c)})

        # 10. dangling_ctor_not_listed_in_induct
        c, _, _ = _make_valid_unit_and_nat_fixture()
        c["Unit.dangling"] = dict(c["Unit.unit"], name="Unit.dangling", cidx=1)
        self.assertIn(
            "dangling_ctor_not_listed_in_induct",
            {v["code"] for v in proto.check_inductive_replay_integrity(c)},
        )

        # 11 & 12. indices_mismatch & is_rec_mismatch
        c, ki, kc = _make_valid_unit_and_nat_fixture()
        c["Nat"]["num_indices"] = 3
        c["Nat"]["is_rec"] = False
        post_codes = {v["code"] for v in proto.check_inductive_replay_integrity(c, ki, kc)}
        self.assertIn("indices_mismatch", post_codes)
        self.assertIn("is_rec_mismatch", post_codes)

    def test_09_valid_mutual_inductive_block_passes_cleanly(self) -> None:
        mut_a = {
            "name": "Even", "kind": "inductive", "level_params": [], "type": "Nat -> Prop",
            "num_params": 0, "num_indices": 1, "all": ["Even", "Odd"], "ctors": ["Even.zero"],
            "is_rec": True, "is_reflexive": False, "is_unsafe": False,
        }
        mut_b = {
            "name": "Odd", "kind": "inductive", "level_params": [], "type": "Nat -> Prop",
            "num_params": 0, "num_indices": 1, "all": ["Even", "Odd"], "ctors": ["Odd.succ"],
            "is_rec": True, "is_reflexive": False, "is_unsafe": False,
        }
        c_a = {
            "name": "Even.zero", "kind": "constructor", "level_params": [], "type": "Even 0",
            "induct": "Even", "cidx": 0, "num_params": 0, "num_fields": 0,
        }
        c_b = {
            "name": "Odd.succ", "kind": "constructor", "level_params": [], "type": "Odd 1",
            "induct": "Odd", "cidx": 0, "num_params": 0, "num_fields": 0,
        }
        consts = {"Even": mut_a, "Odd": mut_b, "Even.zero": c_a, "Odd.succ": c_b}
        viols = proto.check_inductive_replay_integrity(
            consts, {"Even": mut_a, "Odd": mut_b}, {"Even.zero": c_a, "Odd.succ": c_b}
        )
        self.assertEqual(viols, [])

    def test_10_live_olean_inspection_on_trusted_and_proto_zero_violations(self) -> None:
        res = proto.inspect_live_oleans(
            REPO_ROOT,
            import_modules=["Trusted", "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"],
            exact_modules=["Trusted", "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"],
        )
        self.assertEqual(res["violations"], [], f"Unexpected live .olean violations: {res}")
        self.assertEqual(res["modules_checked"], 2)
        self.assertGreater(res["inductives_checked"], 0)
        self.assertGreater(res["ctors_checked"], 0)
        self.assertTrue(set(res["axioms_reached"]).issubset(proto.PERMITTED_FOUNDATIONAL_AXIOMS))


class TestPillar2ShardedAuditAndOrphanGate(unittest.TestCase):
    def test_11_eight_shard_planner_covers_all_discovered_modules_nonempty_disjoint(self) -> None:
        plan = proto.plan_subsystem_shards(REPO_ROOT)
        self.assertEqual(tuple(plan["shard_names"]), proto.SUBSYSTEM_SHARD_NAMES)
        self.assertEqual(len(plan["shards"]), 8)
        for name, mods in plan["shards"].items():
            self.assertGreater(len(mods), 0, f"Shard {name} is unexpectedly empty")
        discovered = sorted(proto.discover_repo_modules(REPO_ROOT).keys())
        viols = proto.check_shard_partition(
            discovered, discovered, [plan["shards"][n] for n in proto.SUBSYSTEM_SHARD_NAMES]
        )
        self.assertEqual(viols, [])

    def test_12_orphan_only_gate_runs_under_250ms_on_live_repo(self) -> None:
        res = proto.run_orphan_only_gate(REPO_ROOT)
        self.assertTrue(res["ok"], f"Orphan-only gate failed: {res}")
        self.assertTrue(res["under_250ms"], f"Expected <0.25s, got {res['elapsed_sec']}s")
        self.assertLess(res["elapsed_sec"], 0.25)
        self.assertGreater(res["on_disk_count"], 150)

    def test_13_shard_partition_catches_all_seven_malformed_partition_cases(self) -> None:
        self.assertIn("empty_shard_list", {v["code"] for v in proto.check_shard_partition(["A"], ["A"], [])})
        self.assertIn("empty_shard", {v["code"] for v in proto.check_shard_partition(["A"], ["A"], [["A"], []])})
        self.assertIn(
            "duplicate_module_in_shard",
            {v["code"] for v in proto.check_shard_partition(["A"], ["A"], [["A", "A"]])},
        )
        self.assertIn(
            "overlapping_shards",
            {v["code"] for v in proto.check_shard_partition(["A", "B"], ["A", "B"], [["A", "B"], ["B"]])},
        )
        self.assertIn(
            "unregistered_module_in_shard",
            {v["code"] for v in proto.check_shard_partition(["A"], ["A"], [["A", "Foreign"]])},
        )
        self.assertIn(
            "uncovered_registered_module",
            {v["code"] for v in proto.check_shard_partition(["A", "B"], ["A", "B"], [["A"]])},
        )
        self.assertIn(
            "unregistered_on_disk_orphan",
            {v["code"] for v in proto.check_shard_partition(["A"], ["A", "Orphan"], [["A"]])},
        )

    def test_14_three_hop_cross_shard_bad_axiom_caught_by_shard1(self) -> None:
        env = {
            "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "decls": [
                {"name": "M1.entry", "origin_mod": "M1", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["M2.mid"]},
                {"name": "M2.mid", "origin_mod": "M2", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["M3.leaf"]},
                {"name": "M3.leaf", "origin_mod": "M3", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["M3.badAxiom"]},
                {"name": "M3.badAxiom", "origin_mod": "M3", "is_axiom": True, "is_unsafe_or_partial": False, "direct_deps": []},
            ],
        }
        res_s1 = proto.audit_repo_graph_exact_modules(env, ["M1"])
        self.assertFalse(res_s1["ok"])
        self.assertIn("M3.badAxiom", res_s1["axioms_reached"])
        self.assertEqual(res_s1["violations"][0]["code"], "disallowed_transitive_axiom")

    def test_15_cross_shard_diamond_and_cycle_terminates_and_matches_monolithic(self) -> None:
        env = {
            "permitted_axioms": ["propext"],
            "decls": [
                {"name": "M1.a", "origin_mod": "M1", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["M2.b", "M3.c"]},
                {"name": "M2.b", "origin_mod": "M2", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["M3.c", "M1.a"]},
                {"name": "M3.c", "origin_mod": "M3", "is_axiom": False, "is_unsafe_or_partial": False, "direct_deps": ["propext"]},
                {"name": "propext", "origin_mod": "Init", "is_axiom": True, "is_unsafe_or_partial": False, "direct_deps": []},
            ],
        }
        mono = proto.audit_repo_graph_exact_modules(env, ["M1", "M2", "M3"])
        s1 = proto.audit_repo_graph_exact_modules(env, ["M1"])
        s2 = proto.audit_repo_graph_exact_modules(env, ["M2"])
        s3 = proto.audit_repo_graph_exact_modules(env, ["M3"])
        self.assertTrue(mono["ok"] and s1["ok"] and s2["ok"] and s3["ok"])
        union_ax = sorted(set(s1["axioms_reached"]) | set(s2["axioms_reached"]) | set(s3["axioms_reached"]))
        self.assertEqual(union_ax, mono["axioms_reached"])

    def test_16_cli_orphan_only_with_modules_and_shard_files_detects_orphan(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-test-sh-") as tmp_str:
            tmp = Path(tmp_str)
            mods_file = tmp / "mods.json"
            shards_file = tmp / "shards.json"
            mods_file.write_text(json.dumps(["Trusted"]), encoding="utf-8")
            shards_file.write_text(json.dumps([["Trusted"]]), encoding="utf-8")
            proc = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPTS_DIR / "proto_sharded_audit_and_inductive_replay.py"),
                    "--orphan-only",
                    "--modules-file",
                    str(mods_file),
                    "--shard-modules-file",
                    str(shards_file),
                ],
                cwd=str(REPO_ROOT),
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 1)
            payload = json.loads(proc.stdout)
            self.assertFalse(payload["ok"])
            self.assertIn("unregistered_on_disk_orphan", {v["code"] for v in payload["violations"]})


class TestPillar3Guard3UnsatisfiableExternEnsures(unittest.TestCase):
    def test_17_catches_external_spec_ensures_false_on_read_volatile(self) -> None:
        src = """
        #[external_spec(
            for = core::ptr::read_volatile,
            ensures: |_ret| false,
        )]
        unsafe fn spec_read_volatile<T>(src: *const T) -> T;
        """
        hits = proto.scan_rust_unsatisfiable_extern_ensures(src)
        self.assertEqual(len(hits), 1)
        self.assertEqual(hits[0]["code"], "unsatisfiable_extern_ensures")
        self.assertEqual(hits[0]["rank"], 3)

    def test_18_catches_extern_block_and_contradictory_ensures(self) -> None:
        src = """
        extern "C" {
            #[ensures(ret != ret)]
            fn c_read_u32(p: *const u32) -> u32;

            #[ensures(x > 0 && !(x > 0))]
            fn c_contradict(x: u32) -> u32;
        }
        """
        hits = proto.scan_rust_unsatisfiable_extern_ensures(src)
        self.assertEqual(len(hits), 2)
        self.assertEqual({h["subject"] for h in hits}, {"c_read_u32", "c_contradict"})

    def test_19_allows_diverging_bang_and_unreachable_requires_false(self) -> None:
        src = """
        #[external_spec(for = core::intrinsics::abort, ensures: |_| false)]
        fn spec_abort() -> !;

        extern "C" {
            #[ensures(false)]
            fn exit(code: i32) -> !;
        }

        #[external_spec(
            for = core::hint::unreachable_unchecked,
            requires: false,
            ensures: |_| false,
        )]
        unsafe fn spec_unreachable() -> u32;
        """
        self.assertEqual(proto.scan_rust_unsatisfiable_extern_ensures(src), [])

    def test_20_ignores_comments_raw_strings_and_dead_false_if_else_true(self) -> None:
        src = r'''
        // #[external_spec(for = foo, ensures: |_| false)] fn commented() -> u32;
        /* /* #[external_spec(for = bar, ensures: |_| false)] fn nested_comment() -> u32; */ */
        const S: &str = r#"#[external_spec(for = baz, ensures: |_| false)] fn in_raw() -> u32;"#;
        #[external_spec(
            for = u32::wrapping_add,
            ensures: |ret| if false { ret == 5 } else { true },
        )]
        fn ok_if_else(a: u32, b: u32) -> u32;
        '''
        self.assertEqual(proto.scan_rust_unsatisfiable_extern_ensures(src), [])


class TestPillar3Guard4FnDefGhostTokenCoercion(unittest.TestCase):
    def test_21_catches_fndef_value_bind_coercion_higher_order_and_closure(self) -> None:
        src = """
        fn bad() {
            let f = Tokens::new;
            let g: fn() -> Tokens = creusot_std::ghost::Tokens::new;
            call_twice(Tokens::new);
            let h = Tokens::new::<()> as fn() -> Tokens;
            let c = || Tokens::new();
        }
        """
        hits = proto.scan_rust_fndef_ghost_token_coercion(src)
        self.assertEqual(len(hits), 5)
        self.assertTrue(all(h["code"] == "fndef_ghost_token_coercion" for h in hits))
        self.assertTrue(all(h["rank"] == 4 for h in hits))

    def test_22_catches_custom_ghost_token_ctor_and_use_aliases(self) -> None:
        src = """
        use crate::ghost::Tokens as MyTok;
        use crate::ghost::Tokens::new as mk_tok;

        struct Auth;
        impl Auth {
            #[ghost_token_ctor]
            fn issue() -> Self { Auth }
        }

        fn exploit() {
            let a = MyTok::new;
            let b = mk_tok;
            call_twice(Auth::issue);
        }
        """
        hits = proto.scan_rust_fndef_ghost_token_coercion(src)
        self.assertEqual(len(hits), 3)
        self.assertEqual({h["subject"] for h in hits}, {"MyTok::new", "mk_tok", "Auth::issue"})

    def test_23_allows_direct_call_and_ignores_comments_strings_chars(self) -> None:
        src = r'''
        // let f = Tokens::new;
        /* /* call_twice(Tokens::new); */ */
        fn main() {
            let _msg = r#"let f = Tokens::new;"#;
            let _ch = '"';
            let _tok = Tokens::new();
            let _tok2 = creusot_std::ghost::Tokens::new::<()>();
        }
        '''
        self.assertEqual(proto.scan_rust_fndef_ghost_token_coercion(src), [])


class TestPillar3Guard5ExternalTypeDropOmission(unittest.TestCase):
    def test_24_catches_direct_drop_and_transitive_drop_glue(self) -> None:
        src = """
        struct InnerGuard { fd: i32 }
        impl Drop for InnerGuard {
            fn drop(&mut self) {}
        }

        struct OuterWrapper {
            inner: InnerGuard,
        }

        #[external_type_specification]
        struct ExInner(InnerGuard);

        #[external_type_specification]
        struct ExOuter(OuterWrapper);

        #[external_type_specification]
        struct ExVecHolder {
            items: Vec<u8>,
        }
        """
        hits = proto.scan_rust_external_type_drop_omission(src)
        self.assertEqual(len(hits), 3)
        self.assertEqual({h["subject"] for h in hits}, {"ExInner", "ExOuter", "ExVecHolder"})
        self.assertTrue(all(h["code"] == "external_type_drop_omission" for h in hits))

    def test_25_catches_external_type_spec_combined_with_external_body_on_drop(self) -> None:
        src = """
        struct Handle(i32);
        impl core::ops::Drop for Handle {
            fn drop(&mut self) {}
        }

        #[external_type_specification]
        #[external_body]
        #[models_drop]
        struct ExHandle(Handle);
        """
        hits = proto.scan_rust_external_type_drop_omission(src)
        self.assertEqual(len(hits), 1)
        self.assertEqual(hits[0]["code"], "external_type_body_with_drop")
        self.assertEqual(hits[0]["rank"], 5)

    def test_26_allows_copy_manually_drop_phantom_borrowed_and_modeled_drop(self) -> None:
        src = """
        struct DropRes(i32);
        impl Drop for DropRes { fn drop(&mut self) {} }

        #[external_type_specification]
        struct ExPlain {
            x: u64,
            m: core::mem::ManuallyDrop<Box<u8>>,
            p: core::marker::PhantomData<Vec<u8>>,
            r: &'static Vec<u8>,
        }

        #[external_type_specification]
        #[models_drop]
        struct ExModeled(DropRes);
        """
        self.assertEqual(proto.scan_rust_external_type_drop_omission(src), [])


class TestPillar3Guard6AssumptionPolarityAndStructSealing(unittest.TestCase):
    def test_27_catches_positive_polarity_flipped_disjunct_nested_imp_and_double_neg(self) -> None:
        lean_src = """
        theorem flipped_consequent (specRes implRes : EvalRes Nat) :
            (implRes.assertionFailed = false ∧ implRes.output = specRes.output) →
              (specRes.assumesHold = true ∧ implRes.assumesHold = true) := by sorry

        theorem positive_disjunct (specRes implRes : EvalRes Nat) :
            specRes.assumesHold = true →
              (implRes.assumesHold = true ∨ implRes.output = specRes.output) := by sorry

        theorem nested_imp_flip (specRes implRes : EvalRes Nat) :
            ((implRes.assumesHold = true → implRes.output = specRes.output) →
              implRes.assertionFailed = false) := by sorry

        theorem double_neg_positive (implRes : EvalRes Nat) :
            ¬ ¬ (implRes.assumesHold = true) := by sorry

        def bad_prop_def (specRes implRes : EvalRes Nat) : Prop :=
            implRes.output = specRes.output ↔ implRes.assumesHold = true
        """
        hits = proto.scan_lean_assumption_polarity(lean_src)
        self.assertEqual(
            {h["subject"] for h in hits},
            {
                "flipped_consequent",
                "positive_disjunct",
                "nested_imp_flip",
                "double_neg_positive",
                "bad_prop_def",
            },
        )
        self.assertTrue(all(h["code"] == "assumption_positive_polarity" for h in hits))
        self.assertTrue(all(h["rank"] == 6 for h in hits))

    def test_28_allows_negative_polarity_and_ignores_comments_and_interpolated_strings(self) -> None:
        lean_src = '''
        /- /- theorem commented_bad : implRes.assumesHold = true := by sorry -/ -/
        def msg (x : Nat) : String :=
          s!"theorem in_str : {x} implRes.assumesHold = true"

        theorem good_equiv (specRes implRes : EvalRes Nat) :
            (specRes.assumesHold = true ∧ implRes.assumesHold = true ∧
              specRes.assertionFailed = false) →
              (implRes.assertionFailed = false ∧ implRes.output = specRes.output) := by
          sorry
        '''
        self.assertEqual(proto.scan_lean_assumption_polarity(lean_src), [])

    def test_29_samite_struct_sealing_rejects_field_decoy_sibling_masking_and_string_tricks(self) -> None:
        lean_src = '''
        namespace Alpha

        structure SealedSibling where
          private mk ::
          x : Nat

        structure FieldDecoy where
          private mk : Nat
          inv : 0 < mk

        structure UnsealedAfterSibling (tag : String := "where private mk ::") where
          val : Nat

        structure MissingWhere (x : Nat) : Prop

        structure InterpDecoy (s : String := s!"{1} private mk ::") where
          protected mk ::
          val : Nat

        end Alpha
        '''
        targets = {
            "Alpha.SealedSibling",
            "Alpha.FieldDecoy",
            "Alpha.UnsealedAfterSibling",
            "Alpha.MissingWhere",
            "Alpha.InterpDecoy",
        }
        hits = proto.scan_lean_invariant_struct_sealing(lean_src, target_structs=targets)
        self.assertEqual(
            {h["subject"] for h in hits},
            {
                "Alpha.FieldDecoy",
                "Alpha.UnsealedAfterSibling",
                "Alpha.MissingWhere",
                "Alpha.InterpDecoy",
            },
        )
        self.assertTrue(all(h["code"] == "unsealed_invariant_struct" for h in hits))

    def test_30_samite_struct_sealing_accepts_private_mk_with_comments_attrs_and_char_lits(self) -> None:
        lean_src = '''
        namespace Beta

        -- @sealed_invariant
        @[ext]
        structure ProperlySealed (c : Char := '"') (tag : String := "not where") where
          /- nested /- comment -/ before ctor -/
          /-- docstring on ctor -/
          @[inline]
          private mk ::
          val : Nat
          inv : 0 < val

        end Beta
        '''
        self.assertEqual(
            proto.scan_lean_invariant_struct_sealing(
                lean_src, target_structs={"Beta.ProperlySealed"}
            ),
            [],
        )
        self.assertEqual(proto.scan_lean_invariant_struct_sealing(lean_src), [])

    def test_31_live_repo_sweep_zero_false_positives_on_theory_and_anneal_spec(self) -> None:
        res = proto.scan_live_repo_peer_guards(REPO_ROOT)
        self.assertTrue(res["ok"], f"Live repo sweep had false positives: {res['findings']}")
        self.assertEqual(res["finding_count"], 0)
        self.assertGreater(res["lean_files_scanned"], 80)
        self.assertGreaterEqual(res["rust_files_scanned"], 4)


if __name__ == "__main__":
    unittest.main()
