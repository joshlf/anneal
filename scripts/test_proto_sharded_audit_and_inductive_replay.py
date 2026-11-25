#!/usr/bin/env python3
"""Comprehensive positive & red-team unit test suite for Track P prototype:
- Cross-language wire schema parity & TrustedBoundary / check_trusted hygiene
- Pillar 1: lean4#16717 forged-inductive replay integrity + live .olean check
- Pillar 2: grmf cl/1029226310 sharded audit + <0.25s --orphan-only + cross-shard chains
- Pillar 3: 4 peer-verifier spec guards (creusot#2388, creusot#2389, verus#3514, Verifrag + Samite)
"""

from __future__ import annotations

import concurrent.futures
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
        # All 13 + 11 + 6 violation codes match Lean 1-for-1
        for code in proto.INDUCTIVE_REPLAY_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        for code in proto.SHARD_AUDIT_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        for code in proto.PEER_GUARD_VIOLATION_CODES:
            self.assertIn(f'"{code}"', lean_text)
        self.assertEqual(len(proto.INDUCTIVE_REPLAY_VIOLATION_CODES), 13)
        self.assertEqual(len(proto.SHARD_AUDIT_VIOLATION_CODES), 11)
        # Exact ORDER parity: extract each Lean `asStr` table and compare to the Python tuple.
        for ns, codes in (
            ("InductiveReplayViolationCode", proto.INDUCTIVE_REPLAY_VIOLATION_CODES),
            ("ShardAuditViolationCode", proto.SHARD_AUDIT_VIOLATION_CODES),
            ("PeerGuardViolationCode", proto.PEER_GUARD_VIOLATION_CODES),
        ):
            block = lean_text.split(f"namespace {ns}", 1)[1].split("def all", 1)[0]
            self.assertEqual(tuple(re.findall(r'=> "([a-z_]+)"', block)), codes, ns)
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
        base, k_ind, k_ctor = _make_valid_unit_and_nat_fixture()
        # NameSet iteration visits FakeFalse BEFORE Unit (attacker-chosen names).
        consts: dict[str, dict] = {}
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
        consts.update(base)
        vuln = proto.simulate_vulnerable_replay(consts, k_ind, k_ctor)
        self.assertTrue(vuln["accepted"], vuln)
        self.assertNotIn("FakeFalse", vuln["replayed_inductives"])

        viols = proto.check_inductive_replay_integrity(consts, k_ind, k_ctor)
        codes = {v["code"] for v in viols}
        self.assertIn("self_not_in_all", codes)

    def test_06b_vulnerable_model_is_faithful_order_sensitive_and_checks_recursors(self) -> None:
        """B1: mirrors Lean `fakeFalse_unitFirst_rejected_by_vulnerable_kernel` and
        `fakeFalseWithRec_rejected_by_vulnerable_postponedRecursors`."""
        base, k_ind, k_ctor = _make_valid_unit_and_nat_fixture()
        fake = {
            "name": "FakeFalse", "kind": "inductive", "level_params": [], "type": "Prop",
            "num_params": 0, "num_indices": 0, "all": ["Unit"], "ctors": [],
            "is_rec": False, "is_reflexive": False, "is_unsafe": False,
        }
        # Unit visited first: the second `inductDecl [Unit]` is "already declared".
        unit_first = dict(base)
        unit_first["FakeFalse"] = fake
        res = proto.simulate_vulnerable_replay(unit_first, k_ind, k_ctor)
        self.assertFalse(res["accepted"])
        self.assertIn("already declared", res["error"])
        # Shipping the eliminator FakeFalse.rec is caught by 4.34.1 checkPostponedRecursors.
        k_rec = {
            "Unit.rec": {"name": "Unit.rec", "kind": "recursor", "all": ["Unit"], "k": True},
            "Nat.rec": {"name": "Nat.rec", "kind": "recursor", "all": ["Nat"], "k": False},
        }
        with_rec = {"FakeFalse": fake, **base,
                    "FakeFalse.rec": {"name": "FakeFalse.rec", "kind": "recursor", "all": ["FakeFalse"], "k": False}}
        res = proto.simulate_vulnerable_replay(with_rec, k_ind, k_ctor, k_rec)
        self.assertFalse(res["accepted"])
        self.assertEqual(res["error"], "postponed recursor mismatch")
        viols = proto.check_inductive_replay_integrity(with_rec, k_ind, k_ctor, k_rec)
        self.assertIn(("recursor_mismatch", "FakeFalse.rec"), {(v["code"], v["subject"]) for v in viols})
        # A forged `k` flag on a shipped recursor is caught by the hardened checker.
        forged = dict(base)
        forged["Nat.rec"] = dict(k_rec["Nat.rec"], k=True)
        viols = proto.check_inductive_replay_integrity(forged, k_ind, k_ctor, k_rec)
        self.assertIn(("recursor_mismatch", "Nat.rec"), {(v["code"], v["subject"]) for v in viols})

    def test_06c_post_replay_check_fails_closed_on_omitted_fields(self) -> None:
        """B1: a forged stored entry must not pass by OMITTING the field it lies about."""
        consts, k_ind, k_ctor = _make_valid_unit_and_nat_fixture()
        del consts["Nat"]["type"]
        del consts["Nat"]["num_indices"]
        del consts["Nat.succ"]["num_fields"]
        codes = {(v["code"], v["subject"]) for v in proto.check_inductive_replay_integrity(consts, k_ind, k_ctor)}
        self.assertIn(("indices_mismatch", "Nat"), codes)
        self.assertIn(("mutual_metadata_mismatch", "Nat"), codes)
        self.assertIn(("ctor_induct_mismatch", "Nat.succ"), codes)

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

    def test_08_all_thirteen_inductive_violation_codes_caught(self) -> None:
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

        # 13. recursor_mismatch
        c, ki, kc = _make_valid_unit_and_nat_fixture()
        kr = {"Nat.rec": {"name": "Nat.rec", "kind": "recursor", "num_minors": 2}}
        c["Nat.rec"] = {"name": "Nat.rec", "kind": "recursor", "num_minors": 3}
        self.assertIn("recursor_mismatch", {v["code"] for v in proto.check_inductive_replay_integrity(c, ki, kc, kr)})

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
        # B1: audit EVERY Trusted.* module directly (the `Trusted` umbrella alone has zero
        # declarations) and re-send every inductive block to the real kernel.
        trusted_mods = sorted(
            m for m, info in proto.discover_repo_modules(REPO_ROOT).items()
            if info["root_group"] == "trusted" and info["has_olean"]
        )
        mods = trusted_mods + ["Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"]
        res = proto.inspect_live_oleans(REPO_ROOT, import_modules=mods, exact_modules=mods)
        self.assertEqual(res["violations"], [], f"Unexpected live .olean violations: {res}")
        self.assertEqual(res["modules_checked"], len(mods))
        self.assertGreater(res["inductives_checked"], 100)
        self.assertGreater(res["ctors_checked"], 100)
        self.assertTrue(res["kernel_replay_enabled"])
        self.assertGreaterEqual(res["kernel_blocks_checked"], res["inductives_checked"] // 2)
        self.assertEqual(res["kernel_blocks_unresolved"], 0)
        self.assertTrue(set(res["axioms_reached"]).issubset(proto.PERMITTED_FOUNDATIONAL_AXIOMS))

    def test_10b_synthetic_forged_oleans_caught_only_with_kernel_replay(self) -> None:
        """B1: forge real compiled `.olean`s (lean4#16717 metadata lies) and feed them through the
        live pipeline. Name/structure-only checks (A0) miss 5/6 forgeries; the kernel
        `checkPostponedInductives` replay catches all 6."""
        mod = "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"
        enum_ind = mod + ".PeerSpecGuardClass"
        struct_ind = mod + ".SimInductVal"
        cases = [
            ("flip_is_rec", enum_ind, "is_rec_mismatch"),
            ("bump_num_indices", enum_ind, "indices_mismatch"),
            ("drop_self_from_all", enum_ind, "self_not_in_all"),
            ("flip_is_reflexive", enum_ind, "mutual_metadata_mismatch"),
            ("flip_rec_k", struct_ind, "recursor_mismatch"),
            ("bump_ctor_fields", struct_ind, "ctor_induct_mismatch"),
        ]
        missed_without_kernel = 0
        with tempfile.TemporaryDirectory(prefix="anneal-forged-olean-") as tmp_str:
            def _run_case(item: tuple[str, str, str]) -> tuple[str, str, dict, dict]:
                mutation, target, expected = item
                out = Path(tmp_str) / f"{mutation}.olean"
                proto.forge_olean_fixture(REPO_ROOT, mod, target, mutation, out)
                hard = proto.inspect_live_oleans(REPO_ROOT, [mod], [mod], olean_overrides={mod: str(out)})
                weak = proto.inspect_live_oleans(
                    REPO_ROOT, [mod], [mod], kernel_replay_inductives=False, olean_overrides={mod: str(out)}
                )
                return mutation, expected, hard, weak

            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                for mutation, expected, hard, weak in pool.map(_run_case, cases):
                    self.assertIn(expected, {v["code"] for v in hard["violations"]}, (mutation, hard["violations"]))
                    if not weak["violations"]:
                        missed_without_kernel += 1
        self.assertEqual(missed_without_kernel, 5)

    def test_10c_forged_cross_mod_all_dangling_rec_and_open_expr_redteam(self) -> None:
        """A1: catches cross-module `all` head hijack (bypassed B1's `constOrigin[head]` gate),
        forged non-`.rec` / dangling recursors (bypassed B1's `n ++ .rec` check), and open
        expressions (`Expr.bvar 0`) inside stored `.olean` declarations."""
        mod = "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"
        enum_ind = mod + ".PeerSpecGuardClass"
        struct_ind = mod + ".SimInductVal"
        cases = [
            ("cross_mod_all_hijack", enum_ind, "mutual_metadata_mismatch"),
            ("append_dangling_rec", struct_ind, "recursor_mismatch"),
            ("forge_open_expr", struct_ind, "disallowed_transitive_axiom"),
        ]
        with tempfile.TemporaryDirectory(prefix="anneal-forged-a1-") as tmp_str:
            def _run(item: tuple[str, str, str]) -> tuple[str, str, dict]:
                mutation, target, expected = item
                out = Path(tmp_str) / f"{mutation}.olean"
                proto.forge_olean_fixture(REPO_ROOT, mod, target, mutation, out)
                res = proto.inspect_live_oleans(REPO_ROOT, [mod], [mod], olean_overrides={mod: str(out)})
                return mutation, expected, res

            with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
                for mutation, expected, res in pool.map(_run, cases):
                    codes = {v["code"] for v in res["violations"]}
                    self.assertIn(expected, codes, (mutation, res["violations"]))
                    if mutation == "append_dangling_rec":
                        self.assertTrue(
                            any(v["subject"].endswith("rec_forged_1") and v["code"] == "recursor_mismatch"
                                for v in res["violations"]),
                            res["violations"],
                        )
                    elif mutation == "forge_open_expr":
                        self.assertTrue(
                            any(v["detail"] == "open_expr_in_constant" for v in res["violations"]),
                            res["violations"],
                        )


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

    def test_12b_orphan_gate_uses_lakefile_ownership_not_tautology(self) -> None:
        """B1: A0 compared discovered modules against THEMSELVES (registered = on_disk), so an
        unowned `.lean` file could never be reported. The gate now derives registration from
        `lakefile.toml` `[[lean_lib]]` srcDir/roots/globs (Lake `isBuildableModule`)."""
        with tempfile.TemporaryDirectory(prefix="anneal-orphan-fixture-") as tmp_str:
            root = Path(tmp_str)
            (root / "lakefile.toml").write_text(
                'name = "Fx"\n\n[[lean_lib]]\nname = "Anneal"\nsrcDir = "theory"\n\n'
                '[[lean_lib]]\nname = "Spec"\nsrcDir = "spec"\nglobs = ["Spec.+"]\n',
                encoding="utf-8",
            )
            (root / "theory" / "Anneal").mkdir(parents=True)
            (root / "spec" / "Spec").mkdir(parents=True)
            (root / "theory" / "Anneal.lean").write_text(
                "/- header -/\nimport Anneal.A -- trailing\n\ndef x := 1\n", encoding="utf-8"
            )
            (root / "theory" / "Anneal" / "A.lean").write_text("def a := 1\n", encoding="utf-8")
            (root / "theory" / "Anneal" / "B.lean").write_text("def b := 1\n", encoding="utf-8")
            (root / "theory" / "Rogue.lean").write_text("axiom bad : False\n", encoding="utf-8")
            (root / "spec" / "Spec" / "Ok.lean").write_text("def ok := 1\n", encoding="utf-8")
            (root / "spec" / "Stray.lean").write_text("def stray := 1\n", encoding="utf-8")
            res = proto.run_orphan_only_gate(root)
            orphans = {v["subject"] for v in res["violations"] if v["code"] == "unregistered_on_disk_orphan"}
            self.assertEqual(orphans, {"Rogue", "Stray"})
            self.assertFalse(res["ok"])
            self.assertIn("Anneal.B", res["outside_lib_root_import_closure"])
            self.assertNotIn("Anneal.A", res["outside_lib_root_import_closure"])
            # Case-fold collision `Anneal.A` vs `Anneal.a` (distinct files on case-sensitive FS).
            (root / "theory" / "Anneal" / "a.lean").write_text("def a2 := 1\n", encoding="utf-8")
            if (root / "theory" / "Anneal" / "A.lean").read_text(encoding="utf-8") == "def a := 1\n":
                res2 = proto.run_orphan_only_gate(root)
                coll = {v["subject"] for v in res2["violations"] if v["code"] == "module_name_collision"}
                self.assertEqual(coll, {"Anneal.A", "Anneal.a"})
        self.assertTrue(proto.lake_is_buildable_module(
            {"name": "L", "roots": ["L"], "globs": ["L"]}, "L.Deep.Sub"))
        self.assertFalse(proto.lake_is_buildable_module(
            {"name": "L", "roots": ["L"], "globs": ["L"]}, "Lx.Deep"))
        self.assertTrue(proto.lake_is_buildable_module(
            {"name": "S", "roots": ["S"], "globs": ["S.*"]}, "S.X"))
        self.assertFalse(proto.lake_is_buildable_module(
            {"name": "S", "roots": ["S"], "globs": ["S.*"]}, "T.X"))

    def test_12c_live_registry_covers_minirust_spec_srcdir(self) -> None:
        """B1: A0 discovery skipped the `MiniRustSpec` lean_lib (`minirust/lean`, 70 files)."""
        discovered = proto.discover_repo_modules(REPO_ROOT)
        minirust = [m for m in discovered if m == "MiniRustSpec" or m.startswith("MiniRustSpec.")]
        self.assertGreater(len(minirust), 50)
        plan = proto.plan_subsystem_shards(REPO_ROOT)
        self.assertTrue(set(minirust).issubset(set(plan["shards"]["Anneal.RustcMir"])))

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
        self.assertIn(
            "module_name_collision",
            {v["code"] for v in proto.check_shard_partition(
                ["Anneal.Foo", "Anneal.foo"], ["Anneal.Foo", "Anneal.foo"], [["Anneal.Foo"], ["Anneal.foo"]])},
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

    def test_15b_cross_shard_fingerprint_reconciliation_closes_b1_duplicate_gap(self) -> None:
        """A1: per-shard `constMap` misses conflicting duplicate declarations across shards;
        `reconcile_cross_shard_fingerprints` catches all cross-shard conflicts while accepting
        identical duplicates and header/private-body merges."""
        shard_fps = {
            "shard_a": [
                # Conflicting theorem type hash across shards
                ("M1", "evalRvalue.eq_4", "thm", "", "111", True, "999", ""),
                # Conflicting def value hash across shards (header + body vs conflicting body)
                ("M1", "helper.def", "defn", "", "222", False, "0", ""),
                ("M1", "helper.def", "defn", "", "222", True, "333", ""),
                # Compatible identical duplicate
                ("M1", "clean.eq_1", "thm", "u", "444", True, "555", ""),
                # Conflicting inductive metadata across shards
                ("M1", "Fake.Ind", "induct", "", "777", False, "0", "ind:0:0:0:false:false:false:Fake.Ind:"),
            ],
            "shard_b": [
                ("M2", "evalRvalue.eq_4", "thm", "", "888", True, "999", ""),
                ("M2", "helper.def", "defn", "", "222", True, "666", ""),
                ("M2", "clean.eq_1", "thm", "u", "444", True, "555", ""),
                ("M2", "Fake.Ind", "induct", "", "777", False, "0", "ind:0:1:0:true:false:false:Fake.Ind:"),
            ],
        }
        recon = proto.reconcile_cross_shard_fingerprints(shard_fps)
        self.assertFalse(recon["ok"])
        self.assertEqual(recon["conflicting_subjects"], ["Fake.Ind", "evalRvalue.eq_4", "helper.def"])
        self.assertTrue(all(v["code"] == "cross_shard_duplicate_conflict" for v in recon["violations"]))
        # Live fingerprint export on our prototype module self-reconciles cleanly.
        mod = "Anneal.Proto.InductiveReplayAndPeerSpecGuardsProto"
        live = proto.inspect_live_oleans(REPO_ROOT, [mod], [mod], export_fingerprints=True)
        fps = live.get("declaration_fingerprints", [])
        self.assertGreater(len(fps), 100)
        self.assertTrue(proto.reconcile_cross_shard_fingerprints({"proto": fps})["ok"])

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


    def test_20b_cfg_attr_trusted_body_and_literal_folding_redteam(self) -> None:
        """B1: A0 missed contracts behind `cfg_attr`, trusted-body (`#[trusted]` /
        `#[verifier::external_body]`) callables, and constant-false literal comparisons."""
        bad = {
            "cfg_attr": 'extern "C" { #[cfg_attr(creusot, ensures(false))] fn f(x: u32) -> u32; }',
            "nested_cfg_attr_external_spec": (
                "#[cfg_attr(all(creusot, x), cfg_attr(y, external_spec(for = a::b, ensures: |_| false)))]\n"
                "fn g() -> u32;"
            ),
            "trusted_body": "#[trusted]\n#[ensures(false)]\nfn rv(p: *const u32) -> u32 { unsafe { *p } }",
            "verus_external_body": "#[verifier::external_body]\n#[ensures(false)]\nfn rv2() -> u32 { 0 }",
            "literal_eq": 'extern "C" { #[ensures(1 == 2)] fn h(x: u32) -> u32; }',
            "literal_lt_suffix": 'extern "C" { #[ensures(5u8 < 0x1)] fn h(x: u32) -> u32; }',
            "negated_tautology": 'extern "C" { #[ensures(!(1 == 1))] fn h(x: u32) -> u32; }',
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                self.assertEqual(len(proto.scan_rust_unsatisfiable_extern_ensures(src)), 1, name)
        ok = {
            "verified_body_not_trusted": "#[ensures(false)]\nfn diverge() -> u32 { loop {} }",
            "literal_true": 'extern "C" { #[ensures(1 < 2)] fn h(x: u32) -> u32; }',
            "trusted_diverging": "#[trusted]\n#[ensures(false)]\nfn die() -> ! { loop {} }",
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_rust_unsatisfiable_extern_ensures(src), [], name)

    def test_20c_guard3_blocks_reflexive_negation_order_and_match_redteam(self) -> None:
        """A1: catches single-expr brace blocks `{ false }`, double negation `!!false`,
        negated reflexive tautologies `!(x == x)`, conflicting literal equalities,
        strict order contradictions (`x < y && x >= y`), and all-unsat `match` arms."""
        bad = {
            "brace_block_false": "#[external_spec(for = f, ensures: |_| { false })]\nfn f() -> u32;",
            "double_neg_false": 'extern "C" { #[ensures(!!false)] fn f() -> u32; }',
            "negated_reflexive_eq": 'extern "C" { #[ensures(!(x == x))] fn f(x: u32) -> u32; }',
            "negated_reflexive_le": 'extern "C" { #[ensures(!(ret <= ret))] fn f(x: u32) -> u32; }',
            "conflicting_lit_eq": 'extern "C" { #[ensures(x == 1 && x == 2)] fn f(x: u32) -> u32; }',
            "order_lt_ge": 'extern "C" { #[ensures(x < y && x >= y)] fn f(x: u32, y: u32) -> u32; }',
            "order_asymmetric": 'extern "C" { #[ensures(x < y && y < x)] fn f(x: u32, y: u32) -> u32; }',
            "eq_vs_bound": 'extern "C" { #[ensures(x == 5 && x < 3)] fn f(x: u32) -> u32; }',
            "match_all_unsat": 'extern "C" { #[ensures(match x { 0 => { false }, _ => 1 == 2 })] fn f(x: u32) -> u32; }',
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                hits = proto.scan_rust_unsatisfiable_extern_ensures(src)
                self.assertEqual([h["code"] for h in hits], ["unsatisfiable_extern_ensures"], name)
        ok = {
            "match_one_sat": 'extern "C" { #[ensures(match x { 0 => false, _ => ret == x })] fn f(x: u32) -> u32; }',
            "consistent_order": 'extern "C" { #[ensures(x < y && y <= 10)] fn f(x: u32, y: u32) -> u32; }',
            "brace_block_true": "#[external_spec(for = f, ensures: |_| { true })]\nfn f() -> u32;",
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_rust_unsatisfiable_extern_ensures(src), [], name)


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
            let _tok = creusot_std::ghost::Tokens::new::<()>();
        }
        '''
        self.assertEqual(proto.scan_rust_fndef_ghost_token_coercion(src), [])

    def test_23b_single_entry_authority_ufcs_and_alias_redteam(self) -> None:
        """B1: A0 allowed ANY number of direct `Tokens::new()` calls anywhere (Lean guard allows
        exactly one `directEntryCall true`), missed `<Tokens>::new` UFCS values, and only
        followed `as` aliases of the literal name `Tokens`."""
        cases = {
            "two_calls_in_main": "fn main() { let a = Tokens::new(); let b = Tokens::new(); }",
            "call_in_loop": "fn main() { for _ in 0..2 { let t = Tokens::new(); } }",
            "call_in_while": "fn main() { while go() { let t = Tokens::new(); } }",
            "call_outside_main": "fn helper() { let a = Tokens::new(); }",
            "ufcs_value": "fn main() { let f = <Tokens>::new; }",
            "ufcs_as_trait_value": "fn main() { let f = <Tokens as Mint>::new; }",
            "type_alias_value": "type T = creusot_std::ghost::Tokens;\nfn main() { let f = T::new; }",
            "custom_ctor_type_alias": (
                "use crate::Auth as A;\nstruct Auth;\nimpl Auth { #[ghost_token_ctor] fn issue() -> Self { Auth } }\n"
                "fn main() { let f = A::issue; }"
            ),
            "second_alias_in_group": (
                "use creusot_std::ghost::{Other as O, Tokens as T};\nfn main() { let f = T::new; }"
            ),
            "cfg_attr_ctor": (
                "struct Auth;\nimpl Auth { #[cfg_attr(creusot, ghost_token_ctor)] fn issue() -> Self { Auth } }\n"
                "fn main() { call_twice(Auth::issue); }"
            ),
        }
        for name, src in cases.items():
            with self.subTest(name=name):
                self.assertTrue(proto.scan_rust_fndef_ghost_token_coercion(src), name)
        ok = "impl Mint for X { fn go() {} }\nfn main() { let t = Tokens::new(); for x in v { use_it(x); } }"
        self.assertEqual(proto.scan_rust_fndef_ghost_token_coercion(ok), [])

    def test_23c_guard4_turbofish_self_loop_header_and_recursion_redteam(self) -> None:
        """A1: catches turbofish before `::new` (`Tokens::<()>::new`), `Self::ctor` inside
        `impl` blocks, struct literals/patterns in `for`/`while let` loop headers, and
        direct or mutual re-entrant recursion on `main()`."""
        bad = {
            "turbofish_type_arg": "fn main() { let f = Tokens::<()>::new; }",
            "turbofish_both": "fn main() { let f = creusot_std::ghost::Tokens::<()>::new::<u8>; }",
            "self_method_val": (
                "struct Auth;\nimpl Auth {\n"
                "  #[ghost_token_ctor] fn issue() -> Self { Auth }\n"
                "  fn sneak() { let f = Self::issue; }\n}"
            ),
            "self_method_call": (
                "struct Auth;\nimpl Auth {\n"
                "  #[ghost_token_ctor] fn issue() -> Self { Auth }\n"
                "  fn sneak() { let _ = Self::issue(); }\n}"
            ),
            "for_header_struct_lit": (
                "fn main() { for _ in [S { a: 1 }, S { a: 2 }] { let _t = Tokens::new(); } }"
            ),
            "while_let_struct_pat": (
                "fn main() { while let Some(S { x }) = next() { let _t = Tokens::new(); } }"
            ),
            "for_struct_pat": (
                "fn main() { for S { a } in items { let _t = Tokens::new(); } }"
            ),
            "direct_recursive_main": (
                "fn main() { let _t = Tokens::new(); if cond() { main(); } }"
            ),
            "mutual_recursive_main": (
                "fn helper() { main(); }\nfn main() { let _t = Tokens::new(); helper(); }"
            ),
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                hits = proto.scan_rust_fndef_ghost_token_coercion(src)
                self.assertTrue(hits, name)
                self.assertTrue(all(h["code"] == "fndef_ghost_token_coercion" for h in hits), name)
        ok = {
            "turbofish_direct_call": "fn main() { let _t = Tokens::<()>::new(); }",
            "struct_lit_in_other_loop": (
                "fn main() { let _t = Tokens::new(); for _ in [S { a: 1 }] { use_it(); } }"
            ),
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_rust_fndef_ghost_token_coercion(src), [], name)


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


    def test_26b_type_alias_and_foreign_type_fail_closed_redteam(self) -> None:
        """B1: A0 missed drop glue behind `type` aliases and treated every foreign wrapped type
        (the normal case for `external_type_specification`!) as drop-free."""
        bad = {
            "alias_to_vec": "type Bytes = Vec<u8>;\n#[external_type_specification]\nstruct ExAl(Bytes);",
            "generic_alias": "type Buf<T> = Box<T>;\n#[external_type_specification]\nstruct ExGA(Buf<u8>);",
            "foreign_type": "#[external_type_specification]\nstruct ExF(other_crate::Foo);",
            "foreign_for_target": "#[external_type_specification(for = other::Bar)]\nstruct ExBar;",
            "lying_no_drop_glue": (
                "struct D; impl Drop for D { fn drop(&mut self) {} }\n"
                "#[external_type_specification]\n#[no_drop_glue]\nstruct ExL(D);"
            ),
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                hits = proto.scan_rust_external_type_drop_omission(src)
                self.assertEqual([h["code"] for h in hits], ["external_type_drop_omission"], name)
        ok = {
            "array_len_const": "const N: usize = 4;\n#[external_type_specification]\nstruct ExArr([u32; N]);",
            "generic_param": "#[external_type_specification]\nstruct ExOpt<T>(Option<T>);",
            "asserted_no_drop_foreign": "#[external_type_specification]\n#[no_drop_glue]\nstruct ExP(other::Pod);",
            "modeled_foreign": "#[external_type_specification]\n#[models_drop]\nstruct ExM(other::Res);",
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_rust_external_type_drop_omission(src), [], name)

    def test_26c_guard5_foreign_ext_body_pub_crate_attrs_and_borrowed_paths_redteam(self) -> None:
        """A1: catches `#[external_type_specification] #[external_body] #[models_drop]` on
        foreign types (must emit `external_type_body_with_drop`), handles `pub(crate)` & field
        attributes on tuple structs without leaking `crate`/`allow`, and handles multi-segment
        borrowed/fn-ptr field types without false positives."""
        hits_ext_body = proto.scan_rust_external_type_drop_omission(
            "#[external_type_specification]\n#[external_body]\n#[models_drop]\n"
            "struct ExLock(other_crate::FileLock);"
        )
        self.assertEqual([h["code"] for h in hits_ext_body], ["external_type_body_with_drop"])

        bad_omission = {
            "pub_crate_box": "#[external_type_specification]\nstruct ExBox(pub(crate) Box<u8>);",
            "field_attr_foreign": "#[external_type_specification]\nstruct ExAttr(#[allow(dead_code)] other::Res);",
        }
        for name, src in bad_omission.items():
            with self.subTest(name=name):
                hits = proto.scan_rust_external_type_drop_omission(src)
                self.assertEqual([h["code"] for h in hits], ["external_type_drop_omission"], name)

        ok = {
            "pub_crate_copy": "#[external_type_specification]\nstruct ExCopy(pub(crate) u32);",
            "field_attr_copy": "#[external_type_specification]\nstruct ExAttrCopy(#[allow(dead_code)] u64);",
            "borrowed_path_and_fn_ptr": (
                "#[external_type_specification]\n"
                "struct ExRef<'a> {\n"
                "  a: Option<&'a std::vec::Vec<u8>>,\n"
                "  b: Option<&'a (Box<u8>, String)>,\n"
                "  c: Option<fn(Vec<u8>) -> Box<u8>>,\n"
                "}"
            ),
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_rust_external_type_drop_omission(src), [], name)


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

    def test_30b_binder_polarity_raw_strings_class_and_ctor_names_redteam(self) -> None:
        """B1: A0 ignored hypothesis/quantifier binder types (`(h : A → P) : Q` puts `A` in
        POSITIVE polarity), desynchronized on Lean raw strings `r#"..."#`, skipped `class`,
        and rejected sealed ctors not literally named `mk`."""
        bad = {
            "hyp_binder": "theorem t (i s : EvalRes Nat) (h : i.assumesHold = true → s.output = i.output) : True := by sorry",
            "forall_binder": "theorem t : ∀ (h : implAssumes s → s.out = 1), False := by sorry",
            # A1 fix: B1 missed `⦃` in header depth tracking, inverting polarity inside `⦃...⦄`.
            # `(implAssumes s → False) → True` has depth-2 (POSITIVE) `implAssumes`;
            # `((implAssumes s → False) → True) → True` has depth-3 (NEGATIVE) `implAssumes` (moved to `ok`).
            "strict_implicit_binder": "theorem t ⦃h : implAssumes s → False⦄ : True := by sorry",
            "raw_string_desync": 'def s : String := r#"a \" -/ /- b"#\ntheorem t (i s : EvalRes Nat) : s.output = i.output → i.assumesHold = true := by sorry',
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                self.assertTrue(proto.scan_lean_assumption_polarity(src), name)
        ok = {
            "hyp_binder_negative": "theorem t (i s : EvalRes Nat) (h : i.assumesHold = true) : s.output = i.output := by sorry",
            "exists_binder_negative_body": "theorem t : (∃ (h : implAssumes s), True) → False := by sorry",
            "strict_implicit_binder_depth3_negative": "theorem t ⦃h : (implAssumes s → False) → True⦄ : True := by sorry",
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_lean_assumption_polarity(src), [], name)
        seal_bad = "-- @sealed_invariant\nclass Cap where\n  val : Nat\n"
        self.assertEqual(len(proto.scan_lean_invariant_struct_sealing(seal_bad)), 1)
        seal_ok = "-- @sealed_invariant\nstructure Cap2 where\n  private mkCap ::\n  val : Nat\n"
        self.assertEqual(proto.scan_lean_invariant_struct_sealing(seal_ok), [])
        seal_raw = 'def s : String := r"structure Victim where private mk ::"\n-- @sealed_invariant\nstructure Victim where\n  val : Nat\n'
        self.assertEqual([h["subject"] for h in proto.scan_lean_invariant_struct_sealing(seal_raw)], ["Victim"])

    def test_30c_guard6a_implicit_anon_binders_ifte_and_prop_def_binders_redteam(self) -> None:
        """A1: catches positive-polarity assumptions inside `{h : A → P} → Q`, `⦃h : A → P⦄ → Q`,
        anonymous `[A → P]` instance binders, `if assumes then P else Q` (even inside an
        antecedent), and `: Prop :=` `def`/`abbrev` hypothesis binders."""
        bad = {
            "implicit_arrow_binder": "theorem t : {h : implRes.assumesHold = true → P} → Q := by sorry",
            "strict_implicit_arrow": "theorem t : ⦃h : implRes.assumesHold = true → P⦄ → Q := by sorry",
            "anon_inst_arrow": "theorem t : [implRes.assumesHold = true → P] → Q := by sorry",
            "anon_inst_sig_binder": "theorem t [implRes.assumesHold = true → P] : Q := by sorry",
            "ifte_in_antecedent": "theorem t : (if implRes.assumesHold = true then P else Q) → R := by sorry",
            "dite_top_level": "theorem t : if h : implRes.assumesHold = true then P else Q := by sorry",
            "prop_def_sig_binder": "def bad_def (h : implRes.assumesHold = true → P) : Prop := Q",
        }
        for name, src in bad.items():
            with self.subTest(name=name):
                hits = proto.scan_lean_assumption_polarity(src)
                self.assertEqual([h["code"] for h in hits], ["assumption_positive_polarity"], name)
        ok = {
            "implicit_neg_binder": "theorem t : {h : implRes.assumesHold = true} → Q := by sorry",
            "anon_inst_neg_binder": "theorem t [implRes.assumesHold = true] : Q := by sorry",
            "prop_def_neg_binder": "def good_def (h : implRes.assumesHold = true) : Prop := Q",
        }
        for name, src in ok.items():
            with self.subTest(name=name):
                self.assertEqual(proto.scan_lean_assumption_polarity(src), [], name)

    def test_30d_guard6b_dotted_namespace_interleaved_comment_and_keyword_ctor_redteam(self) -> None:
        """A1: tracks dotted `namespace A.B` + partial `end B` accurately, catches
        `-- @sealed_invariant` interleaved between `@[ext]` and `structure`, and rejects Lean
        keywords masquerading as constructor names (`private where ::`)."""
        dotted_src = """
        namespace A.B
        structure InsideB where
          x : Nat
        end B
        structure AfterEndB where
          x : Nat
        end A
        """
        hits = proto.scan_lean_invariant_struct_sealing(dotted_src, target_structs={"A.AfterEndB"})
        self.assertEqual([h["subject"] for h in hits], ["A.AfterEndB"])

        interleaved_src = """
        @[ext]
        -- @sealed_invariant
        structure InterleavedBad where
          val : Nat
        """
        hits2 = proto.scan_lean_invariant_struct_sealing(interleaved_src)
        self.assertEqual([h["subject"] for h in hits2], ["InterleavedBad"])

        kw_ctor_src = """
        -- @sealed_invariant
        structure KeywordCtorDecoy where
          private where ::
          val : Nat
        """
        hits3 = proto.scan_lean_invariant_struct_sealing(kw_ctor_src)
        self.assertEqual([h["subject"] for h in hits3], ["KeywordCtorDecoy"])

    def test_31_live_repo_sweep_zero_false_positives_on_theory_and_anneal_spec(self) -> None:
        res = proto.scan_live_repo_peer_guards(REPO_ROOT)
        self.assertTrue(res["ok"], f"Live repo sweep had false positives: {res['findings']}")
        self.assertEqual(res["finding_count"], 0)
        self.assertGreater(res["lean_files_scanned"], 80)
        self.assertGreaterEqual(res["rust_files_scanned"], 4)


if __name__ == "__main__":
    unittest.main()
