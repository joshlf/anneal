# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Live BEFORE/AFTER reproduction suite for all six Lean 4.34.1 `.olean`/kernel vectors.

Exercises concrete BEFORE gaps in current `trusted/audit/OleanEnvAuditor.lean`,
`trusted/audit/TrustedBoundary.lean`, `Lean.Kernel.Environment.replay`, and
`Lean.Kernel.{check,isDefEq,whnf}` against real Lean 4.34.1 compiled `.olean`/`.ir`
binaries, and verifies AFTER fail-closed catches in the pure total DAG-memoized
prototype validator (`tests/mir/OleanQuotMdataUtf8ProtoTests.lean`).
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

SUITE_DIR = Path(__file__).resolve().parent
if str(SUITE_DIR) not in sys.path:
    sys.path.insert(0, str(SUITE_DIR))

import olean_mutators as mut


REPO_ROOT = SUITE_DIR.parent.parent.parent
FIXTURES_DIR = SUITE_DIR / "fixtures"
PROTO_VALIDATOR_LEAN = REPO_ROOT / "tests/mir/OleanQuotMdataUtf8ProtoTests.lean"
OLEAN_AUDITOR_LEAN = REPO_ROOT / "trusted/audit/OleanEnvAuditor.lean"
TRUSTED_BOUNDARY_LEAN = REPO_ROOT / "trusted/audit/TrustedBoundary.lean"
LAKE_LEAN_LIB = REPO_ROOT / ".lake/build/lib/lean"


def _resolve_lean_and_sysroot() -> tuple[Path, Path]:
    lean_env = os.environ.get("LEAN_BIN")
    if lean_env and Path(lean_env).is_file():
        probe_bin = Path(lean_env).resolve()
    else:
        found = shutil.which("lean")
        if found:
            probe_bin = Path(found).resolve()
        else:
            res = subprocess.run(
                ["lake", "env", "which", "lean"],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            probe_bin = Path(res.stdout.strip()).resolve()
    prefix_res = subprocess.run(
        [str(probe_bin), "--print-prefix"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    sysroot = Path(prefix_res.stdout.strip()).resolve()
    lean_bin = (sysroot / "bin/lean").resolve()
    return lean_bin, sysroot


class SixVectorReproductionTests(unittest.TestCase):
    _tmpdir_obj: tempfile.TemporaryDirectory[str]
    tmp: Path
    lean: Path
    sysroot: Path
    auditor_bin: Path
    proto_driver: Path
    proto_lean_path: str

    @classmethod
    def setUpClass(cls) -> None:
        cls._tmpdir_obj = tempfile.TemporaryDirectory(prefix="anneal-six-vectors-")
        cls.tmp = Path(cls._tmpdir_obj.name).resolve()
        cls.lean, cls.sysroot = _resolve_lean_and_sysroot()
        leanc = cls.sysroot / "bin/leanc"

        # 1. Compile production `OleanEnvAuditor.lean` once into a native binary in tmp.
        auditor_c = cls.tmp / "OleanEnvAuditor.c"
        cls.auditor_bin = cls.tmp / "OleanEnvAuditor"
        r_c = subprocess.run(
            [str(cls.lean), "-j1", "-c", str(auditor_c), str(OLEAN_AUDITOR_LEAN)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if r_c.returncode != 0:
            raise AssertionError(f"lean -c OleanEnvAuditor failed:\n{r_c.stdout}\n{r_c.stderr}")
        r_bin = subprocess.run(
            [str(leanc), "-O3", "-rdynamic", "-o", str(cls.auditor_bin), str(auditor_c)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if r_bin.returncode != 0:
            raise AssertionError(f"leanc OleanEnvAuditor failed:\n{r_bin.stdout}\n{r_bin.stderr}")

        # 2. Compile prototype validator `.olean` once into tmp (reuses exact validator code
        # from `tests/mir/OleanQuotMdataUtf8ProtoTests.lean` with zero duplication).
        proto_olean = cls.tmp / "OleanQuotMdataUtf8ProtoTests.olean"
        env_build = os.environ.copy()
        env_build["LEAN_PATH"] = f"{LAKE_LEAN_LIB}:{cls.sysroot / 'lib/lean'}"
        subprocess.run(
            [
                str(cls.lean),
                "-j1",
                "-o",
                str(proto_olean),
                str(PROTO_VALIDATOR_LEAN),
            ],
            cwd=REPO_ROOT,
            env=env_build,
            check=True,
            capture_output=True,
            text=True,
        )
        cls.proto_lean_path = f"{cls.tmp}:{LAKE_LEAN_LIB}:{cls.sysroot / 'lib/lean'}"
        cls.proto_driver = cls.tmp / "run_proto_cli.lean"
        cls.proto_driver.write_text(
            "import OleanQuotMdataUtf8ProtoTests\n"
            "def main (args : List String) : IO UInt32 := Anneal.OleanQuotMdataUtf8Proto.cliMain args\n",
            encoding="utf-8",
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls._tmpdir_obj.cleanup()

    def _compile_fixture(
        self,
        mod_name: str,
        src_text: str,
        imports: list[str],
        *,
        is_module: bool = False,
        subdir: Path | None = None,
    ) -> tuple[list[Path], list[Path]]:
        out_dir = (subdir or (self.tmp / f"build_{mod_name}")).resolve()
        out_dir.mkdir(parents=True, exist_ok=True)
        src_path = out_dir / f"{mod_name}.lean"
        setup_path = out_dir / f"{mod_name}.setup.json"
        olean_path = out_dir / f"{mod_name}.olean"
        src_path.write_text(src_text, encoding="utf-8")
        setup = {
            "name": mod_name,
            "isModule": is_module,
            "imports": [
                {"module": m, "importAll": False, "isExported": True, "isMeta": False}
                for m in imports
            ],
            "importArts": {},
            "dynlibs": [],
            "plugins": [],
            "options": {},
        }
        setup_path.write_text(json.dumps(setup), encoding="utf-8")
        res = subprocess.run(
            [
                str(self.lean),
                "-j1",
                "--setup",
                str(setup_path),
                "-o",
                str(olean_path),
                str(src_path),
            ],
            cwd=out_dir,
            capture_output=True,
            text=True,
        )
        if res.returncode != 0:
            raise AssertionError(
                f"compiling fixture {mod_name} failed:\nstdout:\n{res.stdout}\nstderr:\n{res.stderr}"
            )
        olean_parts = [olean_path]
        ir_parts: list[Path] = []
        if is_module:
            olean_parts.extend(
                [out_dir / f"{mod_name}.olean.server", out_dir / f"{mod_name}.olean.private"]
            )
            ir_parts = [out_dir / f"{mod_name}.ir.sig", out_dir / f"{mod_name}.ir"]
        return olean_parts, ir_parts

    def _run_production_auditor(
        self,
        mod_name: str,
        olean_parts: list[Path],
        ir_parts: list[Path],
        *,
        toolchain_roots: list[str] | None = None,
    ) -> tuple[int, dict]:
        req_path = self.tmp / f"req_{mod_name}_{os.getpid()}.json"
        out_path = self.tmp / f"out_{mod_name}_{os.getpid()}.json"
        req = {
            "mode": "olean-audit",
            "sysroot": str(self.sysroot),
            "artifacts": [
                [mod_name, [[str(p) for p in olean_parts], [str(p) for p in ir_parts]]]
            ],
            "roots": [mod_name],
            "modules": [mod_name],
            "axioms": [
                ["propext", "Init.Core"],
                ["Quot.sound", "Init.Core"],
                ["Classical.choice", "Init.Core"],
                ["propext", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
            ],
            "toolchainRoots": toolchain_roots or ["Init", "Std"],
            "scope": "six-vector-repro",
        }
        req_path.write_text(json.dumps(req), encoding="utf-8")
        res = subprocess.run(
            [str(self.auditor_bin), str(req_path), str(out_path)],
            cwd=self.tmp,
            capture_output=True,
            text=True,
        )
        verdict = json.loads(out_path.read_text(encoding="utf-8"))
        return res.returncode, verdict

    def _run_proto_cli(self, *args: str) -> tuple[int, dict]:
        env = os.environ.copy()
        env["LEAN_PATH"] = self.proto_lean_path
        res = subprocess.run(
            [str(self.lean), "-j1", "--run", str(self.proto_driver), *args],
            cwd=REPO_ROOT,
            env=env,
            capture_output=True,
            text=True,
        )
        lines = [ln for ln in res.stdout.splitlines() if ln.strip()]
        if not lines:
            raise AssertionError(
                f"proto CLI produced no output (rc={res.returncode}):\nstderr:\n{res.stderr}"
            )
        return res.returncode, json.loads(lines[-1])

    def _run_lean_stdin(self, code: str) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["LEAN_PATH"] = self.proto_lean_path
        return subprocess.run(
            [str(self.lean), "-j1", "--stdin"],
            cwd=REPO_ROOT,
            env=env,
            input=code,
            capture_output=True,
            text=True,
        )

    # ------------------------------------------------------------------
    # V-Q1: Unvalidated `.quotInfo` payloads
    # ------------------------------------------------------------------
    def test_v_q1_forged_quotinfo_before_and_after(self) -> None:
        # BEFORE (in-memory replay): `Lean.Kernel.Environment.Replay.replayConstant`
        # ignores QuotVal payloads (`| .quotInfo _ => replayConstant `Eq; addDecl .quotDecl`).
        rc_p, probe = self._run_proto_cli("probe-v1", str(self.sysroot))
        self.assertEqual(rc_p, 0)
        self.assertTrue(
            probe["replayAcceptedForgedQuotInfo"],
            f"expected Replay.lean to accept forged FakeQuot: {probe}",
        )
        self.assertFalse(probe["validatorOk"])
        self.assertIn("forgedQuotInfo", probe["validatorTags"])

        # BEFORE (compiled .olean): build a real `.olean` containing a forged `.quotInfo`
        # `FakeQuot` (non-canonical name, non-Init.Prelude origin, bogus `False` type)
        # using `saveModuleData` and run production `OleanEnvAuditor.lean` on it!
        q_dir = self.tmp / "v_q1_bin"
        q_dir.mkdir(parents=True, exist_ok=True)
        forged_olean = q_dir / "ForgedQuotMod.olean"
        build_code = f"""
import Lean
open Lean
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let forgedCi : ConstantInfo := .quotInfo {{
    name := `FakeQuot
    levelParams := []
    type := mkConst ``False
    kind := .type
  }}
  let md : ModuleData := {{
    isModule := false
    imports := #[{{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }}]
    constNames := #[`FakeQuot]
    constants := #[forgedCi]
    extraConstNames := #[]
    entries := #[]
  }}
  saveModuleData (System.FilePath.mk "{forged_olean}") `ForgedQuotMod md
"""
        r_build = self._run_lean_stdin(build_code)
        self.assertEqual(r_build.returncode, 0, r_build.stderr)
        self.assertTrue(forged_olean.is_file())

        # BEFORE: live production `OleanEnvAuditor.lean` ACCEPTS `ForgedQuotMod.olean`!
        aud_rc, aud_verdict = self._run_production_auditor(
            "ForgedQuotMod", [forged_olean], []
        )
        self.assertEqual(
            aud_rc,
            0,
            f"expected current OleanEnvAuditor to accept forged .quotInfo (BEFORE gap), got: {aud_verdict}",
        )
        self.assertTrue(aud_verdict["ok"], aud_verdict)

        # AFTER: BOTH binary compacted-region validator AND in-memory validator reject
        # `ForgedQuotMod.olean` with `forgedQuotInfo`!
        bin_rc, bin_rep = self._run_proto_cli("validate-bin", "ForgedQuotMod", str(forged_olean))
        self.assertEqual(bin_rc, 1)
        self.assertIn("forgedQuotInfo", bin_rep["tags"])

        env_rc, env_rep = self._run_proto_cli(
            "validate-env", str(self.sysroot), "ForgedQuotMod", str(forged_olean), ""
        )
        self.assertEqual(env_rc, 1)
        self.assertIn("forgedQuotInfo", env_rep["tags"])

        # POSITIVE control: genuine Lean 4.34.1 `Init.Prelude` `.olean` passes binary `.quotInfo`
        # validation (all 4 canonical primitives).
        prelude_olean = self.sysroot / "lib/lean/Init/Prelude.olean"
        if prelude_olean.is_file():
            # Verify `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` are validated cleanly.
            chk_code = f"""
import OleanQuotMdataUtf8ProtoTests
open Lean Anneal.OleanQuotMdataUtf8Proto
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let env ← importModules #[{{ module := `Init.Prelude }}] {{}} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  for qn in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    let some (.quotInfo qv) := env.find? qn | throw (IO.userError s!"missing {{qn}}")
    let vs := validateQuotVal qv (some `Init.Prelude)
    if !vs.isEmpty then throw (IO.userError s!"unexpected violation on {{qn}}: {{reprStr vs}}")
  IO.println "CANON_QUOT_OK"
"""
            r_ok = self._run_lean_stdin(chk_code)
            self.assertEqual(r_ok.returncode, 0, r_ok.stderr)
            self.assertIn("CANON_QUOT_OK", r_ok.stdout)

    # ------------------------------------------------------------------
    # V-M2: Forged `.olean` `Expr.m_data` / `Level.m_data` / `Name.hash`
    # ------------------------------------------------------------------
    def test_v_m2_forged_mdata_level_and_name_hash(self) -> None:
        src = (FIXTURES_DIR / "v_m2_target.lean").read_text(encoding="utf-8")
        olean_parts, _ = self._compile_fixture("Vm2Target", src, ["Init.Core"])
        orig_bytes = olean_parts[0].read_bytes()

        # Baseline: clean `.olean` passes BOTH production auditor and prototype validator.
        aud_rc0, aud_v0 = self._run_production_auditor("Vm2Target", olean_parts, [])
        self.assertEqual(aud_rc0, 0, aud_v0)
        b_rc0, b_rep0 = self._run_proto_cli("validate-bin", "Vm2Target", str(olean_parts[0]))
        self.assertEqual(b_rc0, 0, b_rep0)

        # (a) Open-term camouflage: build a real `.olean` storing an open `Expr.fvar` /
        # `Expr.mvar` / loose `Expr.bvar` / `Level.mvar`, clear cached closedness flags in the
        # binary compacted region, and prove `OleanEnvAuditor.isClosedExpr` is fooled (`true`)!
        open_dir = self.tmp / "v_m2_open"
        open_dir.mkdir(parents=True, exist_ok=True)
        open_olean = open_dir / "Vm2OpenMod.olean"
        build_open = f"""
import Lean
open Lean
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let openExpr := Expr.app
    (Expr.app (Expr.fvar ⟨`open_fv⟩) (Expr.mvar ⟨`open_mv⟩))
    (Expr.app (Expr.bvar 3) (Expr.sort (Level.mvar ⟨`open_lmv⟩)))
  let ci : ConstantInfo := .defnInfo {{
    name := `openTarget
    levelParams := []
    type := mkConst ``Nat
    value := openExpr
    hints := .abbrev
    safety := .safe
    all := [`openTarget]
  }}
  let md : ModuleData := {{
    isModule := false
    imports := #[{{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }}]
    constNames := #[`openTarget]
    constants := #[ci]
    extraConstNames := #[]
    entries := #[]
  }}
  saveModuleData (System.FilePath.mk "{open_olean}") `Vm2OpenMod md
"""
        r_open = self._run_lean_stdin(build_open)
        self.assertEqual(r_open.returncode, 0, r_open.stderr)

        # Clear hasFVar, hasExprMVar, hasLevelMVar, looseBVarRange on the root value Expr!
        img_open = mut.OleanImage(open_olean.read_bytes())
        _, val_ptr = img_open.constant_type_and_value_ptrs(img_open.module_constants()["openTarget"])
        assert val_ptr is not None
        img_open.clear_expr_closedness_flags(val_ptr)
        open_mut_path = open_dir / "Vm2OpenMod.olean"
        open_mut_path.write_bytes(img_open.to_bytes())

        # BEFORE: `isClosedExpr` (reading cached `Expr.m_data`) falsely reports `true`!
        cc_rc, cc_res = self._run_proto_cli(
            "check-cached-closed", str(self.sysroot), "Vm2OpenMod", "openTarget", str(open_mut_path)
        )
        self.assertEqual(cc_rc, 0)
        self.assertTrue(cc_res["cachedIsClosedExpr"], cc_res)
        self.assertFalse(cc_res["recomputedClosed"], cc_res)
        self.assertIn("forgedExprMData", cc_res["validatorTags"])

        # AFTER: binary compacted-region validator also catches `forgedExprMData`!
        bo_rc, bo_rep = self._run_proto_cli("validate-bin", "Vm2OpenMod", str(open_mut_path))
        self.assertEqual(bo_rc, 1)
        self.assertIn("forgedExprMData", bo_rep["tags"])

        # (b) Real closed `.olean` with corrupted `Expr.m_data` (`approxDepth` + `hash`),
        # `Level.m_data` (reserved bit / depth), and `Name.hash` — BEFORE: production
        # `OleanEnvAuditor.lean` ACCEPTS them; AFTER: prototype validator rejects EVERY ONE!
        # b1: Flip `approxDepth` (bit 32) on `m2Id` value Expr
        img_ad = mut.OleanImage(orig_bytes)
        _, m2id_val = img_ad.constant_type_and_value_ptrs(img_ad.module_constants()["m2Id"])
        assert m2id_val is not None
        img_ad.flip_expr_mdata_mask(m2id_val, 1 << 32)
        p_ad = self.tmp / "v_m2_ad/Vm2Target.olean"
        p_ad.parent.mkdir(parents=True, exist_ok=True)
        p_ad.write_bytes(img_ad.to_bytes())
        rc_aud_ad, v_aud_ad = self._run_production_auditor("Vm2Target", [p_ad], [])
        self.assertEqual(rc_aud_ad, 0, f"expected BEFORE auditor acceptance on approxDepth flip: {v_aud_ad}")
        for mode_args in (
            ("validate-bin", "Vm2Target", str(p_ad)),
            ("validate-env", str(self.sysroot), "Vm2Target", str(p_ad), ""),
        ):
            rc_m, rep_m = self._run_proto_cli(*mode_args)
            self.assertEqual(rc_m, 1, rep_m)
            self.assertIn("forgedExprMData", rep_m["tags"])

        # b2: Flip `hash` (low 32 bits) on `m2Id` value Expr
        img_h = mut.OleanImage(orig_bytes)
        _, m2id_val_h = img_h.constant_type_and_value_ptrs(img_h.module_constants()["m2Id"])
        assert m2id_val_h is not None
        img_h.flip_expr_mdata_mask(m2id_val_h, 0x1)
        p_h = self.tmp / "v_m2_hash/Vm2Target.olean"
        p_h.parent.mkdir(parents=True, exist_ok=True)
        p_h.write_bytes(img_h.to_bytes())
        rc_aud_h, v_aud_h = self._run_production_auditor("Vm2Target", [p_h], [])
        self.assertEqual(rc_aud_h, 0, f"expected BEFORE auditor acceptance on Expr.hash flip: {v_aud_h}")
        for mode_args in (
            ("validate-bin", "Vm2Target", str(p_h)),
            ("validate-env", str(self.sysroot), "Vm2Target", str(p_h), ""),
        ):
            rc_m, rep_m = self._run_proto_cli(*mode_args)
            self.assertEqual(rc_m, 1, rep_m)
            self.assertIn("forgedExprMData", rep_m["tags"])

        # b3: Flip `Level.m_data` reserved bit (bit 35) on `m2Poly.{u}`
        img_lvl = mut.OleanImage(orig_bytes)
        m2poly_ty, _ = img_lvl.constant_type_and_value_ptrs(img_lvl.module_constants()["m2Poly"])
        lvl_ptr = img_lvl.find_first_level_in_expr(m2poly_ty)
        self.assertIsNotNone(lvl_ptr)
        assert lvl_ptr is not None
        img_lvl.flip_level_mdata_mask(lvl_ptr, 1 << 35)
        p_lvl = self.tmp / "v_m2_lvl/Vm2Target.olean"
        p_lvl.parent.mkdir(parents=True, exist_ok=True)
        p_lvl.write_bytes(img_lvl.to_bytes())
        rc_aud_lvl, v_aud_lvl = self._run_production_auditor("Vm2Target", [p_lvl], [])
        self.assertEqual(rc_aud_lvl, 0, f"expected BEFORE auditor acceptance on Level.m_data flip: {v_aud_lvl}")
        for mode_args in (
            ("validate-bin", "Vm2Target", str(p_lvl)),
            ("validate-env", str(self.sysroot), "Vm2Target", str(p_lvl), ""),
        ):
            rc_m, rep_m = self._run_proto_cli(*mode_args)
            self.assertEqual(rc_m, 1, rep_m)
            self.assertIn("forgedLevelMData", rep_m["tags"])

        # b4: Flip `Name.hash` on a binder name inside `m2Id` value Expr (`lam x Nat (bvar 0)`)
        img_nh = mut.OleanImage(orig_bytes)
        _, m2id_val_n = img_nh.constant_type_and_value_ptrs(img_nh.module_constants()["m2Id"])
        assert m2id_val_n is not None
        lam_hdr = img_nh.read_header(m2id_val_n)
        binder_name_ptr = img_nh.read_field(lam_hdr, 0)
        img_nh.flip_name_hash_mask(binder_name_ptr, 0x1234)
        p_nh = self.tmp / "v_m2_nh/Vm2Target.olean"
        p_nh.parent.mkdir(parents=True, exist_ok=True)
        p_nh.write_bytes(img_nh.to_bytes())
        rc_aud_nh, v_aud_nh = self._run_production_auditor("Vm2Target", [p_nh], [])
        self.assertEqual(rc_aud_nh, 0, f"expected BEFORE auditor acceptance on Name.hash flip: {v_aud_nh}")
        for mode_args in (
            ("validate-bin", "Vm2Target", str(p_nh)),
            ("validate-env", str(self.sysroot), "Vm2Target", str(p_nh), ""),
        ):
            rc_m, rep_m = self._run_proto_cli(*mode_args)
            self.assertEqual(rc_m, 1, rep_m)
            self.assertIn("forgedNameHash", rep_m["tags"])

        # (c) Adversarial malformed binary compacted-region checks (non-zero m_rc, OOB ptr, cycle)
        for label, bad_bytes in (
            ("nonzero_rc", mut.corrupt_olean_with_nonzero_rc(orig_bytes)),
            ("oob_root", mut.corrupt_olean_with_oob_root(orig_bytes)),
            ("expr_cycle", mut.corrupt_olean_with_expr_cycle(orig_bytes, "m2App")),
        ):
            bp = self.tmp / f"v_m2_mal_{label}/Vm2Target.olean"
            bp.parent.mkdir(parents=True, exist_ok=True)
            bp.write_bytes(bad_bytes)
            rc_mal, rep_mal = self._run_proto_cli("validate-bin", "Vm2Target", str(bp))
            self.assertEqual(rc_mal, 1, f"{label} should fail closed: {rep_mal}")
            self.assertIn("malformedOleanRegion", rep_mal["tags"], f"{label}: {rep_mal}")

    # ------------------------------------------------------------------
    # V-U3: Malformed UTF-8 in `Literal.strVal` and `Name.str` + `m_length`
    # ------------------------------------------------------------------
    def test_v_u3_malformed_utf8_and_m_length_before_and_after(self) -> None:
        src = (FIXTURES_DIR / "v_u3_target.lean").read_text(encoding="utf-8")
        olean_parts, _ = self._compile_fixture("Vu3Target", src, ["Init.Core"])
        orig_bytes = olean_parts[0].read_bytes()

        # Verify clean control passes both BEFORE auditor and AFTER validator.
        rc0, v0 = self._run_production_auditor("Vu3Target", olean_parts, [])
        self.assertEqual(rc0, 0, v0)
        b_rc0, b_rep0 = self._run_proto_cli("validate-bin", "Vu3Target", str(olean_parts[0]))
        self.assertEqual(b_rc0, 0, b_rep0)

        utf8_cases: list[tuple[str, bytes, bytes, int]] = [
            ("lone_surrogate", b"UUUUUUUU", b"\xed\xa0\x80A", 2),
            ("truncated_utf8", b"UUUUUUUU", b"\xe2\x82", 1),
            ("overlong_nul", b"UUUUUUUU", b"\xc0\x80", 1),
            ("overlong_slash", b"UUUUUUUU", b"\xc0\xaf", 1),
            ("invalid_lead_ff", b"UUUUUUUU", b"\xffA", 2),
            ("unexpected_cont_80", b"UUUUUUUU", b"\x80A", 2),
            ("embedded_nul", b"UUUUUUUU", b"A\x00B", 3),
            # Preserve exact UTF-8 bytes so Expr.m_data hash stays 100% valid; only m_length is forged!
            ("m_length_mismatch", b"UUUUUUUU", b"UUUUUUUU", 99),
            ("name_str_surrogate", b"bbbbbbbb", b"\xed\xa0\x80X", 2),
        ]

        for idx, (label, needle, payload, m_len) in enumerate(utf8_cases):
            img = mut.OleanImage(orig_bytes)
            ptrs = img.find_string_ptrs(needle)
            self.assertTrue(ptrs, f"needle {needle!r} not found in Vu3Target.olean")
            for sp in ptrs:
                img.patch_string_payload(sp, payload, new_m_length=m_len)
            mut_path = self.tmp / f"v_u3_{label}/Vu3Target.olean"
            mut_path.parent.mkdir(parents=True, exist_ok=True)
            mut_path.write_bytes(img.to_bytes())

            # BEFORE: Run live `OleanEnvAuditor.lean` on lone_surrogate, m_length_mismatch,
            # and name_str_surrogate (and verify `importModules` loads all 9 cases without error!).
            if label in ("lone_surrogate", "m_length_mismatch", "name_str_surrogate"):
                aud_rc, aud_v = self._run_production_auditor("Vu3Target", [mut_path], [])
                self.assertEqual(
                    aud_rc,
                    0,
                    f"BEFORE gap: expected current OleanEnvAuditor to accept V-U3 ({label}), got {aud_v}",
                )

            # AFTER: BOTH pure binary `.olean` validator AND in-memory validator (post-importModules)
            # reject EVERY ONE of the 9 malformed UTF-8 / m_length cases with `invalidUtf8Literal`!
            bin_rc, bin_rep = self._run_proto_cli("validate-bin", "Vu3Target", str(mut_path))
            self.assertEqual(bin_rc, 1, f"{label} binary should reject: {bin_rep}")
            self.assertIn("invalidUtf8Literal", bin_rep["tags"], f"{label} binary: {bin_rep}")

            env_rc, env_rep = self._run_proto_cli(
                "validate-env", str(self.sysroot), "Vu3Target", str(mut_path), ""
            )
            self.assertEqual(env_rc, 1, f"{label} in-memory should reject: {env_rep}")
            self.assertIn("invalidUtf8Literal", env_rep["tags"], f"{label} in-memory: {env_rep}")

            # Live Lean 4.34.1 memory-safety witness: loading truncated UTF-8 (`E2 82`) via
            # `importModules` succeeds, and then standard `reprStr` walks past the 2-byte
            # payload + NUL terminator into unmapped mmap memory and crashes with SIGSEGV!
            if label == "truncated_utf8":
                crash_probe = f"""
import Lean
open Lean
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let arts := ({{}} : NameMap ImportArtifacts).insert `Vu3Target (.ofArrays #[#[System.FilePath.mk "{mut_path}"], #[]])
  let env ← importModules #[{{ module := `Vu3Target }}] {{}} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let some (.defnInfo d) := env.find? `u3StrTarget | throw (IO.userError "missing")
  match d.value with
  | .lit (.strVal s) => IO.println (reprStr s)
  | _ => throw (IO.userError "unexpected expr")
"""
                r_crash = self._run_lean_stdin(crash_probe)
                self.assertEqual(
                    r_crash.returncode,
                    -signal.SIGSEGV,
                    f"expected SIGSEGV (-11) on truncated UTF-8 reprStr in Lean 4.34.1, got rc={r_crash.returncode}",
                )

        # (b) Malformed UTF-8 hidden inside `ModuleData.entries` (`Lean.docStringExt`):
        # BEFORE: live production `OleanEnvAuditor.lean` ACCEPTS it (exit 0, ok=true);
        # AFTER: our binary compacted-region sweep (`sweepBinRegionGraph`) catches `invalidUtf8Literal`!
        doc_olean, _ = self._compile_fixture(
            "Vu3DocMod",
            "prelude\nimport Init.Core\n/-- DDDDDDDD -/\ndef u3DocFn : Nat := 0\n",
            ["Init.Core"],
        )
        img_doc = mut.OleanImage(doc_olean[0].read_bytes())
        doc_ptrs = img_doc.find_string_ptrs(b"DDDDDDDD ")
        self.assertTrue(doc_ptrs, "docstring needle not found in Vu3DocMod.olean")
        for sp in doc_ptrs:
            img_doc.patch_string_payload(sp, b"\xed\xa0\x80A", new_m_length=2)
        doc_mut_path = self.tmp / "v_u3_doc_entries/Vu3DocMod.olean"
        doc_mut_path.parent.mkdir(parents=True, exist_ok=True)
        doc_mut_path.write_bytes(img_doc.to_bytes())

        aud_doc_rc, aud_doc_v = self._run_production_auditor("Vu3DocMod", [doc_mut_path], [])
        self.assertEqual(
            aud_doc_rc,
            0,
            f"BEFORE gap: expected current OleanEnvAuditor to accept malformed UTF-8 in docStringExt: {aud_doc_v}",
        )
        bin_doc_rc, bin_doc_rep = self._run_proto_cli("validate-bin", "Vu3DocMod", str(doc_mut_path))
        self.assertEqual(bin_doc_rc, 1, bin_doc_rep)
        self.assertIn("invalidUtf8Literal", bin_doc_rep["tags"], bin_doc_rep)

    # ------------------------------------------------------------------
    # V-F4: `_kernel_fresh` `FVarId` collision (`lean4#16767`)
    # ------------------------------------------------------------------
    def test_v_f4_kernel_fresh_collision_before_and_after(self) -> None:
        # 1. Live Lean 4.34.1 kernel reproduction across `isDefEq`, `check`, and `whnf`.
        rc_p, probe = self._run_proto_cli("probe-v4", str(self.sysroot))
        self.assertEqual(rc_p, 0)
        self.assertTrue(probe["kernelIsDefEqCapture"], probe)
        self.assertTrue(probe["kernelCheckWrongType"], probe)
        self.assertTrue(probe["kernelWhnfKReductionCapture"], probe)
        self.assertFalse(probe["validatorOk"], probe)
        self.assertIn("kernelFreshCollision", probe["validatorTags"], probe)

        # 2. Compiled `.olean` containing `_kernel_fresh` decls & binders:
        # BEFORE: current `OleanEnvAuditor.lean` ACCEPTS it with 0 violations!
        src = (FIXTURES_DIR / "v_f4_target.lean").read_text(encoding="utf-8")
        olean_parts, _ = self._compile_fixture("Vf4Target", src, ["Init.Core"])
        aud_rc, aud_v = self._run_production_auditor("Vf4Target", olean_parts, [])
        self.assertEqual(
            aud_rc,
            0,
            f"BEFORE gap: expected current OleanEnvAuditor to accept _kernel_fresh decl/binder: {aud_v}",
        )

        # AFTER: BOTH binary `.olean` validator AND in-memory validator catch `kernelFreshCollision`!
        bin_rc, bin_rep = self._run_proto_cli("validate-bin", "Vf4Target", str(olean_parts[0]))
        self.assertEqual(bin_rc, 1, bin_rep)
        self.assertIn("kernelFreshCollision", bin_rep["tags"], bin_rep)

        env_rc, env_rep = self._run_proto_cli(
            "validate-env", str(self.sysroot), "Vf4Target", str(olean_parts[0]), ""
        )
        self.assertEqual(env_rc, 1, env_rep)
        self.assertIn("kernelFreshCollision", env_rep["tags"], env_rep)

    # ------------------------------------------------------------------
    # V-S5: `@[export]` / `ir_interpreter::lookup_symbol` C-symbol leak
    # ------------------------------------------------------------------
    def test_v_s5_export_attr_and_forged_ir_evasion(self) -> None:
        # (a) Non-module file with zero-unsafe, zero-@[extern] `@[export]`:
        nm_src = (FIXTURES_DIR / "v_s5_export_nonmod.lean").read_text(encoding="utf-8")
        nm_olean, nm_ir = self._compile_fixture("Vs5NonMod", nm_src, ["Init.Core"], is_module=False)
        rc_nm, probe_nm = self._run_proto_cli(
            "probe-export", str(self.sysroot), "Vs5NonMod", str(nm_olean[0]), ""
        )
        self.assertEqual(rc_nm, 0)
        self.assertEqual(probe_nm["moduleEntries"], [["s5NonModExported", "proto_s5_nonmod_sym"]])
        self.assertEqual(probe_nm["moduleIREntries"], [["s5NonModExported", "proto_s5_nonmod_sym"]])
        self.assertIn("forbiddenExportAttr", probe_nm["validatorTags"])

        # Also verify binary `.olean` validator catches `Lean.exportAttr` directly.
        bin_nm_rc, bin_nm_rep = self._run_proto_cli("validate-bin", "Vs5NonMod", str(nm_olean[0]))
        self.assertEqual(bin_nm_rc, 1, bin_nm_rep)
        self.assertIn("forbiddenExportAttr", bin_nm_rep["tags"])

        # Verify `TrustedBoundary.lean` compiled `.olean` audit path has ZERO `@[export]` checks
        # (grep confirmation of zero `exportAttr` / `getExportNameFor?` references in TrustedBoundary.lean).
        tb_text = TRUSTED_BOUNDARY_LEAN.read_text(encoding="utf-8")
        self.assertNotIn("exportAttr", tb_text)
        self.assertNotIn("getExportNameFor?", tb_text)

        # (b) Module-system file with public & private `@[export]`:
        m_src = (FIXTURES_DIR / "v_s5_export_mod.lean").read_text(encoding="utf-8")
        m_olean, m_ir = self._compile_fixture("Vs5Mod", m_src, ["Init.Core"], is_module=True)
        rc_m, probe_m = self._run_proto_cli(
            "probe-export",
            str(self.sysroot),
            "Vs5Mod",
            ",".join(str(p) for p in m_olean),
            ",".join(str(p) for p in m_ir),
        )
        self.assertEqual(rc_m, 0)
        entry_syms = {sym for _, sym in probe_m["moduleEntries"]}
        self.assertEqual(entry_syms, {"proto_s5_mod_pub_sym", "proto_s5_mod_priv_sym"})
        self.assertEqual(probe_m["moduleIREntries"], [])
        self.assertIn("forbiddenExportAttr", probe_m["validatorTags"])

        # (c) Forged `.ir` `Lean.exportAttr` entry evading `OleanEnvAuditor.lean:1649`!
        c_src = (FIXTURES_DIR / "v_s5_clean_mod.lean").read_text(encoding="utf-8")
        c_olean, c_ir = self._compile_fixture("Vs5ForgedIr", c_src, ["Init.Core"], is_module=True)
        # Positive 5-file `module` control via `validate-bin-mod` BEFORE forging `.ir`:
        clean_mod_rc, clean_mod_rep = self._run_proto_cli(
            "validate-bin-mod",
            "Vs5ForgedIr",
            ",".join(str(p) for p in c_olean),
            ",".join(str(p) for p in c_ir),
        )
        self.assertEqual(clean_mod_rc, 0, f"clean 5-file module should pass: {clean_mod_rep}")
        self.assertTrue(clean_mod_rep["ok"], clean_mod_rep)

        donor_olean = self.tmp / "s5_donor.olean"
        forge_code = f"""
import Lean
open Lean
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let parts ← readModuleDataParts #[System.FilePath.mk "{c_ir[0]}", System.FilePath.mk "{c_ir[1]}"]
  if h : 1 < parts.size then
    let irMd := parts[1].1
    let forgedEnv := exportAttr.ext.addEntry (← mkEmptyEnvironment) (`s5CleanFn, `forged_ir_lookup_sym)
    writeModule forgedEnv (System.FilePath.mk "{donor_olean}") (writeIR := false)
    let (donorMd, _) ← readModuleData (System.FilePath.mk "{donor_olean}")
    let expEntries := donorMd.entries.filter (·.1 == `Lean.exportAttr)
    let forgedIrMd : ModuleData := {{ irMd with entries := irMd.entries ++ expEntries }}
    saveModuleData (System.FilePath.mk "{c_ir[1]}") `Vs5ForgedIr forgedIrMd
  else
    throw (IO.userError "missing ir parts")
"""
        r_forge = self._run_lean_stdin(forge_code)
        self.assertEqual(r_forge.returncode, 0, r_forge.stderr)

        # BEFORE: `getModuleEntries` is EMPTY (`#[]`) AND live production `OleanEnvAuditor.lean`
        # ACCEPTS `Vs5ForgedIr` (exit 0, ok=true) despite the forged `.ir` `exportAttr` entry!
        aud_rc_ir, aud_v_ir = self._run_production_auditor("Vs5ForgedIr", c_olean, c_ir)
        self.assertEqual(
            aud_rc_ir,
            0,
            f"BEFORE gap: expected current OleanEnvAuditor.lean:1649 to miss forged .ir exportAttr: {aud_v_ir}",
        )
        self.assertTrue(aud_v_ir["ok"], aud_v_ir)

        rc_pf, probe_f = self._run_proto_cli(
            "probe-export",
            str(self.sysroot),
            "Vs5ForgedIr",
            ",".join(str(p) for p in c_olean),
            ",".join(str(p) for p in c_ir),
        )
        self.assertEqual(rc_pf, 0)
        self.assertEqual(probe_f["moduleEntries"], [])
        self.assertEqual(probe_f["moduleIREntries"], [["s5CleanFn", "forged_ir_lookup_sym"]])
        # AFTER: prototype validator catches BOTH in-memory (`getModuleIREntries`) AND raw binary `.ir`!
        self.assertFalse(probe_f["validatorOk"])
        self.assertIn("forbiddenExportAttr", probe_f["validatorTags"])

        bin_ir_rc, bin_ir_rep = self._run_proto_cli(
            "validate-bin", "Vs5ForgedIr", str(c_ir[1])
        )
        self.assertEqual(bin_ir_rc, 1, bin_ir_rep)
        self.assertIn("forbiddenExportAttr", bin_ir_rep["tags"])

        # (d) Forged `.ir` `IR.Decl.extern` C-symbol stub (ZERO `exportAttr`!):
        e_olean, e_ir = self._compile_fixture("Vs5IrExtern", c_src, ["Init.Core"], is_module=True)
        ext_donor = self.tmp / "s5_ir_extern_donor.olean"
        forge_ir_ext = f"""
import Lean
import Lean.Compiler.IR.Basic
open Lean
#eval show IO Unit from do
  searchPathRef.set [System.FilePath.mk "{self.sysroot}/lib/lean"]
  let parts ← readModuleDataParts #[System.FilePath.mk "{e_ir[0]}", System.FilePath.mk "{e_ir[1]}"]
  if h : 1 < parts.size then
    let irMd := parts[1].1
    let extData : ExternAttrData := {{ entries := [.standard `all "forged_ir_extern_c_sym"] }}
    let extDecl : IR.Decl := .extern `s5CleanFn #[{{ x := ⟨1⟩, borrow := false, ty := .object }}] .object extData
    let env0 := IR.declMapExt.addEntry (← mkEmptyEnvironment) extDecl
    writeModule env0 (System.FilePath.mk "{ext_donor}") (writeIR := false)
    let (donorMd, _) ← readModuleData (System.FilePath.mk "{ext_donor}")
    let kept := irMd.entries.filter (·.1 != `Lean.IR.declMapExt)
    let forgedIrMd : ModuleData := {{ irMd with entries := kept ++ donorMd.entries }}
    saveModuleData (System.FilePath.mk "{e_ir[1]}") `Vs5IrExtern forgedIrMd
  else
    throw (IO.userError "missing ir parts")
"""
        r_fext = self._run_lean_stdin(forge_ir_ext)
        self.assertEqual(r_fext.returncode, 0, r_fext.stderr)

        bin_ext_rc, bin_ext_rep = self._run_proto_cli(
            "validate-bin-mod",
            "Vs5IrExtern",
            ",".join(str(p) for p in e_olean),
            ",".join(str(p) for p in e_ir),
        )
        self.assertEqual(bin_ext_rc, 1, bin_ext_rep)
        self.assertIn("forbiddenExportAttr", bin_ext_rep["tags"])

        env_ext_rc, env_ext_rep = self._run_proto_cli(
            "validate-env",
            str(self.sysroot),
            "Vs5IrExtern",
            ",".join(str(p) for p in e_olean),
            ",".join(str(p) for p in e_ir),
        )
        self.assertEqual(env_ext_rc, 1, env_ext_rep)
        self.assertIn("forbiddenExportAttr", env_ext_rep["tags"])

    # ------------------------------------------------------------------
    # V-N6: `lean4#16831` `Nat.xor` / `[propext]` second-kernel parity
    # ------------------------------------------------------------------
    def test_v_n6_nat_xor_propext_second_kernel_parity(self) -> None:
        rc_p, probe = self._run_proto_cli("probe-v6", str(self.sysroot), str(LAKE_LEAN_LIB))
        self.assertEqual(rc_p, 0, probe)
        self.assertEqual(probe["natXorAxioms"], ["propext"])
        self.assertEqual(probe["natBitwiseAxioms"], ["propext"])
        # Record current 403ebd3b status of `Anneal.NatBitwise.unfold_eq` (`[propext, Quot.sound]`).
        self.assertEqual(probe["unfoldEqAxioms"], ["propext", "Quot.sound"])
        self.assertGreater(probe["zeroAxiomTheoremCount"], 0)
        self.assertGreater(probe["propextOnlyTheoremCount"], 0)
        self.assertGreater(probe["propextQuotTheoremCount"], 0)
        # BEFORE (`lean4#16831`): unconditional `primitiveTargets` leaks `propext` into 0-axiom proofs.
        self.assertEqual(probe["buggyUnconditionalTag"], "nanodaNatXorPropextMismatch")
        self.assertEqual(probe["buggyUnconditionalSecondKernelAxioms"], ["propext"])
        # AFTER: demand-driven `primitiveTargets` restores exact Lean-vs-second-kernel parity.
        self.assertTrue(probe["fixedDemandDrivenZeroOk"])
        self.assertTrue(probe["fixedDemandDrivenPropOk"])
        self.assertTrue(probe["fixedDemandDrivenUnfoldOk"])

        # BEFORE (forged per-module axiom cache): Lean 4.34.1 `#print axioms` / `collectAxioms`
        # never traverses imported declarations; it trusts the axiom arrays stored in each
        # `.olean`'s `exportedAxiomsExt` entries. Emptying them launders `evilAx` out of
        # `#print axioms` for the forged module AND for an honest downstream theorem.
        ax_dir = self.tmp / "v_n6_axcache"
        forged_dir = ax_dir / "forged"
        forged_dir.mkdir(parents=True, exist_ok=True)
        ax_src = (
            "axiom evilAx : False\n"
            "theorem useEvil : False := evilAx\n"
            "theorem useEvil2 : 1 = 2 := useEvil.elim\n"
        )
        ax_parts, _ = self._compile_fixture("Vn6AxCache", ax_src, ["Init"], subdir=ax_dir)
        forged_bytes, patched = mut.empty_exported_axioms(
            ax_parts[0].read_bytes(), {"useEvil", "useEvil2"}
        )
        self.assertEqual(patched, 2)
        forged_olean = forged_dir / "Vn6AxCache.olean"
        forged_olean.write_bytes(forged_bytes)
        driver_src = (
            "import Vn6AxCache\n"
            "#print axioms useEvil2\n"
            "theorem downstream : 1 = 2 := useEvil2\n"
            "#print axioms downstream\n"
        )
        lean_env = os.environ.copy()
        for label, search_dir, expect in (
            ("honest", ax_dir, "depends on axioms: [evilAx]"),
            ("forged", forged_dir, "does not depend on any axioms"),
        ):
            drv = search_dir / f"Driver_{label}.lean"
            drv.write_text(driver_src, encoding="utf-8")
            lean_env["LEAN_PATH"] = f"{search_dir}:{self.sysroot / 'lib/lean'}"
            r_drv = subprocess.run(
                [str(self.lean), "-j1", str(drv)],
                cwd=search_dir,
                env=lean_env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r_drv.returncode, 0, r_drv.stderr)
            self.assertIn(f"'useEvil2' {expect}", r_drv.stdout, (label, r_drv.stdout))
            self.assertIn(f"'downstream' {expect}", r_drv.stdout, (label, r_drv.stdout))

        # AFTER: in-memory validation recomputes closures independently and rejects the
        # forged cache (`forgedExportedAxioms`); the honest olean stays clean of that tag.
        for olean, should_flag in ((ax_parts[0], False), (forged_olean, True)):
            _, rep = self._run_proto_cli(
                "validate-env", str(self.sysroot), "Vn6AxCache", str(olean), ""
            )
            self.assertEqual("forgedExportedAxioms" in rep["tags"], should_flag, rep)


if __name__ == "__main__":
    unittest.main()
