#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and integration test suite for `scripts/olean_replay_key_audit.py`."""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import ast
import errno
import io
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import olean_replay_key_audit as audit


class TestAstAndHygieneInvariants(unittest.TestCase):
    """Verifies strict temp-dir, bytecode, env-sanitization, and RCE-prevention invariants."""

    def test_sys_dont_write_bytecode_enabled(self) -> None:
        self.assertTrue(sys.dont_write_bytecode)
        self.assertTrue(audit.sys.dont_write_bytecode)

    def test_zero_mkdtemp_calls_in_audit_and_test_sources(self) -> None:
        forbidden_fn = "mk" + "dtemp"
        for py_path in (
            SCRIPT_DIR / "olean_replay_key_audit.py",
            SCRIPT_DIR / "test_olean_replay_key_audit.py",
        ):
            src = py_path.read_text(encoding="utf-8")
            tree = ast.parse(src, filename=str(py_path))
            for node in ast.walk(tree):
                if isinstance(node, ast.Attribute):
                    self.assertNotEqual(
                        node.attr,
                        forbidden_fn,
                        f"forbidden {forbidden_fn} attribute found in {py_path.name}",
                    )
                elif isinstance(node, ast.Name):
                    self.assertNotEqual(
                        node.id,
                        forbidden_fn,
                        f"forbidden {forbidden_fn} identifier found in {py_path.name}",
                    )

    def test_inspector_lean_never_enables_initializers_or_load_exts(self) -> None:
        lean_src = audit.INSPECTOR_LEAN_SOURCE
        self.assertNotIn("enableInitializersExecution", lean_src)
        self.assertNotIn("loadExts := true", lean_src)
        self.assertIn("loadExts := false", lean_src)

    def test_sanitized_env_preserves_anneal_lean_run_and_scrubs_lean_path(self) -> None:
        fake_env = {
            "HOME": "/tmp/fake-home",
            "PATH": "/usr/bin:/bin",
            "XDG_RUNTIME_DIR": "/run/user/12345",
            "ANNEAL_LEAN_RUN_ACTIVE": "1",
            "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
            "ANNEAL_LEAN_RUN_LEAN_M_MB": "8192",
            "LEAN_PATH": "/tmp/evil-stdlib-shadow",
            "LEAN_SRC_PATH": "/tmp/evil-src",
            "LAKE_HOME": "/tmp/evil-lake",
            "ELAN_HOME": "/tmp/evil-elan",
            "LD_PRELOAD": "/tmp/evil.so",
            "DYLD_INSERT_LIBRARIES": "/tmp/evil.dylib",
        }
        cleaned = audit.build_sanitized_lean_env(fake_env)
        self.assertEqual(cleaned["ANNEAL_LEAN_RUN_ACTIVE"], "1")
        self.assertEqual(cleaned["ANNEAL_LEAN_RUN_IN_SCOPE"], "1")
        self.assertEqual(cleaned["ANNEAL_LEAN_RUN_LEAN_M_MB"], "8192")
        self.assertEqual(cleaned["XDG_RUNTIME_DIR"], "/run/user/12345")
        self.assertIn("/usr/bin", cleaned["PATH"])
        for forbidden in (
            "LEAN_PATH",
            "LEAN_SRC_PATH",
            "LAKE_HOME",
            "ELAN_HOME",
            "LD_PRELOAD",
            "DYLD_INSERT_LIBRARIES",
        ):
            self.assertNotIn(forbidden, cleaned)


class TestCliArgumentParsing(unittest.TestCase):
    """Tests CLI flags, aliases, mutual exclusion, and exit code 2 on operational errors."""

    def test_parser_accepts_all_required_flags(self) -> None:
        parser = audit.build_arg_parser()
        ns = parser.parse_args(
            [
                "--audit-module",
                "Anneal.ReplayKeyAndTamperAudit",
                "--module",
                "Topic.Proofs",
                "--olean-dir",
                "/tmp/d1",
                "--olean-dir",
                "/tmp/d2",
                "--source-map",
                "/tmp/smap.json",
                "--strict-proofs",
                "--module-mode",
                "--allow-assumptions",
                "--allow-provisional-native",
                "--json",
            ]
        )
        self.assertEqual(ns.modules, ["Anneal.ReplayKeyAndTamperAudit", "Topic.Proofs"])
        self.assertEqual(ns.olean_dirs, [Path("/tmp/d1"), Path("/tmp/d2")])
        self.assertEqual(ns.source_map, Path("/tmp/smap.json"))
        self.assertTrue(ns.strict_proofs)
        self.assertTrue(ns.module_mode)
        self.assertTrue(ns.allow_assumptions)
        self.assertTrue(ns.allow_provisional_native)
        self.assertTrue(ns.json)

    def test_self_test_alias_maps_to_run_tamper_suite(self) -> None:
        parser = audit.build_arg_parser()
        ns = parser.parse_args(["--self-test"])
        self.assertTrue(ns.run_tamper_suite)

    def test_invalid_cli_flags_return_exit_2(self) -> None:
        buf_err = io.StringIO()
        with mock.patch("sys.stderr", buf_err):
            rc = audit.main(["--definitely-unknown-flag"])
        self.assertEqual(rc, 2)

        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            rc_json = audit.main(["--definitely-unknown-flag", "--json"])
        self.assertEqual(rc_json, 2)
        payload = json.loads(buf_out.getvalue())
        self.assertFalse(payload["ok"])
        self.assertTrue(payload["operational_error"])

    def test_no_mode_or_conflicting_modes_return_exit_2(self) -> None:
        with mock.patch("sys.stderr", io.StringIO()):
            self.assertEqual(audit.main([]), 2)
            self.assertEqual(audit.main(["--emit-patch-spec", "--run-tamper-suite"]), 2)
            self.assertEqual(
                audit.main(["--audit-module", "Foo.Bar", "--emit-patch-spec"]), 2
            )

    def test_relative_lean_path_rejected_exit_2(self) -> None:
        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            rc = audit.main(
                ["--audit-module", "Foo.Bar", "--lean", "relative/bin/lean", "--json"]
            )
        self.assertEqual(rc, 2)


class TestFailClosedFilesystemStat(unittest.TestCase):
    """Tests `zerocopy#4161` fail-closed `stat_regular_fail_closed` & `stat_dir_fail_closed`."""

    def test_enoent_returns_none_and_maps_to_policy_missing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            self.assertIsNone(
                audit.stat_regular_fail_closed(p / "DoesNotExist.olean", base_dir=p)
            )
            _, sysroot = audit.resolve_lean_toolchain()
            with self.assertRaises(audit.AuditPolicyError) as ctx:
                audit.precheck_olean_dirs_and_locate_modules(
                    ["Proof.MissingMod"], [p], sysroot, None
                )
            self.assertEqual(ctx.exception.category, "missingOleanPart")

    def test_directory_as_file_raises_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            fake_olean_dir = p / "Proof" / "Fake.olean"
            fake_olean_dir.mkdir(parents=True)
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(fake_olean_dir, base_dir=p)

            buf_out = io.StringIO()
            with mock.patch("sys.stdout", buf_out):
                rc = audit.main(
                    ["--audit-module", "Proof.Fake", "--olean-dir", str(p), "--json"]
                )
            self.assertEqual(rc, 2)

    def test_symlink_and_broken_symlink_and_intermediate_symlink_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            real_file = p / "real.bin"
            real_file.write_bytes(b"olean-bytes")
            sym_file = p / "sym.olean"
            os.symlink(real_file, sym_file)
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(sym_file, base_dir=p, allow_symlink=False)

            broken_sym = p / "broken.olean"
            os.symlink(p / "nonexistent", broken_sym)
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(broken_sym, base_dir=p, allow_symlink=True)

            # Intermediate symlinked directory (`Sub -> real_sub`) must ALSO fail closed!
            real_sub = p / "real_sub"
            real_sub.mkdir()
            (real_sub / "Mod.olean").write_bytes(b"1234")
            (p / "olean_root").mkdir()
            os.symlink(real_sub, p / "olean_root" / "Sub")
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(
                    p / "olean_root" / "Sub" / "Mod.olean",
                    base_dir=p / "olean_root",
                    allow_symlink=False,
                )

    def test_eloop_symlink_cycle_raises_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            loop_a = p / "loop_a"
            loop_b = p / "loop_b"
            os.symlink(loop_b, loop_a)
            os.symlink(loop_a, loop_b)
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(loop_a / "Mod.olean", allow_symlink=True)

    def test_enotdir_component_raises_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            not_a_dir = p / "Proof"
            not_a_dir.write_text("regular file, not dir", encoding="utf-8")
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(not_a_dir / "Mod.olean", base_dir=p)

    def test_fifo_named_pipe_fails_immediately_without_blocking(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            fifo_path = p / "fifo.olean"
            os.mkfifo(fifo_path)
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(fifo_path, base_dir=p)

    def test_unreadable_file_and_unreadable_server_part_exit_2_never_fallback(self) -> None:
        if os.geteuid() == 0:
            self.skipTest("root bypasses chmod 000 permission checks")
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            proof_dir = p / "Proof"
            proof_dir.mkdir()
            olean = proof_dir / "Secret.olean"
            olean.write_bytes(b"valid-placeholder")
            srv = proof_dir / "Secret.olean.server"
            srv.write_bytes(b"unreadable-server-part")
            srv.chmod(0o000)
            try:
                # Even without `--module-mode`, probing `.olean.server` with EACCES MUST raise exit 2!
                buf_out = io.StringIO()
                with mock.patch("sys.stdout", buf_out):
                    rc = audit.main(
                        [
                            "--audit-module",
                            "Proof.Secret",
                            "--olean-dir",
                            str(p),
                            "--json",
                        ]
                    )
                self.assertEqual(rc, 2)
            finally:
                srv.chmod(0o600)

    def test_simulated_eio_raises_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "io_err.olean"
            with mock.patch(
                "os.lstat", side_effect=OSError(errno.EIO, "Input/output error")
            ):
                with self.assertRaises(audit.AuditOperationalError):
                    audit.stat_regular_fail_closed(p)

    def test_symlink_or_fifo_ir_parts_raise_operational_error(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            proof_dir = p / "Proof"
            proof_dir.mkdir()
            (proof_dir / "WithIr.olean").write_bytes(b"placeholder")
            real_ir = p / "real.ir"
            real_ir.write_bytes(b"ir-bytes")
            os.symlink(real_ir, proof_dir / "WithIr.ir.sig")
            _, sysroot = audit.resolve_lean_toolchain()
            with self.assertRaises(audit.AuditOperationalError):
                audit.precheck_olean_dirs_and_locate_modules(
                    ["Proof.WithIr"], [p], sysroot, None
                )
            os.remove(proof_dir / "WithIr.ir.sig")
            os.mkfifo(proof_dir / "WithIr.ir")
            with self.assertRaises(audit.AuditOperationalError):
                audit.precheck_olean_dirs_and_locate_modules(
                    ["Proof.WithIr"], [p], sysroot, None
                )

    def test_duplicate_target_module_rejected_policy(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            proof_dir = p / "Proof"
            proof_dir.mkdir()
            (proof_dir / "Dup.olean").write_bytes(b"placeholder")
            _, sysroot = audit.resolve_lean_toolchain()
            with self.assertRaises(audit.AuditPolicyError) as ctx:
                audit.precheck_olean_dirs_and_locate_modules(
                    ["Proof.Dup", "Proof.Dup"], [p], sysroot, None
                )
            self.assertEqual(ctx.exception.category, "duplicateModuleName")


class TestSourceScannerDefenseInDepth(unittest.TestCase):
    """Tests Episode 1-equivalent lexer desync, token glue, and header/option rules."""

    def test_clean_constructs_and_plain_json_strings_pass(self) -> None:
        clean_samples = [
            "theorem t : True := by decide +kernel\n",
            "-- native_decide set_option debug.skipKernelTC true +1]'\n"
            "/- nested /- unsafe run_cmd -/ comment -/\n"
            'def jsonStr : String := "{\\"ok\\":true,\\"code\\":\\"x\\"}"\n'
            'def ch : Char := \'"\'\n'
            'def raw : String := r#"set_option debug.skipKernelTC true"#\n'
            "def f' : Nat := 1\n"
            'def interp : String := s!"{f\'} and {1 + 1}"\n',
            "import Topic.all\nset_option maxHeartbeats 400000 in\n"
            "set_option linter.deprecated false in\ntheorem ok : True := trivial\n",
        ]
        for sample in clean_samples:
            audit.scan_source_defense_in_depth("Proof.Clean", sample)

    def test_lexer_desync_and_forbidden_constructs_rejected(self) -> None:
        bad_samples = [
            ('def g := f\'""\nset_option debug.skipKernelTC true in\ndef h := 1 --"', "forbiddenSourceOption"),
            ('prefix:0x1r"\\" => id\nset_option debug.skipKernelTC true in\ndef a := ""', "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide (config := ⟨false, true, true, false⟩)", "forbiddenSourceOption"),
            ("theorem p : True := by iterate 1native_decide", "forbiddenSourceOption"),
            ("theorem p : True := by bv_decide?", "forbiddenSourceOption"),
            ("def x : Nat := unsafe (0 : Nat)", "forbiddenSourceOption"),
            ("#exit", "forbiddenSourceOption"),
            ("prelude\ndef x : Nat := 0", "forbiddenSourceOption"),
            ("import all Topic.Defs", "forbiddenImportAll"),
            ("private import Topic.Defs", "forbiddenImportModifier"),
            ('def s := s!"{«}"»}"', "unsupportedSourceLexing"),
            ('def x := xs[i+1]\'"proof"', "unsupportedSourceLexing"),
            ('def s := s! "{show Nat from by native_decide}"', "forbiddenSourceOption"),
            ('def s := s! /- comment -/ "{show Nat from by set_option debug.skipKernelTC true in exact 0}"', "forbiddenSourceOption"),
            ('def s := «s!» "{show Nat from by native_decide}"', "forbiddenSourceOption"),
        ]
        for sample, expected_cat in bad_samples:
            with self.assertRaises(audit.AuditPolicyError, msg=sample) as ctx:
                audit.scan_source_defense_in_depth("Proof.Bad", sample)
            self.assertEqual(ctx.exception.category, expected_cat)

    def test_axiom_source_gating_for_assumptions_and_test_roles(self) -> None:
        ax_src = "namespace Assumptions.Hw\naxiom mmioOk : True\nend Assumptions.Hw\n"
        with self.assertRaises(audit.AuditPolicyError) as ctx:
            audit.scan_source_defense_in_depth("Assumptions.Hw", ax_src, allow_assumptions=False)
        self.assertEqual(ctx.exception.category, "forbiddenAxiom")
        audit.scan_source_defense_in_depth("Assumptions.Hw", ax_src, allow_assumptions=True)

        test_src = "namespace Topic.Tests\naxiom localOnly : True\nend Topic.Tests\n"
        with self.assertRaises(audit.AuditPolicyError) as ctx2:
            audit.scan_source_defense_in_depth("Topic.Tests", test_src, allow_local_test_axioms=False)
        self.assertEqual(ctx2.exception.category, "forbiddenAxiom")
        audit.scan_source_defense_in_depth("Topic.Tests", test_src, allow_local_test_axioms=True)


class TestPatchSpecAndFixtureManifest(unittest.TestCase):
    """Tests JSON schema stability, `--emit-patch-spec`, fixture manifest, and live `.olean` audit."""

    def test_emit_patch_spec_json_completeness(self) -> None:
        buf = io.StringIO()
        with mock.patch("sys.stdout", buf):
            rc = audit.main(["--emit-patch-spec", "--json"])
        self.assertEqual(rc, 0)
        spec = json.loads(buf.getvalue())
        self.assertTrue(spec["ok"])
        self.assertEqual(spec["schema_version"], 1)
        self.assertEqual(spec["target_file"], "trusted/audit/TrustedBoundary.lean")
        self.assertEqual(spec["patch_count"], 12)
        all_symbols = {sym for p in spec["patches"] for sym in p["target_symbols"]}
        for required_sym in (
            "verifyModuleInventory",
            "insertReplayLocalUnique",
            "verifyCheckedEnvKeys",
            "isCompilerTrustAxiom",
            "isCodegenUnsafeRec",
            "cleanNonWorkspace",
            "verifyStdlibProvenance",
            "inspectSyntax",
        ):
            self.assertIn(required_sym, all_symbols)

    def test_fixture_directory_completeness_and_zero_binaries(self) -> None:
        fx_dir = audit.FIXTURES_DIR
        self.assertTrue(fx_dir.is_dir())
        manifest = audit.load_fixture_manifest(fx_dir)
        self.assertEqual(len(manifest["positive_fixtures"]), 1)
        self.assertEqual(len(manifest["negative_fixtures"]), 18)
        self.assertEqual(manifest["positive_fixtures"][0]["id"], "00_clean_positive")

        expected_prefixes = [f"{i:02d}_" for i in range(1, 19)]
        for idx, neg in enumerate(manifest["negative_fixtures"]):
            self.assertTrue(neg["id"].startswith(expected_prefixes[idx]))
            fpath = fx_dir / neg["file"]
            self.assertTrue(fpath.is_file(), f"missing fixture {fpath}")
            self.assertTrue(bool(neg["expected_category"]))

        forbidden_exts = (".olean", ".ilean", ".ir", ".c", ".pyc", ".o", ".so")
        for root, dirs, files in os.walk(fx_dir):
            self.assertNotIn("__pycache__", dirs)
            for fn in files:
                for ext in forbidden_exts:
                    self.assertFalse(
                        fn.endswith(ext), f"forbidden binary artifact in fixtures: {root}/{fn}"
                    )

    def test_live_audit_of_replay_key_and_tamper_audit_and_zero_temp_leak(self) -> None:
        olean_path = (
            REPO_ROOT
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Anneal"
            / "ReplayKeyAndTamperAudit.olean"
        )
        self.assertTrue(
            olean_path.is_file(),
            f"expected compiled {olean_path}; run `lake build Anneal.ReplayKeyAndTamperAudit` first",
        )
        tmp_root = Path(tempfile.gettempdir())
        before = {
            p.name
            for p in tmp_root.iterdir()
            if p.name.startswith(("anneal-olean-audit-", "anneal-tamper-suite-"))
        }
        buf = io.StringIO()
        with mock.patch("sys.stdout", buf):
            rc = audit.main(
                ["--audit-module", "Anneal.ReplayKeyAndTamperAudit", "--json"]
            )
        after = {
            p.name
            for p in tmp_root.iterdir()
            if p.name.startswith(("anneal-olean-audit-", "anneal-tamper-suite-"))
        }
        self.assertEqual(after - before, set(), "temporary directory leaked!")
        self.assertEqual(rc, 0, f"live audit failed: {buf.getvalue()}")
        report = json.loads(buf.getvalue())
        self.assertTrue(report["ok"])
        self.assertEqual(report["schema_version"], 1)
        self.assertEqual(report["violations"], [])
        self.assertGreater(report["summary"]["replayed_declarations"], 3000)
        self.assertEqual(report["summary"]["reached_axioms"], [])


class TestPassB1AdversarialRegressions(unittest.TestCase):
    """Compiled Lean 4.34.1 `.olean` regressions for Pass B1 adversarial bypasses."""

    def test_verify_binders_unlisted_multi_item_extensions_shadowing_and_source_dir(self) -> None:
        lean_bin, sysroot = audit.resolve_lean_toolchain()
        repo_olean = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
        with tempfile.TemporaryDirectory(prefix="anneal-b1-reg-") as td:
            tmp = Path(td)
            insp = audit.compile_lean_helper_binary(
                lean_bin, audit.INSPECTOR_LEAN_SOURCE, "OleanReplayInspector", tmp, sysroot=sysroot
            )
            self.assertIsNotNone(insp)

            jobs: list[tuple[Path, Path, Path, list[Path]]] = []
            b1_dir = tmp / "b1_ext"
            for rel, code in (
                ("Proof/B1UnsafeTerm", "namespace Proof.B1UnsafeTerm\ndef sneaky : Nat := unsafe (0 : Nat)\nend Proof.B1UnsafeTerm\n"),
                ("Proof/B1CbvEval", "namespace Proof.B1CbvEval\ndef f (x : Nat) : Nat := x\n@[cbv_eval] theorem f_eq (x : Nat) : f x = x := rfl\nend Proof.B1CbvEval\n"),
                ("Proof/B1CbvOpaque", "namespace Proof.B1CbvOpaque\n@[cbv_opaque] def h (x : Nat) : Nat := x\nend Proof.B1CbvOpaque\n"),
                ("Proof/Sub/B1ShadowNat", "namespace Proof.Sub.B1ShadowNat\ndef Nat : Type := Unit\nend Proof.Sub.B1ShadowNat\n"),
                ("Topic/Proofs/Defs", "namespace Topic.Proofs.Defs\ntheorem spoof : True := True.intro\nend Topic.Proofs.Defs\n"),
                ("Topic/B1Coe/Defs", "namespace Topic.B1Coe.Defs\ninductive DummyLocal | mk\n@[coe] def evilCoe (_ : DummyLocal) (n : Nat) : Bool := false\nend Topic.B1Coe.Defs\n"),
            ):
                s = b1_dir / f"{rel}.lean"
                s.parent.mkdir(parents=True, exist_ok=True)
                s.write_text(code, encoding="utf-8")
                jobs.append((b1_dir, s, b1_dir / f"{rel}.olean", []))

            pkg_pub15 = tmp / "pkg_pub15"
            for rel, code in (
                ("Topic/Defs", "module\nnamespace Topic.Defs\npublic inductive PubTag | mk\npublic instance pubInst : Inhabited PubTag := ⟨.mk⟩\nend Topic.Defs\n"),
                ("Proof/ImpAllPub", "module\npublic import Topic.Defs\nimport all Topic.Defs\nnamespace Proof.ImpAllPub\npublic def x : Topic.Defs.PubTag := default\nend Proof.ImpAllPub\n"),
            ):
                s = pkg_pub15 / f"{rel}.lean"
                s.parent.mkdir(parents=True, exist_ok=True)
                s.write_text(code, encoding="utf-8")
                jobs.append((pkg_pub15, s, pkg_pub15 / f"{rel}.olean", [pkg_pub15]))

            pkg_v = tmp / "pkg_verify"
            import shutil

            shutil.copytree(audit.FIXTURES_DIR / "00_clean_positive_pkg", pkg_v)
            v_deps = [pkg_v] + ([repo_olean] if repo_olean.is_dir() else [])
            for rel in ("Topic/Defs", "Anneal/TheoryHelper", "Topic/Proofs", "Verify/Topic"):
                jobs.append((pkg_v, pkg_v / f"{rel}.lean", pkg_v / f"{rel}.olean", v_deps))
            for rel, code in (
                ("Proof/B1ShadowTrusted", "import Trusted.VerificationResult\nnamespace Proof.B1ShadowTrusted\ndef VerificationResult.VerificationResult : Prop := True\nend Proof.B1ShadowTrusted\n"),
                ("Verify/EvilForall", 'import Trusted.VerificationResult\nnamespace Verify.EvilForall\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "evil", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified (_ : False) :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "evil", mirDialect := "V1", items := [{ identity := id1, certificate := False }] } :=\n  False.elim ‹False›\nend Verify.EvilForall\n'),
                ("Verify/OuterGood", 'import Trusted.VerificationResult\nimport Verify.Topic\nnamespace Verify.OuterGood\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "og", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "og", mirDialect := "V1", items := [{ identity := id1, certificate := True }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 True.intro\nend Verify.OuterGood\n'),
                ("Proof/ProvHelper", "namespace Proof.ProvHelper\ntheorem provEq : 1 + 1 = 2 := by native_decide\nend Proof.ProvHelper\n"),
                ("Verify/ItemProv", 'import Trusted.VerificationResult\nimport Proof.ProvHelper\nnamespace Verify.ItemProv\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "ip", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "ip", mirDialect := "V1", items := [{ identity := id1, certificate := 1 + 1 = 2 }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 Proof.ProvHelper.provEq\nend Verify.ItemProv\n'),
            ):
                s = pkg_v / f"{rel}.lean"
                s.parent.mkdir(parents=True, exist_ok=True)
                s.write_text(code, encoding="utf-8")
                jobs.append((pkg_v, s, pkg_v / f"{rel}.olean", v_deps))

            audit._compile_lean_jobs(lean_bin, tmp, jobs)

            cases: list[tuple[str, bool, str | None, dict[str, object]]] = [
                ("unsafe_term_only", False, "forbiddenInitOrCodegenHook", {"target_modules": ["Proof.B1UnsafeTerm"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("cbv_eval", False, "forbiddenMacroOrElab", {"target_modules": ["Proof.B1CbvEval"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("cbv_opaque", False, "forbiddenMacroOrElab", {"target_modules": ["Proof.B1CbvOpaque"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("len4_nat_shadow", False, "forbiddenShadowingOrExport", {"target_modules": ["Proof.Sub.B1ShadowNat"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("spoofed_defs", False, "spoofedExemptModule", {"target_modules": ["Topic.Proofs.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("coe_unused_binder", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B1Coe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("public_inst_import_all", False, "forbiddenImportAll", {"target_modules": ["Proof.ImpAllPub"], "olean_dirs": [pkg_pub15], "module_mode": True, "strict_proofs": True}),
                ("trusted_shadow", False, "forbiddenShadowingOrExport", {"target_modules": ["Proof.B1ShadowTrusted"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("verify_forall_false", False, "invalidVerifyRoot", {"target_modules": ["Verify.EvilForall"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("verify_unlisted_transitive", False, "invalidVerifyRoot", {"target_modules": ["Verify.OuterGood"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("verify_multi_item_isolated", True, None, {
                    "target_modules": ["Verify.ItemProv", "Verify.Topic"],
                    "olean_dirs": [pkg_v],
                    "source_map_dir": pkg_v,
                    "require_sources": True,
                    "allow_provisional_native": True,
                    "strict_proofs": True,
                }),
            ]
            reps = audit.batch_audit_modules(
                [c for (_, _, _, c) in cases],
                lean_bin=lean_bin,
                sysroot=sysroot,
                stage_dir=tmp,
                compiled_inspector=insp,
                chunk_size=5,
            )
            for (cid, exp_ok, exp_cat, _), rep in zip(cases, reps):
                self.assertEqual(rep["ok"], exp_ok, f"{cid}: {rep}")
                if exp_cat is not None:
                    self.assertEqual(rep["violations"][0]["category"], exp_cat, f"{cid}: {rep}")
                elif cid == "verify_multi_item_isolated":
                    by_mod = {it["module"]: it for it in rep["summary"]["items"]}
                    self.assertEqual(by_mod["Verify.ItemProv"]["status"], "ProvisionalNative")
                    self.assertEqual(by_mod["Verify.Topic"]["status"], "VerifiedUnconditional")


if __name__ == "__main__":
    unittest.main()
