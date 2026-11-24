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
        for lean_src in (audit.FAST_SMAP_LEAN_SOURCE, audit.INSPECTOR_LEAN_SOURCE):
            self.assertNotIn("enableInitializersExecution", lean_src)
            self.assertNotIn("loadExts := true", lean_src)
        self.assertIn("loadExts := false", audit.INSPECTOR_LEAN_SOURCE)

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

    def test_empty_path_cli_args_and_malformed_source_map_keys_return_exit_2(self) -> None:
        for argv in (
            ["--audit-module", "Proof.A", "--olean-dir", ""],
            ["--audit-module", "Proof.A", "--olean-dir", "   "],
            ["--audit-module", "Proof.A", "--source-map", ""],
            ["--audit-module", "Proof.A", "--lean", ""],
        ):
            with mock.patch("sys.stderr", io.StringIO()):
                self.assertEqual(audit.main(argv), 2, f"expected exit 2 for {argv}")
        with tempfile.TemporaryDirectory(prefix="anneal-smap-key-") as td:
            tmp = Path(td)
            valid_lean = tmp / "Valid.lean"
            valid_lean.write_text("theorem ok : True := True.intro\n", encoding="utf-8")
            bad_mod_json = tmp / "bad_mod.json"
            bad_mod_json.write_text(json.dumps({"../Bad": str(valid_lean)}), encoding="utf-8")
            with self.assertRaises(audit.AuditOperationalError):
                audit.resolve_source_map_arg(bad_mod_json, ["Proof.A"])
            empty_val_json = tmp / "empty_val.json"
            empty_val_json.write_text(json.dumps({"Proof.A": ""}), encoding="utf-8")
            with self.assertRaises(audit.AuditOperationalError):
                audit.resolve_source_map_arg(empty_val_json, ["Proof.A"])

    def test_relative_lean_path_rejected_exit_2(self) -> None:
        buf_out = io.StringIO()
        with mock.patch("sys.stdout", buf_out):
            rc = audit.main(
                ["--audit-module", "Foo.Bar", "--lean", "relative/bin/lean", "--json"]
            )
        self.assertEqual(rc, 2)

    def test_source_map_duplicate_keys_symlink_and_missing_target_handling(self) -> None:
        self.assertEqual(audit.classify_module_role_py("CrateVerify_zerocopy"), "verify")
        self.assertEqual(audit.classify_module_role_py("CrateVerify_zerocopy.Rollup"), "verify")
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            s1 = p / "A.lean"
            s1.write_text("theorem ok : True := True.intro\n", encoding="utf-8")
            dup_json = p / "dup_smap.json"
            dup_json.write_text(
                f'{{"Proof.A": "{s1}", "Proof.A": "{s1}"}}', encoding="utf-8"
            )
            buf_dup = io.StringIO()
            with mock.patch("sys.stdout", buf_dup):
                rc_dup = audit.main(
                    ["--audit-module", "Proof.A", "--source-map", str(dup_json), "--json"]
                )
            self.assertEqual(rc_dup, 2)
            self.assertTrue(json.loads(buf_dup.getvalue())["operational_error"])

            sym_json = p / "sym_smap.json"
            os.symlink(dup_json, sym_json)
            buf_sym = io.StringIO()
            with mock.patch("sys.stdout", buf_sym):
                rc_sym = audit.main(
                    ["--audit-module", "Proof.A", "--source-map", str(sym_json), "--json"]
                )
            self.assertEqual(rc_sym, 2)

            miss_json = p / "miss_smap.json"
            miss_json.write_text(
                json.dumps({"Proof.A": str(p / "DoesNotExist.lean")}), encoding="utf-8"
            )
            buf_miss = io.StringIO()
            with mock.patch("sys.stdout", buf_miss):
                rc_miss = audit.main(
                    ["--audit-module", "Proof.A", "--source-map", str(miss_json), "--json"]
                )
            self.assertEqual(rc_miss, 1)
            miss_payload = json.loads(buf_miss.getvalue())
            self.assertFalse(miss_payload["ok"])
            self.assertEqual(miss_payload["violations"][0]["category"], "missingSourceText")

            # Non-UTF-8 `--source-map` JSON must exit 2 cleanly (never crash with UnicodeDecodeError).
            bad_utf8_json = p / "bad_utf8.json"
            bad_utf8_json.write_bytes(b"\xff\xfe\xfd")
            buf_utf8 = io.StringIO()
            with mock.patch("sys.stdout", buf_utf8):
                rc_utf8 = audit.main(
                    ["--audit-module", "Proof.A", "--source-map", str(bad_utf8_json), "--json"]
                )
            self.assertEqual(rc_utf8, 2)
            self.assertTrue(json.loads(buf_utf8.getvalue())["operational_error"])


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

    def test_path_escape_and_slash_module_names_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            base = p / "base"
            outside = p / "outside"
            base.mkdir()
            outside.mkdir()
            ext_file = outside / "Out.olean"
            ext_file.write_bytes(b"placeholder")
            sym_outside = p / "sym_outside"
            os.symlink(outside, sym_outside)
            # `_check_intermediate_dirs_fail_closed` MUST raise AuditOperationalError on base_dir escape
            # (never silently return True on ValueError and follow an out-of-tree symlink!).
            with self.assertRaises(audit.AuditOperationalError):
                audit.stat_regular_fail_closed(sym_outside / "Out.olean", base_dir=base)
            # Slash / backslash / whitespace / NUL in module names MUST fail before touching disk!
            _, sysroot = audit.resolve_lean_toolchain()
            for bad_mod in (
                str(sym_outside / "Out"),
                "Proof/SlashSpoof",
                "Proof\\Backslash",
                "Proof Bad",
                "Proof\x00Null",
            ):
                with self.assertRaises(audit.AuditPolicyError, msg=bad_mod) as ctx:
                    audit.precheck_olean_dirs_and_locate_modules([bad_mod], [base], sysroot, None)
                self.assertEqual(ctx.exception.category, "anonymousConstantName")
                self.assertIsNone(audit.classify_module_role_py(bad_mod))


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
            'def echo! (s : String) : String := s\ndef bangCall : String := echo! "{"\n',
            'def «echo!» (s : String) : String := s\ndef escBangCall : String := «echo!» "{"\n',
            "def decideTerm : Bool := decide ('.' ∉ ['a'])\n",
            "def trace : Array Nat := #[0]\ndef traceIdx : Nat := trace[0]!\n",
            'def f (trace : List (String -> Nat)) (h : 0 < trace.length) : Nat := trace[0] "{"\n',
            'structure S where trace : Array (String -> Nat)\ndef dotTrace (x : S) (i : Fin x.trace.size) : Nat := x.trace[i] "{"\n',
            'structure S2 where trace : Array (String -> Nat)\ndef escDotTrace («x» : S2) (i : Fin «x».trace.size) : Nat := «x».trace[i] "{"\n',
            'structure G where trace_goal : Array (String -> Nat)\ndef dotTraceGoal (x : G) (i : Fin x.trace_goal.size) : Nat := x.trace_goal[i] "{"\n',
            'def g : String := trace[a b] "{"\n',
            'def numsInHole : String := s!"{1.5} {1e-2} {1e+2} {0x1f} {p.1}"\n',
            'def decOkHole : String := s!"{by decide +kernel}"\n',
            "def «decide» : Int := 5\ndef kernel : Int := 3\ndef ok : Int := «decide» -kernel\n",
            'def strWithDecide : String := "decide -kernel"\n',
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
            ("theorem p : 1 + 1 = 2 := by decide -kernel", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide +revert", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide /- comment -/ -kernel", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide (kernel := false)", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide (revert := true)", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide(kernel := false)", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide-kernel", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide+revert", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide +kernel-kernel", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by iterate 1decide -kernel", "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide +«revert»", "forbiddenSourceOption"),
            ('def «"» : Nat := 1\ntheorem evil : 1 + 1 = 2 := by decide -kernel\ndef «"2» : Nat := 2', "forbiddenSourceOption"),
            ("def «--» : Nat := 1; theorem evil : 1 + 1 = 2 := by decide -kernel", "forbiddenSourceOption"),
            ("def «/-» : Nat := 1\ntheorem evil : 1 + 1 = 2 := by decide -kernel\ndef «-/» : Nat := 2", "forbiddenSourceOption"),
            ('def s : String := «s!» "{let _ : 1 + 1 = 2 := by decide -kernel; 0}"', "forbiddenSourceOption"),
            ('def sneak : Nat := dbg_trace "{(by set_option debug.skipKernelTC true in exact (0 : Nat) : Nat)}"; 0', "forbiddenSourceOption"),
            ('def sneak : Nat := dbg_trace "{let _ : 1 + 1 = 2 := (by decide -kernel); 0}"; 0', "forbiddenSourceOption"),
            ('def sneak : IO Unit := println! "{(by set_option debug.skipKernelTC true in exact (0 : Nat) : Nat)}"', "forbiddenSourceOption"),
            ('def sneak : IO Unit := println! "{let _ : 1 + 1 = 2 := (by decide -kernel); 0}"', "forbiddenSourceOption"),
            ('def sneak := Macro.trace[foo] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s : String := s!"{show Prop from by decide -kernel}"', "forbiddenSourceOption"),
            ("@[app_delab Nat.add] def badDelab : Nat := 0", "forbiddenSourceOption"),
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
            ("theorem binSkip : 1 + 1 = 2 := by iterate 0b1decide -kernel", "forbiddenSourceOption"),
            ("theorem octSkip : 1 + 1 = 2 := by iterate 0o1decide -kernel", "forbiddenSourceOption"),
            ("theorem undSkip : 1 + 1 = 2 := by iterate 1_0decide -kernel", "forbiddenSourceOption"),
            ('def s := v! "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := throwError "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := reportIssue! "{let _ : 1 + 1 = 2 := (by decide -kernel); 0}"', "forbiddenSourceOption"),
            ('def s := reportDbgIssue! "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := reportEMatchIssue! "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := trace_goal[grind] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := s!"{0x1builtin_elab}"', "forbiddenSourceOption"),
            ("theorem p : 1 + 1 = 2 := by decide («kernel» := false)", "forbiddenSourceOption"),
            ("set_option «debug».«skipKernelTC» true in def x := 0", "forbiddenSourceOption"),
            ('def s := Macro.trace[foo ] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := Macro.trace[foo /- c -/] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := Lean.Macro.trace[foo] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := «Macro».trace[foo] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ("@[command_code_action] def badCA : Nat := 0", "forbiddenSourceOption"),
            ("@[combinator_formatter Foo] def badFmt : Nat := 0", "forbiddenSourceOption"),
            ('def s := trace_goal[foo ] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := «trace»[foo] "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := throwErrorAt stx "{(by set_option debug.skipKernelTC true in exact 0)}"', "forbiddenSourceOption"),
            ('def s := s!"{by iterate 0b1decide -kernel}"', "forbiddenSourceOption"),
            ('def s := s!"{by iterate 0o1decide -kernel}"', "forbiddenSourceOption"),
            ('def s := s!"{by 1.5decide -kernel}"', "forbiddenSourceOption"),
            ('def s := s!"{by 1e5decide -kernel}"', "forbiddenSourceOption"),
            ('def s := s!"{by 1e+5decide -kernel}"', "forbiddenSourceOption"),
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
                ("Proof/A1EvilSizeOfNat", "namespace Proof.A1EvilSizeOfNat\ninductive P : Prop | mk\ninstance P._sizeOf_inst : SizeOf Nat := ⟨fun _ => 999999⟩\nend Proof.A1EvilSizeOfNat\n"),
                ("Proof/A1EvilSizeOfProp", "namespace Proof.A1EvilSizeOfProp\ninductive P : Prop | mk\ninstance P._sizeOf_inst : SizeOf P := ⟨fun _ => 999999⟩\nend Proof.A1EvilSizeOfProp\n"),
                ("Topic/A1InstCoe/Defs", "namespace Topic.A1InstCoe.Defs\ninductive LocalAnchor | mk\ninstance : Inhabited LocalAnchor := ⟨.mk⟩\n@[coe] def sneakyInstCoe (n : Nat) [Inhabited LocalAnchor] : Bool := false\nend Topic.A1InstCoe.Defs\n"),
                ("Topic/A1OptCoe/Defs", "namespace Topic.A1OptCoe.Defs\ninductive LocalAnchor | mk\n@[coe] def sneakyOptCoe (n : Nat) (_ : LocalAnchor := .mk) : Bool := false\nend Topic.A1OptCoe.Defs\n"),
                ("Topic/A1AbbrCoe/Defs", "namespace Topic.A1AbbrCoe.Defs\ninductive LocalAnchor | mk\nabbrev HiddenTail := (_ : LocalAnchor := .mk) → Bool\n@[coe] def sneakyAbbrCoe (n : Nat) : HiddenTail := fun _ => false\nend Topic.A1AbbrCoe.Defs\n"),
                ("Topic/B2CoeFirstArg/Defs", "namespace Topic.B2CoeFirstArg.Defs\ninductive LocalAnchor | mk\n@[coe] def evilCoe (n : Nat) (x : LocalAnchor) : Bool := false\nend Topic.B2CoeFirstArg.Defs\n"),
                ("Topic/B2GoodCoe/Defs", "namespace Topic.B2GoodCoe.Defs\ninductive GoodTag | mk\n@[coe] def toNat (_ : GoodTag) : Nat := 0\n@[coe] def ofNat (_ : Nat) : GoodTag := .mk\nend Topic.B2GoodCoe.Defs\n"),
                ("Topic/B2OutCls", "namespace Topic.B2OutCls\nabbrev MyOut (α : Sort u) := outParam α\nclass MyClass (a : Type) (b : MyOut Type) where val : a\nend Topic.B2OutCls\n"),
                ("Proof/B2DbgTraceSkip", 'namespace Proof.B2DbgTraceSkip\ndef sneak : Nat :=\n  dbg_trace "{(by set_option debug.skipKernelTC true in exact (0 : Nat) : Nat)}"\n  0\nend Proof.B2DbgTraceSkip\n'),
                ("Proof/B2PrintlnDecide", 'namespace Proof.B2PrintlnDecide\ndef sneak : IO Unit :=\n  println! "{let _ : 1 + 1 = 2 := (by decide -kernel); (0 : Nat)}"\nend Proof.B2PrintlnDecide\n'),
                ("Proof/B2DecideNoSpace", "namespace Proof.B2DecideNoSpace\ntheorem t1 : 1 + 1 = 2 := by decide(kernel := false)\nend Proof.B2DecideNoSpace\n"),
                ("Proof/B2GuillDecide", 'namespace Proof.B2GuillDecide\ndef «"» : Nat := 1\ntheorem evil : 1 + 1 = 2 := by decide -kernel\ndef «"2» : Nat := 2\nend Proof.B2GuillDecide\n'),
                ("Proof/A2BinDecide", "namespace Proof.A2BinDecide\ntheorem binSkip : 1 + 1 = 2 := by iterate 0b1decide -kernel\nend Proof.A2BinDecide\n"),
                ("Proof/A2OctDecide", "namespace Proof.A2OctDecide\ntheorem octSkip : 1 + 1 = 2 := by iterate 0o1decide -kernel\nend Proof.A2OctDecide\n"),
                ("Proof/A2ValidMutual", "namespace Proof.A2ValidMutual\nmutual\n  def isEven : Nat -> Bool\n    | 0 => true\n    | n + 1 => isOdd n\n  def isOdd : Nat -> Bool\n    | 0 => false\n    | n + 1 => isEven n\nend\ntheorem even4 : isEven 4 = true := rfl\nend Proof.A2ValidMutual\n"),
                ("Topic/A2GoodCoeFun/Defs", "namespace Topic.A2GoodCoeFun.Defs\nstructure MyPred where\n  run : Nat -> Bool\ninstance : CoeFun MyPred (fun _ => Nat -> Bool) where\n  coe p := p.run\ninstance : Inhabited (Nat -> MyPred) := ⟨fun _ => ⟨fun _ => true⟩⟩\nend Topic.A2GoodCoeFun.Defs\n"),
                ("Topic/A2NoindexHijack/Defs", "namespace Topic.A2NoindexHijack.Defs\ninductive LocalAnchor | mk\ninstance evilWildcard : Inhabited (no_index LocalAnchor) := ⟨.mk⟩\nend Topic.A2NoindexHijack.Defs\n"),
                ("Topic/B3GoodAlias/Defs", "namespace Topic.B3GoodAlias.Defs\ninductive LocalAnchor | mk\ndef LocalAlias := LocalAnchor\ninductive ParamInd (α : Type u) : Nat -> Type u | nil : ParamInd α 0\ninstance instAlias : Inhabited LocalAlias := ⟨LocalAnchor.mk⟩\ninstance instArrow : Inhabited (Nat -> LocalAnchor) := ⟨fun _ => .mk⟩\ninstance instProd : Inhabited (Prod Nat LocalAnchor) := ⟨(0, .mk)⟩\ninstance instMyHAdd : HAdd LocalAnchor Nat LocalAnchor := ⟨fun a _ => a⟩\n@[coe] def toNat (_ : LocalAnchor) : Nat := 0\nend Topic.B3GoodAlias.Defs\n"),
                ("Proof/B3HoleBinDecide", 'namespace Proof.B3HoleBinDecide\ndef sneak : String := s!"{(by iterate 0b1decide -kernel : 1 + 1 = 2) |> fun _ => (0 : Nat)}"\nend Proof.B3HoleBinDecide\n'),
                ("Topic/BadSkipSrc", "namespace Topic.BadSkipSrc\nset_option debug.skipKernelTC true in\ndef v : Nat := 1\nend Topic.BadSkipSrc\n"),
            ):
                s = b1_dir / f"{rel}.lean"
                s.parent.mkdir(parents=True, exist_ok=True)
                s.write_text(code, encoding="utf-8")
                jobs.append((b1_dir, s, b1_dir / f"{rel}.olean", []))
            b2_hijack = b1_dir / "Topic" / "B2OutHijack" / "Defs.lean"
            b2_hijack.parent.mkdir(parents=True, exist_ok=True)
            b2_hijack.write_text(
                "import Topic.B2OutCls\nnamespace Topic.B2OutHijack.Defs\ninductive LocalAnchor | mk\ninstance evilOutParamHijack : Topic.B2OutCls.MyClass Nat LocalAnchor := ⟨999⟩\nend Topic.B2OutHijack.Defs\n",
                encoding="utf-8",
            )
            jobs.append((b1_dir, b2_hijack, b1_dir / "Topic" / "B2OutHijack" / "Defs.olean", [b1_dir]))
            top_clean = b1_dir / "Proof" / "TopClean.lean"
            top_clean.parent.mkdir(parents=True, exist_ok=True)
            top_clean.write_text(
                "import Topic.BadSkipSrc\nnamespace Proof.TopClean\ntheorem ok : Topic.BadSkipSrc.v = 1 := rfl\nend Proof.TopClean\n",
                encoding="utf-8",
            )
            jobs.append((b1_dir, top_clean, b1_dir / "Proof" / "TopClean.olean", [b1_dir]))

            pkg_pub15 = tmp / "pkg_pub15"
            for rel, code in (
                ("Topic/Defs", "module\nnamespace Topic.Defs\npublic inductive PubTag | mk\npublic instance pubInst : Inhabited PubTag := ⟨.mk⟩\nend Topic.Defs\n"),
                ("Proof/ImpAllPub", "module\npublic import Topic.Defs\nimport all Topic.Defs\nnamespace Proof.ImpAllPub\npublic def x : Topic.Defs.PubTag := default\nend Proof.ImpAllPub\n"),
                (
                    "Topic/A3ModPriv/Defs",
                    "module\nnamespace Topic.A3ModPriv.Defs\npublic inductive LocalAnchor | mk\npublic abbrev MyAnchor := LocalAnchor\nprivate structure PrivT where x : Nat\nprivate inductive PrivList | nil | cons (x : Nat) (tl : PrivList)\nprivate instance : Inhabited PrivT := ⟨⟨0⟩⟩\npublic structure Holder where trace : Array (String -> Nat)\npublic def useDotTrace (h : Holder) (i : Fin h.trace.size) : Nat := h.trace[i] \"{\"\npublic inductive Tag {n : Nat} (α : Type) | mk (x : α)\npublic inductive Box (h : True) (α : Type) | mk (x : α)\npublic inductive LocalProp : Prop | mk\npublic instance instTagImpl : Inhabited (@Tag 5 LocalAnchor) := ⟨.mk .mk⟩\npublic instance instBoxProof : Inhabited (Box True.intro LocalAnchor) := ⟨.mk .mk⟩\npublic instance instFinAdd (n : Nat) : Inhabited (Fin (n + 1) → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instFinSucc (n : Nat) : Inhabited (Fin (Nat.succ n) → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instAndProp : Decidable (And False LocalProp) := isFalse (fun h => h.1)\npublic instance instQuotArr : Inhabited (Quot (fun (_ _ : Nat) => True) → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instOptAbbr : Inhabited (Option MyAnchor) := ⟨some .mk⟩\npublic instance instSub : Inhabited { x : LocalAnchor // x = x } := ⟨⟨.mk, rfl⟩⟩\npublic instance instFinArr : Inhabited (Fin 8 → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instOptArr : Inhabited (Option Nat → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instArrArr : Inhabited ((Nat → Bool) → LocalAnchor) := ⟨fun _ => .mk⟩\npublic instance instProd : Inhabited (Prod Nat LocalAnchor) := ⟨(0, .mk)⟩\nend Topic.A3ModPriv.Defs\n",
                ),
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
                ("Proof/ProvHelper", "namespace Proof.ProvHelper\ntheorem provEq : 1 + 1 = 2 := by native_decide\ndef provProp : Prop := True\nend Proof.ProvHelper\n"),
                ("Verify/ItemProv", 'import Trusted.VerificationResult\nimport Proof.ProvHelper\nnamespace Verify.ItemProv\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "ip", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "ip", mirDialect := "V1", items := [{ identity := id1, certificate := 1 + 1 = 2 }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 Proof.ProvHelper.provEq\nend Verify.ItemProv\n'),
                ("Verify/ProofLeak", 'import Trusted.VerificationResult\nimport Topic.Proofs\nnamespace Verify.ProofLeak\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "pl", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "pl", mirDialect := "V1", items := [{ identity := id1, certificate := Topic.Proofs.quoteCh = \'"\' }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 rfl\nend Verify.ProofLeak\n'),
                ("CrateVerify_demo/Rollup", 'import Trusted.VerificationResult\nnamespace CrateVerify_demo.Rollup\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "cv", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "cv", mirDialect := "V1", items := [{ identity := id1, certificate := True }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 True.intro\nend CrateVerify_demo.Rollup\n'),
                ("Verify/B3PrivMod", 'import Trusted.VerificationResult\nnamespace Verify.B3PrivMod\ndef id1 : Trusted.VerificationResult.ArtifactIdentity :=\n  { defPath := "pm", mirDialect := "V1", mirModuleSha256 := "00" }\ntheorem verified :\n    Trusted.VerificationResult.CrateVerificationResult\n      { crateName := "pm", mirDialect := "V1", items := [{ identity := id1, certificate := True }] } :=\n  Trusted.VerificationResult.mkPolyVerificationResult id1 True.intro\nend Verify.B3PrivMod\n'),
            ):
                s = pkg_v / f"{rel}.lean"
                s.parent.mkdir(parents=True, exist_ok=True)
                s.write_text(code, encoding="utf-8")
                jobs.append((pkg_v, s, pkg_v / f"{rel}.olean", v_deps))

            clean_nm_lean = b1_dir / "Topic" / "B1CleanNonMod.lean"
            clean_nm_lean.parent.mkdir(parents=True, exist_ok=True)
            clean_nm_lean.write_text(
                "namespace Topic.B1CleanNonMod\ntheorem ok : True := True.intro\nend Topic.B1CleanNonMod\n",
                encoding="utf-8",
            )
            jobs.append((b1_dir, clean_nm_lean, b1_dir / "Topic" / "B1CleanNonMod.olean", []))

            audit._compile_lean_jobs(lean_bin, tmp, jobs)

            # Forge Pass A1 binary `.olean` edge cases (`extraConstNames` provenance spoofing,
            # cyclic `.defnInfo` before `Kernel.whnf`, and split-brain exported extension injection)
            a1_forged = tmp / "a1_forged"
            a1_forge_lean = tmp / "A1Forge.lean"
            a1_forge_lean.write_text(
                r"""import Lean
import Lean.Meta.Instances
import Lean.Meta.CoeAttr
open Lean
def writeO (dir : System.FilePath) (m : Name) (d : ModuleData) : IO Unit := do
  let p := dir / (System.mkFilePath (m.components.map Name.toString) |>.addExtension "olean")
  if let some par := p.parent then IO.FS.createDirAll par
  saveModuleData p m d

def main (args : List String) : IO UInt32 := do
  let [outStr, _] := args | return 2
  let out := System.FilePath.mk outStr
  let okThm : ConstantInfo := .thmInfo {
    name := `Proof.A1ExtraSpoof.ok, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro,
    all := [`Proof.A1ExtraSpoof.ok]
  }
  writeO (out / "extra_spoof") `Proof.A1ExtraSpoof {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.A1ExtraSpoof.ok], constants := #[okThm],
    extraConstNames := #[``Nat.add], entries := #[]
  }
  let cycDef : ConstantInfo := .defnInfo {
    name := `Proof.A1CyclicWhnf.loop, levelParams := [],
    type := mkConst ``Bool, value := mkConst `Proof.A1CyclicWhnf.loop,
    hints := .regular 0, safety := .safe, all := [`Proof.A1CyclicWhnf.loop]
  }
  let cycAxName := `Proof.A1CyclicWhnf.f._native.decide.ax_1
  let cycAx : ConstantInfo := .axiomInfo {
    name := cycAxName, levelParams := [],
    type := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) (mkConst `Proof.A1CyclicWhnf.loop) (mkConst ``Bool.true),
    isUnsafe := false
  }
  writeO (out / "cyclic_whnf") `Proof.A1CyclicWhnf {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.A1CyclicWhnf.loop, cycAxName], constants := #[cycDef, cycAx],
    extraConstNames := #[], entries := #[]
  }
  let cycDef2 : ConstantInfo := .defnInfo {
    name := `Proof.A1CyclicBehindRec.loop, levelParams := [],
    type := mkConst ``Bool, value := mkConst `Proof.A1CyclicBehindRec.loop,
    hints := .regular 0, safety := .safe, all := [`Proof.A1CyclicBehindRec.loop]
  }
  let cycAxName2 := `Proof.A1CyclicBehindRec.f._native.decide.ax_1
  let cycAx2 : ConstantInfo := .axiomInfo {
    name := cycAxName2, levelParams := [],
    type := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool)
      (mkApp (mkConst ``Bool.not) (mkConst `Proof.A1CyclicBehindRec.loop)) (mkConst ``Bool.true),
    isUnsafe := false
  }
  writeO (out / "cyclic_behind_rec") `Proof.A1CyclicBehindRec {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.A1CyclicBehindRec.loop, cycAxName2], constants := #[cycDef2, cycAx2],
    extraConstNames := #[], entries := #[]
  }
  let sbDir := out / "split_ext" / "Proof"
  IO.FS.createDirAll sbDir
  let sbFile := sbDir / "A1SplitExt.olean"
  let sbThm : ConstantInfo := .thmInfo {
    name := `Proof.A1SplitExt.ok, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro,
    all := [`Proof.A1SplitExt.ok]
  }
  let sbPriv : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[`Proof.A1SplitExt.ok], constants := #[sbThm],
    extraConstNames := #[], entries := #[]
  }
  let sbExp : ModuleData := {
    sbPriv with
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast ()])]
  }
  saveModuleDataParts `Proof.A1SplitExt #[
    (sbFile, sbExp),
    (OLeanLevel.server.adjustFileName sbFile, sbPriv),
    (OLeanLevel.private.adjustFileName sbFile, sbPriv)
  ]
  -- Pass B2 forged edge cases: 10-layer opaque chain, Init.Prelude-only batch leakage,
  -- `folderExt` interpreter hook, `.ir.sig` split-brain constants/non-IR ext, `isModule` mismatch,
  -- and `module` importing non-`module`.
  let mut opNames : Array Name := #[]
  let mut opInfos : Array ConstantInfo := #[]
  let op0 := `Proof.B2DeepOp.op0
  opNames := opNames.push op0
  opInfos := opInfos.push (.opaqueInfo {
    name := op0, levelParams := [], type := mkConst ``Bool,
    value := mkConst ``Bool.false, isUnsafe := false, all := [op0]
  })
  let mut prevOp := op0
  for i in [:10] do
    let dn := Name.str `Proof.B2DeepOp s!"d{i}"
    opNames := opNames.push dn
    opInfos := opInfos.push (.defnInfo {
      name := dn, levelParams := [], type := mkConst ``Bool,
      value := mkApp2 (mkConst ``Bool.and) (mkConst ``Bool.true) (mkConst prevOp),
      hints := .regular 1, safety := .safe, all := [dn]
    })
    let on := Name.str `Proof.B2DeepOp s!"o{i+1}"
    opNames := opNames.push on
    opInfos := opInfos.push (.opaqueInfo {
      name := on, levelParams := [], type := mkConst ``Bool,
      value := mkConst dn, isUnsafe := false, all := [on]
    })
    prevOp := on
  let deepAx := `Proof.B2DeepOp.f._native.decide.ax_1
  opNames := opNames.push deepAx
  opInfos := opInfos.push (.axiomInfo {
    name := deepAx, levelParams := [],
    type := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) (mkConst prevOp) (mkConst ``Bool.true),
    isUnsafe := false
  })
  writeO (out / "b2_deep_opaque") `Proof.B2DeepOp {
    isModule := false, imports := #[{ module := `Init }],
    constNames := opNames, constants := opInfos, extraConstNames := #[], entries := #[]
  }
  let prelDef : ConstantInfo := .defnInfo {
    name := `Proof.B2PrelOnly.useXor, levelParams := [], type := mkConst ``Nat,
    value := mkApp2 (mkConst ``Nat.xor) (mkConst ``Nat.zero) (mkConst ``Nat.zero),
    hints := .regular 1, safety := .safe, all := [`Proof.B2PrelOnly.useXor]
  }
  writeO (out / "b2_prelude_only") `Proof.B2PrelOnly {
    isModule := false, imports := #[{ module := `Init.Prelude }],
    constNames := #[`Proof.B2PrelOnly.useXor], constants := #[prelDef],
    extraConstNames := #[], entries := #[]
  }
  let foldOk : ConstantInfo := .thmInfo {
    name := `Proof.B2FolderExt.ok, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B2FolderExt.ok]
  }
  writeO (out / "b2_folder_ext") `Proof.B2FolderExt {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.B2FolderExt.ok], constants := #[foldOk], extraConstNames := #[],
    entries := #[(`Lean.Compiler.LCNF.Simp.ConstantFold.folderExt, #[unsafe unsafeCast ()])]
  }
  let irDir := out / "b2_ir_split" / "Proof"
  IO.FS.createDirAll irDir
  let irOlean := irDir / "B2IrSplit.olean"
  let cleanIr : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[`Proof.B2IrSplit.ok],
    constants := #[.thmInfo { name := `Proof.B2IrSplit.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B2IrSplit.ok] }],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B2IrSplit #[
    (irOlean, cleanIr),
    (OLeanLevel.server.adjustFileName irOlean, cleanIr),
    (OLeanLevel.private.adjustFileName irOlean, cleanIr)
  ]
  let badIrSig : ModuleData := {
    isModule := false, imports := #[],
    constNames := #[], constants := #[], extraConstNames := #[],
    entries := #[(`Lean.aliasExtension, #[unsafe unsafeCast ()])]
  }
  let emptyIr : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[], constants := #[], extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B2IrSplit #[
    (irOlean.withExtension "ir.sig", badIrSig),
    (irOlean.withExtension "ir", emptyIr)
  ]
  let mmDir := out / "b2_ismod" / "Proof"
  IO.FS.createDirAll mmDir
  let mmOlean := mmDir / "B2IsMod.olean"
  let mmExp : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[`Proof.B2IsMod.ok],
    constants := #[.thmInfo { name := `Proof.B2IsMod.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B2IsMod.ok] }],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B2IsMod #[
    (mmOlean, mmExp),
    (OLeanLevel.server.adjustFileName mmOlean, { mmExp with isModule := false }),
    (OLeanLevel.private.adjustFileName mmOlean, { mmExp with isModule := false })
  ]
  let mnDir := out / "b2_mod_imp_nm" / "Proof"
  IO.FS.createDirAll mnDir
  saveModuleData (mnDir / "DepNM.olean") `Proof.DepNM {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.DepNM.ok],
    constants := #[.thmInfo { name := `Proof.DepNM.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.DepNM.ok] }],
    extraConstNames := #[], entries := #[]
  }
  let topModData : ModuleData := {
    isModule := true, imports := #[{ module := `Init }, { module := `Proof.DepNM }],
    constNames := #[`Proof.TopMod.ok],
    constants := #[.thmInfo { name := `Proof.TopMod.ok, levelParams := [], type := mkConst ``True, value := mkConst `Proof.DepNM.ok, all := [`Proof.TopMod.ok] }],
    extraConstNames := #[], entries := #[]
  }
  let topOlean := mnDir / "TopMod.olean"
  saveModuleDataParts `Proof.TopMod #[
    (topOlean, topModData),
    (OLeanLevel.server.adjustFileName topOlean, topModData),
    (OLeanLevel.private.adjustFileName topOlean, topModData)
  ]
  -- Pass A2 forged edge cases:
  -- 1. Stdlib `@[extern]` opaque (`String.Internal.length "anneal" == 0`) under `--allow-provisional-native`
  let a2ExtAx := `Proof.A2ExternFalse.f._native.decide.ax_1
  let a2ExtLhs := mkApp2 (mkConst ``Nat.beq) (mkApp (mkConst ``String.Internal.length) (mkStrLit "anneal")) (mkNatLit 0)
  let a2ExtCi : ConstantInfo := .axiomInfo {
    name := a2ExtAx, levelParams := [],
    type := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) a2ExtLhs (mkConst ``Bool.true),
    isUnsafe := false
  }
  writeO (out / "a2_extern_false") `Proof.A2ExternFalse {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2ExtAx], constants := #[a2ExtCi],
    extraConstNames := #[], entries := #[]
  }
  -- 2. Forged `Meta.instanceExtension` entry spoofing `globalName? := some goodInst` while `val := evilNatFn`
  let a2AnchorName := `Topic.A2SpoofInst.Defs.Anchor
  let a2AnchorMk := `Topic.A2SpoofInst.Defs.Anchor.mk
  let a2AnchorInd : ConstantInfo := .inductInfo {
    name := a2AnchorName, levelParams := [], type := mkSort Level.one,
    numParams := 0, numIndices := 0, all := [a2AnchorName], ctors := [a2AnchorMk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  }
  let a2AnchorCtor : ConstantInfo := .ctorInfo {
    name := a2AnchorMk, levelParams := [], type := mkConst a2AnchorName,
    induct := a2AnchorName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  }
  let a2AnchorRec : ConstantInfo := .recInfo {
    name := `Topic.A2SpoofInst.Defs.Anchor.rec, levelParams := [`u],
    type := mkForall `motive .implicit (mkForall `x .default (mkConst a2AnchorName) (mkSort (.param `u)))
      (mkForall `h .default (mkApp (mkBVar 0) (mkConst a2AnchorMk))
        (mkForall `t .default (mkConst a2AnchorName) (mkApp (mkBVar 2) (mkBVar 0)))),
    all := [a2AnchorName], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := a2AnchorMk, nfields := 0, rhs := mkLambda `motive .implicit (mkForall `x .default (mkConst a2AnchorName) (mkSort (.param `u))) (mkLambda `h .default (mkApp (mkBVar 0) (mkConst a2AnchorMk)) (mkBVar 0)) }],
    k := true, isUnsafe := false
  }
  let a2GoodInstName := `Topic.A2SpoofInst.Defs.goodInst
  let a2GoodInst : ConstantInfo := .defnInfo {
    name := a2GoodInstName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) (mkConst a2AnchorName),
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) (mkConst a2AnchorName) (mkConst a2AnchorMk),
    hints := .abbrev, safety := .safe, all := [a2GoodInstName]
  }
  let a2EvilFnName := `Topic.A2SpoofInst.Defs.evilNatInst
  let a2EvilFn : ConstantInfo := .defnInfo {
    name := a2EvilFnName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) (mkConst ``Nat),
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) (mkConst ``Nat) (mkNatLit 999),
    hints := .abbrev, safety := .safe, all := [a2EvilFnName]
  }
  let spoofEntry : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[.const ``Inhabited 1, .const a2AnchorName 0],
    val := mkConst a2EvilFnName,
    priority := 1000,
    globalName? := some a2GoodInstName,
    synthOrder := #[],
    attrKind := .global
  }
  writeO (out / "a2_spoof_inst") `Topic.A2SpoofInst.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, a2GoodInstName, a2EvilFnName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, a2GoodInst, a2EvilFn],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast spoofEntry])]
  }
  -- 3. Duplicate extension keys in `ModuleData.entries`
  let dupExtThm : ConstantInfo := .thmInfo {
    name := `Proof.A2DupExt.ok, levelParams := [],
    type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.A2DupExt.ok]
  }
  writeO (out / "a2_dup_ext") `Proof.A2DupExt {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.A2DupExt.ok], constants := #[dupExtThm],
    extraConstNames := #[],
    entries := #[(`Lean.declRangeExt, #[]), (`Lean.declRangeExt, #[])]
  }
  -- 4. Non-module `.olean` paired with stray `.ir.sig` + `.ir`
  let nmIrDir := out / "a2_nm_ir" / "Proof"
  IO.FS.createDirAll nmIrDir
  let nmIrOlean := nmIrDir / "A2NmIr.olean"
  saveModuleData nmIrOlean `Proof.A2NmIr {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.A2NmIr.ok],
    constants := #[.thmInfo { name := `Proof.A2NmIr.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.A2NmIr.ok] }],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.A2NmIr #[
    (nmIrOlean.withExtension "ir.sig", emptyIr),
    (nmIrOlean.withExtension "ir", emptyIr)
  ]
  -- 5. Transitive early `finalizeImport` `"already contains"` collision across two dependencies
  let trDir := out / "a2_trans_dup" / "Proof"
  IO.FS.createDirAll trDir
  let dupSharedDef1 : ConstantInfo := .defnInfo {
    name := `Proof.SharedCollision.val, levelParams := [], type := mkConst ``Nat,
    value := mkConst ``Nat.zero, hints := .abbrev, safety := .safe, all := [`Proof.SharedCollision.val]
  }
  let dupSharedDef2 : ConstantInfo := .defnInfo {
    name := `Proof.SharedCollision.val, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 1, hints := .abbrev, safety := .safe, all := [`Proof.SharedCollision.val]
  }
  saveModuleData (trDir / "DepA.olean") `Proof.DepA {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.SharedCollision.val], constants := #[dupSharedDef1],
    extraConstNames := #[], entries := #[]
  }
  saveModuleData (trDir / "DepB.olean") `Proof.DepB {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.SharedCollision.val], constants := #[dupSharedDef2],
    extraConstNames := #[], entries := #[]
  }
  saveModuleData (trDir / "TopDup.olean") `Proof.TopDup {
    isModule := false, imports := #[{ module := `Init }, { module := `Proof.DepA }, { module := `Proof.DepB }],
    constNames := #[`Proof.TopDup.ok],
    constants := #[.thmInfo { name := `Proof.TopDup.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.TopDup.ok] }],
    extraConstNames := #[], entries := #[]
  }
  -- Pass B3 forged regressions:
  -- B3-1: Forged `_sizeOf_inst` trailing-key wildcard (`#[.const SizeOf 1, .star, .const Anchor 0]`)
  let b3SizeOfName := `Proof.B3SizeOfOv.Anchor._sizeOf_inst
  let b3Anc := `Proof.B3SizeOfOv.Anchor
  let b3AncMk := `Proof.B3SizeOfOv.Anchor.mk
  let b3AncInd : ConstantInfo := .inductInfo {
    name := b3Anc, levelParams := [], type := mkSort Level.one,
    numParams := 0, numIndices := 0, all := [b3Anc], ctors := [b3AncMk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  }
  let b3AncCtor : ConstantInfo := .ctorInfo {
    name := b3AncMk, levelParams := [], type := mkConst b3Anc,
    induct := b3Anc, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  }
  let b3AncRec : ConstantInfo := .recInfo {
    name := `Proof.B3SizeOfOv.Anchor.rec, levelParams := [`u],
    type := mkForall `motive .implicit (mkForall `x .default (mkConst b3Anc) (mkSort (.param `u)))
      (mkForall `h .default (mkApp (mkBVar 0) (mkConst b3AncMk))
        (mkForall `t .default (mkConst b3Anc) (mkApp (mkBVar 2) (mkBVar 0)))),
    all := [b3Anc], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := b3AncMk, nfields := 0, rhs := mkLambda `motive .implicit (mkForall `x .default (mkConst b3Anc) (mkSort (.param `u))) (mkLambda `h .default (mkApp (mkBVar 0) (mkConst b3AncMk)) (mkBVar 0)) }],
    k := true, isUnsafe := false
  }
  let b3SizeOfDef : ConstantInfo := .defnInfo {
    name := b3SizeOfName, levelParams := [],
    type := mkApp (mkConst ``SizeOf [Level.one]) (mkConst b3Anc),
    value := mkApp2 (mkConst ``SizeOf.mk [Level.one]) (mkConst b3Anc) (mkLambda `_ .default (mkConst b3Anc) (mkNatLit 0)),
    hints := .abbrev, safety := .safe, all := [b3SizeOfName]
  }
  let b3SizeOfEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``SizeOf 1, Meta.DiscrTree.Key.star, Meta.DiscrTree.Key.const b3Anc 0],
    val := mkConst b3SizeOfName, priority := 1000, globalName? := some b3SizeOfName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "b3_sizeof_ov") `Proof.B3SizeOfOv {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[b3Anc, b3AncMk, `Proof.B3SizeOfOv.Anchor.rec, b3SizeOfName],
    constants := #[b3AncInd, b3AncCtor, b3AncRec, b3SizeOfDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast b3SizeOfEnt])]
  }
  -- B3-2: Forged arrow domain `.star` (`Inhabited (Nat -> Anchor)` with `#[.const Inhabited 1, .arrow, .star]`)
  --       + forged `Prod` trailing key + forged `HAdd` outParam swap + forged scoped instance overflow + forged scoped `coeExt`!
  let arrTy := mkForall `_ .default (mkConst ``Nat) (mkConst a2AnchorName)
  let arrInstName := `Topic.B3ArrowDom.Defs.instArr
  let arrInst : ConstantInfo := .defnInfo {
    name := arrInstName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) arrTy,
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) arrTy (mkLambda `_ .default (mkConst ``Nat) (mkConst a2AnchorMk)),
    hints := .abbrev, safety := .safe, all := [arrInstName]
  }
  let arrDomStarEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.arrow, Meta.DiscrTree.Key.star],
    val := mkConst arrInstName, priority := 1000, globalName? := some arrInstName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "b3_arrow_dom_star") `Topic.B3ArrowDom.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, arrInstName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, arrInst],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast arrDomStarEnt])]
  }
  let prodTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst a2AnchorName)
  let prodInstName := `Topic.B3ProdOv.Defs.instProd
  let prodInst : ConstantInfo := .defnInfo {
    name := prodInstName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) prodTy,
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) prodTy
      (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) (mkConst a2AnchorName) (mkNatLit 0) (mkConst a2AnchorMk)),
    hints := .abbrev, safety := .safe, all := [prodInstName]
  }
  let prodOvEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.const ``Nat 0, Meta.DiscrTree.Key.const a2AnchorName 0],
    val := mkConst prodInstName, priority := 1000, globalName? := some prodInstName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "b3_prod_ov") `Topic.B3ProdOv.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, prodInstName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, prodInst],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast prodOvEnt])]
  }
  let haddInstName := `Topic.B3HAddSwap.Defs.instHAdd
  let haddInst : ConstantInfo := .defnInfo {
    name := haddInstName, levelParams := [],
    type := mkApp3 (mkConst ``HAdd [Level.zero, Level.zero, Level.zero]) (mkConst a2AnchorName) (mkConst ``Nat) (mkConst a2AnchorName),
    value := mkApp4 (mkConst ``HAdd.mk [Level.zero, Level.zero, Level.zero]) (mkConst a2AnchorName) (mkConst ``Nat) (mkConst a2AnchorName)
      (mkLambda `a .default (mkConst a2AnchorName) (mkLambda `_ .default (mkConst ``Nat) (mkBVar 1))),
    hints := .abbrev, safety := .safe, all := [haddInstName]
  }
  let haddSwapEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``HAdd 3, Meta.DiscrTree.Key.star, Meta.DiscrTree.Key.const ``Nat 0, Meta.DiscrTree.Key.const a2AnchorName 0],
    val := mkConst haddInstName, priority := 1000, globalName? := some haddInstName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "b3_hadd_swap") `Topic.B3HAddSwap.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, haddInstName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, haddInst],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast haddSwapEnt])]
  }
  let scopedClsName := `Topic.B3ScopedOv.Defs.LocalCls
  let scopedClsMk := `Topic.B3ScopedOv.Defs.LocalCls.mk
  let scopedClsInd : ConstantInfo := .inductInfo {
    name := scopedClsName, levelParams := [], type := mkForall `α .default (mkSort Level.one) (mkSort Level.one),
    numParams := 1, numIndices := 0, all := [scopedClsName], ctors := [scopedClsMk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  }
  let scopedClsCtor : ConstantInfo := .ctorInfo {
    name := scopedClsMk, levelParams := [],
    type := mkForall `α .implicit (mkSort Level.one) (mkApp (mkConst scopedClsName) (mkBVar 0)),
    induct := scopedClsName, cidx := 0, numParams := 1, numFields := 0, isUnsafe := false
  }
  let scopedClsRec : ConstantInfo := .recInfo {
    name := `Topic.B3ScopedOv.Defs.LocalCls.rec, levelParams := [`u],
    type := mkForall `α .implicit (mkSort Level.one)
      (mkForall `motive .implicit (mkForall `x .default (mkApp (mkConst scopedClsName) (mkBVar 0)) (mkSort (.param `u)))
        (mkForall `h .default (mkApp (mkBVar 0) (mkApp (mkConst scopedClsMk) (mkBVar 1)))
          (mkForall `t .default (mkApp (mkConst scopedClsName) (mkBVar 2)) (mkApp (mkBVar 2) (mkBVar 0))))),
    all := [scopedClsName], numParams := 1, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := scopedClsMk, nfields := 0, rhs := mkLambda `α .implicit (mkSort Level.one) (mkLambda `motive .implicit (mkForall `x .default (mkApp (mkConst scopedClsName) (mkBVar 0)) (mkSort (.param `u))) (mkLambda `h .default (mkApp (mkBVar 0) (mkApp (mkConst scopedClsMk) (mkBVar 1))) (mkBVar 0))) }],
    k := true, isUnsafe := false
  }
  let scopedInstName := `Topic.B3ScopedOv.Defs.sInst
  let scopedInstDef : ConstantInfo := .defnInfo {
    name := scopedInstName, levelParams := [],
    type := mkApp (mkConst scopedClsName) (mkConst ``Nat),
    value := mkApp (mkConst scopedClsMk) (mkConst ``Nat),
    hints := .abbrev, safety := .safe, all := [scopedInstName]
  }
  let scopedOvEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .scoped `Topic.B3ScopedOv.Defs {
    keys := #[Meta.DiscrTree.Key.const scopedClsName 1, Meta.DiscrTree.Key.star, Meta.DiscrTree.Key.const ``Nat 0],
    val := mkConst scopedInstName, priority := 1000, globalName? := some scopedInstName,
    synthOrder := #[], attrKind := .scoped
  }
  writeO (out / "b3_scoped_ov") `Topic.B3ScopedOv.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[scopedClsName, scopedClsMk, `Topic.B3ScopedOv.Defs.LocalCls.rec, scopedInstName],
    constants := #[scopedClsInd, scopedClsCtor, scopedClsRec, scopedInstDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast scopedOvEnt])]
  }
  -- B3-3: Forged `.scoped` `Meta.coeExt` entry
  let coeFnName := `Topic.B3ScopedCoe.Defs.toNat
  let coeFnDef : ConstantInfo := .defnInfo {
    name := coeFnName, levelParams := [],
    type := mkForall `_ .default (mkConst a2AnchorName) (mkConst ``Nat),
    value := mkLambda `_ .default (mkConst a2AnchorName) (mkNatLit 0),
    hints := .regular 1, safety := .safe, all := [coeFnName]
  }
  let scopedCoeEnt : ScopedEnvExtension.Entry (Name × Meta.CoeFnInfo) :=
    .scoped `Nat (coeFnName, { numArgs := 1, coercee := 0, type := .coe })
  writeO (out / "b3_scoped_coe") `Topic.B3ScopedCoe.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, coeFnName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, coeFnDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.coeExt, #[unsafe unsafeCast scopedCoeEnt])]
  }
  -- B3-4: Forged non-mutual `_unsafe_rec` cycle across unrelated safe functions
  let urSafeA : ConstantInfo := .defnInfo {
    name := `Proof.B3BadURAll.safeA, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 0, hints := .opaque, safety := .safe, all := [`Proof.B3BadURAll.safeA]
  }
  let urSafeB : ConstantInfo := .defnInfo {
    name := `Proof.B3BadURAll.safeB, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit 1, hints := .opaque, safety := .safe, all := [`Proof.B3BadURAll.safeB]
  }
  let urBadA : ConstantInfo := .defnInfo {
    name := `Proof.B3BadURAll.safeA._unsafe_rec, levelParams := [], type := mkConst ``Nat,
    value := mkConst `Proof.B3BadURAll.safeB._unsafe_rec, hints := .opaque, safety := .partial,
    all := [`Proof.B3BadURAll.safeA._unsafe_rec, `Proof.B3BadURAll.safeB._unsafe_rec]
  }
  let urBadB : ConstantInfo := .defnInfo {
    name := `Proof.B3BadURAll.safeB._unsafe_rec, levelParams := [], type := mkConst ``Nat,
    value := mkConst `Proof.B3BadURAll.safeA._unsafe_rec, hints := .opaque, safety := .partial,
    all := [`Proof.B3BadURAll.safeA._unsafe_rec, `Proof.B3BadURAll.safeB._unsafe_rec]
  }
  writeO (out / "b3_bad_ur_all") `Proof.B3BadURAll {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.B3BadURAll.safeA, `Proof.B3BadURAll.safeB, `Proof.B3BadURAll.safeA._unsafe_rec, `Proof.B3BadURAll.safeB._unsafe_rec],
    constants := #[urSafeA, urSafeB, urBadA, urBadB], extraConstNames := #[], entries := #[]
  }
  -- B3-5: Forged public `.olean` exposing `_private.*` constant name
  let privLeakName := Name.str (Name.num (`_private ++ `Proof.B3PubPriv) 0) "secret"
  let privLeakThm : ConstantInfo := .thmInfo {
    name := privLeakName, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro, all := [privLeakName]
  }
  let ppDir := out / "b3_pub_priv" / "Proof"
  IO.FS.createDirAll ppDir
  let ppBase := ppDir / "B3PubPriv.olean"
  let ppMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[privLeakName], constants := #[privLeakThm],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B3PubPriv #[
    (ppBase, ppMd),
    (OLeanLevel.server.adjustFileName ppBase, ppMd),
    (OLeanLevel.private.adjustFileName ppBase, ppMd)
  ]
  -- B3-6: Forged module-mode `Verify.B3PrivMod` whose public `.olean` hides `verified`
  let pvDir := out / "b3_priv_verify" / "Verify"
  IO.FS.createDirAll pvDir
  let pvBase := pvDir / "B3PrivMod.olean"
  let pvSrcPath := System.FilePath.mk args[1]!
  let (pvOrig, _) ← readModuleData pvSrcPath
  let pvPub : ModuleData := { pvOrig with isModule := true, constNames := #[], constants := #[] }
  let pvPriv : ModuleData := { pvOrig with isModule := true }
  saveModuleDataParts `Verify.B3PrivMod #[
    (pvBase, pvPub),
    (OLeanLevel.server.adjustFileName pvBase, pvPub),
    (OLeanLevel.private.adjustFileName pvBase, pvPriv)
  ]
  -- B3-7: Forged `.ir` (with clean empty `.ir.sig`) smuggling `imports := #[{ module := `Lean }]`
  let irImpDir := out / "b3_ir_imp" / "Proof"
  IO.FS.createDirAll irImpDir
  let irImpBase := irImpDir / "B3IrImp.olean"
  let irImpMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[`Proof.B3IrImp.ok],
    constants := #[.thmInfo { name := `Proof.B3IrImp.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B3IrImp.ok] }],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B3IrImp #[
    (irImpBase, irImpMd),
    (OLeanLevel.server.adjustFileName irImpBase, irImpMd),
    (OLeanLevel.private.adjustFileName irImpBase, irImpMd)
  ]
  let cleanIrSig : ModuleData := {
    isModule := false, imports := #[], constNames := #[], constants := #[], extraConstNames := #[], entries := #[]
  }
  let evilIrBody : ModuleData := {
    isModule := true, imports := #[{ module := `Init }, { module := `Lean }],
    constNames := #[], constants := #[], extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts `Proof.B3IrImp #[
    (irImpBase.withExtension "ir.sig", cleanIrSig),
    (irImpBase.withExtension "ir", evilIrBody)
  ]
  -- Pass A3 forged edge cases:
  -- A3-1: `Inhabited (Option Nat -> Anchor)` with forged `#[.const Inhabited 1, .arrow, .const Option 1, .star]`
  let optNatTy := mkApp (mkConst ``Option [Level.zero]) (mkConst ``Nat)
  let optArrTy := mkForall `_ .default optNatTy (mkConst a2AnchorName)
  let a3OptArrName := `Topic.A3OptArrStar.Defs.instOptArr
  let a3OptArrDef : ConstantInfo := .defnInfo {
    name := a3OptArrName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) optArrTy,
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) optArrTy (mkLambda `_ .default optNatTy (mkConst a2AnchorMk)),
    hints := .abbrev, safety := .safe, all := [a3OptArrName]
  }
  let a3OptArrEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.arrow, Meta.DiscrTree.Key.const ``Option 1, Meta.DiscrTree.Key.star],
    val := mkConst a3OptArrName, priority := 1000, globalName? := some a3OptArrName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "a3_opt_arr_star") `Topic.A3OptArrStar.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, a3OptArrName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, a3OptArrDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast a3OptArrEnt])]
  }
  -- A3-2: `Inhabited ((Nat -> Bool) -> Anchor)` with forged `#[.const Inhabited 1, .arrow, .arrow, .star]`
  let natBoolArr := mkForall `_ .default (mkConst ``Nat) (mkConst ``Bool)
  let nestedArrTy := mkForall `_ .default natBoolArr (mkConst a2AnchorName)
  let a3NestArrName := `Topic.A3NestArrStar.Defs.instNestArr
  let a3NestArrDef : ConstantInfo := .defnInfo {
    name := a3NestArrName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) nestedArrTy,
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) nestedArrTy (mkLambda `_ .default natBoolArr (mkConst a2AnchorMk)),
    hints := .abbrev, safety := .safe, all := [a3NestArrName]
  }
  let a3NestArrEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.arrow, Meta.DiscrTree.Key.arrow, Meta.DiscrTree.Key.star],
    val := mkConst a3NestArrName, priority := 1000, globalName? := some a3NestArrName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "a3_nest_arr_star") `Topic.A3NestArrStar.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, a3NestArrName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, a3NestArrDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast a3NestArrEnt])]
  }
  -- A3-3: `Inhabited (Prod Nat Anchor)` with forged sibling `.star` `#[.const Inhabited 1, .const Prod 2, .star, .const Anchor 0]`
  let prodSibEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.const ``Prod 2, Meta.DiscrTree.Key.star, Meta.DiscrTree.Key.const a2AnchorName 0],
    val := mkConst prodInstName, priority := 1000, globalName? := some prodInstName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "a3_prod_sib_star") `Topic.A3ProdSibStar.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, prodInstName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, prodInst],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast prodSibEnt])]
  }
  -- A3-4: Cross-module `_private.Specs.Target.0.secret` prefix spoofing inside `Proof.A3CrossPriv`
  let crossPrivName := Name.str (Name.num (`_private ++ `Specs.Target) 0) "secret"
  let crossPrivThm : ConstantInfo := .thmInfo {
    name := crossPrivName, levelParams := [], type := mkConst ``True,
    value := mkConst ``True.intro, all := [crossPrivName]
  }
  writeO (out / "a3_cross_priv") `Proof.A3CrossPriv {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[crossPrivName], constants := #[crossPrivThm],
    extraConstNames := #[], entries := #[]
  }
  -- A3-5: Split-brain module-mode `Topic.A3PubLeakInst.Defs` whose public `.olean` exports a private instance
  -- (`partCnt = 1 <= privCnt = 1` in `instanceExtension`!)
  let plMod := `Topic.A3PubLeakInst.Defs
  let plPrivIndName := Name.str (Name.num (`_private ++ plMod) 0) "PrivInd"
  let plPrivMk := plPrivIndName.str "mk"
  let plPrivRecName := plPrivIndName.str "rec"
  let plPrivInd : ConstantInfo := .inductInfo {
    name := plPrivIndName, levelParams := [], type := mkSort Level.one,
    numParams := 0, numIndices := 0, all := [plPrivIndName], ctors := [plPrivMk],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false
  }
  let plPrivCtor : ConstantInfo := .ctorInfo {
    name := plPrivMk, levelParams := [], type := mkConst plPrivIndName,
    induct := plPrivIndName, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false
  }
  let plPrivRec : ConstantInfo := .recInfo {
    name := plPrivRecName, levelParams := [`u],
    type := mkForall `motive .implicit (mkForall `x .default (mkConst plPrivIndName) (mkSort (.param `u)))
      (mkForall `h .default (mkApp (mkBVar 0) (mkConst plPrivMk))
        (mkForall `t .default (mkConst plPrivIndName) (mkApp (mkBVar 2) (mkBVar 0)))),
    all := [plPrivIndName], numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
    rules := [{ ctor := plPrivMk, nfields := 0, rhs := mkLambda `motive .implicit (mkForall `x .default (mkConst plPrivIndName) (mkSort (.param `u))) (mkLambda `h .default (mkApp (mkBVar 0) (mkConst plPrivMk)) (mkBVar 0)) }],
    k := true, isUnsafe := false
  }
  let plPrivInstName := Name.str (Name.num (`_private ++ plMod) 0) "instPriv"
  let plPrivInstDef : ConstantInfo := .defnInfo {
    name := plPrivInstName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) (mkConst plPrivIndName),
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) (mkConst plPrivIndName) (mkConst plPrivMk),
    hints := .abbrev, safety := .safe, all := [plPrivInstName]
  }
  let plPrivInstEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.const plPrivIndName 0],
    val := mkConst plPrivInstName, priority := 1000, globalName? := some plPrivInstName,
    synthOrder := #[], attrKind := .global
  }
  let plDir := out / "a3_pub_leak_inst" / "Topic" / "A3PubLeakInst"
  IO.FS.createDirAll plDir
  let plBase := plDir / "Defs.olean"
  let plExpMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[plPrivIndName, plPrivMk, plPrivRecName],
    constants := #[plPrivInd, plPrivCtor, plPrivRec],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast plPrivInstEnt])]
  }
  let plPrivMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[plPrivIndName, plPrivMk, plPrivRecName, plPrivInstName],
    constants := #[plPrivInd, plPrivCtor, plPrivRec, plPrivInstDef],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast plPrivInstEnt])]
  }
  saveModuleDataParts plMod #[
    (plBase, plExpMd),
    (OLeanLevel.server.adjustFileName plBase, plPrivMd),
    (OLeanLevel.private.adjustFileName plBase, plPrivMd)
  ]
  -- A3-6: Split-brain module-mode `Proof.A3PubDangle` whose public `.olean` exports `pubThm`
  -- with a `type` referencing `.olean.private`-only `_private.Proof.A3PubDangle.0.privProp`!
  let pdMod := `Proof.A3PubDangle
  let pdPrivProp := Name.str (Name.num (`_private ++ pdMod) 0) "privProp"
  let pdPrivDef : ConstantInfo := .defnInfo {
    name := pdPrivProp, levelParams := [], type := mkSort Level.zero,
    value := mkConst ``True, hints := .abbrev, safety := .safe, all := [pdPrivProp]
  }
  let pdPubName := `Proof.A3PubDangle.pubThm
  let pdPubThmPriv : ConstantInfo := .thmInfo {
    name := pdPubName, levelParams := [], type := mkConst pdPrivProp,
    value := mkConst ``True.intro, all := [pdPubName]
  }
  let pdPubThmExp : ConstantInfo := .axiomInfo {
    name := pdPubName, levelParams := [], type := mkConst pdPrivProp, isUnsafe := false
  }
  let pdDir := out / "a3_pub_dangle" / "Proof"
  IO.FS.createDirAll pdDir
  let pdBase := pdDir / "A3PubDangle.olean"
  let pdExpMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[pdPubName], constants := #[pdPubThmExp],
    extraConstNames := #[], entries := #[]
  }
  let pdPrivMd : ModuleData := {
    isModule := true, imports := #[{ module := `Init }],
    constNames := #[pdPrivProp, pdPubName], constants := #[pdPrivDef, pdPubThmPriv],
    extraConstNames := #[], entries := #[]
  }
  saveModuleDataParts pdMod #[
    (pdBase, pdExpMd),
    (OLeanLevel.server.adjustFileName pdBase, pdPrivMd),
    (OLeanLevel.private.adjustFileName pdBase, pdPrivMd)
  ]
  -- Pass B4 forged regressions:
  -- B4-1: `Inhabited (Quot r -> Anchor)` with forged `#[.const Inhabited 1, .arrow, .star]` (`Quot` rigid head!)
  let qRel := mkLambda `_ .default (mkConst ``Nat) (mkLambda `_ .default (mkConst ``Nat) (mkConst ``True))
  let quotNat := mkApp2 (mkConst ``Quot [Level.one]) (mkConst ``Nat) qRel
  let quotArrTy := mkForall `_ .default quotNat (mkConst a2AnchorName)
  let b4QuotInstName := `Topic.B4QuotStar.Defs.instQuot
  let b4QuotInst : ConstantInfo := .defnInfo {
    name := b4QuotInstName, levelParams := [],
    type := mkApp (mkConst ``Inhabited [Level.one]) quotArrTy,
    value := mkApp2 (mkConst ``Inhabited.mk [Level.one]) quotArrTy (mkLambda `_ .default quotNat (mkConst a2AnchorMk)),
    hints := .abbrev, safety := .safe, all := [b4QuotInstName]
  }
  let b4QuotEnt : ScopedEnvExtension.Entry Meta.InstanceEntry := .global {
    keys := #[Meta.DiscrTree.Key.const ``Inhabited 1, Meta.DiscrTree.Key.arrow, Meta.DiscrTree.Key.star],
    val := mkConst b4QuotInstName, priority := 1000, globalName? := some b4QuotInstName,
    synthOrder := #[], attrKind := .global
  }
  writeO (out / "b4_quot_star") `Topic.B4QuotStar.Defs {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[a2AnchorName, a2AnchorMk, `Topic.A2SpoofInst.Defs.Anchor.rec, b4QuotInstName],
    constants := #[a2AnchorInd, a2AnchorCtor, a2AnchorRec, b4QuotInst],
    extraConstNames := #[],
    entries := #[(`Lean.Meta.instanceExtension, #[unsafe unsafeCast b4QuotEnt])]
  }
  -- B4-2: Module-mode `Proof.B4PrivImpLeak` privately importing `Topic.Defs` (`isExported := false`)
  --       yet leaking `Topic.Defs.PubTag` in a public `.olean` declaration!
  let pilMod := `Proof.B4PrivImpLeak
  let pilThmName := `Proof.B4PrivImpLeak.pubLeak
  let pilTy := mkForall `_ .default (mkConst `Topic.Defs.PubTag) (mkConst ``True)
  let pilPrivCi : ConstantInfo := .thmInfo {
    name := pilThmName, levelParams := [], type := pilTy,
    value := mkLambda `_ .default (mkConst `Topic.Defs.PubTag) (mkConst ``True.intro),
    all := [pilThmName]
  }
  let pilExpCi : ConstantInfo := .axiomInfo {
    name := pilThmName, levelParams := [], type := pilTy, isUnsafe := false
  }
  let pilImps : Array Import := #[
    { module := `Init, isExported := true },
    { module := `Topic.Defs, isExported := false }
  ]
  let pilDir := out / "b4_priv_imp_leak" / "Proof"
  IO.FS.createDirAll pilDir
  let pilBase := pilDir / "B4PrivImpLeak.olean"
  saveModuleDataParts pilMod #[
    (pilBase, { isModule := true, imports := pilImps, constNames := #[pilThmName], constants := #[pilExpCi], extraConstNames := #[], entries := #[] }),
    (OLeanLevel.server.adjustFileName pilBase, { isModule := true, imports := pilImps, constNames := #[pilThmName], constants := #[pilPrivCi], extraConstNames := #[], entries := #[] }),
    (OLeanLevel.private.adjustFileName pilBase, { isModule := true, imports := pilImps, constNames := #[pilThmName], constants := #[pilPrivCi], extraConstNames := #[], entries := #[] })
  ]
  -- B4-3: Bare `_private.Proof.B4BarePriv.0`, non-zero `_private.Proof.B4NonZeroPriv.7.secret`,
  --       and cross-module `_private.Specs.Other.0.secret` in `extraConstNames`
  let barePrivName := Name.num (`_private ++ `Proof.B4BarePriv) 0
  writeO (out / "b4_bare_priv") `Proof.B4BarePriv {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[barePrivName],
    constants := #[.thmInfo { name := barePrivName, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [barePrivName] }],
    extraConstNames := #[], entries := #[]
  }
  let nzPrivName := Name.str (Name.num (`_private ++ `Proof.B4NonZeroPriv) 7) "secret"
  writeO (out / "b4_nz_priv") `Proof.B4NonZeroPriv {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[nzPrivName],
    constants := #[.thmInfo { name := nzPrivName, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [nzPrivName] }],
    extraConstNames := #[], entries := #[]
  }
  let extraForeignPriv := Name.str (Name.num (`_private ++ `Specs.Other) 0) "secret"
  writeO (out / "b4_extra_priv") `Proof.B4ExtraPriv {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.B4ExtraPriv.ok],
    constants := #[.thmInfo { name := `Proof.B4ExtraPriv.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B4ExtraPriv.ok] }],
    extraConstNames := #[extraForeignPriv], entries := #[]
  }
  -- B4-4: Unblocked `Lean.PrettyPrinter.formatterAttribute` persistent extension
  writeO (out / "b4_formatter_ext") `Proof.B4FormatterExt {
    isModule := false, imports := #[{ module := `Init }],
    constNames := #[`Proof.B4FormatterExt.ok],
    constants := #[.thmInfo { name := `Proof.B4FormatterExt.ok, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro, all := [`Proof.B4FormatterExt.ok] }],
    extraConstNames := #[],
    entries := #[(`Lean.PrettyPrinter.formatterAttribute, #[unsafe unsafeCast ()])]
  }
  return 0
""",
                encoding="utf-8",
            )
            forge_r = audit.run_governed_cmd(
                [str(lean_bin), "--run", str(a1_forge_lean), str(a1_forged), str(pkg_v / "Verify" / "B3PrivMod.olean")],
                cwd=tmp,
                mode="file",
            )
            self.assertEqual(forge_r.returncode, 0, forge_r.stdout + "\n" + forge_r.stderr)

            spoof_mod_hdr_src = tmp / "SpoofModHdr.lean"
            spoof_mod_hdr_src.write_text(
                "module\nnamespace Topic.B1CleanNonMod\ntheorem ok : True := True.intro\nend Topic.B1CleanNonMod\n",
                encoding="utf-8",
            )

            cases: list[tuple[str, bool, str | None, dict[str, object]]] = [
                ("unsafe_term_only", False, "forbiddenInitOrCodegenHook", {"target_modules": ["Proof.B1UnsafeTerm"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("cbv_eval", False, "forbiddenMacroOrElab", {"target_modules": ["Proof.B1CbvEval"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("cbv_opaque", False, "forbiddenMacroOrElab", {"target_modules": ["Proof.B1CbvOpaque"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("len4_nat_shadow", False, "forbiddenShadowingOrExport", {"target_modules": ["Proof.Sub.B1ShadowNat"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("spoofed_defs", False, "spoofedExemptModule", {"target_modules": ["Topic.Proofs.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("coe_unused_binder", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B1Coe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_sizeof_nat", False, "forbiddenInstanceOrCoe", {"target_modules": ["Proof.A1EvilSizeOfNat"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_sizeof_prop", False, "forbiddenInstanceOrCoe", {"target_modules": ["Proof.A1EvilSizeOfProp"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_coe_inst_anchor", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A1InstCoe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_coe_opt_anchor", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A1OptCoe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_coe_abbrev_tail_opt", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A1AbbrCoe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("a1_clean_module_without_flag", True, None, {
                    "target_modules": ["Topic.Defs"],
                    "olean_dirs": [pkg_pub15],
                    "source_map": {"Topic.Defs": pkg_pub15 / "Topic" / "Defs.lean"},
                    "require_sources": True,
                    "module_mode": False,
                    "strict_proofs": True,
                }),
                ("a1_fake_module_hdr_on_nonmodule_olean", False, "forbiddenSourceOption", {
                    "target_modules": ["Topic.B1CleanNonMod"],
                    "olean_dirs": [b1_dir],
                    "source_map": {"Topic.B1CleanNonMod": spoof_mod_hdr_src},
                    "require_sources": False,
                    "module_mode": False,
                    "strict_proofs": True,
                }),
                ("a1_transitive_source_scanned_when_optional", False, "forbiddenSourceOption", {
                    "target_modules": ["Proof.TopClean"],
                    "olean_dirs": [b1_dir],
                    "source_map": {"Topic.BadSkipSrc": b1_dir / "Topic" / "BadSkipSrc.lean"},
                    "require_sources": False,
                    "strict_proofs": True,
                }),
                ("a1_extra_const_provenance_spoof", False, "extraConstNameProvenance", {
                    "target_modules": ["Proof.A1ExtraSpoof"],
                    "olean_dirs": [a1_forged / "extra_spoof"],
                    "strict_proofs": True,
                }),
                ("a1_cyclic_defn_direct_lhs_budget", False, "invalidNativeAxiomType", {
                    "target_modules": ["Proof.A1CyclicWhnf"],
                    "olean_dirs": [a1_forged / "cyclic_whnf"],
                    "allow_provisional_native": True,
                    "strict_proofs": True,
                }),
                ("a1_cyclic_defn_caught_by_replay_before_whnf", False, "kernelTypeError", {
                    "target_modules": ["Proof.A1CyclicBehindRec"],
                    "olean_dirs": [a1_forged / "cyclic_behind_rec"],
                    "allow_provisional_native": True,
                    "strict_proofs": True,
                }),
                ("a1_split_brain_exported_ext", False, "keyNameMismatch", {
                    "target_modules": ["Proof.A1SplitExt"],
                    "olean_dirs": [a1_forged / "split_ext"],
                    "strict_proofs": True,
                }),
                ("b2_coe_first_arg_trailing_anchor", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B2CoeFirstArg.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("b2_coe_valid_unary_passes", True, None, {"target_modules": ["Topic.B2GoodCoe.Defs"], "olean_dirs": [b1_dir], "strict_proofs": True}),
                ("b2_outparam_behind_abbrev", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B2OutHijack.Defs"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b2_dbg_trace_skip_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.B2DbgTraceSkip"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b2_println_decide_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.B2PrintlnDecide"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b2_decide_nospace_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.B2DecideNoSpace"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b2_guillemet_decide_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.B2GuillDecide"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b2_deep_opaque_chain_refuted", False, "invalidNativeAxiomType", {"target_modules": ["Proof.B2DeepOp"], "olean_dirs": [a1_forged / "b2_deep_opaque"], "allow_provisional_native": True, "strict_proofs": True}),
                ("b2_prelude_only_batch_no_init_leak", False, "unknownConstant", {"target_modules": ["Proof.B2PrelOnly"], "olean_dirs": [a1_forged / "b2_prelude_only"], "strict_proofs": True}),
                ("b2_folder_ext_rejected", False, "forbiddenInitOrCodegenHook", {"target_modules": ["Proof.B2FolderExt"], "olean_dirs": [a1_forged / "b2_folder_ext"], "strict_proofs": True}),
                ("b2_ir_split_non_ir_ext", False, "keyNameMismatch", {"target_modules": ["Proof.B2IrSplit"], "olean_dirs": [a1_forged / "b2_ir_split"], "strict_proofs": True}),
                ("b2_ismodule_flag_mismatch", False, "keyNameMismatch", {"target_modules": ["Proof.B2IsMod"], "olean_dirs": [a1_forged / "b2_ismod"], "strict_proofs": True}),
                ("b2_module_imports_nonmodule", False, "foreignImport", {"target_modules": ["Proof.TopMod"], "olean_dirs": [a1_forged / "b2_mod_imp_nm"], "strict_proofs": True}),
                ("a2_bin_decide_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.A2BinDecide"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("a2_oct_decide_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.A2OctDecide"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("a2_valid_mutual_def_passes", True, None, {"target_modules": ["Proof.A2ValidMutual"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("a2_valid_coefun_passes", True, None, {"target_modules": ["Topic.A2GoodCoeFun.Defs"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("a2_noindex_local_anchor_orphan_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A2NoindexHijack.Defs"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("a2_forged_extern_opaque_native_rejected", False, "invalidNativeAxiomType", {"target_modules": ["Proof.A2ExternFalse"], "olean_dirs": [a1_forged / "a2_extern_false"], "allow_provisional_native": True, "strict_proofs": True}),
                ("a2_forged_instance_entry_spoof_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A2SpoofInst.Defs"], "olean_dirs": [a1_forged / "a2_spoof_inst"], "strict_proofs": True}),
                ("a2_duplicate_ext_keys_in_entries_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.A2DupExt"], "olean_dirs": [a1_forged / "a2_dup_ext"], "strict_proofs": True}),
                ("a2_nonmodule_with_stray_ir_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.A2NmIr"], "olean_dirs": [a1_forged / "a2_nm_ir"], "strict_proofs": True}),
                ("b3_good_semireducible_alias_and_param_sizeof_passes", True, None, {"target_modules": ["Topic.B3GoodAlias.Defs"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b3_hole_bin_decide_e2e", False, "forbiddenSourceOption", {"target_modules": ["Proof.B3HoleBinDecide"], "olean_dirs": [b1_dir], "source_map_dir": b1_dir, "require_sources": True, "strict_proofs": True}),
                ("b3_sizeof_trailing_key_overflow_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Proof.B3SizeOfOv"], "olean_dirs": [a1_forged / "b3_sizeof_ov"], "strict_proofs": True}),
                ("b3_arrow_domain_star_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B3ArrowDom.Defs"], "olean_dirs": [a1_forged / "b3_arrow_dom_star"], "strict_proofs": True}),
                ("b3_prod_trailing_key_overflow_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B3ProdOv.Defs"], "olean_dirs": [a1_forged / "b3_prod_ov"], "strict_proofs": True}),
                ("b3_hadd_outparam_swap_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B3HAddSwap.Defs"], "olean_dirs": [a1_forged / "b3_hadd_swap"], "strict_proofs": True}),
                ("b3_scoped_instance_overflow_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B3ScopedOv.Defs"], "olean_dirs": [a1_forged / "b3_scoped_ov"], "strict_proofs": True}),
                ("b3_forged_scoped_coe_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B3ScopedCoe.Defs"], "olean_dirs": [a1_forged / "b3_scoped_coe"], "strict_proofs": True}),
                ("b3_forged_nonmutual_unsafe_rec_cycle_rejected", False, "unsafeOrPartialDecl", {"target_modules": ["Proof.B3BadURAll"], "olean_dirs": [a1_forged / "b3_bad_ur_all"], "strict_proofs": True}),
                ("b3_public_olean_private_name_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.B3PubPriv"], "olean_dirs": [a1_forged / "b3_pub_priv"], "module_mode": True, "strict_proofs": True}),
                ("b3_module_verify_private_verified_rejected", False, "invalidVerifyRoot", {"target_modules": ["Verify.B3PrivMod"], "olean_dirs": [a1_forged / "b3_priv_verify", pkg_v], "module_mode": True, "strict_proofs": True}),
                ("b3_forged_ir_body_imports_lean_rejected", False, "foreignImport", {"target_modules": ["Proof.B3IrImp"], "olean_dirs": [a1_forged / "b3_ir_imp"], "module_mode": True, "strict_proofs": True}),
                ("a3_module_priv_struct_and_rich_instances_passes", True, None, {
                    "target_modules": ["Topic.A3ModPriv.Defs"],
                    "olean_dirs": [pkg_pub15],
                    "source_map": {"Topic.A3ModPriv.Defs": pkg_pub15 / "Topic" / "A3ModPriv" / "Defs.lean"},
                    "require_sources": True,
                    "module_mode": True,
                    "strict_proofs": True,
                }),
                ("a3_forged_arrow_option_star_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A3OptArrStar.Defs"], "olean_dirs": [a1_forged / "a3_opt_arr_star"], "strict_proofs": True}),
                ("a3_forged_nested_arrow_star_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A3NestArrStar.Defs"], "olean_dirs": [a1_forged / "a3_nest_arr_star"], "strict_proofs": True}),
                ("a3_forged_prod_sibling_star_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A3ProdSibStar.Defs"], "olean_dirs": [a1_forged / "a3_prod_sib_star"], "strict_proofs": True}),
                ("a3_cross_module_private_prefix_spoof_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.A3CrossPriv"], "olean_dirs": [a1_forged / "a3_cross_priv"], "strict_proofs": True}),
                ("a3_split_brain_public_olean_leaks_private_instance_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.A3PubLeakInst.Defs"], "olean_dirs": [a1_forged / "a3_pub_leak_inst"], "module_mode": True, "strict_proofs": True}),
                ("a3_split_brain_public_olean_dangling_private_type_ref_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.A3PubDangle"], "olean_dirs": [a1_forged / "a3_pub_dangle"], "module_mode": True, "strict_proofs": True}),
                ("b4_forged_quot_arrow_star_rejected", False, "forbiddenInstanceOrCoe", {"target_modules": ["Topic.B4QuotStar.Defs"], "olean_dirs": [a1_forged / "b4_quot_star"], "strict_proofs": True}),
                ("b4_private_import_leaked_in_public_olean_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.B4PrivImpLeak"], "olean_dirs": [a1_forged / "b4_priv_imp_leak", pkg_pub15], "module_mode": True, "strict_proofs": True}),
                ("b4_bare_private_prefix_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.B4BarePriv"], "olean_dirs": [a1_forged / "b4_bare_priv"], "strict_proofs": True}),
                ("b4_nonzero_private_prefix_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.B4NonZeroPriv"], "olean_dirs": [a1_forged / "b4_nz_priv"], "strict_proofs": True}),
                ("b4_cross_module_private_extra_const_rejected", False, "keyNameMismatch", {"target_modules": ["Proof.B4ExtraPriv"], "olean_dirs": [a1_forged / "b4_extra_priv"], "strict_proofs": True}),
                ("b4_formatter_ext_rejected", False, "forbiddenMacroOrElab", {"target_modules": ["Proof.B4FormatterExt"], "olean_dirs": [a1_forged / "b4_formatter_ext"], "strict_proofs": True}),
                ("public_inst_import_all", False, "forbiddenImportAll", {"target_modules": ["Proof.ImpAllPub"], "olean_dirs": [pkg_pub15], "module_mode": True, "strict_proofs": True}),
                ("trusted_shadow", False, "forbiddenShadowingOrExport", {"target_modules": ["Proof.B1ShadowTrusted"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("verify_forall_false", False, "invalidVerifyRoot", {"target_modules": ["Verify.EvilForall"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("verify_unlisted_transitive", False, "invalidVerifyRoot", {"target_modules": ["Verify.OuterGood"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("a1_verify_stmt_proof_leak", False, "statementTheoryLeak", {"target_modules": ["Verify.ProofLeak"], "olean_dirs": [pkg_v], "strict_proofs": True}),
                ("a1_crate_verify_prefix_good", True, None, {"target_modules": ["CrateVerify_demo.Rollup"], "olean_dirs": [pkg_v], "strict_proofs": True}),
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
                chunk_size=70,
            )
            for (cid, exp_ok, exp_cat, _), rep in zip(cases, reps):
                self.assertEqual(rep["ok"], exp_ok, f"{cid}: {rep}")
                if exp_cat is not None:
                    self.assertEqual(rep["violations"][0]["category"], exp_cat, f"{cid}: {rep}")
                    if cid == "a2_forged_extern_opaque_native_rejected":
                        self.assertEqual(rep["violations"][0]["module"], "Proof.A2ExternFalse")
                elif cid == "verify_multi_item_isolated":
                    by_mod = {it["module"]: it for it in rep["summary"]["items"]}
                    self.assertEqual(by_mod["Verify.ItemProv"]["status"], "ProvisionalNative")
                    self.assertEqual(by_mod["Verify.Topic"]["status"], "VerifiedUnconditional")

            # Transitive `.olean.server` FIFO/EACCES must raise AuditOperationalError (exit 2)
            # EVEN when `finalizeImport` throws early `"already contains"` policy error!
            trans_dup_dir = a1_forged / "a2_trans_dup"
            fifo_srv = trans_dup_dir / "Proof" / "DepA.olean.server"
            os.mkfifo(fifo_srv)
            try:
                with self.assertRaises(audit.AuditOperationalError):
                    audit.audit_modules(
                        ["Proof.TopDup"],
                        olean_dirs=[trans_dup_dir],
                        strict_proofs=True,
                        lean_bin=lean_bin,
                        sysroot=sysroot,
                        compiled_inspector=insp,
                        stage_dir=tmp,
                    )
            finally:
                if fifo_srv.exists() or os.path.lexists(fifo_srv):
                    os.unlink(fifo_srv)

            # Non-UTF-8 `.lean` source file referenced by `--source-map` must raise AuditOperationalError (exit 2).
            bad_utf8_lean = tmp / "BadUtf8Source.lean"
            bad_utf8_lean.write_bytes(b"\xff\xfe\xfd")
            with self.assertRaises(audit.AuditOperationalError):
                audit.audit_modules(
                    ["Topic.B2GoodCoe.Defs"],
                    olean_dirs=[b1_dir],
                    source_map={"Topic.B2GoodCoe.Defs": bad_utf8_lean},
                    require_sources=True,
                    strict_proofs=True,
                    lean_bin=lean_bin,
                    sysroot=sysroot,
                    compiled_inspector=insp,
                    stage_dir=tmp,
                )


if __name__ == "__main__":
    unittest.main()
