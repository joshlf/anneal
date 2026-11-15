#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Live, tamper, toolchain and Lean-hygiene tests for
`scripts/verify_lean_miri_pin_proto.py` (Track P prototype).

Run from the repository root:

    python3 -B -m unittest scripts/test_verify_lean_miri_pin_proto.py -v

Tamper tests only ever modify throwaway copies (`tempfile.TemporaryDirectory`)
of `lean-miri/{UPSTREAM_PIN.json,vendor/}` + `lean-toolchain` and a fake
toolchain; the real checkout and the real `elan` toolchain are only read.

Environment knobs:
  ANNEAL_PROTO_SKIP_LEAN_COMPILE=1   skip the (slow) Lean compile test.
  ANNEAL_PROTO_LEAN_RUN_TIMEOUT=S    pass `--timeout S` to anneal-lean-run
                                     (default: its 180 s file-mode limit).
  ANNEAL_PROTO_DEINIT_PATCH_DIFF=P   also apply the real 6-file
                                     `deinitMovedPlace` diff at P to a copy.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import hashlib  # noqa: E402
import importlib.util  # noqa: E402
import json  # noqa: E402
import os  # noqa: E402
import re  # noqa: E402
import shutil  # noqa: E402
import stat  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
import unittest  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
VERIFIER_PATH = SCRIPTS_DIR / "verify_lean_miri_pin_proto.py"
LEAN_PROTOTYPE_REL = "theory/Anneal/LeanMiriDeinitAndCodecPrototype.lean"
LEAN_PROTOTYPE = REPO_ROOT / LEAN_PROTOTYPE_REL


def _load_verifier() -> Any:
    spec = importlib.util.spec_from_file_location("verify_lean_miri_pin_proto", VERIFIER_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module  # dataclasses resolve string annotations via sys.modules
    spec.loader.exec_module(module)
    return module


V = _load_verifier()

LOCKED_MANIFEST = "081747a37a96c7443997ba12b02565f45c9642dd0dec9e3dcb3a30e7053c8d16"
LIBLEANSHARED = ("libleanshared.so", "libleanshared_1.so", "libleanshared_2.so")
FAKE_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")
TAMPER_TARGET = "Miri/ABI/Size.lean"
ALLOWLIST = sorted(V.PATCH_ALLOWLIST)

REPO_TOOLCHAIN = V.read_lean_toolchain(REPO_ROOT)
REPO_LEAN_VERSION = REPO_TOOLCHAIN.split(":", 1)[1].lstrip("v")
LIVE_TOOLCHAIN_DIR = V.default_elan_home() / "toolchains" / V.toolchain_dir_name(REPO_TOOLCHAIN)
HAVE_LIVE_TOOLCHAIN = LIVE_TOOLCHAIN_DIR.is_dir()


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


class Workspace:
    """A throwaway repository root holding copies of the pinned inputs."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.lean_miri = root / "lean-miri"
        self.vendor = self.lean_miri / "vendor"
        self.pin_path = self.lean_miri / "UPSTREAM_PIN.json"

    @classmethod
    def create(cls, base: Path) -> "Workspace":
        root = base / "repo"
        (root / "lean-miri").mkdir(parents=True)
        os.chmod(root, 0o755)
        os.chmod(root / "lean-miri", 0o755)
        shutil.copy2(REPO_ROOT / V.PIN_RELPATH, root / V.PIN_RELPATH)
        shutil.copytree(REPO_ROOT / V.VENDOR_RELPATH, root / V.VENDOR_RELPATH, symlinks=True)
        shutil.copy2(REPO_ROOT / V.LEAN_TOOLCHAIN_RELPATH, root / V.LEAN_TOOLCHAIN_RELPATH)
        return cls(root)

    def pin(self) -> Dict[str, Any]:
        return json.loads(self.pin_path.read_text(encoding="utf-8"))

    def write_pin(self, pin: Dict[str, Any]) -> None:
        self.pin_path.write_text(json.dumps(pin, indent=2) + "\n", encoding="utf-8")

    def path(self, rel: str) -> Path:
        return self.vendor / rel

    def manifest_entry(self, pin: Dict[str, Any], rel: str) -> Dict[str, str]:
        for entry in pin["vendor_tree"]["files"] + pin["vendor_aux_files"]:
            if entry["path"] == rel:
                return entry
        raise KeyError(rel)

    def apply_overlay(self, rels: Iterable[str], *, suffix: bytes = b"") -> List[Dict[str, str]]:
        """Append a comment to each file and declare it in `patched_files`."""
        pin = self.pin()
        entries = []
        for rel in rels:
            original = self.path(rel).read_bytes()
            patched = original + b"\n-- anneal test overlay: opt-in deinitMovedPlace (synthetic)\n" + suffix
            self.path(rel).write_bytes(patched)
            entries.append(
                {
                    "path": rel,
                    "upstream_sha256": _sha256(original),
                    "patched_sha256": _sha256(patched),
                    "patch_reason": "opt-in deinitMovedPlace / pendingMoveDeinit move deinitialization",
                    "upstream_git_blob": V.git_blob_sha1(original),
                }
            )
        pin["patched_files"] = entries
        self.write_pin(pin)
        return entries


def make_fake_toolchain(base: Path, *, version: str = REPO_LEAN_VERSION, name: str = "toolchain", lean_body: Optional[str] = None, lake_body: Optional[str] = None) -> Path:
    """Tiny fake elan toolchain: shell-script bin/lean + bin/lake and small
    fake `lib/lean/*.so` files (including the split `libleanshared_{1,2}.so`)."""
    root = base / name
    (root / "bin").mkdir(parents=True)
    (root / "lib" / "lean").mkdir(parents=True)
    lean_body = lean_body if lean_body is not None else f"echo 'Lean (version {version}, x86_64-unknown-linux-gnu, commit {FAKE_COMMIT}, Release)'"
    lake_body = lake_body if lake_body is not None else f"echo 'Lake version 5.0.0-src+{FAKE_COMMIT[:7]} (Lean version {version})'"
    for binary, body in (("lean", lean_body), ("lake", lake_body)):
        path = root / "bin" / binary
        path.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
        os.chmod(path, 0o755)
    for lib in LIBLEANSHARED + ("libInit_shared.so",):
        path = root / "lib" / "lean" / lib
        path.write_bytes(hashlib.sha256(lib.encode()).digest() * 128)
        os.chmod(path, 0o644)
    for directory in (root, root / "bin", root / "lib", root / "lib" / "lean"):
        os.chmod(directory, 0o755)
    return root


class TempCase(unittest.TestCase):
    """Per-test temporary directory + rejection assertion helpers."""

    def setUp(self) -> None:
        old_umask = os.umask(0o022)  # fixtures must not inherit a permissive umask
        self.addCleanup(os.umask, old_umask)
        tmp = tempfile.TemporaryDirectory(prefix="anneal-pin-proto-")
        self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)

    def workspace(self) -> Workspace:
        return Workspace.create(self.tmp)

    def assertRejected(self, fn: Callable[[], Any], *needles: str, absent: Sequence[str] = ()) -> Tuple[str, ...]:
        with self.assertRaises(V.PinVerificationError) as cm:
            fn()
        errors = cm.exception.errors
        report = "\n".join(errors)
        for needle in needles:
            self.assertTrue(any(needle in e for e in errors), f"expected an error containing {needle!r}; got:\n{report}")
        for needle in absent:
            self.assertFalse(any(needle in e for e in errors), f"unexpected error containing {needle!r}; got:\n{report}")
        return errors


# ---------------------------------------------------------------------------
# Live checkout + real toolchain
# ---------------------------------------------------------------------------


class LiveCheckoutTests(TempCase):
    def test_live_vendor_strict_mode_608_lean_9_aux(self) -> None:
        v = V.verify_vendor(REPO_ROOT)
        self.assertEqual(v.mode, "strict")
        self.assertEqual(v.verified_vendor_files, 608)
        self.assertEqual(v.verified_aux_files, 9)
        self.assertEqual(v.manifest_sha256, LOCKED_MANIFEST)
        self.assertEqual(v.commit, V.LOCKED_UPSTREAM_IDENTITY["commit"])
        self.assertEqual(v.git_objects["Miri"], "tree")
        self.assertEqual(len(v.git_objects), 11)
        self.assertEqual(v.patched_files, ())
        self.assertEqual(v.closure.status, "absent")
        self.assertEqual(v.locked_identity, "matched")
        self.assertEqual(v.build_lean_toolchain, REPO_TOOLCHAIN)

    def test_live_allow_deinit_patch_accepts_unpatched_checkout(self) -> None:
        v = V.verify_vendor(REPO_ROOT, allow_deinit_patch=True)
        self.assertEqual(v.mode, "deinit-patch")
        self.assertEqual((v.verified_vendor_files, v.verified_aux_files), (608, 9))
        self.assertEqual(v.patched_files, ())

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_end_to_end_real_toolchain_and_split_libleanshared(self) -> None:
        result = V.verify_all(REPO_ROOT)
        t = result.toolchain
        self.assertIsNotNone(t)
        self.assertEqual(t.name, REPO_TOOLCHAIN)
        self.assertEqual(t.resolved_by, "elan")
        self.assertEqual(Path(t.toolchain_dir), LIVE_TOOLCHAIN_DIR)
        self.assertEqual(t.libleanshared, LIBLEANSHARED)
        for rel in ("bin/lean", "bin/lake") + tuple(f"lib/lean/{n}" for n in LIBLEANSHARED):
            self.assertRegex(t.files[rel], HEX64, rel)
        # Independent recomputation of the companion libraries' digests.
        for lib in LIBLEANSHARED[1:]:
            self.assertEqual(t.files[f"lib/lean/{lib}"], _sha256((LIVE_TOOLCHAIN_DIR / "lib" / "lean" / lib).read_bytes()))
        self.assertIn(f"version {REPO_LEAN_VERSION}", t.lean_version)
        self.assertIn(f"(Lean version {REPO_LEAN_VERSION})", t.lake_version)
        summary = result.to_json_dict()
        self.assertEqual((summary["verified_vendor_files"], summary["verified_aux_files"]), (608, 9))

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_toolchain_pin_dump_and_verify_roundtrip(self) -> None:
        t = V.verify_toolchain(REPO_ROOT, expected_toolchain=REPO_TOOLCHAIN)
        pin_path = self.tmp / "toolchain-pin.json"
        V.write_toolchain_pin(t, pin_path)
        pin = json.loads(pin_path.read_text())
        self.assertEqual(set(pin), {"toolchain", "versions", "files"})
        self.assertTrue({f"lib/lean/{n}" for n in LIBLEANSHARED} <= set(pin["files"]))
        again = V.verify_toolchain(REPO_ROOT, toolchain_pin_json=pin_path)
        self.assertEqual(again.pin_status, "verified")
        self.assertEqual(dict(again.files), pin["files"])

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_cli_json_smoke(self) -> None:
        proc = subprocess.run(
            [sys.executable, "-B", str(VERIFIER_PATH), "--repo-root", str(REPO_ROOT), "--json"],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=600,
            check=False,
        )
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        summary = json.loads(proc.stdout)
        self.assertIs(summary["ok"], True)
        self.assertEqual(summary["verified_vendor_files"], 608)
        self.assertEqual(summary["verified_aux_files"], 9)
        self.assertEqual(summary["manifest_sha256"], LOCKED_MANIFEST)
        digests = summary["toolchain"]["sha256"]
        for rel in ("bin/lean", "bin/lake") + tuple(f"lib/lean/{n}" for n in LIBLEANSHARED):
            self.assertRegex(digests[rel], HEX64, rel)


# ---------------------------------------------------------------------------
# Hash primitives + manifest formula
# ---------------------------------------------------------------------------


class HashPrimitiveTests(TempCase):
    def test_git_blob_and_tree_ids_match_git(self) -> None:
        self.assertEqual(V.git_blob_sha1(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")
        self.assertEqual(V.git_blob_sha1(b"hello\n"), "ce013625030ba8dba906f756967f9e9ca394464a")
        self.assertEqual(V.git_tree_sha1({}), "4b825dc642cb6eb9a060e54bf8d69288fbee4904")
        # Ordering trap: a directory `a` sorts as `a/`, i.e. after `a-c` and
        # `a.b` but before `a0`; plus a 100755 entry.
        files = {"a/x.lean": b"x\n", "a.b": b"dot\n", "a-c": b"dash\n", "a0": b"zero\n", "run.sh": b"#!/bin/sh\n"}
        entries = {rel: ("100755" if rel == "run.sh" else "100644", V.git_blob_sha1(data)) for rel, data in files.items()}
        ours = V.git_tree_sha1(entries)
        # The same tree hashed with plain name order (directory `a` sorting
        # first) must differ, so the `name + "/"` rule is actually exercised.
        sub = V.git_tree_sha1({"x.lean": entries["a/x.lean"]})
        top = [("a", "40000", sub)] + [(rel, mode, blob) for rel, (mode, blob) in entries.items() if "/" not in rel]
        naive_body = b"".join(f"{m} {n}".encode() + b"\0" + bytes.fromhex(h) for n, m, h in sorted(top))
        self.assertNotEqual(ours, hashlib.sha1(b"tree %d\0" % len(naive_body) + naive_body).hexdigest())
        git = shutil.which("git")
        if git is None:
            self.skipTest("git not installed; hard-coded vectors checked")
        repo = self.tmp / "gitrepo"
        for rel, data in files.items():
            (repo / rel).parent.mkdir(parents=True, exist_ok=True)
            (repo / rel).write_bytes(data)
        os.chmod(repo / "run.sh", 0o755)
        env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
        run = lambda *a: subprocess.run([git, *a], cwd=repo, env=env, check=True, capture_output=True, text=True).stdout.strip()  # noqa: E731
        run("init", "-q")
        run("add", "-A")
        self.assertEqual(ours, run("write-tree"))
        self.assertEqual(V.git_tree_sha1({k[2:]: v for k, v in entries.items() if k.startswith("a/")}), run("rev-parse", f"{run('write-tree')}:a"))

    def test_manifest_formula_reproduces_pinned_digest_and_rejects_alternatives(self) -> None:
        pin = json.loads((REPO_ROOT / V.PIN_RELPATH).read_text())
        files = pin["vendor_tree"]["files"]
        self.assertEqual(V.compute_manifest_sha256(files), LOCKED_MANIFEST)
        self.assertEqual(pin["vendor_tree"]["manifest_sha256"], LOCKED_MANIFEST)
        alternatives = [
            _sha256("".join(f"{e['sha256']}  {e['path']}\n" for e in sorted(files, key=lambda e: e["path"])).encode()),
            _sha256("".join(f"{e['path']}  {e['sha256']}\n" for e in files).encode()),
            _sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()),
            _sha256(json.dumps(files).encode()),
        ]
        self.assertNotIn(LOCKED_MANIFEST, alternatives)
        paths = [e["path"] for e in files]
        self.assertEqual(paths, sorted(paths, key=V.canonical_manifest_key))
        self.assertNotEqual(paths, sorted(paths))  # canonical order is not plain byte order
        self.assertEqual(paths[0], "Miri.lean")

    def test_toolchain_dir_name_and_name_validation(self) -> None:
        self.assertEqual(V.toolchain_dir_name("leanprover/lean4:v4.34.1"), "leanprover--lean4---v4.34.1")
        self.assertIsNone(V.toolchain_name_problem("leanprover/lean4:v4.34.1"))
        self.assertIsNotNone(V.toolchain_name_problem("leanprover/lean4:stable"))
        self.assertIsNotNone(V.toolchain_name_problem("v4.34.1"))
        for bad in ("/abs.lean", "a/../b.lean", "a//b.lean", "./a.lean", "a\\b.lean", "", "a b.lean"):
            self.assertIsNotNone(V.relpath_problem(bad), bad)
        self.assertIsNone(V.relpath_problem("upstream/.pins/miri.commit"))


# ---------------------------------------------------------------------------
# Vendor tree tamper tests (on copies)
# ---------------------------------------------------------------------------


class VendorTamperTests(TempCase):
    def test_copy_baseline_passes_with_fake_toolchain(self) -> None:
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        result = V.verify_all(ws.root, toolchain_dir=tc)
        self.assertEqual((result.vendor.verified_vendor_files, result.vendor.verified_aux_files), (608, 9))
        self.assertEqual(result.toolchain.libleanshared, LIBLEANSHARED)
        self.assertIn("lib/lean/libInit_shared.so", result.toolchain.files)

    def test_unpatched_lean_byte_tamper_rejected_in_both_modes(self) -> None:
        ws = self.workspace()
        data = bytearray(ws.path(TAMPER_TARGET).read_bytes())
        data[len(data) // 2] ^= 0x01  # same size, one flipped bit
        ws.path(TAMPER_TARGET).write_bytes(bytes(data))
        for allow in (False, True):
            with self.subTest(allow_deinit_patch=allow):
                self.assertRejected(
                    lambda: V.verify_vendor(ws.root, allow_deinit_patch=allow),
                    f"SHA-256 mismatch for {TAMPER_TARGET}",
                    "git tree SHA-1 mismatch for Miri/",
                )

    def test_valid_six_file_deinit_patch_accepted_only_with_flag(self) -> None:
        ws = self.workspace()
        ws.apply_overlay(ALLOWLIST)
        v = V.verify_vendor(ws.root, allow_deinit_patch=True)
        self.assertEqual([p.path for p in v.patched_files], ALLOWLIST)
        self.assertEqual((v.verified_vendor_files, v.verified_aux_files), (608, 9))
        self.assertEqual(v.manifest_sha256, LOCKED_MANIFEST)  # manifest keeps describing upstream bytes
        self.assertEqual(v.git_objects["Miri"], "tree")  # recomputed with upstream_git_blob substitution
        self.assertRejected(
            lambda: V.verify_vendor(ws.root),
            "strict mode: UPSTREAM_PIN.json declares 6 patched_files entries",
            "SHA-256 mismatch for Miri/Interpreter/ExecutionMachine.lean",
        )

    def test_patch_subset_of_allowlist_accepted(self) -> None:
        ws = self.workspace()
        ws.apply_overlay(["Miri/Interpreter/Place.lean", "Miri/Interpreter/PlaceMachine.lean"])
        v = V.verify_vendor(ws.root, allow_deinit_patch=True)
        self.assertEqual(len(v.patched_files), 2)

    def test_seventh_non_allowlisted_patch_rejected(self) -> None:
        ws = self.workspace()
        ws.apply_overlay(ALLOWLIST + [TAMPER_TARGET])
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
            f"{TAMPER_TARGET!r} is not in the closed 6-file deinit patch allowlist",
            f"SHA-256 mismatch for {TAMPER_TARGET}",
        )

    def test_noop_patch_entry_rejected(self) -> None:
        ws = self.workspace()
        pin = ws.pin()
        rel = "Miri/Interpreter/Place.lean"
        digest = ws.manifest_entry(pin, rel)["sha256"]
        pin["patched_files"] = [
            {
                "path": rel,
                "upstream_sha256": digest,
                "patched_sha256": digest,
                "patch_reason": "claims a patch but changes nothing",
                "upstream_git_blob": V.git_blob_sha1(ws.path(rel).read_bytes()),
            }
        ]
        ws.write_pin(pin)
        self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "no-op patch for 'Miri/Interpreter/Place.lean'")

    def test_malformed_or_inconsistent_patch_entries_rejected(self) -> None:
        ws = self.workspace()
        good = ws.apply_overlay(ALLOWLIST)
        rel = good[0]["path"]
        base_pin = ws.pin()

        def mutate(fn: Callable[[List[Dict[str, Any]]], None]) -> None:
            pin = json.loads(json.dumps(base_pin))
            fn(pin["patched_files"])
            ws.write_pin(pin)

        cases: List[Tuple[str, Callable[[List[Dict[str, Any]]], None], str]] = [
            ("missing reason", lambda e: e[0].pop("patch_reason"), "missing key 'patch_reason'"),
            ("blank reason", lambda e: e[0].update(patch_reason="   "), "patch_reason for"),
            ("uppercase digest", lambda e: e[0].update(patched_sha256=e[0]["patched_sha256"].upper()), "patched_sha256 for"),
            ("short git blob", lambda e: e[0].update(upstream_git_blob="abc123"), "upstream_git_blob for"),
            ("unknown key", lambda e: e[0].update(rationale="joshlf spelling"), "unknown key 'rationale'"),
            ("duplicate entry", lambda e: e.append(dict(e[0])), f"duplicate patched_files entry for {rel!r}"),
            ("traversal path", lambda e: e[0].update(path="../" + rel), "path traversal"),
            ("wrong patched digest", lambda e: e[0].update(patched_sha256="0" * 64), f"{rel}: on-disk SHA-256"),
            ("wrong upstream digest", lambda e: e[0].update(upstream_sha256="1" * 64), "must equal upstream_sha256"),
            ("wrong upstream git blob", lambda e: e[0].update(upstream_git_blob="2" * 40), "git tree SHA-1 mismatch for Miri/"),
        ]
        for label, fn, needle in cases:
            with self.subTest(label):
                mutate(fn)
                self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), needle)
        with self.subTest("declared patched but bytes are upstream"):
            ws.write_pin(base_pin)
            original = ws.path(rel).read_bytes()
            ws.path(rel).write_bytes(original[: original.rindex(b"\n-- anneal test overlay")])
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), f"{rel}: declared as patched but holds the unpatched upstream bytes")

    def test_file_symlink_attacks_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("extra symlink alias"):
            os.symlink(TAMPER_TARGET.rsplit("/", 1)[1], ws.path("Miri/ABI/Alias.lean"))
            self.assertRejected(lambda: V.verify_vendor(ws.root), "symlink forbidden (file symlink): Miri/ABI/Alias.lean")
            ws.path("Miri/ABI/Alias.lean").unlink()
        with self.subTest("pinned file replaced by symlink to identical bytes outside the tree"):
            outside = self.tmp / "outside-Size.lean"
            shutil.copy2(ws.path(TAMPER_TARGET), outside)
            ws.path(TAMPER_TARGET).unlink()
            os.symlink(outside, ws.path(TAMPER_TARGET))
            self.assertRejected(
                lambda: V.verify_vendor(ws.root),
                f"symlink forbidden (file symlink): {TAMPER_TARGET}",
                f"missing pinned file: {TAMPER_TARGET}",
            )

    def test_directory_symlink_attacks_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("pinned directory replaced by symlink to an identical copy"):
            outside = self.tmp / "outside-ABI"
            shutil.move(str(ws.path("Miri/ABI")), str(outside))
            os.symlink(outside, ws.path("Miri/ABI"))
            self.assertRejected(lambda: V.verify_vendor(ws.root), "symlink forbidden (directory symlink): Miri/ABI", "missing pinned file: Miri/ABI/Size.lean")
            ws.path("Miri/ABI").unlink()
            shutil.move(str(outside), str(ws.path("Miri/ABI")))
            V.verify_vendor(ws.root)  # restored copy verifies again
        with self.subTest("extra directory symlink"):
            os.symlink(self.tmp, ws.path("Miri/Evil"))
            self.assertRejected(lambda: V.verify_vendor(ws.root), "symlink forbidden (directory symlink): Miri/Evil")
        with self.subTest("vendor root itself is a symlink"):
            ws.path("Miri/Evil").unlink()
            real = self.tmp / "real-vendor"
            shutil.move(str(ws.vendor), str(real))
            os.symlink(real, ws.vendor)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "lean-miri/vendor/ is a symlink")

    def test_unlisted_lean_injection_rejected(self) -> None:
        ws = self.workspace()
        ws.path("Miri/ABI/Rogue.lean").write_bytes(b"-- rogue\n")
        ws.path("Evil.lean").write_bytes(b"-- rogue root module\n")
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
            "unlisted .lean file (not in UPSTREAM_PIN.json): Miri/ABI/Rogue.lean",
            "unlisted .lean file (not in UPSTREAM_PIN.json): Evil.lean",
        )

    def test_unlisted_aux_injection_rejected(self) -> None:
        ws = self.workspace()
        ws.path("tools/evil.py").write_bytes(b"print('pwned')\n")
        ws.path("README.md").write_bytes(b"# rogue\n")
        self.assertRejected(
            lambda: V.verify_vendor(ws.root),
            "unlisted auxiliary file (not in UPSTREAM_PIN.json): tools/evil.py",
            "unlisted auxiliary file (not in UPSTREAM_PIN.json): README.md",
        )

    def test_planted_build_artifacts_rejected(self) -> None:
        ws = self.workspace()
        for rel in (
            "Miri/ABI/Size.olean",
            "Miri/ABI/Size.olean.server",
            "Miri/ABI/Size.ilean",
            "Miri/ABI/Size.ir",
            "Miri/ABI/Size.c",
            "Miri/ABI/Size.olean.hash",
            "Miri/ABI/Size.trace",
            "Miri/cache.ltar",
        ):
            with self.subTest(rel):
                ws.path(rel).write_bytes(b"\x00planted")
                self.assertRejected(lambda: V.verify_vendor(ws.root), f"planted build artifact: {rel}")
                ws.path(rel).unlink()
        with self.subTest(".lake directory"):
            (ws.vendor / ".lake" / "build").mkdir(parents=True)
            (ws.vendor / ".lake" / "build" / "Miri.olean").write_bytes(b"\x00")
            self.assertRejected(lambda: V.verify_vendor(ws.root), "planted build artifact directory: .lake/")

    def test_missing_files_rejected(self) -> None:
        ws = self.workspace()
        ws.path(TAMPER_TARGET).unlink()
        ws.path("LICENSE-MIT").unlink()
        self.assertRejected(lambda: V.verify_vendor(ws.root), f"missing pinned file: {TAMPER_TARGET}", "missing pinned file: LICENSE-MIT")

    def test_manifest_sha256_mismatch_and_noncanonical_order_rejected(self) -> None:
        ws = self.workspace()
        pristine = ws.pin()
        with self.subTest("bogus manifest_sha256"):
            pin = json.loads(json.dumps(pristine))
            pin["vendor_tree"]["manifest_sha256"] = "0" * 64
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "vendor_tree.manifest_sha256 mismatch", "[identity] vendor_tree.manifest_sha256")
        with self.subTest("reordered entries with recomputed manifest"):
            pin = json.loads(json.dumps(pristine))
            files = pin["vendor_tree"]["files"]
            files[1], files[2] = files[2], files[1]
            pin["vendor_tree"]["manifest_sha256"] = V.compute_manifest_sha256(files)
            ws.write_pin(pin)
            self.assertRejected(
                lambda: V.verify_vendor(ws.root),
                "vendor_tree.files is not in canonical order",
                absent=("vendor_tree.manifest_sha256 mismatch",),
            )

    def test_git_blob_sha1_mismatch_rejected(self) -> None:
        # Aux content and its SHA-256 entry updated consistently, but
        # upstream_git_objects left stale: only the git cross-check catches it.
        ws = self.workspace()
        ws.path("LICENSE-MIT").write_bytes(ws.path("LICENSE-MIT").read_bytes() + b"\nrelicensed\n")
        pin = ws.pin()
        ws.manifest_entry(pin, "LICENSE-MIT")["sha256"] = _sha256(ws.path("LICENSE-MIT").read_bytes())
        ws.write_pin(pin)
        self.assertRejected(lambda: V.verify_vendor(ws.root), "git blob SHA-1 mismatch for LICENSE-MIT", absent=("SHA-256 mismatch for LICENSE-MIT",))

    def test_miri_tree_hash_mismatch_rejected(self) -> None:
        ws = self.workspace()
        ws.path(TAMPER_TARGET).write_bytes(ws.path(TAMPER_TARGET).read_bytes() + b"\n-- tampered\n")
        pin = ws.pin()
        ws.manifest_entry(pin, TAMPER_TARGET)["sha256"] = _sha256(ws.path(TAMPER_TARGET).read_bytes())
        pin["vendor_tree"]["manifest_sha256"] = V.compute_manifest_sha256(pin["vendor_tree"]["files"])
        ws.write_pin(pin)
        errors = self.assertRejected(
            lambda: V.verify_vendor(ws.root, locked_identity=None),
            "git tree SHA-1 mismatch for Miri/",
            absent=(f"SHA-256 mismatch for {TAMPER_TARGET}", "manifest_sha256 mismatch"),
        )
        self.assertEqual(len(errors), 1, errors)

    def test_mode_only_change_caught_by_tree_hash(self) -> None:
        ws = self.workspace()
        path = ws.path(TAMPER_TARGET)
        os.chmod(path, path.stat().st_mode | stat.S_IXUSR)
        errors = self.assertRejected(lambda: V.verify_vendor(ws.root), "git tree SHA-1 mismatch for Miri/")
        self.assertEqual(len(errors), 1, errors)

    def test_forged_self_consistent_pin_rejected_by_locked_identity(self) -> None:
        ws = self.workspace()
        ws.path(TAMPER_TARGET).write_bytes(b"-- forged upstream\n")
        pin = ws.pin()
        ws.manifest_entry(pin, TAMPER_TARGET)["sha256"] = _sha256(b"-- forged upstream\n")
        pin["vendor_tree"]["manifest_sha256"] = V.compute_manifest_sha256(pin["vendor_tree"]["files"])
        entries = {}
        for entry in pin["vendor_tree"]["files"]:
            if entry["path"].startswith("Miri/"):
                rel = entry["path"]
                entries[rel[len("Miri/"):]] = (V.git_mode(ws.path(rel).stat().st_mode), V.git_blob_sha1(ws.path(rel).read_bytes()))
        pin["upstream_git_objects"]["Miri"] = V.git_tree_sha1(entries)
        ws.write_pin(pin)
        V.verify_vendor(ws.root, locked_identity=None)  # self-consistent forgery passes without the lock
        self.assertRejected(
            lambda: V.verify_vendor(ws.root),
            "[identity] vendor_tree.manifest_sha256",
            "[identity] upstream_git_objects['Miri']",
        )

    def test_upstream_pins_marker_cross_check(self) -> None:
        ws = self.workspace()
        with self.subTest("pin metadata disagrees with vendored marker"):
            pin = ws.pin()
            pin["upstream_pins"]["miri_commit"] = "f" * 40
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root, locked_identity=None), "upstream_pins.miri_commit 'ffff")
        with self.subTest("source lock digest disagrees"):
            pin = ws.pin()
            pin["upstream_pins"]["miri_commit"] = V.LOCKED_UPSTREAM_IDENTITY["upstream_pins"]["miri_commit"]
            pin["upstream_pins"]["source_lock_sha256"] = "e" * 64
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "upstream_pins.source_lock_sha256", "[identity] upstream_pins")

    def test_schema_violations_rejected(self) -> None:
        ws = self.workspace()
        pristine_text = ws.pin_path.read_text()

        def files(pin: Dict[str, Any]) -> List[Dict[str, Any]]:
            return pin["vendor_tree"]["files"]

        cases: List[Tuple[str, Callable[[Dict[str, Any]], None], str]] = [
            ("unknown top-level key", lambda p: p.update(extra=1), "unknown key 'extra'"),
            ("schema_version 3", lambda p: p.update(schema_version=3), "schema_version must be the integer 2"),
            ("schema_version bool", lambda p: p.update(schema_version=True), "schema_version must be the integer 2"),
            ("missing notes", lambda p: p.pop("notes"), "missing key 'notes'"),
            ("uppercase commit", lambda p: p.update(commit=p["commit"].upper()), "commit must be 40 lowercase hex"),
            ("short commit", lambda p: p.update(commit="c92d1d97"), "commit must be 40 lowercase hex"),
            ("bad upstream pin", lambda p: p["upstream_pins"].update(aes_commit="xyz"), "upstream_pins.aes_commit"),
            ("moving toolchain", lambda p: p.update(build_lean_toolchain="leanprover/lean4:stable"), "moving channel"),
            ("file_count drift", lambda p: p["vendor_tree"].update(file_count=607), "file_count 607 != 608"),
            ("path traversal", lambda p: files(p)[5].update(path="../escape.lean"), "path traversal"),
            ("absolute path", lambda p: files(p)[5].update(path="/etc/evil.lean"), "is absolute"),
            ("duplicate path", lambda p: files(p)[6].update(path=files(p)[5]["path"]), "duplicate path"),
            ("case collision", lambda p: files(p)[6].update(path=files(p)[5]["path"].upper().replace(".LEAN", ".lean")), "collides case-insensitively"),
            ("aux .lean", lambda p: p["vendor_aux_files"][0].update(path="Sneaky.lean"), "is a .lean file (belongs in vendor_tree)"),
            ("extra entry key", lambda p: files(p)[0].update(patched_sha256="0" * 64), "unknown key 'patched_sha256'"),
            ("bad git object", lambda p: p["upstream_git_objects"].update(Miri="not-hex"), "upstream_git_objects['Miri'] must be 40"),
            ("non-https repository", lambda p: p.update(repository="git://evil/lean-miri"), "repository must be an https:// URL"),
            ("file shadows directory", lambda p: p["vendor_aux_files"][0].update(path="Miri"), "listed file 'Miri' is also the parent directory"),
        ]
        for label, fn, needle in cases:
            with self.subTest(label):
                pin = json.loads(pristine_text)
                fn(pin)
                ws.write_pin(pin)
                self.assertRejected(lambda: V.verify_vendor(ws.root), needle)
        for label, text, needle in (
            ("duplicate JSON key", pristine_text.replace('"schema_version": 2,', '"schema_version": 2, "schema_version": 2,', 1), "duplicate JSON object key 'schema_version'"),
            ("NaN", pristine_text.replace('"schema_version": 2,', '"schema_version": NaN,', 1), "non-finite JSON number"),
            ("not an object", "[]", "top level must be a JSON object"),
            ("nesting bomb", "[" * 200000 + "]" * 200000, "JSON nesting too deep"),
        ):
            with self.subTest(label):
                self.assertNotEqual(text, pristine_text)
                ws.pin_path.write_text(text)
                self.assertRejected(lambda: V.verify_vendor(ws.root), needle)

    def test_unsafe_modes_special_files_and_extraneous_dirs_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("world-writable vendored file"):
            os.chmod(ws.path("LICENSE-MIT"), 0o666)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "world-writable file: LICENSE-MIT")
            os.chmod(ws.path("LICENSE-MIT"), 0o644)
        with self.subTest("world-writable directory"):
            os.chmod(ws.path("Miri/ABI"), 0o777)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "world-writable directory: Miri/ABI/")
            os.chmod(ws.path("Miri/ABI"), 0o755)
        with self.subTest("hard link to a file outside the tree"):
            outside = self.tmp / "outside-LICENSE-MIT"
            os.link(ws.path("LICENSE-MIT"), outside)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "hard-linked file (st_nlink=2, writable through another path): LICENSE-MIT")
            outside.unlink()
        with self.subTest("FIFO"):
            os.mkfifo(ws.path("Miri/ABI/pipe"))
            self.assertRejected(lambda: V.verify_vendor(ws.root), "non-regular file (device, FIFO or socket): Miri/ABI/pipe")
            ws.path("Miri/ABI/pipe").unlink()
        with self.subTest("empty extraneous directory"):
            ws.path("Miri/Empty").mkdir()
            self.assertRejected(lambda: V.verify_vendor(ws.root), "extraneous directory (contains no pinned file): Miri/Empty/")
            ws.path("Miri/Empty").rmdir()
        with self.subTest("UPSTREAM_PIN.json symlink"):
            real = self.tmp / "pin-copy.json"
            shutil.copy2(ws.pin_path, real)
            ws.pin_path.unlink()
            os.symlink(real, ws.pin_path)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "lean-miri/UPSTREAM_PIN.json is a symlink")

    def test_execution_machine_closure_requires_explicit_olean_dir(self) -> None:
        ws = self.workspace()
        olean = self.tmp / "olean"
        blobs = {"Miri/Interpreter/ExecutionMachine.olean": b"olean-em", "Miri/Interpreter/Place.olean": b"olean-place"}
        for rel, data in blobs.items():
            (olean / rel).parent.mkdir(parents=True, exist_ok=True)
            (olean / rel).write_bytes(data)
        with self.subTest("olean dir without closure in the pin"):
            self.assertRejected(lambda: V.verify_vendor(ws.root, olean_dir=olean), "--olean-dir was supplied but UPSTREAM_PIN.json has no execution_machine_closure")
        pin = ws.pin()
        pin["execution_machine_closure"] = [{"path": rel, "sha256": _sha256(data)} for rel, data in blobs.items()]
        ws.write_pin(pin)
        with self.subTest("no olean dir: skipped"):
            v = V.verify_vendor(ws.root)
            self.assertEqual((v.closure.status, v.closure.entries), ("skipped", 2))
            self.assertTrue(any("skipped" in w for w in v.warnings))
        with self.subTest("verified"):
            self.assertEqual(V.verify_vendor(ws.root, olean_dir=olean).closure.status, "verified")
        with self.subTest("tampered olean"):
            (olean / "Miri/Interpreter/Place.olean").write_bytes(b"evil")
            self.assertRejected(lambda: V.verify_vendor(ws.root, olean_dir=olean), ".olean SHA-256 mismatch for Miri/Interpreter/Place.olean")
            (olean / "Miri/Interpreter/Place.olean").write_bytes(blobs["Miri/Interpreter/Place.olean"])
        with self.subTest("symlinked olean"):
            (olean / "Miri/Interpreter/Place.olean").unlink()
            outside = self.tmp / "Place.olean"
            outside.write_bytes(blobs["Miri/Interpreter/Place.olean"])
            os.symlink(outside, olean / "Miri/Interpreter/Place.olean")
            self.assertRejected(lambda: V.verify_vendor(ws.root, olean_dir=olean), "cannot hash closure artifact Miri/Interpreter/Place.olean")
        with self.subTest("closure without ExecutionMachine / without vendored source"):
            pin["execution_machine_closure"] = [{"path": "Miri/Evil.olean", "sha256": "0" * 64}]
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root), "must include 'Miri/Interpreter/ExecutionMachine.olean'", "has no vendored source 'Miri/Evil.lean'")

    def test_real_joshlf_six_file_patch_if_available(self) -> None:
        diff = os.environ.get("ANNEAL_PROTO_DEINIT_PATCH_DIFF")
        if not diff or not Path(diff).is_file() or shutil.which("git") is None:
            self.skipTest("set ANNEAL_PROTO_DEINIT_PATCH_DIFF to the d9b41b58b 6-file diff to run")
        ws = self.workspace()
        originals = {rel: ws.path(rel).read_bytes() for rel in ALLOWLIST}
        subprocess.run(["git", "apply", "-p3", str(Path(diff).resolve())], cwd=ws.vendor, check=True, capture_output=True)
        pre_images = set(re.findall(r"^index ([0-9a-f]+)\.\.", Path(diff).read_text(), re.M))
        pin = ws.pin()
        pin["patched_files"] = []
        for rel in ALLOWLIST:
            patched = ws.path(rel).read_bytes()
            self.assertNotEqual(patched, originals[rel], rel)
            blob = V.git_blob_sha1(originals[rel])
            self.assertTrue(any(blob.startswith(p) for p in pre_images), rel)
            pin["patched_files"].append(
                {"path": rel, "upstream_sha256": _sha256(originals[rel]), "patched_sha256": _sha256(patched), "patch_reason": "joshlf d9b41b58b deinitMovedPlace", "upstream_git_blob": blob}
            )
        ws.write_pin(pin)
        self.assertEqual(len(V.verify_vendor(ws.root, allow_deinit_patch=True).patched_files), 6)
        self.assertRejected(lambda: V.verify_vendor(ws.root), "strict mode")


# ---------------------------------------------------------------------------
# Toolchain tests (fake toolchain)
# ---------------------------------------------------------------------------


class ToolchainTests(TempCase):
    def setUp(self) -> None:
        super().setUp()
        self.ws = self.workspace()
        self.tc = make_fake_toolchain(self.tmp)
        self.pin = self.tmp / "toolchain-pin.json"
        V.write_toolchain_pin(V.verify_toolchain(self.ws.root, toolchain_dir=self.tc), self.pin)

    def verify(self, **kwargs: Any) -> Any:
        kwargs.setdefault("toolchain_dir", self.tc)
        kwargs.setdefault("toolchain_pin_json", self.pin)
        return V.verify_toolchain(self.ws.root, **kwargs)

    def lib(self, name: str) -> Path:
        return self.tc / "lib" / "lean" / name

    def test_fake_toolchain_pin_roundtrip(self) -> None:
        t = self.verify()
        self.assertEqual(t.pin_status, "verified")
        self.assertEqual(t.resolved_by, "override")
        self.assertTrue(any("test-only override" in w for w in t.warnings))
        self.assertEqual(set(t.files), {"bin/lean", "bin/lake", "lib/lean/libInit_shared.so"} | {f"lib/lean/{n}" for n in LIBLEANSHARED})
        self.assertEqual(t.libleanshared, LIBLEANSHARED)

    def test_libleanshared_tamper_vs_pin_rejected(self) -> None:
        self.lib("libleanshared.so").write_bytes(b"trojan")
        self.assertRejected(self.verify, "SHA-256 mismatch for lib/lean/libleanshared.so")

    def test_companion_libleanshared_1_tamper_rejected_while_main_lib_untouched(self) -> None:
        main_before = self.lib("libleanshared.so").read_bytes()
        self.lib("libleanshared_1.so").write_bytes(self.lib("libleanshared_1.so").read_bytes() + b"\x90")
        self.assertRejected(self.verify, "SHA-256 mismatch for lib/lean/libleanshared_1.so", absent=("lib/lean/libleanshared.so:",))
        self.assertEqual(self.lib("libleanshared.so").read_bytes(), main_before)

    def test_extra_libleanshared_evil_injection_rejected(self) -> None:
        self.lib("libleanshared_evil.so").write_bytes(b"evil")
        os.chmod(self.lib("libleanshared_evil.so"), 0o644)
        self.assertRejected(self.verify, "unpinned toolchain file added: lib/lean/libleanshared_evil.so")

    def test_deleted_libleanshared_2_rejected(self) -> None:
        self.lib("libleanshared_2.so").unlink()
        self.assertRejected(self.verify, "pinned toolchain file deleted or unverifiable: lib/lean/libleanshared_2.so")

    def test_libleanshared_so_required_even_without_pin(self) -> None:
        self.lib("libleanshared.so").unlink()
        self.assertRejected(lambda: self.verify(toolchain_pin_json=None), "required toolchain file lib/lean/libleanshared.so is missing")

    def test_world_writable_bin_lean_rejected_and_not_executed(self) -> None:
        os.chmod(self.tc / "bin" / "lean", 0o757)
        self.assertRejected(self.verify, "bin/lean is world-writable", "skipped `bin/lean --version`")

    def test_world_writable_library_rejected(self) -> None:
        os.chmod(self.lib("libleanshared_2.so"), 0o646)
        self.assertRejected(lambda: self.verify(toolchain_pin_json=None), "lib/lean/libleanshared_2.so is world-writable")

    def test_hard_linked_library_rejected(self) -> None:
        os.link(self.lib("libleanshared_1.so"), self.tmp / "alias.so")
        self.assertRejected(self.verify, "lib/lean/libleanshared_1.so is hard-linked (st_nlink=2", "skipped `bin/lean --version`")

    def test_toolchain_symlinks_rejected_escaping_or_not(self) -> None:
        outside = self.tmp / "outside"
        outside.mkdir()
        with self.subTest("bin/lean escapes the toolchain root"):
            shutil.copy2(self.tc / "bin" / "lean", outside / "lean")
            (self.tc / "bin" / "lean").unlink()
            os.symlink(outside / "lean", self.tc / "bin" / "lean")
            self.assertRejected(self.verify, "symlink forbidden: bin/lean ->", "(escapes the toolchain root)")
            (self.tc / "bin" / "lean").unlink()
            shutil.copy2(outside / "lean", self.tc / "bin" / "lean")
        with self.subTest("companion library escapes the toolchain root"):
            shutil.copy2(self.lib("libleanshared_1.so"), outside / "libleanshared_1.so")
            self.lib("libleanshared_1.so").unlink()
            os.symlink(outside / "libleanshared_1.so", self.lib("libleanshared_1.so"))
            self.assertRejected(self.verify, "symlink forbidden: lib/lean/libleanshared_1.so ->", "(escapes the toolchain root)")
            self.lib("libleanshared_1.so").unlink()
            shutil.copy2(outside / "libleanshared_1.so", self.lib("libleanshared_1.so"))
        with self.subTest("internal symlink is still forbidden"):
            self.lib("libleanshared_2.so").unlink()
            os.symlink("libleanshared_1.so", self.lib("libleanshared_2.so"))
            self.assertRejected(self.verify, "symlink forbidden: lib/lean/libleanshared_2.so -> libleanshared_1.so (stays inside")
        with self.subTest("lib/lean directory escapes the toolchain root"):
            shutil.move(str(self.tc / "lib" / "lean"), str(outside / "lean-lib"))
            os.symlink(outside / "lean-lib", self.tc / "lib" / "lean")
            self.assertRejected(self.verify, "symlink forbidden: lib/lean ->")

    def test_lean_toolchain_drift_rejected(self) -> None:
        (self.ws.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        self.assertRejected(
            lambda: V.verify_all(self.ws.root, toolchain_dir=self.tc),
            "toolchain drift: lean-toolchain is 'leanprover/lean4:v4.35.0' but UPSTREAM_PIN.json build_lean_toolchain is",
            "bin/lean reports version",
        )
        (self.ws.root / "lean-toolchain").write_text("leanprover/lean4:stable\n")
        self.assertRejected(lambda: V.verify_all(self.ws.root, toolchain_dir=self.tc), "moving channel")

    def test_version_and_commit_mismatches_rejected(self) -> None:
        cases = [
            ("lean version", dict(lean_body=f"echo 'Lean (version 4.0.0, x86_64-unknown-linux-gnu, commit {FAKE_COMMIT}, Release)'"), "bin/lean reports version 4.0.0"),
            ("lake version", dict(lake_body=f"echo 'Lake version 5.0.0-src+{FAKE_COMMIT[:7]} (Lean version 4.0.0)'"), "bin/lake reports Lean version 4.0.0"),
            ("lake commit", dict(lake_body=f"echo 'Lake version 5.0.0-src+deadbee (Lean version {REPO_LEAN_VERSION})'"), "build commit deadbee does not match"),
            ("garbage", dict(lean_body="echo 'totally not lean'"), "unrecognized `bin/lean --version` output"),
            ("non-zero exit", dict(lean_body="echo boom >&2; exit 3"), "`bin/lean --version` exited 3"),
            ("reads stdin", dict(lean_body="read line || exit 4; echo got"), "`bin/lean --version` exited 4"),
        ]
        for index, (label, kwargs, needle) in enumerate(cases):
            with self.subTest(label):
                tc = make_fake_toolchain(self.tmp, name=f"tc{index}", **kwargs)
                self.assertRejected(lambda: V.verify_toolchain(self.ws.root, toolchain_dir=tc), needle)

    def test_version_probe_timeout_rejected(self) -> None:
        tc = make_fake_toolchain(self.tmp, name="slow", lean_body="exec sleep 30")
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, toolchain_dir=tc, timeout=0.5), "`bin/lean --version` timed out")

    def test_toolchain_pin_name_and_schema_rejections(self) -> None:
        pin = json.loads(self.pin.read_text())
        cases = [
            ("other toolchain", dict(pin, toolchain="leanprover/lean4:v4.0.0"), "toolchain pin is for 'leanprover/lean4:v4.0.0'"),
            ("unknown key", dict(pin, extra=True), "unknown key 'extra'"),
            ("bad digest", dict(pin, files=dict(pin["files"], **{"bin/lean": "xyz"})), "toolchain pin entry 'bin/lean': invalid path or SHA-256"),
            ("version drift", dict(pin, versions=dict(pin["versions"], **{"bin/lake": "Lake version 0"})), "bin/lake --version"),
        ]
        for label, doc, needle in cases:
            with self.subTest(label):
                self.pin.write_text(json.dumps(doc))
                self.assertRejected(self.verify, needle)

    def test_elan_home_resolution_and_override_detection(self) -> None:
        elan = self.tmp / "elan"
        installed = elan / "toolchains" / V.toolchain_dir_name(REPO_TOOLCHAIN)
        installed.parent.mkdir(parents=True)
        shutil.copytree(self.tc, installed, symlinks=True)
        t = V.verify_toolchain(self.ws.root, elan_home=elan, environ={}, toolchain_pin_json=self.pin)
        self.assertEqual(Path(t.toolchain_dir), installed)
        self.assertEqual((t.resolved_by, t.warnings), ("elan", ()))
        shadow = self.tmp / "shadow-bin"
        shadow.mkdir()
        shutil.copy2(self.tc / "bin" / "lean", shadow / "lean")
        shadowed = V.verify_toolchain(self.ws.root, elan_home=elan, environ={"PATH": str(shadow)})
        self.assertTrue(any("`lean` on PATH resolves to" in w for w in shadowed.warnings), shadowed.warnings)
        self.assertEqual(V.verify_toolchain(self.ws.root, environ={"ELAN_HOME": str(elan)}).toolchain_dir, str(installed))
        self.assertRejected(
            lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={"ELAN_TOOLCHAIN": "leanprover/lean4:v4.0.0"}),
            "ELAN_TOOLCHAIN='leanprover/lean4:v4.0.0' overrides",
        )
        (elan / "settings.toml").write_text(f'default_toolchain = "{REPO_TOOLCHAIN}"\n\n[overrides]\n"{self.ws.root.resolve()}" = "leanprover/lean4:v4.0.0"\n')
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), "elan override")
        (elan / "settings.toml").unlink()
        shutil.rmtree(installed)
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), "is not installed as a real directory")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


class CliTests(TempCase):
    def run_cli(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, "-B", str(VERIFIER_PATH), *args],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=600,
            check=False,
        )

    def test_cli_json_dump_verify_and_tamper(self) -> None:
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        pin = self.tmp / "pin.json"
        ok = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--dump-toolchain-pin", str(pin), "--json")
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        summary = json.loads(ok.stdout)
        self.assertEqual((summary["verified_vendor_files"], summary["verified_aux_files"]), (608, 9))
        self.assertEqual(summary["dumped_toolchain_pin"], str(pin))
        self.assertEqual(json.loads(pin.read_text())["files"], summary["toolchain"]["sha256"])
        (tc / "lib" / "lean" / "libleanshared_2.so").write_bytes(b"swapped")
        bad = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--toolchain-pin-json", str(pin), "--json")
        self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
        failure = json.loads(bad.stdout)
        self.assertIs(failure["ok"], False)
        self.assertTrue(any("SHA-256 mismatch for lib/lean/libleanshared_2.so" in e for e in failure["errors"]), failure)

    def test_cli_allow_deinit_patch_flag_and_human_output(self) -> None:
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        ws.apply_overlay(ALLOWLIST)
        strict = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc))
        self.assertEqual(strict.returncode, 1, strict.stdout + strict.stderr)
        self.assertIn("lean-miri pin verification FAILED", strict.stderr)
        self.assertIn("strict mode", strict.stderr)
        patched = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch")
        self.assertEqual(patched.returncode, 0, patched.stdout + patched.stderr)
        self.assertIn("verified_vendor_files: 608", patched.stdout)
        self.assertIn("patched_files: 6", patched.stdout)

    def test_cli_rejects_bad_arguments(self) -> None:
        proc = self.run_cli("--expected-pin-sha256", "nothex")
        self.assertEqual(proc.returncode, 2)
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        wrong = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--expected-pin-sha256", "0" * 64, "--json")
        self.assertEqual(wrong.returncode, 1)
        self.assertTrue(any("[identity] lean-miri/UPSTREAM_PIN.json SHA-256" in e for e in json.loads(wrong.stdout)["errors"]))


# ---------------------------------------------------------------------------
# Lean prototype hygiene
# ---------------------------------------------------------------------------

#: Keywords that must not occur in Lean code (comments/strings stripped).
LEAN_FORBIDDEN_KEYWORDS = ("sorry", "admit", "native_decide", "axiom", "unsafe", "partial", "implemented_by", "extern")
#: Names that smuggle in unchecked trust even when qualified (`Lean.ofReduceBool`).
LEAN_FORBIDDEN_NAMES = ("ofReduceBool", "reduceBool", "trustCompiler", "skipKernelTC", "sorryAx", "admitGoal", "mkSorry", "addDecl", "axiomDecl")
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})
_LEAN_ID = "A-Za-z0-9_'!?"
_GUARD_PRINT_RE = re.compile(r"#guard_msgs(?:\s*\(([^)]*)\))?\s+in\s+#print\s+axioms\s+(\S+)")
_PRINT_AXIOMS_RE = re.compile(r"#print\s+axioms\s+(\S+)")


def strip_lean_comments_and_strings(src: str) -> str:
    """Blank out comments (nested `/- -/`, `--`), string and char literals,
    preserving length and newlines so offsets and line numbers survive."""

    def blank(segment: str) -> str:
        return "".join("\n" if ch == "\n" else " " for ch in segment)

    out: List[str] = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
            continue
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise ValueError(f"unterminated block comment at offset {i}")
            out.append(blank(src[i:j]))
            i = j
            continue
        ch = src[i]
        prev = src[i - 1] if i else ""
        prev_ident = bool(prev) and (prev.isalnum() or prev in "_'!?.")
        if ch == "r" and not prev_ident:
            m = re.match(r'r(#*)"', src[i:])
            if m:
                end = src.find('"' + m.group(1), i + len(m.group(0)))
                if end < 0:
                    raise ValueError(f"unterminated raw string at offset {i}")
                j = end + 1 + len(m.group(1))
                out.append(blank(src[i:j]))
                i = j
                continue
        if ch == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if j >= n:
                raise ValueError(f"unterminated string literal at offset {i}")
            out.append(blank(src[i : j + 1]))
            i = j + 1
            continue
        if ch == "'" and not prev_ident:
            m = re.match(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'", src[i:])
            if m:
                out.append(blank(m.group(0)))
                i += len(m.group(0))
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def find_forbidden_lean_tokens(code: str) -> List[Tuple[int, str]]:
    hits = []
    for token in LEAN_FORBIDDEN_KEYWORDS:
        for m in re.finditer(rf"(?<![{_LEAN_ID}.]){re.escape(token)}(?![{_LEAN_ID}])", code):
            hits.append((code.count("\n", 0, m.start()) + 1, token))
    for token in LEAN_FORBIDDEN_NAMES:
        for m in re.finditer(rf"(?<![{_LEAN_ID}]){re.escape(token)}(?![{_LEAN_ID}])", code):
            hits.append((code.count("\n", 0, m.start()) + 1, token))
    return sorted(hits)


def parse_axiom_guards(src: str) -> Tuple[List[Dict[str, Any]], List[str]]:
    """Return (`#guard_msgs in #print axioms` pairs, problems)."""
    code = strip_lean_comments_and_strings(src)
    guards: List[Dict[str, Any]] = []
    problems: List[str] = []
    for m in _GUARD_PRINT_RE.finditer(code):
        spec, target, line = m.group(1) or "", m.group(2), code.count("\n", 0, m.start()) + 1
        if "drop" in spec:
            problems.append(f"line {line}: `#guard_msgs ({spec})` drops messages, so it cannot pin the axioms of {target}")
        before = src[: m.start()].rstrip()
        doc = None
        if before.endswith("-/"):
            start = before.rfind("/--")
            if start >= 0:
                doc = " ".join(before[start + 3 : -2].split())
        guard = {"target": target, "line": line, "doc": doc, "axioms": None}
        guards.append(guard)
        if doc is None:
            problems.append(f"line {line}: #guard_msgs for {target} has no expected-output docstring")
            continue
        dm = re.fullmatch(r"info: '?([^']+?)'? (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", doc)
        if dm is None:
            problems.append(f"line {line}: unrecognized #print axioms expectation for {target}: {doc!r}")
            continue
        printed = dm.group(1)
        if not (printed == target or printed.endswith("." + target) or target.endswith("." + printed)):
            problems.append(f"line {line}: guard expects axioms of {printed!r} but prints {target!r}")
        axioms = [a.strip() for a in (dm.group(2) or "").split(",") if a.strip()]
        guard["axioms"] = axioms
        extra = sorted(set(axioms) - ALLOWED_AXIOMS)
        if extra:
            problems.append(f"line {line}: {target} depends on axioms outside {{propext, Quot.sound}}: {extra}")
    unguarded = len(_PRINT_AXIOMS_RE.findall(code)) - len(guards)
    if unguarded:
        problems.append(f"{unguarded} `#print axioms` command(s) are not pinned by `#guard_msgs in`")
    return guards, problems


class LeanHygieneScannerSelfTests(unittest.TestCase):
    """Non-vacuity: the scanners must flag planted violations."""

    def test_stripper_ignores_comments_and_strings_but_flags_code(self) -> None:
        src = (
            "/- sorry /- nested admit -/ still comment native_decide -/\n"
            "-- axiom in a line comment\n"
            'def s : String := "sorry \\" unsafe"\n'
            "def c : Char := 'x'\n"
            "theorem h' : True := trivial -- partial\n"
            "theorem bad : False := by sorry\n"
            "@[implemented_by foo] def g := 1\n"
            "def r := r#\"extern\"#\n"
            "#print axioms h'\n"
        )
        hits = find_forbidden_lean_tokens(strip_lean_comments_and_strings(src))
        self.assertEqual(hits, [(6, "sorry"), (7, "implemented_by")])
        self.assertEqual(find_forbidden_lean_tokens("axiom foo : False\nunsafe def x := 1\n"), [(1, "axiom"), (2, "unsafe")])
        self.assertEqual(find_forbidden_lean_tokens("example := Lean.ofReduceBool\n"), [(1, "ofReduceBool")])
        self.assertEqual(find_forbidden_lean_tokens("#print axioms foo\ntheorem partialFoo : True := trivial\n"), [])

    def test_guard_parser_accepts_clean_and_flags_bad_expectations(self) -> None:
        good = (
            "theorem t : True := trivial\n"
            "/--\ninfo: 'Ns.t' depends on axioms: [propext, Quot.sound]\n-/\n#guard_msgs in\n#print axioms t\n"
            "/-- info: 'Ns.u' does not depend on any axioms -/\n#guard_msgs in\n#print axioms u\n"
        )
        guards, problems = parse_axiom_guards(good)
        self.assertEqual((len(guards), problems), (2, []))
        self.assertEqual(guards[0]["axioms"], ["propext", "Quot.sound"])
        for bad, needle in (
            ("/-- info: 'Ns.t' depends on axioms: [propext, sorryAx] -/\n#guard_msgs in\n#print axioms t\n", "sorryAx"),
            ("/-- info: 'Ns.t' depends on axioms: [Classical.choice, propext] -/\n#guard_msgs in\n#print axioms t\n", "Classical.choice"),
            ("/-- info: 'Ns.t' depends on axioms: [Lean.ofReduceBool] -/\n#guard_msgs in\n#print axioms t\n", "Lean.ofReduceBool"),
            ("#guard_msgs in\n#print axioms t\n", "no expected-output docstring"),
            ("/-- info: 'Ns.other' does not depend on any axioms -/\n#guard_msgs in\n#print axioms t\n", "guard expects axioms of"),
            ("#print axioms t\n", "not pinned by `#guard_msgs in`"),
            ("/-- info: 'Ns.t' depends on axioms: [propext] -/\n#guard_msgs (drop info) in\n#print axioms t\n", "drops messages"),
        ):
            with self.subTest(needle):
                _, problems = parse_axiom_guards(bad)
                self.assertTrue(any(needle in p for p in problems), problems)


@unittest.skipUnless(LEAN_PROTOTYPE.is_file(), f"{LEAN_PROTOTYPE_REL} not present")
class LeanPrototypeHygieneTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.src = LEAN_PROTOTYPE.read_text(encoding="utf-8")
        cls.code = strip_lean_comments_and_strings(cls.src)

    def test_imports_trusted(self) -> None:
        self.assertRegex(self.code, re.compile(r"^import\s+Trusted(\.[A-Za-z0-9_.]+)?\s*$", re.M))

    def test_no_forbidden_tokens(self) -> None:
        hits = find_forbidden_lean_tokens(self.code)
        self.assertEqual(hits, [], f"forbidden tokens in {LEAN_PROTOTYPE_REL}: {hits}")

    def test_axiom_guards_pin_only_propext_and_quot_sound(self) -> None:
        guards, problems = parse_axiom_guards(self.src)
        self.assertEqual(problems, [])
        self.assertGreaterEqual(len(guards), 20, f"only {len(guards)} `#guard_msgs in #print axioms` pairs")
        for guard in guards:
            self.assertFalse({"sorryAx", "Lean.ofReduceBool", "Classical.choice"} & set(guard["axioms"] or []), guard)

    def test_compiles_without_errors_warnings_or_sorry(self) -> None:
        if os.environ.get("ANNEAL_PROTO_SKIP_LEAN_COMPILE") == "1":
            self.skipTest("ANNEAL_PROTO_SKIP_LEAN_COMPILE=1")
        home = Path.home()
        env = dict(os.environ)
        env["PATH"] = f"{home / '.elan' / 'bin'}{os.pathsep}{home / '.local' / 'bin'}{os.pathsep}{env.get('PATH', '')}"
        missing = [tool for tool in ("anneal-lean-run", "lake") if shutil.which(tool, path=env["PATH"]) is None]
        if missing:
            self.skipTest(f"missing tools: {missing}")
        cmd = ["anneal-lean-run", "--mode", "file", "--concurrency", "1"]
        if os.environ.get("ANNEAL_PROTO_LEAN_RUN_TIMEOUT"):
            cmd += ["--timeout", os.environ["ANNEAL_PROTO_LEAN_RUN_TIMEOUT"]]
        proc = subprocess.run(
            cmd + ["--", "lake", "env", "lean", LEAN_PROTOTYPE_REL],
            cwd=REPO_ROOT,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=1500,
            check=False,
        )
        output = proc.stdout
        self.assertEqual(proc.returncode, 0, output[-4000:])
        for needle in ("error:", "warning:", "sorry"):
            self.assertNotIn(needle, output, output[-4000:])


if __name__ == "__main__":
    unittest.main()
