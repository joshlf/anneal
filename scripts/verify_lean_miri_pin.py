#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fail-closed verifier for `lean-miri/UPSTREAM_PIN.json`, the vendored
`lean-miri/vendor/` tree, and the active `elan` Lean toolchain.

Stdlib-only Python 3 (promoted from the validated `af95b30265`
`verify_lean_miri_pin_proto.py` prototype). Every check fails closed: anything
that is not positively verified is reported as an error, and the CLI exits
non-zero listing every error found. The module defines no `@dataclass` (result
records are `typing.NamedTuple`s), so it also loads through
`importlib.util.spec_from_file_location` loaders that never register it in
`sys.modules`. `trusted/audit/check_trusted.py` embeds an independent,
standalone copy of the security-relevant subset (it may not import this file);
`scripts/test_verify_lean_miri_pin.py` cross-checks that both carry the same
locked constants.

Vendor checks (`verify_vendor`)
-------------------------------
1. Schema: `schema_version == 2`; exact required top-level keys; unknown keys
   rejected except the optional extensions `patched_files` and
   `execution_machine_closure`; 40-hex commits, 64-hex SHA-256 digests
   (lowercase only); duplicate JSON object keys rejected; clean relative POSIX
   paths only (no absolute, `.`/`..`, empty, backslash or exotic components;
   exact and case-folded duplicates rejected).
2. Filesystem: `os.walk(followlinks=False)` + `lstat` over `lean-miri/vendor/`;
   any symlink (file or directory), non-regular file, world-writable or
   setuid/setgid mode, hard link (`st_nlink != 1`), planted build artifact
   (`*.olean*`, `*.ilean`, `*.ir`, `*.c`, `*.ltar`, `*.hash`, `*.trace`,
   `.lake/`, ...) or extraneous directory is an error. The on-disk file set
   must be in exact bijection with `vendor_tree.files` (`.lean`) plus
   `vendor_aux_files` (everything else). Files are opened with `O_NOFOLLOW`
   and re-checked with `fstat` (same inode as the walk's `lstat`) so a symlink
   cannot be swapped in mid-scan.
3. Digests: per-file SHA-256 (streamed) and recomputation of
   `vendor_tree.manifest_sha256` with the canonical formula below.
4. Git cross-check: every `upstream_git_objects` entry is recomputed from the
   vendored bytes and file modes: git blob ids
   (`sha1(b"blob <size>\\0" + content)`) for file entries and recursive git
   tree ids for directory entries such as `Miri` (entries
   `<mode> <name>\\0<20 raw bytes>`, modes `100644`/`100755`/`40000`, git sort
   order where directory names compare as `name + "/"`). Every vendored file
   must be covered by some git object entry, and the `upstream/.pins/*.commit`
   markers and `upstream/source-lock.json` must agree with `upstream_pins`.
5. Locked upstream identity (`LOCKED_UPSTREAM_IDENTITY`): repository, commit,
   upstream toolchain, `upstream_pins`, the full `upstream_git_objects`
   mapping and `vendor_tree.{file_count,manifest_sha256}` are compiled into
   this verifier, so a forged-but-self-consistent pin (vendored bytes, manifest
   and git ids all recomputed by an attacker) is still rejected. Updating the
   upstream pin therefore requires a reviewed change to this file as well. The
   pin's `build_lean_toolchain` must name a toolchain with compiled-in release
   digests (`LOCKED_TOOLCHAIN_PINS`), like `check_trusted.py`'s locked `TOOLCHAIN`.
6. Patch modes. Strict mode (the CLI default) rejects any `patched_files`
   entry and any byte difference from upstream. With `allow_deinit_patch=True`
   (`--allow-deinit-patch`), `patched_files` may overlay a subset of the closed
   10-file `PATCH_ALLOWLIST` (the Episode 1 `deinitMovedPlace` /
   `pendingMoveDeinit` patch); each entry needs `path`, distinct valid
   `upstream_sha256` / `patched_sha256`, a non-empty `patch_reason` and the
   40-hex `upstream_git_blob`, which must equal the locked pre-image blob.
   Design choice: the `vendor_tree` manifest keeps describing UPSTREAM bytes
   (the entry's `sha256` must equal `upstream_sha256`), so `manifest_sha256`
   and the locked identity are unchanged by the patch, while the on-disk file
   must hash to `patched_sha256`; the `Miri` tree id is recomputed substituting
   `upstream_git_blob` for patched files.
   `LOCKED_DEINIT_PATCHED_FILES` compiles in the reviewed Episode 1 patch
   (`upstream_sha256`, `patched_sha256`, `upstream_git_blob` of all 10 files).
   `require_locked_deinit_patch=True` (`--require-locked-deinit-patch`, implies
   `--allow-deinit-patch`) requires `patched_files` to be exactly that 10-entry
   set. The default (`require_locked_deinit_patch=None`) applies the same
   exact-digest check automatically whenever `patched_files` declares the whole
   10-file allowlist, so the complete patch can only ever be the reviewed one;
   a proper subset (synthetic overlays) is accepted with the flag alone.
   `require_locked_deinit_patch=False` (API only, for synthetic full overlays)
   disables the lock. Updating the patch requires a reviewed change here and
   in `trusted/audit/check_trusted.py`.
7. Optional `execution_machine_closure` (`[{path, sha256}]`, `.olean` paths
   relative to an explicit `--olean-dir`): verified only when `olean_dir` is
   supplied, otherwise reported as `skipped`.

Canonical manifest formula (derived from the real pin; reproduces
`081747a37a96c7443997ba12b02565f45c9642dd0dec9e3dcb3a30e7053c8d16`)::

    manifest_sha256 = sha256("".join(f"{e['sha256']}  {e['path']}\\n"
                                     for e in vendor_tree["files"]))

i.e. `sha256sum`-style lines (digest, two spaces, path, LF) concatenated in
listed order, the same formula as `joshlf`'s `verify_upstream_pin`. The listed
order must be canonical: root-level files first, then path-component order
(`Miri.lean`, then `sorted(Path("Miri").rglob("*.lean"))`). Rejected
candidates: byte-sorted lines, `path  sha` lines, and `json.dumps(files)` in
every separator / key-order variant.

Toolchain checks (`verify_toolchain`, after cl/1021969520)
-----------------------------------------------------------
The repository `lean-toolchain` must name an immutable release and equal the
pin's `build_lean_toolchain`. The active toolchain is resolved like `elan`
does (`$ELAN_HOME` or `~/.elan`, `toolchains/<name>` with `/` -> `--` and
`:` -> `---`); a conflicting `ELAN_TOOLCHAIN` or an `elan override` covering
the repository is an error. Every `bin/*` entry (`lean`, `lake` and, in the
official release, the companion executables `leanc`, `leanchecker`, `leanir`,
`leanmake`, `leantar`, `cadical`, `clang`, `ld.lld`, `llvm-ar`) and every
top-level `lib/lean/*.so` (the required `libleanshared*.so` family --
`libleanshared.so`, `libleanshared_1.so`, `libleanshared_2.so` -- plus
`libInit_shared.so` and `libLake_shared.so`) must be a regular file (no symlink
anywhere below the toolchain root, escaping or not), not world-writable, not
setuid/setgid and not hard-linked; `bin/lean`, `bin/lake` and
`lib/lean/libleanshared.so` are required (`TOOLCHAIN_REQUIRED_FILES`). All of
them are SHA-256 hashed in 1 MiB chunks. The default run compares them with
the compiled-in `LOCKED_TOOLCHAIN_PINS` (the official
`leanprover/lean4:v4.34.1` `x86_64-unknown-linux-gnu` release archive: all 16
files were checked against `lean-4.34.1-linux.zip` from the GitHub release),
so any added, deleted or modified pinned file fails closed. Before anything is
executed, the stdlib ELF64 parser (`elf_dynamic_info`) and the glibc-faithful
`_check_runpath_shadowing` resolve every `DT_NEEDED` soname of every
RUNPATH-checked object (`RUNPATH_CHECKED_BINARIES` plus `lib/lean/*.so`)
through every `DT_RUNPATH` / `DT_RPATH` directory, and glibc / Lean sonames
planted in `lib/` or `lib/lean/` are rejected. Only when every file check
passed are `bin/lean --version` and `bin/lake --version` executed (with
`stdin=DEVNULL`, a scrubbed environment and a timeout); both must report the
toolchain's version and the same build commit.
`--dump-toolchain-pin PATH` writes `{toolchain, versions, files{relpath:
sha256}}`; `--toolchain-pin-json PATH` fails closed on any added, deleted or
modified pinned file (including companion `libleanshared_*.so` and `bin/*`
files) or on a name/version mismatch.

Known limits: the `elan` proxy binaries in `$ELAN_HOME/bin` are not pinned;
the companion `clang` / `ld.lld` / `llvm-ar` / `cadical` executables are
digest-pinned but excluded from the RUNPATH analysis because their `DT_NEEDED`
closure is the release's own top-level `lib/` (`libLLVM`, `libclang-cpp`,
`libc++`, `libz`, ...), which is not pinned; a `lean`/`lake` on `PATH` that is
neither the elan proxy nor the verified binary only produces a warning; checks
are point-in-time (a writer with access to the verified files can still change
them after verification).
"""

from __future__ import annotations

import sys

sys.dont_write_bytecode = True

import argparse  # noqa: E402
import hashlib  # noqa: E402
import json  # noqa: E402
import os  # noqa: E402
import platform  # noqa: E402
import re  # noqa: E402
import shutil  # noqa: E402
import stat  # noqa: E402
import struct  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
from pathlib import Path  # noqa: E402
from typing import Any, Dict, List, Mapping, NamedTuple, NoReturn, Optional, Sequence, Set, Tuple  # noqa: E402

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

SCHEMA_VERSION = 2
PIN_RELPATH = "lean-miri/UPSTREAM_PIN.json"
VENDOR_RELPATH = "lean-miri/vendor"
LEAN_TOOLCHAIN_RELPATH = "lean-toolchain"
CHUNK_SIZE = 1 << 20  # 1 MiB streaming chunks
DEFAULT_VERSION_TIMEOUT = 60.0

MANIFEST_FORMULA = (
    "sha256(concat(f\"{sha256}  {path}\\n\" for each vendor_tree.files entry in "
    "listed canonical order: root-level files first, then path-component order))"
)

#: The closed Episode 1 `deinitMovedPlace` / `pendingMoveDeinit` patch allowlist
#: (`joshlf-mir-deinit` d9b41b58b's six files plus the consumer-side call / cast
#: files of `ws-lean-miri-deinit-pin-and-correspondence-codec` Episode 1).
PATCH_ALLOWLIST = frozenset(
    {
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
    }
)

REQUIRED_TOP_LEVEL_KEYS = (
    "schema_version",
    "repository",
    "commit",
    "upstream_lean_toolchain",
    "build_lean_toolchain",
    "upstream_pins",
    "notes",
    "upstream_git_objects",
    "vendor_tree",
    "vendor_aux_files",
)
OPTIONAL_TOP_LEVEL_KEYS = ("patched_files", "execution_machine_closure")
UPSTREAM_PINS_COMMIT_KEYS = ("miri_commit", "rustc_commit", "rustc_apfloat_commit", "aes_commit")
UPSTREAM_PINS_KEYS = UPSTREAM_PINS_COMMIT_KEYS + ("source_lock_sha256",)
VENDOR_TREE_KEYS = ("file_count", "manifest_sha256", "files")
FILE_ENTRY_KEYS = ("path", "sha256")
PATCHED_FILE_KEYS = ("path", "upstream_sha256", "patched_sha256", "patch_reason")
PATCHED_FILE_OPTIONAL_KEYS = ("upstream_git_blob",)
CLOSURE_REQUIRED_KEYS = ("path", "sha256")
CLOSURE_OPTIONAL_KEYS = ("module",)
CLOSURE_ROOT_OLEAN = "Miri/Interpreter/ExecutionMachine.olean"

#: Vendored marker files that must agree with `upstream_pins`.
PIN_MARKER_FILES = {
    "miri_commit": "upstream/.pins/miri.commit",
    "rustc_commit": "upstream/.pins/rustc.commit",
    "rustc_apfloat_commit": "upstream/.pins/rustc_apfloat.commit",
    "aes_commit": "upstream/.pins/aes.commit",
}
SOURCE_LOCK_FILE = "upstream/source-lock.json"

#: Upstream identity compiled into the verifier (`proofs-rs/lean-miri` at
#: c92d1d97). Every value is a fact about the immutable upstream commit; a pin
#: bump must update this mapping in the same reviewed change.
LOCKED_UPSTREAM_IDENTITY: Mapping[str, Any] = {
    "repository": "https://github.com/proofs-rs/lean-miri.git",
    "commit": "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a",
    "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
    "upstream_pins": {
        "miri_commit": "7fa591d7d4dd9af8154becbc8332f8096f8323b1",
        "rustc_commit": "8144389c895da997dbdecaa635e41d6a50be6ffd",
        "rustc_apfloat_commit": "eeaacad81247af65d4043cb3e32d023a652d7951",
        "aes_commit": "c1534361e7549e29a16c3505f45a04c92d26b62a",
        "source_lock_sha256": "371f3b91e61ff027121b9706a15aac9b6f272ef1cb5ce0d150707a9cf8883873",
    },
    "vendor_tree.file_count": 608,
    "vendor_tree.manifest_sha256": "081747a37a96c7443997ba12b02565f45c9642dd0dec9e3dcb3a30e7053c8d16",
    "upstream_git_objects": {
        "Miri": "ef473f04eed9bbfed474a7b5f6f91a2f6350c41b",
        "Miri.lean": "4c2b87b06a1786f369cc6ae26e94b3cc72652d85",
        "LICENSE-APACHE": "1b5ec8b78e237b5c3b3d812a7c0a6589d0f7161d",
        "LICENSE-MIT": "31aa79387f27e730e33d871925e152e35e428031",
        "tools/check_implementation_ledger.py": "e1879ecc717b1ec24d8f4d51fa84835693b6d69b",
        "tools/check_semantic_sources.py": "7a9d8f8628d536ac3eab665c578fa7901c3efb09",
        "upstream/.pins/aes.commit": "2aadc7ac8eb1930b6dbdf28d4c6443f805038d6a",
        "upstream/.pins/miri.commit": "3dff1349544fc7ef71be7266ee7437817efa0b18",
        "upstream/.pins/rustc.commit": "60438fb681c3b95d7163a689a5e2cb0d54cc1ef3",
        "upstream/.pins/rustc_apfloat.commit": "e3e2ad8b3762b9b9dffa17c6ec9f9ad3544d54f5",
        "upstream/source-lock.json": "503d1c21ca5096c1cdbec40d235da58c1f12efd0",
    },
}

#: The reviewed Episode 1 `deinitMovedPlace` patch (`[adv ep1-A4]`, 8cb8f3e2):
#: for each of the 10 allowlisted files, the SHA-256 of the upstream bytes (also
#: pinned by the locked `vendor_tree` manifest), the SHA-256 of the patched
#: bytes on disk, and the git blob id of the upstream bytes (pinned by the locked
#: `Miri` tree id). `trusted/audit/check_trusted.py` embeds the same table.
LOCKED_DEINIT_PATCHED_FILES: Mapping[str, Mapping[str, str]] = {
    "Miri/Interpreter/Call.lean": {
        "upstream_sha256": "4f84e6562232130ab86a9ea057a63e8f1a57c17daef2f91d2bb9ca6251fb0287",
        "patched_sha256": "315de29e02fc5b8d4d0a7e1ef6a0bbfe29e83ea51e4c3f21977776298bfaa470",
        "upstream_git_blob": "1de0bbe80a2620c98cdc9371d7400db9f4a775bd",
    },
    "Miri/Interpreter/Cast.lean": {
        "upstream_sha256": "34d19a23f5128f4d00301bc3d9655e0b8a1e83c4877ae8adf188ddba57952661",
        "patched_sha256": "b602d3c23ab8c0ef333747cdb50566aa3ea9dc9cab43fe33aae901ca51488157",
        "upstream_git_blob": "787f482061f213dade377a0a360637bc7a3ed0c3",
    },
    "Miri/Interpreter/ExecutionCalls.lean": {
        "upstream_sha256": "0e401e0f72d5ac5dcb13ebb794e2e2affe742f25a8557fd68a4440dc15cf33d8",
        "patched_sha256": "1bbd8cf0553ae0560c8e3ecc57d70bee3aeec70ee854ed3b25cb7caa55bb5c58",
        "upstream_git_blob": "512a0af720bfab4b1cb36f9ad1cc31c29fa9f53a",
    },
    "Miri/Interpreter/ExecutionCast.lean": {
        "upstream_sha256": "037c6660d02ec418bc48a12f5465c322c8e9ddd666f7e8d2edbd2bdade54298b",
        "patched_sha256": "59a329b3c016e80c94cfcea915f57ddecfe1c4bffcb06e3ae82bc3c41964ce2f",
        "upstream_git_blob": "67f877548d3a5d2c600b5e144a58b91c4aed16bc",
    },
    "Miri/Interpreter/ExecutionMachine.lean": {
        "upstream_sha256": "e601f25d2c9c87014984ec580979cb8d8beb052b4c7c63507b1d98c7098a8796",
        "patched_sha256": "8cfa22538b2e34e74b157b1e3b138d9fded41f8d237985a23082ffdf2b4d15b1",
        "upstream_git_blob": "66048728edfdb3295f3cfcefb97b041236715bfa",
    },
    "Miri/Interpreter/LocalAccess.lean": {
        "upstream_sha256": "051fe91f8ceee3bcb583332585dfdfe19187db5e4d8d9dc4cb9a552430d9d0eb",
        "patched_sha256": "9f416048aa310ef9690433935789e4b34c4725be902da0398c5f9c0dcde3b574",
        "upstream_git_blob": "7a032dfea7048c153c07f263cfb88e19ccf9ac22",
    },
    "Miri/Interpreter/MachineHooks.lean": {
        "upstream_sha256": "1df4df7ce4fbc696360b4a7ba0bf4bc921c6b91ed3793cb6c234eb826b8dad36",
        "patched_sha256": "59df22918a063cac09fd12dba087a03a86a19e7d201c79a9ddac550acb9b15b4",
        "upstream_git_blob": "673eabdf0fbee9a4ea6b08311973c0b5469cb222",
    },
    "Miri/Interpreter/OperandMachine.lean": {
        "upstream_sha256": "ee81c3890c4c8ac0e3e8812b7e5754855c80716c8d5d262157dec3866d00d9a5",
        "patched_sha256": "77e437f1e43abb55e0116faab37035033f229870b3883920dbd2c174d6e20c99",
        "upstream_git_blob": "579beda13592aad81242dea8b9a4d86201e29a92",
    },
    "Miri/Interpreter/Place.lean": {
        "upstream_sha256": "75ed68eb91c983532dcf3184bf590e32993aef961c2f709051b7d1844bb0b9ab",
        "patched_sha256": "b57b04136b40c0c01c85e69c48fbffb9dc6944098cf791715f7e93740df24ddd",
        "upstream_git_blob": "327fd613c9852fef27d764e591060d6a335ca191",
    },
    "Miri/Interpreter/PlaceMachine.lean": {
        "upstream_sha256": "573ff212da394ad9ec43f2f7010b1d6f3050dfcc218785168a66a0ebdc804e96",
        "patched_sha256": "7b0211bdaf8dfcc8761b67b322ffc86da57ece261d4a57c2c35ff7b30a9c8250",
        "upstream_git_blob": "1b3e5cedb4ad98392086ef6867f156a15a74ef5f",
    },
}

#: Upstream pre-image git blob ids of the allowlisted files (fallback for the
#: legacy 4-key `patched_files` schema that omits `upstream_git_blob`).
LOCKED_DEINIT_BLOBS: Mapping[str, str] = {
    path: entry["upstream_git_blob"] for path, entry in LOCKED_DEINIT_PATCHED_FILES.items()
}
if set(LOCKED_DEINIT_PATCHED_FILES) != PATCH_ALLOWLIST:  # pragma: no cover - static invariant
    raise AssertionError("LOCKED_DEINIT_PATCHED_FILES must cover exactly PATCH_ALLOWLIST")

_HEX40_RE = re.compile(r"\A[0-9a-f]{40}\Z")
_HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_PATH_COMPONENT_RE = re.compile(r"\A[A-Za-z0-9_.+\-]+\Z")
_TOOLCHAIN_RE = re.compile(
    r"\A[A-Za-z0-9][A-Za-z0-9._\-]*/[A-Za-z0-9][A-Za-z0-9._\-]*:[A-Za-z0-9][A-Za-z0-9._+\-]*\Z"
)
_MOVING_CHANNELS = frozenset({"stable", "beta", "nightly", "latest"})
_REPOSITORY_RE = re.compile(r"\Ahttps://[A-Za-z0-9.\-]+/[A-Za-z0-9._\-/]+\Z")
_SHARED_OBJECT_RE = re.compile(r"\.so(?:\.[A-Za-z0-9_.+\-]+)?\Z")
_LIBLEANSHARED_RE = re.compile(r"\Alibleanshared.*\.so(?:\.[A-Za-z0-9_.+\-]+)?\Z")
_SHADOW_LEAN_LIB_RE = re.compile(r"\A(libleanshared|libInit_shared|libLake_shared).*\.so(?:\.[A-Za-z0-9_.+\-]+)?\Z")
#: Official Lean runtime shared library basenames in `lib/lean/`.
KNOWN_LEAN_SHARED_LIBS = frozenset(
    {"libleanshared.so", "libleanshared_1.so", "libleanshared_2.so", "libInit_shared.so", "libLake_shared.so"}
)
#: glibc / loader sonames that `bin/lean`, `bin/lake` and `lib/lean/*.so` list in
#: DT_NEEDED. ld.so searches DT_RUNPATH (`$ORIGIN/../lib`, `$ORIGIN/../lib/lean`,
#: `$ORIGIN/..`, `$ORIGIN`) *before* the system default directories, so any of
#: these planted in a toolchain RUNPATH directory is loaded into every Lean
#: process. (`lib/glibc/` holds link-time stubs and is not on any RUNPATH.)
_SYSTEM_SONAME_RE = re.compile(
    r"\A(libc\.so\.6|libm\.so\.6|libpthread\.so\.0|libdl\.so\.2|librt\.so\.1|ld-linux[\w.\-]*\.so(?:\.[A-Za-z0-9_.+\-]+)?)(?:\.[A-Za-z0-9_.+\-]+)?\Z"
)
#: glibc `is_dst`: `$ORIGIN` / `${ORIGIN}` is a dynamic string token only when
#: not followed by an identifier character; `$ORIGINX/lib` stays a literal,
#: i.e. a relative (current-working-directory-based) search directory.
_ORIGIN_DST_RE = re.compile(r"\$(?:\{ORIGIN\}|ORIGIN(?![A-Za-z0-9_]))")

#: Planted build-artifact detection inside `lean-miri/vendor/`.
_ARTIFACT_SUFFIXES = (
    ".olean",
    ".ilean",
    ".ir",
    ".c",
    ".ltar",
    ".hash",
    ".trace",
    ".o",
    ".a",
    ".so",
    ".dylib",
    ".dll",
    ".exe",
    ".pyc",
    ".pyo",
)
_ARTIFACT_INFIXES = (".olean.", ".ilean.", ".so.")
_ARTIFACT_DIRS = frozenset({".lake", "lake-packages", "__pycache__", ".git"})

#: Toolchain files that must always be present and pinned. (Every other
#: `bin/*` entry and `lib/lean/*.so*` is hashed and, under the locked release
#: pin or an explicit `--toolchain-pin-json`, must be pinned too; synthetic test
#: toolchains therefore only need these three.)
TOOLCHAIN_REQUIRED_FILES = ("bin/lean", "bin/lake", "lib/lean/libleanshared.so")

#: `bin/*` executables whose `DT_NEEDED` x `DT_RUNPATH`/`DT_RPATH` resolution is
#: checked (with every `lib/lean/*.so*`): `lean` and `lake`, plus the Lean-built
#: companions `leanc` (run by `trusted/audit/check_trusted.py --fast`),
#: `leanchecker` and `leanir`, which load only the `lib/lean/` Lean runtime and
#: glibc. `clang`, `ld.lld`, `llvm-ar` and `cadical` are digest-pinned only: their
#: closure is the release's own top-level `lib/` (see "Known limits").
RUNPATH_CHECKED_BINARIES = ("bin/lean", "bin/lake", "bin/leanc", "bin/leanchecker", "bin/leanir")

# Compiled-in release digests of the official elan toolchain pinned by the
# repository's `lean-toolchain` (cl/1021969520). Like LOCKED_UPSTREAM_IDENTITY,
# this makes the *default* run (no --toolchain-pin-json) fail closed on any
# added, deleted or modified `bin/*` or `lib/lean/*.so` -- in particular a
# substituted companion `libleanshared_{1,2}.so` while `libleanshared.so` is
# untouched, or a trojaned companion executable such as `bin/leanc`. Without it
# the default run would only compute (trust-on-first-use) digests. All 16
# digests were checked against the `lean-4.34.1-linux.zip` asset of the GitHub
# `leanprover/lean4` v4.34.1 release (the bytes elan installs from
# `lean-4.34.1-linux.tar.zst`, `sha256:47bf4bbd...`, also pinned by
# `flake.nix`). An explicit --toolchain-pin-json takes precedence; test-only
# --toolchain-dir overrides are never matched against it.
# `trusted/audit/check_trusted.py` embeds the same `files` table.
LOCKED_TOOLCHAIN_PINS: Mapping[str, Mapping[str, Any]] = {
    "leanprover/lean4:v4.34.1": {
        "platform": "x86_64-unknown-linux-gnu",
        "files": {
            "bin/cadical": "8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce",
            "bin/clang": "9fcd5fc4baeea9c449bcc9ca4b9db7714465107669498b0056a853f22f5f4def",
            "bin/lake": "6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d",
            "bin/ld.lld": "d32d5121d96810b624306e48faacc75e41f7302ad0e4865be63c3bbf8f4cd810",
            "bin/lean": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
            "bin/leanc": "68a45f8329e2d79133cdcc7b1fa494e37844282d7b5f8908ce1deda7cfdf161a",
            "bin/leanchecker": "ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe",
            "bin/leanir": "ccfab978605f2b346cc8b82374917468aa6bc02498337b0013737dec2cb194e9",
            "bin/leanmake": "07c96082b95fce057ed9656cc80da50477d596250973cfdd414f74e7631eb56d",
            "bin/leantar": "06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3",
            "bin/llvm-ar": "697c4da3ff7080716bf591ddf38d02fb093f3173e12188ddd4243304228004ad",
            "lib/lean/libInit_shared.so": "07f8c1156271ab6ec36c14c3031b5572329325d5f73dde3e89a1615d88f4e5cb",
            "lib/lean/libLake_shared.so": "ef0eb8942cd68ffb61ae573850a7181f70860580959e296c6e1a0e31ec50a38a",
            "lib/lean/libleanshared.so": "6b30cc963d065fc9d2f87f7e9cbe0682b23000ae5425bccd769c5d477fa74f13",
            "lib/lean/libleanshared_1.so": "69e900c025f40bf05c14f5b9ec48071b3130e34c96a7c45ee2eb5b6f307e19e6",
            "lib/lean/libleanshared_2.so": "38d0a03750b2e8d51161885ad597a8b4f6d3b85215c5a52aecd2b3753273cf3f",
        },
        "versions": {
            "bin/lean": "Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)",
            "bin/lake": "Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)",
        },
    },
}
TOOLCHAIN_PIN_KEYS = ("toolchain", "files")
TOOLCHAIN_PIN_OPTIONAL_KEYS = ("versions",)


def host_platform_triple() -> Optional[str]:
    """`<machine>-unknown-linux-gnu` on Linux hosts (the elan release triple), else `None`."""
    if sys.platform.startswith("linux"):
        return f"{platform.machine()}-unknown-linux-gnu"
    return None


# ---------------------------------------------------------------------------
# Result types and errors
# ---------------------------------------------------------------------------


class PinVerificationError(Exception):
    """Raised when verification fails. `errors` lists every detected problem."""

    def __init__(self, errors: Sequence[str], warnings: Sequence[str] = ()) -> None:
        self.errors: Tuple[str, ...] = tuple(errors) or ("[internal] verification failed",)
        self.warnings: Tuple[str, ...] = tuple(warnings)
        super().__init__("\n".join(self.errors))


class PatchedFile(NamedTuple):
    path: str
    upstream_sha256: str
    patched_sha256: str
    patch_reason: str
    upstream_git_blob: str


class ClosureVerification(NamedTuple):
    #: "absent" (no `execution_machine_closure`), "skipped" (present but no
    #: olean dir supplied) or "verified".
    status: str
    entries: int
    olean_dir: Optional[str] = None


class VendorVerification(NamedTuple):
    repo_root: str
    #: "strict", "deinit-patch" or "locked-deinit-patch" (`--require-locked-deinit-patch`).
    mode: str
    pin_path: str
    pin_sha256: str
    schema_version: int
    repository: str
    commit: str
    upstream_lean_toolchain: str
    build_lean_toolchain: str
    verified_vendor_files: int
    verified_aux_files: int
    manifest_sha256: str
    git_objects: Mapping[str, str]  # path -> "blob" | "tree"
    patched_files: Tuple[PatchedFile, ...]
    closure: ClosureVerification
    locked_identity: str  # "matched" | "disabled"
    #: "matched" when `patched_files` is exactly `LOCKED_DEINIT_PATCHED_FILES`
    #: (verified digest by digest), "absent" when nothing is patched, "subset"
    #: for an accepted proper subset of the allowlist and "unlocked" for a full
    #: overlay accepted with the lock explicitly disabled (API only).
    deinit_patch_lock: str = "absent"
    warnings: Tuple[str, ...] = ()


class ToolchainVerification(NamedTuple):
    name: str
    toolchain_dir: str
    lean_version: str
    lake_version: str
    files: Mapping[str, str]  # relpath -> sha256
    libleanshared: Tuple[str, ...]
    pin_json: Optional[str]
    pin_status: str  # "verified" | "locked-verified" | "not-requested"
    resolved_by: str = "elan"  # "elan" | "override" (test-only --toolchain-dir)
    warnings: Tuple[str, ...] = ()

    def to_pin(self) -> Dict[str, Any]:
        """The `--dump-toolchain-pin` document for this toolchain."""
        return {
            "toolchain": self.name,
            "versions": {"bin/lean": self.lean_version, "bin/lake": self.lake_version},
            "files": dict(sorted(self.files.items())),
        }


class PinVerificationResult(NamedTuple):
    vendor: VendorVerification
    toolchain: Optional[ToolchainVerification]
    warnings: Tuple[str, ...] = ()

    def to_json_dict(self) -> Dict[str, Any]:
        v = self.vendor
        out: Dict[str, Any] = {
            "ok": True,
            "verifier": "scripts/verify_lean_miri_pin.py",
            "repo_root": v.repo_root,
            "mode": v.mode,
            "pin_path": v.pin_path,
            "pin_sha256": v.pin_sha256,
            "schema_version": v.schema_version,
            "repository": v.repository,
            "commit": v.commit,
            "upstream_lean_toolchain": v.upstream_lean_toolchain,
            "build_lean_toolchain": v.build_lean_toolchain,
            "verified_vendor_files": v.verified_vendor_files,
            "verified_aux_files": v.verified_aux_files,
            "manifest_sha256": v.manifest_sha256,
            "manifest_formula": MANIFEST_FORMULA,
            "verified_git_objects": dict(sorted(v.git_objects.items())),
            "locked_identity": v.locked_identity,
            "patched_files": [p.path for p in v.patched_files],
            "deinit_patch_lock": v.deinit_patch_lock,
            "execution_machine_closure": {
                "status": v.closure.status,
                "entries": v.closure.entries,
                "olean_dir": v.closure.olean_dir,
            },
            "toolchain": None,
            "warnings": list(self.warnings),
        }
        t = self.toolchain
        if t is not None:
            out["toolchain"] = {
                "name": t.name,
                "dir": t.toolchain_dir,
                "lean_version": t.lean_version,
                "lake_version": t.lake_version,
                "sha256": dict(sorted(t.files.items())),
                "libleanshared": list(t.libleanshared),
                "pin_json": t.pin_json,
                "pin_status": t.pin_status,
                "resolved_by": t.resolved_by,
            }
        return out


class _Collector:
    """Accumulates errors and warnings; `fatal` aborts with everything so far."""

    def __init__(self) -> None:
        self.errors: List[str] = []
        self.warnings: List[str] = []

    def err(self, category: str, message: str) -> None:
        line = f"[{category}] {message}"
        if line not in self.errors:
            self.errors.append(line)

    def warn(self, category: str, message: str) -> None:
        line = f"[{category}] {message}"
        if line not in self.warnings:
            self.warnings.append(line)

    def fatal(self, category: str, message: str) -> NoReturn:
        self.err(category, message)
        raise PinVerificationError(self.errors, self.warnings)

    def raise_if_errors(self) -> None:
        if self.errors:
            raise PinVerificationError(self.errors, self.warnings)


# ---------------------------------------------------------------------------
# Hashing helpers (public: reused by the tests)
# ---------------------------------------------------------------------------


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data: bytes) -> str:
    """Git blob object id: `sha1(b"blob <size>\\0" + content)`."""
    h = hashlib.sha1(b"blob %d\0" % len(data))
    h.update(data)
    return h.hexdigest()


def git_mode(st_mode: int) -> str:
    """Git tree-entry mode of a regular file (git only records the exec bit)."""
    return "100755" if st_mode & stat.S_IXUSR else "100644"


def git_tree_sha1(entries: Mapping[str, Tuple[str, str]]) -> str:
    """Recursive git tree id of `entries` (relpath -> (mode, 40-hex blob id)).

    Tree entries are `<mode> <name>\\0<20 raw bytes>`; subtrees use mode
    `40000`; entries are sorted by name bytes with directory names compared as
    `name + "/"` (git's `base_name_compare`).
    """
    root: Dict[str, Any] = {}
    for rel, leaf in entries.items():
        parts = rel.split("/")
        node = root
        for comp in parts[:-1]:
            child = node.setdefault(comp, {})
            if not isinstance(child, dict):
                raise ValueError(f"path {rel!r} nests below a file")
            node = child
        if parts[-1] in node:
            raise ValueError(f"duplicate tree entry {rel!r}")
        node[parts[-1]] = leaf
    return _git_tree_node_sha1(root)


def _git_tree_node_sha1(node: Mapping[str, Any]) -> str:
    items: List[Tuple[bytes, bytes]] = []
    for name, child in node.items():
        raw_name = name.encode("utf-8")
        if isinstance(child, dict):
            entry = b"40000 " + raw_name + b"\0" + bytes.fromhex(_git_tree_node_sha1(child))
            items.append((raw_name + b"/", entry))
        else:
            mode, blob_hex = child
            entry = mode.encode("ascii") + b" " + raw_name + b"\0" + bytes.fromhex(blob_hex)
            items.append((raw_name, entry))
    items.sort(key=lambda item: item[0])
    body = b"".join(entry for _, entry in items)
    h = hashlib.sha1(b"tree %d\0" % len(body))
    h.update(body)
    return h.hexdigest()


def compute_manifest_sha256(files: Sequence[Mapping[str, str]]) -> str:
    """Canonical `vendor_tree.manifest_sha256` (see module docstring)."""
    h = hashlib.sha256()
    for entry in files:
        h.update(f"{entry['sha256']}  {entry['path']}\n".encode("utf-8"))
    return h.hexdigest()


def canonical_manifest_key(path: str) -> Tuple[bool, List[str]]:
    """Sort key of the canonical `vendor_tree.files` order."""
    parts = path.split("/")
    return (len(parts) > 1, parts)


def toolchain_dir_name(name: str) -> str:
    """`elan` toolchain directory name (`/` -> `--`, `:` -> `---`)."""
    return name.replace("/", "--").replace(":", "---")


def _hash_open_file(path: Path, *, want_blob: bool, expect: Optional[os.stat_result] = None) -> Tuple[str, Optional[str], os.stat_result]:
    """Stream-hash a regular file opened with `O_NOFOLLOW`.

    Returns `(sha256, git_blob_sha1 | None, fstat)`. Raises `OSError` (e.g.
    `ELOOP` for a symlink) or `ValueError` when the file is not a regular file,
    is not the inode recorded in `expect`, or changes size while hashing.
    """
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    fd = os.open(str(path), flags)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError("not a regular file")
        if expect is not None and (st.st_dev, st.st_ino) != (expect.st_dev, expect.st_ino):
            raise ValueError("file was replaced while scanning")
        sha = hashlib.sha256()
        blob = hashlib.sha1(b"blob %d\0" % st.st_size) if want_blob else None
        total = 0
        while True:
            chunk = os.read(fd, CHUNK_SIZE)
            if not chunk:
                break
            total += len(chunk)
            sha.update(chunk)
            if blob is not None:
                blob.update(chunk)
        if total != st.st_size:
            raise ValueError("file changed size while hashing")
    finally:
        os.close(fd)
    return sha.hexdigest(), (blob.hexdigest() if blob is not None else None), st


def sha256_file(path: Path) -> str:
    """SHA-256 of a regular, non-symlink file, streamed in 1 MiB chunks."""
    return _hash_open_file(Path(path), want_blob=False)[0]


def _read_small_regular_file(path: Path, limit: int = 1 << 24, expect: Optional[os.stat_result] = None) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    fd = os.open(str(path), flags)
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError("not a regular file")
        if expect is not None and (st.st_dev, st.st_ino) != (expect.st_dev, expect.st_ino):
            raise ValueError("file was replaced while reading")
        if st.st_size > limit:
            raise ValueError(f"file larger than {limit} bytes")
        chunks = []
        total = 0
        while True:
            chunk = os.read(fd, CHUNK_SIZE)
            if not chunk:
                break
            total += len(chunk)
            chunks.append(chunk)
        if total != st.st_size:
            raise ValueError("file changed size while reading")
        return b"".join(chunks)
    finally:
        os.close(fd)


# ---------------------------------------------------------------------------
# Small validators
# ---------------------------------------------------------------------------


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_hex40(value: Any) -> bool:
    return isinstance(value, str) and bool(_HEX40_RE.match(value))


def _is_hex64(value: Any) -> bool:
    return isinstance(value, str) and bool(_HEX64_RE.match(value))


def relpath_problem(path: Any) -> Optional[str]:
    """Why `path` is not a clean relative POSIX path (None when it is)."""
    if not isinstance(path, str) or not path:
        return "must be a non-empty string"
    if path.startswith("/"):
        return "is absolute"
    if "\\" in path or "\x00" in path:
        return "contains a backslash or NUL byte"
    for part in path.split("/"):
        if part in ("", ".", ".."):
            return "contains an empty, '.' or '..' component (path traversal)"
        if not _PATH_COMPONENT_RE.match(part):
            return f"component {part!r} has characters outside [A-Za-z0-9_.+-]"
    return None


def toolchain_name_problem(name: Any) -> Optional[str]:
    """Why `name` is not an immutable `owner/repo:version` toolchain name."""
    if not isinstance(name, str) or not _TOOLCHAIN_RE.match(name):
        return "must have the form <owner>/<repo>:<version>"
    if name.split(":", 1)[1] in _MOVING_CHANNELS:
        return "names a moving channel instead of an immutable release"
    return None


def _readlink(path: Any) -> str:
    try:
        return os.readlink(path)
    except OSError:
        return "?"


def _is_artifact_name(name: str) -> bool:
    return name.endswith(_ARTIFACT_SUFFIXES) or any(infix in name for infix in _ARTIFACT_INFIXES)


def _mode_problems(st: os.stat_result) -> List[str]:
    problems = []
    if st.st_mode & stat.S_IWOTH:
        problems.append("world-writable")
    if st.st_mode & (stat.S_ISUID | stat.S_ISGID):
        problems.append("setuid/setgid")
    return problems


def _load_json_strict(data: bytes) -> Any:
    def pairs_hook(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
        obj: Dict[str, Any] = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError(f"duplicate JSON object key {key!r}")
            obj[key] = value
        return obj

    def bad_constant(name: str) -> Any:
        raise ValueError(f"non-finite JSON number {name}")

    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=pairs_hook, parse_constant=bad_constant)
    except RecursionError:
        raise ValueError("JSON nesting too deep") from None


def _check_exact_keys(obj: Mapping[str, Any], required: Sequence[str], optional: Sequence[str], where: str, c: _Collector, category: str = "schema") -> None:
    for key in required:
        if key not in obj:
            c.err(category, f"{where}: missing key {key!r}")
    for key in sorted(set(obj) - set(required) - set(optional)):
        c.err(category, f"{where}: unknown key {key!r}")


def _lstat_real_dir(path: Path, label: str, c: _Collector, category: str) -> Optional[os.stat_result]:
    try:
        st = os.lstat(path)
    except OSError as exc:
        c.err(category, f"{label} is missing or unreadable: {exc.strerror}")
        return None
    if stat.S_ISLNK(st.st_mode):
        c.err(category, f"{label} is a symlink (symlink forbidden)")
        return None
    if not stat.S_ISDIR(st.st_mode):
        c.err(category, f"{label} is not a directory")
        return None
    if st.st_mode & stat.S_IWOTH:
        c.err(category, f"{label} is world-writable")
    return st


def _read_pinned_text_file(path: Path, label: str, c: _Collector, category: str) -> Optional[bytes]:
    """Read a small regular file that must not be a symlink, hardlink, or world-writable."""
    try:
        st = os.lstat(path)
    except OSError as exc:
        c.err(category, f"{label} is missing or unreadable: {exc.strerror}")
        return None
    if stat.S_ISLNK(st.st_mode):
        c.err(category, f"{label} is a symlink (symlink forbidden)")
        return None
    if not stat.S_ISREG(st.st_mode):
        c.err(category, f"{label} is not a regular file")
        return None
    for problem in _mode_problems(st):
        c.err(category, f"{label} is {problem}")
    if st.st_nlink != 1:
        c.err(category, f"{label} is hard-linked (st_nlink={st.st_nlink}, writable through another path)")
    try:
        return _read_small_regular_file(path, expect=st)
    except (OSError, ValueError) as exc:
        c.err(category, f"cannot read {label}: {exc}")
        return None


# ---------------------------------------------------------------------------
# UPSTREAM_PIN.json schema
# ---------------------------------------------------------------------------


class _ParsedPin(NamedTuple):
    raw: Dict[str, Any]
    lean_entries: List[Tuple[str, str]]
    aux_entries: List[Tuple[str, str]]
    patched: Dict[str, PatchedFile]
    git_objects: Dict[str, str]
    closure: Optional[List[Tuple[str, str]]]
    deinit_patch_lock: str


def _validate_file_list(value: Any, where: str, *, lean: bool, c: _Collector) -> Optional[List[Tuple[str, str]]]:
    if not isinstance(value, list):
        c.err("schema", f"{where} must be a list")
        return None
    entries: List[Tuple[str, str]] = []
    seen: Set[str] = set()
    seen_folded: Dict[str, str] = {}
    ok = True
    for index, entry in enumerate(value):
        label = f"{where}[{index}]"
        if not isinstance(entry, dict):
            c.err("schema", f"{label} must be an object")
            ok = False
            continue
        _check_exact_keys(entry, FILE_ENTRY_KEYS, (), label, c)
        path, digest = entry.get("path"), entry.get("sha256")
        problem = relpath_problem(path)
        if problem is not None:
            c.err("schema", f"{label}: path {path!r} {problem}")
            ok = False
            continue
        if lean and not path.endswith(".lean"):
            c.err("schema", f"{label}: vendor_tree path {path!r} is not a .lean file")
            ok = False
        if not lean and path.endswith(".lean"):
            c.err("schema", f"{label}: vendor_aux_files path {path!r} is a .lean file (belongs in vendor_tree)")
            ok = False
        if not _is_hex64(digest):
            c.err("schema", f"{label}: sha256 for {path!r} is not 64 lowercase hex digits")
            ok = False
        if path in seen:
            c.err("schema", f"{label}: duplicate path {path!r}")
            ok = False
            continue
        folded = path.casefold()
        if folded in seen_folded:
            c.err("schema", f"{label}: path {path!r} collides case-insensitively with {seen_folded[folded]!r}")
            ok = False
        seen.add(path)
        seen_folded[folded] = path
        entries.append((path, digest if isinstance(digest, str) else ""))
    return entries if ok else None


def _validate_pin_schema(pin: Any, allow_deinit_patch: bool, require_locked: Optional[bool], c: _Collector) -> _ParsedPin:
    if not isinstance(pin, dict):
        c.fatal("schema", "UPSTREAM_PIN.json top level must be a JSON object")
    _check_exact_keys(pin, REQUIRED_TOP_LEVEL_KEYS, OPTIONAL_TOP_LEVEL_KEYS, "UPSTREAM_PIN.json", c)

    sv = pin.get("schema_version")
    if not _is_int(sv) or sv != SCHEMA_VERSION:
        c.err("schema", f"schema_version must be the integer {SCHEMA_VERSION}, got {sv!r}")
    repo = pin.get("repository")
    if not isinstance(repo, str) or not _REPOSITORY_RE.match(repo):
        c.err("schema", f"repository must be an https:// URL, got {repo!r}")
    if not _is_hex40(pin.get("commit")):
        c.err("schema", f"commit must be 40 lowercase hex digits, got {pin.get('commit')!r}")
    for key in ("upstream_lean_toolchain", "build_lean_toolchain"):
        problem = toolchain_name_problem(pin.get(key))
        if problem is not None:
            c.err("schema", f"{key} {pin.get(key)!r} {problem}")

    pins = pin.get("upstream_pins")
    if not isinstance(pins, dict):
        c.err("schema", "upstream_pins must be an object")
    else:
        _check_exact_keys(pins, UPSTREAM_PINS_KEYS, (), "upstream_pins", c)
        for key in UPSTREAM_PINS_COMMIT_KEYS:
            if key in pins and not _is_hex40(pins[key]):
                c.err("schema", f"upstream_pins.{key} must be 40 lowercase hex digits, got {pins[key]!r}")
        if "source_lock_sha256" in pins and not _is_hex64(pins["source_lock_sha256"]):
            c.err("schema", "upstream_pins.source_lock_sha256 must be 64 lowercase hex digits")

    notes = pin.get("notes")
    if not isinstance(notes, list) or not all(isinstance(n, str) for n in notes):
        c.err("schema", "notes must be a list of strings")

    git_objects: Dict[str, str] = {}
    objs = pin.get("upstream_git_objects")
    if not isinstance(objs, dict) or not objs:
        c.err("schema", "upstream_git_objects must be a non-empty object")
    else:
        for key, value in objs.items():
            problem = relpath_problem(key)
            if problem is not None:
                c.err("schema", f"upstream_git_objects key {key!r} {problem}")
            elif not _is_hex40(value):
                c.err("schema", f"upstream_git_objects[{key!r}] must be 40 lowercase hex digits")
            else:
                git_objects[key] = value

    lean_entries: Optional[List[Tuple[str, str]]] = None
    tree = pin.get("vendor_tree")
    if not isinstance(tree, dict):
        c.err("schema", "vendor_tree must be an object")
    else:
        _check_exact_keys(tree, VENDOR_TREE_KEYS, (), "vendor_tree", c)
        if not _is_hex64(tree.get("manifest_sha256")):
            c.err("schema", "vendor_tree.manifest_sha256 must be 64 lowercase hex digits")
        lean_entries = _validate_file_list(tree.get("files"), "vendor_tree.files", lean=True, c=c)
        count = tree.get("file_count")
        if not _is_int(count):
            c.err("schema", f"vendor_tree.file_count must be an integer, got {count!r}")
        elif isinstance(tree.get("files"), list) and count != len(tree["files"]):
            c.err("schema", f"vendor_tree.file_count {count} != {len(tree['files'])} listed files")
        if lean_entries is not None and not lean_entries:
            c.err("schema", "vendor_tree.files must not be empty")
    aux_entries = _validate_file_list(pin.get("vendor_aux_files"), "vendor_aux_files", lean=False, c=c)
    if lean_entries is not None and aux_entries is not None:
        lean_folded = {p.casefold() for p, _ in lean_entries}
        for path, _ in aux_entries:
            if path.casefold() in lean_folded:
                c.err("schema", f"path {path!r} is listed in both vendor_tree and vendor_aux_files")
        listed = {p for p, _ in lean_entries + aux_entries}
        for path in sorted(listed):
            parts = path.split("/")
            for i in range(1, len(parts)):
                parent = "/".join(parts[:i])
                if parent in listed:
                    c.err("schema", f"listed file {parent!r} is also the parent directory of listed file {path!r}")

    patched, lock = _validate_patched_files(pin, allow_deinit_patch, require_locked, c)
    closure = _validate_closure_schema(pin, lean_entries, c)

    if lean_entries is None or aux_entries is None:
        c.fatal("schema", "cannot build the expected vendor file set from UPSTREAM_PIN.json")
    return _ParsedPin(pin, lean_entries, aux_entries, patched, git_objects, closure, lock)


def _validate_patched_files(
    pin: Mapping[str, Any], allow_deinit_patch: bool, require_locked: Optional[bool], c: _Collector
) -> Tuple[Dict[str, PatchedFile], str]:
    """Validate `patched_files`; returns `(entries, deinit_patch_lock)`.

    `require_locked`: `True` requires exactly `LOCKED_DEINIT_PATCHED_FILES`;
    `None` (default) applies the same digest check whenever the whole 10-file
    allowlist is declared; `False` never locks (synthetic full overlays)."""
    patched: Dict[str, PatchedFile] = {}
    if "patched_files" not in pin:
        if require_locked:
            c.err("patch", "locked deinit patch required but UPSTREAM_PIN.json has no patched_files")
        return patched, "absent"
    value = pin["patched_files"]
    if not isinstance(value, list):
        c.err("schema", "patched_files must be a list")
        return patched, "absent"
    if value and not allow_deinit_patch:
        c.err(
            "patch",
            f"strict mode: UPSTREAM_PIN.json declares {len(value)} patched_files entr"
            f"{'y' if len(value) == 1 else 'ies'}; vendored sources must be byte-identical to "
            "upstream unless --allow-deinit-patch is given",
        )
    for index, entry in enumerate(value):
        label = f"patched_files[{index}]"
        if not isinstance(entry, dict):
            c.err("patch", f"{label} must be an object")
            continue
        _check_exact_keys(entry, PATCHED_FILE_KEYS, PATCHED_FILE_OPTIONAL_KEYS, label, c, category="patch")
        path = entry.get("path")
        problem = relpath_problem(path)
        if problem is not None:
            c.err("patch", f"{label}: path {path!r} {problem}")
            continue
        if path not in PATCH_ALLOWLIST:
            c.err("patch", f"{label}: {path!r} is not in the closed {len(PATCH_ALLOWLIST)}-file deinit patch allowlist")
        up, new = entry.get("upstream_sha256"), entry.get("patched_sha256")
        reason, blob = entry.get("patch_reason"), entry.get("upstream_git_blob")
        valid = path in PATCH_ALLOWLIST
        if not _is_hex64(up):
            c.err("patch", f"{label}: upstream_sha256 for {path!r} is not 64 lowercase hex digits")
            valid = False
        if not _is_hex64(new):
            c.err("patch", f"{label}: patched_sha256 for {path!r} is not 64 lowercase hex digits")
            valid = False
        if _is_hex64(up) and up == new:
            c.err("patch", f"{label}: no-op patch for {path!r} (patched_sha256 == upstream_sha256)")
            valid = False
        if not isinstance(reason, str) or not reason.strip():
            c.err("patch", f"{label}: patch_reason for {path!r} must be a non-empty string")
            valid = False
        if "upstream_git_blob" in entry:
            if not _is_hex40(blob):
                c.err("patch", f"{label}: upstream_git_blob for {path!r} is not 40 lowercase hex digits")
                valid = False
            elif path in LOCKED_DEINIT_BLOBS and blob != LOCKED_DEINIT_BLOBS[path]:
                c.err("patch", f"{label}: upstream_git_blob {blob} for {path!r} != locked pre-image blob {LOCKED_DEINIT_BLOBS[path]}")
        else:
            blob = LOCKED_DEINIT_BLOBS.get(path, "")
            if not _is_hex40(blob):
                c.err("patch", f"{label}: upstream_git_blob for {path!r} is not 40 lowercase hex digits")
                valid = False
        if path in patched:
            c.err("patch", f"{label}: duplicate patched_files entry for {path!r}")
            continue
        if valid:
            patched[path] = PatchedFile(path, up, new, reason, blob)
    return patched, _check_locked_deinit_patch(value, patched, allow_deinit_patch, require_locked, c)


def _check_locked_deinit_patch(
    entries: Sequence[Any],
    patched: Mapping[str, PatchedFile],
    allow_deinit_patch: bool,
    require_locked: Optional[bool],
    c: _Collector,
) -> str:
    """Compare the declared overlay with `LOCKED_DEINIT_PATCHED_FILES`."""
    declared = {e.get("path") for e in entries if isinstance(e, dict) and isinstance(e.get("path"), str)}
    if not declared and not require_locked:
        return "absent"
    full = declared >= PATCH_ALLOWLIST
    if require_locked is False or not allow_deinit_patch or (require_locked is None and not full):
        if not allow_deinit_patch:
            return "absent" if not declared else "unlocked"
        return "subset" if not full else "unlocked"
    why = "--require-locked-deinit-patch" if require_locked else "the complete 10-file overlay"
    for path in sorted(PATCH_ALLOWLIST - declared):
        c.err("patch", f"locked deinit patch ({why}): missing patched_files entry for {path!r}")
    ok = not (PATCH_ALLOWLIST - declared)
    for path in sorted(PATCH_ALLOWLIST & declared):
        locked = LOCKED_DEINIT_PATCHED_FILES[path]
        pf = patched.get(path)
        if pf is None:
            ok = False  # already reported as invalid
            continue
        for key, actual in (("upstream_sha256", pf.upstream_sha256), ("patched_sha256", pf.patched_sha256), ("upstream_git_blob", pf.upstream_git_blob)):
            if actual != locked[key]:
                ok = False
                c.err("patch", f"locked deinit patch ({why}): {key} {actual} for {path!r} != reviewed Episode 1 {key} {locked[key]}")
    return "matched" if ok else "unlocked"


def _validate_closure_schema(pin: Mapping[str, Any], lean_entries: Optional[List[Tuple[str, str]]], c: _Collector) -> Optional[List[Tuple[str, str]]]:
    if "execution_machine_closure" not in pin:
        return None
    value = pin["execution_machine_closure"]
    if not isinstance(value, list) or not value:
        c.err("closure", "execution_machine_closure must be a non-empty list")
        return []
    lean_paths = {p for p, _ in lean_entries or []}
    out: List[Tuple[str, str]] = []
    seen: Set[str] = set()
    for index, entry in enumerate(value):
        label = f"execution_machine_closure[{index}]"
        if not isinstance(entry, dict):
            c.err("closure", f"{label} must be an object")
            continue
        _check_exact_keys(entry, CLOSURE_REQUIRED_KEYS, CLOSURE_OPTIONAL_KEYS, label, c, category="closure")
        path, digest = entry.get("path"), entry.get("sha256")
        problem = relpath_problem(path)
        if problem is not None or not path.endswith(".olean"):
            c.err("closure", f"{label}: path {path!r} must be a clean relative .olean path")
            continue
        source = path[: -len(".olean")] + ".lean"
        if lean_entries is not None and source not in lean_paths:
            c.err("closure", f"{label}: {path!r} has no vendored source {source!r}")
        if "module" in entry and entry["module"] != path[: -len(".olean")].replace("/", "."):
            c.err("closure", f"{label}: module {entry['module']!r} does not match path {path!r}")
        if not _is_hex64(digest):
            c.err("closure", f"{label}: sha256 for {path!r} is not 64 lowercase hex digits")
            continue
        if path in seen:
            c.err("closure", f"{label}: duplicate closure entry {path!r}")
            continue
        seen.add(path)
        out.append((path, digest))
    if CLOSURE_ROOT_OLEAN not in seen:
        c.err("closure", f"execution_machine_closure must include {CLOSURE_ROOT_OLEAN!r}")
    return out


# ---------------------------------------------------------------------------
# Vendor filesystem scan
# ---------------------------------------------------------------------------


def _scan_vendor(vendor_root: Path, c: _Collector) -> Tuple[Dict[str, os.stat_result], Set[str]]:
    """Walk without following symlinks. Returns (regular files, directories)."""
    files: Dict[str, os.stat_result] = {}
    dirs: Set[str] = set()

    def onerror(exc: OSError) -> None:
        c.err("vendor", f"cannot scan {exc.filename}: {exc.strerror}")

    for dirpath, dirnames, filenames in os.walk(str(vendor_root), topdown=True, onerror=onerror, followlinks=False):
        rel_dir = os.path.relpath(dirpath, str(vendor_root))
        prefix = "" if rel_dir == "." else rel_dir.replace(os.sep, "/") + "/"
        kept = []
        for name in sorted(dirnames):
            rel = prefix + name
            try:
                st = os.lstat(os.path.join(dirpath, name))
            except OSError as exc:
                c.err("vendor", f"cannot lstat directory {rel}: {exc.strerror}")
                continue
            if stat.S_ISLNK(st.st_mode):
                c.err("vendor", f"symlink forbidden (directory symlink): {rel} -> {_readlink(os.path.join(dirpath, name))}")
                continue
            if not stat.S_ISDIR(st.st_mode):
                c.err("vendor", f"non-regular entry: {rel}")
                continue
            if name in _ARTIFACT_DIRS:
                c.err("vendor", f"planted build artifact directory: {rel}/")
                continue
            if st.st_mode & stat.S_IWOTH:
                c.err("vendor", f"world-writable directory: {rel}/")
            dirs.add(rel)
            kept.append(name)
        dirnames[:] = kept
        for name in sorted(filenames):
            rel = prefix + name
            full = os.path.join(dirpath, name)
            try:
                st = os.lstat(full)
            except OSError as exc:
                c.err("vendor", f"cannot lstat {rel}: {exc.strerror}")
                continue
            if stat.S_ISLNK(st.st_mode):
                c.err("vendor", f"symlink forbidden (file symlink): {rel} -> {_readlink(full)}")
                continue
            if not stat.S_ISREG(st.st_mode):
                c.err("vendor", f"non-regular file (device, FIFO or socket): {rel}")
                continue
            if _is_artifact_name(name):
                c.err("vendor", f"planted build artifact: {rel}")
                continue
            for problem in _mode_problems(st):
                c.err("vendor", f"{problem} file: {rel}")
            if st.st_nlink != 1:
                c.err("vendor", f"hard-linked file (st_nlink={st.st_nlink}, writable through another path): {rel}")
            files[rel] = st
    return files, dirs


# ---------------------------------------------------------------------------
# Vendor verification
# ---------------------------------------------------------------------------


def _verify_vendor_impl(
    repo_root: Path,
    allow_deinit_patch: bool,
    require_locked: Optional[bool],
    olean_dir: Optional[Path],
    locked_identity: Optional[Mapping[str, Any]],
    expected_pin_sha256: Optional[str],
    c: _Collector,
) -> VendorVerification:
    mode = vendor_mode(allow_deinit_patch, require_locked)
    pin_path = repo_root / PIN_RELPATH
    vendor_root = repo_root / VENDOR_RELPATH

    _lstat_real_dir(repo_root / "lean-miri", "lean-miri/", c, "vendor")
    if _lstat_real_dir(vendor_root, "lean-miri/vendor/", c, "vendor") is None:
        c.fatal("vendor", "cannot verify a missing or non-directory lean-miri/vendor/")
    pin_bytes = _read_pinned_text_file(pin_path, PIN_RELPATH, c, "schema")
    if pin_bytes is None:
        c.fatal("schema", f"cannot read {PIN_RELPATH}")
    pin_sha = sha256_bytes(pin_bytes)
    if expected_pin_sha256 is not None and pin_sha != expected_pin_sha256:
        c.err("identity", f"{PIN_RELPATH} SHA-256 {pin_sha} != expected {expected_pin_sha256}")
    try:
        raw = _load_json_strict(pin_bytes)
    except (UnicodeDecodeError, ValueError) as exc:
        c.fatal("schema", f"malformed {PIN_RELPATH}: {exc}")
    parsed = _validate_pin_schema(raw, allow_deinit_patch, require_locked, c)

    # Canonical order + manifest recomputation.
    listed = [{"path": p, "sha256": s} for p, s in parsed.lean_entries]
    paths = [p for p, _ in parsed.lean_entries]
    if paths != sorted(paths, key=canonical_manifest_key):
        c.err("manifest", "vendor_tree.files is not in canonical order (root-level files first, then path-component order)")
    manifest = compute_manifest_sha256(listed)
    pinned_manifest = raw.get("vendor_tree", {}).get("manifest_sha256")
    if manifest != pinned_manifest:
        c.err("manifest", f"vendor_tree.manifest_sha256 mismatch: pinned {pinned_manifest}, recomputed {manifest}")

    # Patched entries must describe upstream bytes in the manifest.
    expected_lean = dict(parsed.lean_entries)
    for path, pf in sorted(parsed.patched.items()):
        if path not in expected_lean:
            c.err("patch", f"patched file {path!r} is not listed in vendor_tree.files")
        elif expected_lean[path] != pf.upstream_sha256:
            c.err(
                "patch",
                f"{path}: vendor_tree entry sha256 {expected_lean[path]} must equal upstream_sha256 "
                f"{pf.upstream_sha256} (the manifest pins upstream bytes; the overlay lives in patched_files)",
            )

    # Filesystem bijection + digests.
    on_disk, on_disk_dirs = _scan_vendor(vendor_root, c)
    expected: Dict[str, str] = dict(parsed.lean_entries)
    expected.update(parsed.aux_entries)
    lean_set = set(expected_lean)
    for rel in sorted(set(on_disk) - set(expected)):
        kind = "unlisted .lean file" if rel.endswith(".lean") else "unlisted auxiliary file"
        c.err("vendor", f"{kind} (not in UPSTREAM_PIN.json): {rel}")
    needed_dirs: Set[str] = set()
    for rel in expected:
        parts = rel.split("/")
        for i in range(1, len(parts)):
            needed_dirs.add("/".join(parts[:i]))
    for rel in sorted(on_disk_dirs - needed_dirs):
        c.err("vendor", f"extraneous directory (contains no pinned file): {rel}/")

    git_inputs: Dict[str, Tuple[str, str]] = {}
    verified_lean = verified_aux = 0
    for rel, pinned_sha in expected.items():
        st = on_disk.get(rel)
        if st is None:
            c.err("vendor", f"missing pinned file: {rel}")
            continue
        try:
            actual_sha, blob, _ = _hash_open_file(vendor_root / rel, want_blob=True, expect=st)
        except (OSError, ValueError) as exc:
            c.err("vendor", f"cannot hash {rel}: {exc}")
            continue
        assert blob is not None
        pf = parsed.patched.get(rel) if allow_deinit_patch else None
        if pf is not None:
            if actual_sha == pf.patched_sha256:
                ok = True
                blob = pf.upstream_git_blob  # tree ids describe upstream bytes
            elif actual_sha == pf.upstream_sha256:
                ok = False
                c.err("patch", f"{rel}: declared as patched but holds the unpatched upstream bytes")
            else:
                ok = False
                c.err("patch", f"{rel}: on-disk SHA-256 {actual_sha} != patched_sha256 {pf.patched_sha256}")
        else:
            ok = actual_sha == pinned_sha
            if not ok:
                c.err("vendor", f"SHA-256 mismatch for {rel}: pinned {pinned_sha}, on disk {actual_sha}")
        git_inputs[rel] = (git_mode(st.st_mode), blob)
        if ok:
            if rel in lean_set:
                verified_lean += 1
            else:
                verified_aux += 1

    # Git object cross-check + coverage.
    git_kinds: Dict[str, str] = {}
    for key, pinned in sorted(parsed.git_objects.items()):
        if key in expected:
            if key not in git_inputs:
                c.err("git", f"cannot recompute git blob for {key}: file missing or unreadable")
                continue
            actual = git_inputs[key][1]
            if actual != pinned:
                c.err("git", f"git blob SHA-1 mismatch for {key}: upstream_git_objects {pinned}, recomputed {actual}")
            else:
                git_kinds[key] = "blob"
            continue
        prefix = key + "/"
        members = [rel for rel in expected if rel.startswith(prefix)]
        if not members:
            c.err("git", f"upstream_git_objects entry {key!r} matches no vendored file or directory")
            continue
        if any(rel not in git_inputs for rel in members):
            c.err("git", f"cannot recompute git tree for {key}: some files are missing or unreadable")
            continue
        try:
            actual = git_tree_sha1({rel[len(prefix):]: git_inputs[rel] for rel in members})
        except ValueError as exc:
            c.err("git", f"cannot recompute git tree for {key}: {exc}")
            continue
        if actual != pinned:
            c.err("git", f"git tree SHA-1 mismatch for {key}/: upstream_git_objects {pinned}, recomputed {actual}")
        else:
            git_kinds[key] = "tree"
    for rel in sorted(expected):
        parts = rel.split("/")
        covered = rel in parsed.git_objects or any("/".join(parts[:i]) in parsed.git_objects for i in range(1, len(parts)))
        if not covered:
            c.err("git", f"vendored file {rel} is not covered by any upstream_git_objects entry")

    _check_pin_markers(parsed, vendor_root, on_disk, c)
    if locked_identity is not None:
        _check_locked_identity(raw, locked_identity, c)
    closure = _verify_closure(parsed.closure, olean_dir, c)

    c.raise_if_errors()
    return VendorVerification(
        repo_root=str(repo_root),
        mode=mode,
        pin_path=PIN_RELPATH,
        pin_sha256=pin_sha,
        schema_version=raw["schema_version"],
        repository=raw["repository"],
        commit=raw["commit"],
        upstream_lean_toolchain=raw["upstream_lean_toolchain"],
        build_lean_toolchain=raw["build_lean_toolchain"],
        verified_vendor_files=verified_lean,
        verified_aux_files=verified_aux,
        manifest_sha256=manifest,
        git_objects=git_kinds,
        patched_files=tuple(parsed.patched[p] for p in sorted(parsed.patched)),
        closure=closure,
        locked_identity="matched" if locked_identity is not None else "disabled",
        deinit_patch_lock=parsed.deinit_patch_lock,
        warnings=tuple(c.warnings),
    )


def _check_pin_markers(parsed: _ParsedPin, vendor_root: Path, on_disk: Mapping[str, os.stat_result], c: _Collector) -> None:
    pins = parsed.raw.get("upstream_pins")
    if not isinstance(pins, dict):
        return
    aux_paths = {p for p, _ in parsed.aux_entries}
    for key, rel in PIN_MARKER_FILES.items():
        if rel not in aux_paths:
            c.err("pins", f"upstream_pins.{key} cannot be cross-checked: {rel} is not a vendored aux file")
            continue
        if rel not in on_disk:
            continue  # reported as missing
        try:
            content = _read_small_regular_file(vendor_root / rel, expect=on_disk[rel])
        except (OSError, ValueError) as exc:
            c.err("pins", f"cannot read {rel}: {exc}")
            continue
        if content != f"{pins.get(key)}\n".encode("utf-8"):
            c.err("pins", f"upstream_pins.{key} {pins.get(key)!r} disagrees with vendored {rel} ({content[:64]!r})")
    if SOURCE_LOCK_FILE not in aux_paths:
        c.err("pins", f"upstream_pins.source_lock_sha256 cannot be cross-checked: {SOURCE_LOCK_FILE} is not a vendored aux file")
    elif SOURCE_LOCK_FILE in on_disk:
        try:
            digest = _hash_open_file(vendor_root / SOURCE_LOCK_FILE, want_blob=False, expect=on_disk[SOURCE_LOCK_FILE])[0]
        except (OSError, ValueError) as exc:
            c.err("pins", f"cannot hash {SOURCE_LOCK_FILE}: {exc}")
        else:
            if digest != pins.get("source_lock_sha256"):
                c.err("pins", f"upstream_pins.source_lock_sha256 {pins.get('source_lock_sha256')} != SHA-256 of {SOURCE_LOCK_FILE} ({digest})")


def _check_locked_identity(raw: Mapping[str, Any], identity: Mapping[str, Any], c: _Collector) -> None:
    for key in ("repository", "commit", "upstream_lean_toolchain", "upstream_pins"):
        if raw.get(key) != identity[key]:
            c.err("identity", f"{key} {raw.get(key)!r} != locked upstream identity {identity[key]!r}")
    # `build_lean_toolchain` is ours, not an upstream fact: it must name a toolchain
    # whose release digests are compiled in (`LOCKED_TOOLCHAIN_PINS`), exactly as
    # `trusted/audit/check_trusted.py` locks it to its `TOOLCHAIN` -- otherwise a pin
    # retargeted (together with `lean-toolchain`) at an unpinned release would only warn.
    build = raw.get("build_lean_toolchain")
    if not isinstance(build, str) or build not in LOCKED_TOOLCHAIN_PINS:
        c.err("identity", f"build_lean_toolchain {build!r} is not a toolchain with compiled-in release digests "
                          f"{sorted(LOCKED_TOOLCHAIN_PINS)}")
    tree = raw.get("vendor_tree") if isinstance(raw.get("vendor_tree"), dict) else {}
    for key in ("file_count", "manifest_sha256"):
        locked = identity[f"vendor_tree.{key}"]
        if tree.get(key) != locked:
            c.err("identity", f"vendor_tree.{key} {tree.get(key)!r} != locked upstream identity {locked!r}")
    objs = raw.get("upstream_git_objects") if isinstance(raw.get("upstream_git_objects"), dict) else {}
    locked_objs = identity["upstream_git_objects"]
    for key in sorted(set(objs) | set(locked_objs)):
        if objs.get(key) != locked_objs.get(key):
            c.err("identity", f"upstream_git_objects[{key!r}] {objs.get(key)!r} != locked upstream identity {locked_objs.get(key)!r}")


def _verify_closure(closure: Optional[List[Tuple[str, str]]], olean_dir: Optional[Path], c: _Collector) -> ClosureVerification:
    if closure is None:
        if olean_dir is not None:
            c.err("closure", "--olean-dir was supplied but UPSTREAM_PIN.json has no execution_machine_closure to verify")
        return ClosureVerification("absent", 0, str(olean_dir) if olean_dir else None)
    if olean_dir is None:
        c.warn("closure", f"execution_machine_closure ({len(closure)} .olean digests) skipped: no --olean-dir supplied")
        return ClosureVerification("skipped", len(closure), None)
    if _lstat_real_dir(olean_dir, f"olean dir {olean_dir}", c, "closure") is None:
        return ClosureVerification("skipped", len(closure), str(olean_dir))
    closure_rels = set()
    for rel, pinned in closure:
        closure_rels.add(rel)
        parts = rel.split("/")
        broken = False
        for i in range(1, len(parts)):
            sub = olean_dir.joinpath(*parts[:i])
            try:
                st = os.lstat(sub)
            except OSError:
                break  # reported by the hash below
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode) or (st.st_mode & 0o022):
                c.err("closure", f"{'/'.join(parts[:i])}/ inside the olean dir is a symlink, not a directory, or world-writable")
                broken = True
                break
        if broken:
            continue
        path = olean_dir / rel
        try:
            st = os.lstat(path)
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode) or (st.st_mode & 0o022) or st.st_nlink != 1:
                c.err("closure", f"invalid file mode for {rel}")
                continue
            actual = _hash_open_file(path, want_blob=False, expect=st)[0]
        except (OSError, ValueError) as exc:
            c.err("closure", f"cannot hash closure artifact {rel}: {exc}")
            continue
        if actual != pinned:
            c.err("closure", f".olean SHA-256 mismatch for {rel}: pinned {pinned}, on disk {actual}")
    for root, dirs, files in os.walk(olean_dir, topdown=True, followlinks=False):
        kept_dirs = []
        for d in sorted(dirs):
            dp = Path(root) / d
            rel_d = dp.relative_to(olean_dir).as_posix()
            try:
                dst = os.lstat(dp)
            except OSError:
                continue
            if stat.S_ISLNK(dst.st_mode) or not stat.S_ISDIR(dst.st_mode) or (dst.st_mode & 0o022):
                c.err("closure", f"{rel_d}/ inside the olean dir is a symlink, not a directory, or world-writable")
                continue
            kept_dirs.append(d)
        dirs[:] = kept_dirs
        for f in sorted(files):
            if f.endswith(".olean"):
                p = Path(root) / f
                rel = p.relative_to(olean_dir).as_posix()
                if rel not in closure_rels:
                    c.err("closure", f"unlisted .olean file found: {rel}")
    return ClosureVerification("verified", len(closure), str(olean_dir))


def vendor_mode(allow_deinit_patch: bool, require_locked_deinit_patch: Optional[bool]) -> str:
    """`"locked-deinit-patch"`, `"deinit-patch"` or `"strict"`."""
    if require_locked_deinit_patch:
        return "locked-deinit-patch"
    return "deinit-patch" if allow_deinit_patch else "strict"


def verify_vendor(
    repo_root: os.PathLike | str,
    *,
    allow_deinit_patch: bool = False,
    require_locked_deinit_patch: Optional[bool] = None,
    olean_dir: Optional[os.PathLike | str] = None,
    locked_identity: Optional[Mapping[str, Any]] = LOCKED_UPSTREAM_IDENTITY,
    expected_pin_sha256: Optional[str] = None,
) -> VendorVerification:
    """Verify `lean-miri/UPSTREAM_PIN.json` + `lean-miri/vendor/` (raises
    `PinVerificationError` listing every problem).

    `require_locked_deinit_patch=True` implies `allow_deinit_patch=True` and
    requires `patched_files` to be exactly `LOCKED_DEINIT_PATCHED_FILES`; the
    default `None` applies that check whenever the whole 10-file allowlist is
    declared; `False` disables it (synthetic full overlays only)."""
    if require_locked_deinit_patch:
        allow_deinit_patch = True
    c = _Collector()
    return _verify_vendor_impl(
        Path(repo_root).resolve(),
        allow_deinit_patch,
        require_locked_deinit_patch,
        Path(olean_dir) if olean_dir is not None else None,
        locked_identity,
        expected_pin_sha256,
        c,
    )


# ---------------------------------------------------------------------------
# Toolchain verification
# ---------------------------------------------------------------------------


def read_lean_toolchain(repo_root: os.PathLike | str) -> str:
    """Read and validate the repository `lean-toolchain` file."""
    c = _Collector()
    name = _read_lean_toolchain(Path(repo_root), c)
    c.raise_if_errors()
    assert name is not None
    return name


def _read_lean_toolchain(repo_root: Path, c: _Collector) -> Optional[str]:
    data = _read_pinned_text_file(repo_root / LEAN_TOOLCHAIN_RELPATH, LEAN_TOOLCHAIN_RELPATH, c, "toolchain")
    if data is None:
        return None
    try:
        text = data.decode("ascii")
    except UnicodeDecodeError:
        c.err("toolchain", f"{LEAN_TOOLCHAIN_RELPATH} is not ASCII")
        return None
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if len(lines) != 1:
        c.err("toolchain", f"{LEAN_TOOLCHAIN_RELPATH} must contain exactly one toolchain name, got {len(lines)} lines")
        return None
    problem = toolchain_name_problem(lines[0])
    if problem is not None:
        c.err("toolchain", f"{LEAN_TOOLCHAIN_RELPATH} {lines[0]!r} {problem}")
        return None
    return lines[0]


def default_elan_home(environ: Optional[Mapping[str, str]] = None) -> Path:
    env = os.environ if environ is None else environ
    if env.get("ELAN_HOME"):
        return Path(env["ELAN_HOME"])
    return Path(env.get("HOME") or os.path.expanduser("~")) / ".elan"


def _check_elan_overrides(repo_root: Path, name: str, elan_home: Path, environ: Mapping[str, str], c: _Collector) -> None:
    env_tc = environ.get("ELAN_TOOLCHAIN")
    if env_tc and env_tc != name:
        c.err("toolchain", f"ELAN_TOOLCHAIN={env_tc!r} overrides the repository lean-toolchain {name!r}")
    settings = elan_home / "settings.toml"
    if not settings.exists():
        return
    try:
        import tomllib  # Python >= 3.11
    except ImportError:  # pragma: no cover - older interpreters
        c.warn("toolchain", f"cannot parse {settings} (tomllib unavailable); elan directory overrides not checked")
        return
    try:
        data = tomllib.loads(_read_small_regular_file(settings).decode("utf-8"))
    except (OSError, ValueError) as exc:
        c.err("toolchain", f"cannot parse elan settings {settings}: {exc}")
        return
    overrides = data.get("overrides") or {}
    if not isinstance(overrides, dict):
        c.err("toolchain", f"{settings}: [overrides] is not a table")
        return
    root = repo_root.resolve()
    for directory, toolchain in overrides.items():
        try:
            override_dir = Path(directory).resolve()
        except OSError:
            continue
        if (override_dir == root or root in override_dir.parents or override_dir in root.parents) and toolchain != name:
            c.err("toolchain", f"elan override {directory!r} -> {toolchain!r} shadows the repository lean-toolchain {name!r}")


def _expected_version(name: str) -> Optional[str]:
    match = re.match(r"\Av(\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.\-+]+)?)\Z", name.split(":", 1)[1])
    return match.group(1) if match else None


def _scrubbed_env() -> Dict[str, str]:
    return {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C"}


def _run_version(binary: Path, label: str, timeout: float, c: _Collector) -> Optional[str]:
    try:
        proc = subprocess.run(
            [str(binary), "--version"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            env=_scrubbed_env(),
            cwd=str(binary.parent),
            check=False,
        )
    except subprocess.TimeoutExpired:
        c.err("toolchain", f"`{label} --version` timed out after {timeout:g}s")
        return None
    except OSError as exc:
        c.err("toolchain", f"cannot execute `{label} --version`: {exc}")
        return None
    out = proc.stdout.decode("utf-8", "replace").strip()
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", "replace").strip()
        c.err("toolchain", f"`{label} --version` exited {proc.returncode}: {err[:200] or out[:200]}")
        return None
    if not out:
        c.err("toolchain", f"`{label} --version` printed nothing")
        return None
    return out.splitlines()[0]


def elf_dynamic_info(path: os.PathLike | str) -> Optional[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
    """Return `(DT_NEEDED sonames, DT_RUNPATH + DT_RPATH entries)` of a 64-bit
    little-endian ELF object, or `None` if `path` has no ELF magic at all (e.g.
    a shell script). Malformed or unsupported ELF objects raise `ValueError`.

    Only the ELF header, program headers, the PT_INTERP/PT_DYNAMIC segments and
    the individual NUL-terminated dynamic strings that are referenced are read:
    the dynamic string table of `libleanshared.so` alone is ~24 MiB (every
    exported symbol name), so it is never slurped."""
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    with os.fdopen(os.open(path, flags), "rb") as fh:
        st = os.fstat(fh.fileno())
        if not stat.S_ISREG(st.st_mode):
            raise ValueError("ELF path is not a regular file")
        file_size = st.st_size
        ehdr = fh.read(64)
        if ehdr[:4] != b"\x7fELF":
            return None
        if len(ehdr) < 64 or ehdr[4] != 2 or ehdr[5] != 1:
            # Fail closed: an ELF object we cannot parse is never silently
            # exempted from the DT_RUNPATH shadowing check.
            raise ValueError("unsupported ELF object (only complete ELF64 little-endian headers are parsed)")
        (e_phoff,) = struct.unpack_from("<Q", ehdr, 0x20)
        e_phentsize, e_phnum = struct.unpack_from("<HH", ehdr, 0x36)
        if e_phnum == 0xFFFF:
            raise ValueError("unsupported ELF extended program header numbering (PN_XNUM)")
        if e_phentsize != 56 or e_phnum == 0 or e_phnum > 4096:
            raise ValueError("malformed ELF program header table")
        if e_phoff + e_phentsize * e_phnum > file_size:
            raise ValueError("truncated ELF program header table")
        fh.seek(e_phoff)
        phdrs = fh.read(e_phentsize * e_phnum)
        if len(phdrs) < e_phentsize * e_phnum:
            raise ValueError("truncated ELF program header table")
        loads: List[Tuple[int, int, int, int]] = []
        dynamic: Optional[Tuple[int, int, int, int]] = None
        interp: Optional[Tuple[int, int]] = None
        for i in range(e_phnum):
            p_type, _flags, p_offset, p_vaddr, _paddr, p_filesz, p_memsz, _align = struct.unpack_from(
                "<IIQQQQQQ", phdrs, i * e_phentsize
            )
            if p_type == 1:  # PT_LOAD
                if p_offset + p_filesz > file_size:
                    raise ValueError("PT_LOAD segment overruns EOF")
                if p_filesz > p_memsz:
                    raise ValueError("PT_LOAD segment has p_filesz > p_memsz")
                loads.append((p_vaddr, p_offset, p_filesz, p_memsz))
            elif p_type == 2:  # PT_DYNAMIC
                if dynamic is not None:
                    raise ValueError("more than one PT_DYNAMIC segment")
                if p_offset + p_filesz > file_size or p_filesz > p_memsz:
                    raise ValueError("truncated PT_DYNAMIC segment")
                dynamic = (p_vaddr, p_offset, p_filesz, p_memsz)
            elif p_type == 3:  # PT_INTERP
                if interp is not None:
                    raise ValueError("more than one PT_INTERP segment")
                if p_filesz == 0 or p_filesz > 4096 or p_offset + p_filesz > file_size:
                    raise ValueError("malformed or truncated PT_INTERP segment")
                interp = (p_offset, p_filesz)
        sorted_loads = sorted(loads, key=lambda seg: seg[0])
        for i in range(len(sorted_loads) - 1):
            v1, _o1, _f1, m1 = sorted_loads[i]
            v2, _o2, _f2, _m2 = sorted_loads[i + 1]
            if m1 > 0 and v1 + m1 > v2:
                raise ValueError("overlapping PT_LOAD segments")
        if interp is not None:
            fh.seek(interp[0])
            iraw = fh.read(interp[1])
            if not iraw.endswith(b"\0") or b"\0" in iraw[:-1]:
                raise ValueError("unterminated or embedded-NUL PT_INTERP path")
            ipath = iraw[:-1].decode("utf-8", "surrogateescape")
            if not os.path.isabs(ipath) or ".." in ipath.split("/"):
                raise ValueError(f"invalid PT_INTERP path {ipath!r}")
            if dynamic is None:
                raise ValueError("PT_INTERP present without PT_DYNAMIC")
        if dynamic is None:
            return ((), ())
        dyn_vaddr, dyn_off, dyn_filesz, _dyn_memsz = dynamic
        if dyn_filesz > (1 << 20):
            raise ValueError("oversized PT_DYNAMIC segment")
        if dyn_filesz < 16:
            raise ValueError("unterminated PT_DYNAMIC segment (missing DT_NULL)")
        dyn_backed = False
        for vaddr, offset, filesz, memsz in loads:
            if vaddr <= dyn_vaddr < vaddr + memsz:
                if dyn_vaddr + dyn_filesz > vaddr + filesz:
                    raise ValueError("PT_DYNAMIC segment overruns PT_LOAD file-backed bytes (NOBITS/BSS tail)")
                if dyn_off != (dyn_vaddr - vaddr) + offset:
                    raise ValueError("PT_DYNAMIC p_offset disagrees with its enclosing PT_LOAD mapping")
                dyn_backed = True
                break
        if not dyn_backed:
            raise ValueError("PT_DYNAMIC segment is not inside a PT_LOAD segment")
        fh.seek(dyn_off)
        raw = fh.read(dyn_filesz)
        if len(raw) < dyn_filesz:
            raise ValueError("truncated PT_DYNAMIC segment")
        entries: List[Tuple[int, int]] = []
        strtab = strsz = None
        saw_dt_null = False
        for j in range(0, len(raw) - 15, 16):
            tag, val = struct.unpack_from("<qQ", raw, j)
            if tag == 0:  # DT_NULL
                saw_dt_null = True
                break
            entries.append((tag, val))
            if tag == 5:  # DT_STRTAB (virtual address)
                if strtab is not None and strtab != val:
                    raise ValueError("conflicting duplicate DT_STRTAB entries")
                strtab = val
            elif tag == 10:  # DT_STRSZ
                if strsz is not None and strsz != val:
                    raise ValueError("conflicting duplicate DT_STRSZ entries")
                strsz = val
        if not saw_dt_null:
            raise ValueError("unterminated PT_DYNAMIC segment (missing DT_NULL)")
        if strtab is None or strsz is None:
            if any(t in (1, 15, 29) for t, _ in entries):
                raise ValueError("DT_NEEDED/DT_RUNPATH present without DT_STRTAB/DT_STRSZ")
            return ((), ())
        file_off = None
        for vaddr, offset, filesz, memsz in loads:
            if vaddr <= strtab < vaddr + memsz:
                if strtab >= vaddr + filesz or strtab + strsz > vaddr + filesz:
                    raise ValueError("DT_STRTAB/DT_STRSZ overruns its PT_LOAD segment (or falls in NOBITS/BSS tail)")
                file_off = strtab - vaddr + offset
                break
        if file_off is None:
            raise ValueError("DT_STRTAB is not inside a PT_LOAD segment")

        def string_at(index: int) -> str:
            if index >= strsz:
                raise ValueError("dynamic string index out of DT_STRSZ bounds")
            fh.seek(file_off + index)
            chunk = fh.read(min(4096, strsz - index))
            end = chunk.find(b"\0")
            if end < 0:
                raise ValueError("unterminated (or > 4 KiB) dynamic string")
            return chunk[:end].decode("utf-8", "surrogateescape")

        needed = tuple(string_at(v) for t, v in entries if t == 1)  # DT_NEEDED
        runpath: List[str] = []
        for t, v in entries:
            if t in (15, 29):  # DT_RPATH, DT_RUNPATH
                # Empty components are kept: glibc's `fillin_rpath` searches the
                # current working directory for an empty RUNPATH/RPATH element.
                runpath.extend(string_at(v).split(":"))
    return needed, tuple(runpath)


def _validate_runpath_entry(entry: str, origin: str, real_root: str) -> Tuple[Optional[Path], Optional[str]]:
    """Validate one `DT_RUNPATH` / `DT_RPATH` entry against `origin` and `real_root`.

    Returns `(resolved_dir, None)` when valid, or `(None, reason)` where `reason`
    is `"empty"`, `"unsupported"`, or `"outside"`."""
    if entry == "":
        return None, "empty"
    if "$" in _ORIGIN_DST_RE.sub("", entry):
        return None, "unsupported"
    expanded = _ORIGIN_DST_RE.sub(lambda _m: origin, entry)
    if not os.path.isabs(expanded):
        return None, "unsupported"
    m = _ORIGIN_DST_RE.match(entry)
    if m is not None:
        rest = entry[m.end():]
        if _ORIGIN_DST_RE.search(rest) is not None:
            return None, "unsupported"
        if rest != "":
            if not rest.startswith("/") or rest.endswith("/") or "//" in rest:
                return None, "unsupported"
            curr = os.path.realpath(origin)
            saw_down = False
            for part in rest[1:].split("/"):
                if part in ("", "."):
                    return None, "unsupported"
                if part == "..":
                    if saw_down:
                        return None, "outside"
                    curr = os.path.dirname(curr)
                    if curr != real_root and not curr.startswith(real_root + os.sep):
                        return None, "outside"
                else:
                    saw_down = True
                    curr = os.path.realpath(os.path.join(curr, part))
                    if not curr.startswith(real_root + os.sep):
                        return None, "outside"
    else:
        if any(part in (".", "..") for part in expanded.split("/")):
            return None, "outside"
    real = os.path.realpath(expanded)
    if real == real_root or not real.startswith(real_root + os.sep):
        return None, "outside"
    return Path(os.path.normpath(expanded)), None


def _check_runpath_shadowing(toolchain_dir: Path, real_root: str, elf_rels: Sequence[str], files: Mapping[str, str], c: _Collector) -> None:
    """Reject any unpinned toolchain file that ld.so could load, via a
    DT_RUNPATH/DT_RPATH directory, for a DT_NEEDED soname of a pinned ELF object.

    ld.so searches an object's DT_RUNPATH (or, when it has none, the DT_RPATH
    chain of it *and of every object that loaded it*) before the system default
    paths, so e.g. bin/lean's `$ORIGIN/../lib` makes `lib/libm.so.6` win over
    `/lib/x86_64-linux-gnu/libm.so.6`. This check over-approximates the loader:
    every RUNPATH/RPATH directory of every checked object is searched for every
    DT_NEEDED soname of every checked object, so the verdict is independent of
    entry order, of DT_RUNPATH-over-DT_RPATH precedence and of DT_RPATH
    inheritance; every existing entry found must be a pinned/verified file. All
    RUNPATH/RPATH directories must resolve strictly inside the toolchain root.
    Entries are interpreted like glibc's `fillin_rpath` / `is_dst`: an empty
    component means the current working directory and is rejected, and only
    `$ORIGIN` / `${ORIGIN}` tokens not followed by an identifier character are
    expanded."""
    needs: List[Tuple[str, str]] = []
    search_dirs: List[Path] = []
    for rel in elf_rels:
        path = toolchain_dir / rel
        try:
            info = elf_dynamic_info(path)
        except (OSError, ValueError, struct.error) as exc:
            c.err("toolchain", f"cannot parse the ELF dynamic section of {rel}: {exc}")
            continue
        if info is None:
            continue
        needed, runpath = info
        origin = str(path.parent)
        for entry in runpath:
            directory, reason = _validate_runpath_entry(entry, origin, real_root)
            if reason == "empty":
                c.err("toolchain", f"{rel}: empty DT_RUNPATH/DT_RPATH component (glibc ld.so searches the current working directory)")
                continue
            if reason == "unsupported":
                c.err("toolchain", f"{rel}: unsupported DT_RUNPATH entry {entry!r}")
                continue
            if reason == "outside" or directory is None:
                c.err("toolchain", f"{rel}: DT_RUNPATH entry {entry!r} resolves outside the toolchain root")
                continue
            if directory not in search_dirs:
                search_dirs.append(directory)
        for soname in needed:
            if "/" in soname or soname in ("", ".", ".."):
                c.err("toolchain", f"{rel}: DT_NEEDED entry {soname!r} is a path")
                continue
            needs.append((rel, soname))
    for rel, soname in needs:
        for directory in search_dirs:
            hit = directory / soname
            if os.path.lexists(hit):
                hit_rel = os.path.relpath(hit, toolchain_dir).replace(os.sep, "/")
                if hit_rel not in files:
                    c.err(
                        "toolchain",
                        f"RUNPATH shadowing: {rel} needs {soname!r}, which ld.so can resolve to the unpinned toolchain file {hit_rel}",
                    )


def _check_toolchain_path(root: Path, real_root: str, rel: str, *, want_dir: bool, c: _Collector) -> Optional[os.stat_result]:
    """lstat every component of `rel` below `root`; reject symlinks and bad
    modes. Returns the final `lstat` only when every component is clean."""
    parts = rel.split("/")
    st: Optional[os.stat_result] = None
    clean = True
    for i in range(1, len(parts) + 1):
        sub_rel = "/".join(parts[:i])
        sub = root.joinpath(*parts[:i])
        last = i == len(parts)
        try:
            st = os.lstat(sub)
        except OSError as exc:
            c.err("toolchain", f"{sub_rel} is missing or unreadable in the toolchain: {exc.strerror}")
            return None
        if stat.S_ISLNK(st.st_mode):
            target = os.path.realpath(sub)
            escapes = not (target == real_root or target.startswith(real_root + os.sep))
            where = "escapes the toolchain root" if escapes else "stays inside the toolchain root but is still forbidden"
            c.err("toolchain", f"symlink forbidden: {sub_rel} -> {_readlink(sub)} ({where})")
            return None
        is_dir = stat.S_ISDIR(st.st_mode)
        if (not last or want_dir) and not is_dir:
            c.err("toolchain", f"{sub_rel} is not a directory")
            return None
        if last and not want_dir and not stat.S_ISREG(st.st_mode):
            c.err("toolchain", f"{sub_rel} is not a regular file")
            return None
        if is_dir:
            if st.st_mode & stat.S_IWOTH:
                c.err("toolchain", f"{sub_rel} is world-writable")
                clean = False
            continue
        for problem in _mode_problems(st):
            c.err("toolchain", f"{sub_rel} is {problem}")
            clean = False
        if st.st_nlink != 1:
            c.err("toolchain", f"{sub_rel} is hard-linked (st_nlink={st.st_nlink}, writable through another path)")
            clean = False
    return st if clean else None


def load_toolchain_pin(path: os.PathLike | str) -> Dict[str, Any]:
    """Load and validate a `--dump-toolchain-pin` document."""
    c = _Collector()
    pin = _load_toolchain_pin(Path(path), c)
    c.raise_if_errors()
    assert pin is not None
    return pin


def _load_toolchain_pin(path: Path, c: _Collector) -> Optional[Dict[str, Any]]:
    data = _read_pinned_text_file(path, f"toolchain pin {path}", c, "toolchain-pin")
    if data is None:
        return None
    try:
        pin = _load_json_strict(data)
    except (UnicodeDecodeError, ValueError) as exc:
        c.err("toolchain-pin", f"malformed toolchain pin {path}: {exc}")
        return None
    if not isinstance(pin, dict):
        c.err("toolchain-pin", "toolchain pin must be a JSON object")
        return None
    before = len(c.errors)
    _check_exact_keys(pin, TOOLCHAIN_PIN_KEYS, TOOLCHAIN_PIN_OPTIONAL_KEYS, "toolchain pin", c, category="toolchain-pin")
    if toolchain_name_problem(pin.get("toolchain")) is not None:
        c.err("toolchain-pin", f"toolchain pin names an invalid toolchain {pin.get('toolchain')!r}")
    files = pin.get("files")
    if not isinstance(files, dict) or not files:
        c.err("toolchain-pin", "toolchain pin 'files' must be a non-empty object")
    else:
        for rel, digest in files.items():
            if relpath_problem(rel) is not None or not _is_hex64(digest):
                c.err("toolchain-pin", f"toolchain pin entry {rel!r}: invalid path or SHA-256")
        for req in TOOLCHAIN_REQUIRED_FILES:
            if req not in files:
                c.err("toolchain-pin", f"toolchain pin 'files' is missing required entry {req!r}")
    versions = pin.get("versions")
    if versions is not None and (not isinstance(versions, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in versions.items())):
        c.err("toolchain-pin", "toolchain pin 'versions' must map strings to strings")
    return pin if len(c.errors) == before else None


def _verify_toolchain_impl(
    repo_root: Path,
    expected_toolchain: Optional[str],
    toolchain_dir: Optional[Path],
    elan_home: Optional[Path],
    toolchain_pin_json: Optional[Path],
    timeout: float,
    environ: Mapping[str, str],
    c: _Collector,
) -> ToolchainVerification:
    name = _read_lean_toolchain(repo_root, c)
    if name is None:
        c.fatal("toolchain", "cannot determine the repository Lean toolchain")
    if expected_toolchain is not None and name != expected_toolchain:
        c.err(
            "toolchain",
            f"toolchain drift: {LEAN_TOOLCHAIN_RELPATH} is {name!r} but UPSTREAM_PIN.json build_lean_toolchain is {expected_toolchain!r}",
        )
    resolved_by = "override"
    home: Optional[Path] = None
    if toolchain_dir is None:
        resolved_by = "elan"
        home = elan_home if elan_home is not None else default_elan_home(environ)
        _check_elan_overrides(repo_root, name, home, environ, c)
        toolchain_dir = home / "toolchains" / toolchain_dir_name(name)
    else:
        c.warn("toolchain", f"toolchain resolved via test-only override {toolchain_dir}, not via elan")
    if _lstat_real_dir(toolchain_dir, f"toolchain root {toolchain_dir}", c, "toolchain") is None:
        c.fatal("toolchain", f"active toolchain {name!r} is not installed as a real directory at {toolchain_dir}")
    real_root = os.path.realpath(toolchain_dir)

    integrity_errors_before = len(c.errors)
    for rel in ("bin", "lib", "lib/lean"):
        _check_toolchain_path(toolchain_dir, real_root, rel, want_dir=True, c=c)
    parent_lib_dir = toolchain_dir / "lib"
    try:
        parent_lib_names = sorted(entry.name for entry in os.scandir(parent_lib_dir))
    except OSError as exc:
        c.fatal("toolchain", f"cannot list lib in the toolchain: {exc.strerror}")
    for n in parent_lib_names:
        if _SHADOW_LEAN_LIB_RE.match(n):
            c.err("toolchain", f"RUNPATH shadowing library in lib/ (shadows lib/lean/): lib/{n}")
        if _SYSTEM_SONAME_RE.match(n):
            c.err("toolchain", f"system soname planted in a toolchain RUNPATH directory: lib/{n}")
    try:
        bin_names = sorted(entry.name for entry in os.scandir(toolchain_dir / "bin"))
    except OSError as exc:
        c.fatal("toolchain", f"cannot list bin in the toolchain: {exc.strerror}")
    # Every `bin/*` entry is a candidate: hashed and, under the locked release
    # pin or an explicit pin, required to be pinned, so neither a trojaned
    # companion executable (`leanc`, `leanchecker`, ...) nor a planted extra
    # one (e.g. a `bin/ld` that `clang` would prefer) can hide.
    candidates = [f"bin/{n}" for n in bin_names]
    lib_dir = toolchain_dir / "lib" / "lean"
    try:
        lib_names = sorted(entry.name for entry in os.scandir(lib_dir))
    except OSError as exc:
        c.fatal("toolchain", f"cannot list lib/lean in the toolchain: {exc.strerror}")
    candidates += [f"lib/lean/{n}" for n in lib_names if _SHARED_OBJECT_RE.search(n)]
    for rel in TOOLCHAIN_REQUIRED_FILES:
        if rel not in candidates:
            c.err("toolchain", f"required toolchain file {rel} is missing")

    files: Dict[str, str] = {}
    for rel in candidates:
        st = _check_toolchain_path(toolchain_dir, real_root, rel, want_dir=False, c=c)
        if st is None:
            continue
        try:
            files[rel] = _hash_open_file(toolchain_dir / rel, want_blob=False, expect=st)[0]
        except (OSError, ValueError) as exc:
            c.err("toolchain", f"cannot hash {rel}: {exc}")
    libleanshared = tuple(n for n in lib_names if _LIBLEANSHARED_RE.match(n))
    for n in lib_names:
        if _SYSTEM_SONAME_RE.match(n):
            c.err("toolchain", f"system soname planted in a toolchain RUNPATH directory: lib/lean/{n}")

    pin_status = "not-requested"
    active_pin: Optional[Mapping[str, Any]] = None
    locked_prefix = False
    if toolchain_pin_json is not None:
        active_pin = _load_toolchain_pin(toolchain_pin_json, c)
        if active_pin is not None:
            pin_status = "verified"
    elif resolved_by == "elan" and name in LOCKED_TOOLCHAIN_PINS:
        locked = LOCKED_TOOLCHAIN_PINS[name]
        if host_platform_triple() == locked["platform"]:
            active_pin = {"toolchain": name, "files": dict(locked["files"]), "versions": dict(locked["versions"])}
            locked_prefix = True
            pin_status = "locked-verified"
        else:
            c.warn("toolchain", f"no locked release pin for {name!r} on {host_platform_triple()!r}; digests computed but not pinned (pass --toolchain-pin-json)")
    elif resolved_by == "elan":
        c.warn("toolchain", f"no locked release pin for {name!r}; digests computed but not pinned (pass --toolchain-pin-json)")

    # Determine the trusted/pinned set BEFORE `_check_runpath_shadowing`: in A3,
    # passing `files` (which includes every `lib/lean/*.so*` on disk) exempted
    # any `.so` planted inside `lib/lean/` from `hit_rel not in files` and parsed
    # attacker-planted `lib/lean/*.so*` as trusted `elf_rels`.
    if active_pin is not None and isinstance(active_pin.get("files"), Mapping):
        pinned_files = {rel: sha for rel, sha in files.items() if rel in active_pin["files"]}
    else:
        for n in lib_names:
            if _SHARED_OBJECT_RE.search(n) and n not in KNOWN_LEAN_SHARED_LIBS and not _SYSTEM_SONAME_RE.match(n):
                c.err("toolchain", f"unpinned non-Lean shared library in lib/lean/: lib/lean/{n}")
        pinned_files = {
            rel: sha
            for rel, sha in files.items()
            if rel in RUNPATH_CHECKED_BINARIES or (rel.startswith("lib/lean/") and Path(rel).name in KNOWN_LEAN_SHARED_LIBS)
        }
    # Only the Lean-runtime objects are resolved through DT_RUNPATH here; the
    # pinned `clang` / `ld.lld` / `llvm-ar` / `cadical` load the release's own
    # (unpinned) top-level `lib/` and would otherwise always be reported.
    elf_rels = [rel for rel in candidates if rel in pinned_files and (rel in RUNPATH_CHECKED_BINARIES or rel.startswith("lib/lean/"))]
    # ld.so resolution of every DT_NEEDED soname through DT_RUNPATH must land on
    # a pinned/verified file (checked before anything in the toolchain is executed).
    _check_runpath_shadowing(toolchain_dir, real_root, elf_rels, pinned_files, c)

    if active_pin is not None:
        errors_before_lock = len(c.errors)
        _compare_toolchain_pin_files(active_pin, name, files, c)
        if locked_prefix:
            for i in range(errors_before_lock, len(c.errors)):
                c.errors[i] = c.errors[i].replace("[toolchain-pin]", "[toolchain-pin] (locked release pin)", 1)

    lean_version = lake_version = ""
    expected_version = _expected_version(name)
    if expected_version is None:
        c.warn("toolchain", f"cannot derive a release version from {name!r}; --version outputs not compared")
    if len(c.errors) != integrity_errors_before:
        # Fail closed: never execute a toolchain whose files or pinned digests failed the checks.
        c.err("toolchain", "skipped `bin/lean --version` / `bin/lake --version`: toolchain file checks failed")
    else:
        lean_version = _run_version(toolchain_dir / "bin" / "lean", "bin/lean", timeout, c) or ""
        lake_version = _run_version(toolchain_dir / "bin" / "lake", "bin/lake", timeout, c) or ""
        if active_pin is not None:
            errors_before_ver = len(c.errors)
            _compare_toolchain_pin_versions(active_pin, {"bin/lean": lean_version, "bin/lake": lake_version}, c)
            if locked_prefix:
                for i in range(errors_before_ver, len(c.errors)):
                    c.errors[i] = c.errors[i].replace("[toolchain-pin]", "[toolchain-pin] (locked release pin)", 1)
    lean_commit = lake_commit = None
    if lean_version:
        m = re.match(r"\ALean \(version ([0-9A-Za-z.+\-]+)[,)]", lean_version)
        if m is None:
            c.err("toolchain", f"unrecognized `bin/lean --version` output: {lean_version!r}")
        elif expected_version is not None and m.group(1) != expected_version:
            c.err("toolchain", f"bin/lean reports version {m.group(1)} but the toolchain is {name!r}")
        cm = re.search(r"commit ([0-9a-f]{40})", lean_version)
        lean_commit = cm.group(1) if cm else None
    if lake_version:
        m = re.match(r"\ALake version (\S+) \(Lean version ([0-9A-Za-z.+\-]+)\)", lake_version)
        if m is None:
            c.err("toolchain", f"unrecognized `bin/lake --version` output: {lake_version!r}")
        else:
            if expected_version is not None and m.group(2) != expected_version:
                c.err("toolchain", f"bin/lake reports Lean version {m.group(2)} but the toolchain is {name!r}")
            cm = re.search(r"\+([0-9a-f]{7,40})\Z", m.group(1))
            lake_commit = cm.group(1) if cm else None
    if lean_commit and lake_commit and not lean_commit.startswith(lake_commit):
        c.err("toolchain", f"bin/lake build commit {lake_commit} does not match bin/lean commit {lean_commit}")

    if home is not None and environ.get("PATH"):
        for tool in ("lean", "lake"):
            found = shutil.which(tool, path=environ["PATH"])
            allowed = {os.path.realpath(home / "bin" / tool), os.path.realpath(toolchain_dir / "bin" / tool)}
            if found and os.path.realpath(found) not in allowed:
                c.warn("toolchain", f"`{tool}` on PATH resolves to {found}, neither the elan proxy nor the verified toolchain binary")
    for var in ("LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT"):
        if environ.get(var):
            c.warn("toolchain", f"{var} is set in the environment; Lean processes launched with it may load unpinned code")
    c.raise_if_errors()
    return ToolchainVerification(
        name=name,
        toolchain_dir=str(toolchain_dir),
        lean_version=lean_version,
        lake_version=lake_version,
        files=files,
        libleanshared=libleanshared,
        pin_json=str(toolchain_pin_json) if toolchain_pin_json is not None else None,
        pin_status=pin_status,
        resolved_by=resolved_by,
        warnings=tuple(c.warnings),
    )


def _compare_toolchain_pin_files(pin: Mapping[str, Any], name: str, files: Mapping[str, str], c: _Collector) -> None:
    if pin["toolchain"] != name:
        c.err("toolchain-pin", f"toolchain pin is for {pin['toolchain']!r} but the active toolchain is {name!r}")
    pinned: Mapping[str, str] = pin["files"]
    for rel in sorted(set(files) - set(pinned)):
        c.err("toolchain-pin", f"unpinned toolchain file added: {rel}")
    for rel in sorted(set(pinned) - set(files)):
        c.err("toolchain-pin", f"pinned toolchain file deleted or unverifiable: {rel}")
    for rel in sorted(set(files) & set(pinned)):
        if files[rel] != pinned[rel]:
            c.err("toolchain-pin", f"SHA-256 mismatch for {rel}: pinned {pinned[rel]}, actual {files[rel]}")


def _compare_toolchain_pin_versions(pin: Mapping[str, Any], versions: Mapping[str, str], c: _Collector) -> None:
    for rel, version in (pin.get("versions") or {}).items():
        if versions.get(rel) != version:
            c.err("toolchain-pin", f"{rel} --version {versions.get(rel)!r} != pinned {version!r}")


def _compare_toolchain_pin(pin: Mapping[str, Any], name: str, files: Mapping[str, str], versions: Mapping[str, str], c: _Collector) -> None:
    _compare_toolchain_pin_files(pin, name, files, c)
    _compare_toolchain_pin_versions(pin, versions, c)


def verify_toolchain(
    repo_root: os.PathLike | str,
    *,
    expected_toolchain: Optional[str] = None,
    toolchain_dir: Optional[os.PathLike | str] = None,
    elan_home: Optional[os.PathLike | str] = None,
    toolchain_pin_json: Optional[os.PathLike | str] = None,
    timeout: float = DEFAULT_VERSION_TIMEOUT,
    environ: Optional[Mapping[str, str]] = None,
) -> ToolchainVerification:
    """Verify the active elan toolchain (raises `PinVerificationError`)."""
    c = _Collector()
    return _verify_toolchain_impl(
        Path(repo_root).resolve(),
        expected_toolchain,
        Path(toolchain_dir) if toolchain_dir is not None else None,
        Path(elan_home) if elan_home is not None else None,
        Path(toolchain_pin_json) if toolchain_pin_json is not None else None,
        timeout,
        os.environ if environ is None else environ,
        c,
    )


def write_toolchain_pin(toolchain: ToolchainVerification, path: os.PathLike | str) -> None:
    """Atomically write `toolchain.to_pin()` as JSON to `path`."""
    target = Path(path)
    data = (json.dumps(toolchain.to_pin(), indent=2, sort_keys=True) + "\n").encode("utf-8")
    fd, tmp = tempfile.mkstemp(prefix=".toolchain-pin-", suffix=".tmp", dir=str(target.parent or Path(".")))
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
        os.chmod(tmp, 0o644)
        os.replace(tmp, target)
    except BaseException:
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


# ---------------------------------------------------------------------------
# Combined verification + CLI
# ---------------------------------------------------------------------------


def _peek_build_toolchain(repo_root: Path) -> Optional[str]:
    try:
        raw = _load_json_strict(_read_small_regular_file(repo_root / PIN_RELPATH))
    except (OSError, ValueError):
        return None
    value = raw.get("build_lean_toolchain") if isinstance(raw, dict) else None
    return value if isinstance(value, str) else None


def verify_all(
    repo_root: os.PathLike | str,
    *,
    allow_deinit_patch: bool = False,
    require_locked_deinit_patch: Optional[bool] = None,
    olean_dir: Optional[os.PathLike | str] = None,
    check_toolchain: bool = True,
    toolchain_dir: Optional[os.PathLike | str] = None,
    elan_home: Optional[os.PathLike | str] = None,
    toolchain_pin_json: Optional[os.PathLike | str] = None,
    timeout: float = DEFAULT_VERSION_TIMEOUT,
    environ: Optional[Mapping[str, str]] = None,
    locked_identity: Optional[Mapping[str, Any]] = LOCKED_UPSTREAM_IDENTITY,
    expected_pin_sha256: Optional[str] = None,
) -> PinVerificationResult:
    """Run vendor + toolchain verification, raising one `PinVerificationError`
    that lists the errors of both phases."""
    root = Path(repo_root).resolve()
    errors: List[str] = []
    warnings: List[str] = []
    vendor: Optional[VendorVerification] = None
    toolchain: Optional[ToolchainVerification] = None
    try:
        vendor = verify_vendor(
            root,
            allow_deinit_patch=allow_deinit_patch,
            require_locked_deinit_patch=require_locked_deinit_patch,
            olean_dir=olean_dir,
            locked_identity=locked_identity,
            expected_pin_sha256=expected_pin_sha256,
        )
        warnings += vendor.warnings
    except PinVerificationError as exc:
        errors += exc.errors
        warnings += exc.warnings
    if check_toolchain:
        try:
            toolchain = verify_toolchain(
                root,
                expected_toolchain=vendor.build_lean_toolchain if vendor else _peek_build_toolchain(root),
                toolchain_dir=toolchain_dir,
                elan_home=elan_home,
                toolchain_pin_json=toolchain_pin_json,
                timeout=timeout,
                environ=environ,
            )
            warnings += toolchain.warnings
        except PinVerificationError as exc:
            errors += exc.errors
            warnings += exc.warnings
    if errors or vendor is None:
        raise PinVerificationError(errors, warnings)
    return PinVerificationResult(vendor, toolchain, tuple(warnings))


def _parse_args(argv: Optional[Sequence[str]]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail-closed verifier for lean-miri/UPSTREAM_PIN.json, lean-miri/vendor/ and the active elan Lean toolchain.",
    )
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent, help="repository root (default: the checkout containing this script)")
    parser.add_argument(
        "--allow-deinit-patch",
        action="store_true",
        help="accept patched_files overlays restricted to the closed 10-file deinitMovedPlace allowlist "
        "(the complete 10-file overlay must equal the compiled-in reviewed Episode 1 patch)",
    )
    parser.add_argument(
        "--require-locked-deinit-patch",
        action="store_true",
        help="require patched_files to be exactly the compiled-in reviewed Episode 1 10-file patch "
        "(LOCKED_DEINIT_PATCHED_FILES); implies --allow-deinit-patch",
    )
    parser.add_argument("--olean-dir", type=Path, help="directory holding compiled Miri .olean files; enables execution_machine_closure verification")
    parser.add_argument("--dump-toolchain-pin", type=Path, metavar="PATH", help="after successful verification, write the toolchain digest pin JSON to PATH")
    parser.add_argument("--toolchain-pin-json", type=Path, metavar="PATH", help="verify bin/* and lib/lean/*.so digests against a pin written by --dump-toolchain-pin")
    parser.add_argument("--expected-pin-sha256", metavar="HEX", help="additionally require UPSTREAM_PIN.json to have this SHA-256")
    parser.add_argument("--json", action="store_true", help="print a machine-readable JSON summary")
    parser.add_argument("--timeout", type=float, default=DEFAULT_VERSION_TIMEOUT, help="timeout in seconds for each `--version` probe")
    parser.add_argument("--toolchain-dir", type=Path, help=argparse.SUPPRESS)  # test-only override
    parser.add_argument("--elan-home", type=Path, help=argparse.SUPPRESS)  # test-only override
    args = parser.parse_args(argv)
    if args.expected_pin_sha256 is not None and not _is_hex64(args.expected_pin_sha256):
        parser.error("--expected-pin-sha256 must be 64 lowercase hex digits")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    return args


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = _parse_args(argv)
    try:
        result = verify_all(
            args.repo_root,
            allow_deinit_patch=args.allow_deinit_patch,
            require_locked_deinit_patch=True if args.require_locked_deinit_patch else None,
            olean_dir=args.olean_dir,
            toolchain_dir=args.toolchain_dir,
            elan_home=args.elan_home,
            toolchain_pin_json=args.toolchain_pin_json,
            timeout=args.timeout,
            expected_pin_sha256=args.expected_pin_sha256,
        )
        dumped = None
        if args.dump_toolchain_pin is not None:
            assert result.toolchain is not None
            write_toolchain_pin(result.toolchain, args.dump_toolchain_pin)
            dumped = str(args.dump_toolchain_pin)
    except PinVerificationError as exc:
        if args.json:
            print(json.dumps({
                "ok": False,
                "repo_root": str(args.repo_root),
                "mode": vendor_mode(args.allow_deinit_patch, args.require_locked_deinit_patch or None),
                "errors": list(exc.errors),
                "warnings": list(exc.warnings),
            }, indent=2))
        else:
            print(f"lean-miri pin verification FAILED ({len(exc.errors)} error(s)):", file=sys.stderr)
            for line in exc.errors:
                print(f"  - {line}", file=sys.stderr)
            for line in exc.warnings:
                print(f"  ! {line}", file=sys.stderr)
        return 1
    except OSError as exc:
        print(f"lean-miri pin verification FAILED: {exc}", file=sys.stderr)
        return 1
    summary = result.to_json_dict()
    summary["dumped_toolchain_pin"] = dumped
    if args.json:
        print(json.dumps(summary, indent=2))
        return 0
    v, t = result.vendor, result.toolchain
    print(f"lean-miri pin verification OK (mode={v.mode})")
    print(f"  {v.pin_path}: sha256 {v.pin_sha256}, commit {v.commit}")
    print(f"  verified_vendor_files: {v.verified_vendor_files}")
    print(f"  verified_aux_files: {v.verified_aux_files}")
    print(f"  manifest_sha256: {v.manifest_sha256} (recomputed; locked identity {v.locked_identity})")
    kinds = list(v.git_objects.values())
    print(f"  upstream_git_objects: {len(kinds)} verified ({kinds.count('tree')} tree, {kinds.count('blob')} blob)")
    print(f"  patched_files: {len(v.patched_files)} {[p.path for p in v.patched_files]} (deinit patch lock: {v.deinit_patch_lock})")
    print(f"  execution_machine_closure: {v.closure.status} ({v.closure.entries} entries)")
    if t is not None:
        print(f"  toolchain: {t.name} at {t.toolchain_dir} (pin: {t.pin_status})")
        print(f"    {t.lean_version}")
        print(f"    {t.lake_version}")
        for rel, digest in sorted(t.files.items()):
            print(f"    {digest}  {rel}")
    if dumped:
        print(f"  wrote toolchain pin: {dumped}")
    for line in result.warnings:
        print(f"  ! {line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
