#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Clean-room integrity, semantic-source lint, module-isolation, and
# proof-hygiene audit for the vendored `proofs-rs/lean-miri` formalization
# (`Miri`) and its correspondence bridge (`LeanMiriSpec`).
#
# The audit needs only this repository and `python3`. It recomputes upstream
# git object ids (blob and tree SHA-1s) from the vendored bytes and file modes,
# so anyone holding a clone of `proofs-rs/lean-miri` can confirm the pinned ids
# independently with `git rev-parse <commit>:<path>`.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# Importing the pinned upstream lint helper must not write `__pycache__` into
# the byte-pinned vendored tree.
export PYTHONDONTWRITEBYTECODE=1

echo "=== [1/4] Verifying lean-miri/UPSTREAM_PIN.json against the vendored tree ==="
python3 - <<'PY'
import hashlib
import json
import os
import pathlib
import sys

# Anchors duplicated here on purpose: changing the vendored tree requires
# editing this script as well as UPSTREAM_PIN.json.
EXPECTED = {
    "repository": "https://github.com/proofs-rs/lean-miri.git",
    "commit": "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a",
    "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
    "miri_commit": "7fa591d7d4dd9af8154becbc8332f8096f8323b1",
    "rustc_commit": "8144389c895da997dbdecaa635e41d6a50be6ffd",
    "rustc_apfloat_commit": "eeaacad81247af65d4043cb3e32d023a652d7951",
    "aes_commit": "c1534361e7549e29a16c3505f45a04c92d26b62a",
    "miri_tree_sha1": "ef473f04eed9bbfed474a7b5f6f91a2f6350c41b",
    "miri_root_blob_sha1": "4c2b87b06a1786f369cc6ae26e94b3cc72652d85",
    "manifest_sha256": "081747a37a96c7443997ba12b02565f45c9642dd0dec9e3dcb3a30e7053c8d16",
    "file_count": 608,
}
PIN_FILES = {
    "miri_commit": "upstream/.pins/miri.commit",
    "rustc_commit": "upstream/.pins/rustc.commit",
    "rustc_apfloat_commit": "upstream/.pins/rustc_apfloat.commit",
    "aes_commit": "upstream/.pins/aes.commit",
}


def fail(message):
    print(f"ERROR: {message}", file=sys.stderr)
    sys.exit(1)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def git_tree_sha1(path):
    entries = []
    for child in path.iterdir():
        if child.is_symlink():
            fail(f"symlink in vendored tree: {child}")
        if child.is_dir():
            mode, sha, key = b"40000", git_tree_sha1(child), child.name + "/"
        else:
            mode = b"100755" if os.stat(child).st_mode & 0o111 else b"100644"
            sha, key = git_blob_sha1(child.read_bytes()), child.name
        entries.append((key.encode(), mode, child.name.encode(), sha))
    entries.sort(key=lambda entry: entry[0])
    body = b"".join(m + b" " + n + b"\0" + bytes.fromhex(s) for _, m, n, s in entries)
    return hashlib.sha1(b"tree %d\0" % len(body) + body).hexdigest()


pin_path = pathlib.Path("lean-miri/UPSTREAM_PIN.json")
if not pin_path.is_file():
    fail("lean-miri/UPSTREAM_PIN.json is missing")
pin = json.loads(pin_path.read_text(encoding="utf-8"))
vendor = pathlib.Path("lean-miri/vendor")

if pin.get("schema_version") != 2:
    fail(f"unexpected schema_version {pin.get('schema_version')!r}")
for key in ("repository", "commit", "upstream_lean_toolchain"):
    if pin.get(key) != EXPECTED[key]:
        fail(f"{key} is {pin.get(key)!r}, expected {EXPECTED[key]!r}")

build_toolchain = pathlib.Path("examples/lean-toolchain").read_text(encoding="utf-8").strip()
if pin.get("build_lean_toolchain") != build_toolchain:
    fail(f"build_lean_toolchain {pin.get('build_lean_toolchain')!r} != examples/lean-toolchain {build_toolchain!r}")

upstream_pins = pin.get("upstream_pins", {})
for key, rel in PIN_FILES.items():
    recorded = upstream_pins.get(key)
    on_disk = (vendor / rel).read_text(encoding="utf-8").strip()
    if recorded != EXPECTED[key] or on_disk != EXPECTED[key]:
        fail(f"{key}: UPSTREAM_PIN.json={recorded!r}, {rel}={on_disk!r}, expected {EXPECTED[key]!r}")
if upstream_pins.get("source_lock_sha256") != sha256(vendor / "upstream/source-lock.json"):
    fail("upstream/source-lock.json SHA-256 does not match UPSTREAM_PIN.json")

# Exact file set: no vendored file may be added, removed, or replaced by a link.
for path in vendor.rglob("*"):
    if path.is_symlink():
        fail(f"symlink in vendored tree: {path}")
tree = pin.get("vendor_tree", {})
aux = pin.get("vendor_aux_files", [])
pinned_paths = sorted([row["path"] for row in tree.get("files", [])] + [row["path"] for row in aux])
actual_paths = sorted(p.relative_to(vendor).as_posix() for p in vendor.rglob("*") if p.is_file())
if actual_paths != pinned_paths:
    extra = sorted(set(actual_paths) - set(pinned_paths))
    missing = sorted(set(pinned_paths) - set(actual_paths))
    fail(f"vendored file set differs from UPSTREAM_PIN.json (extra={extra}, missing={missing})")

# SHA-256 manifest of the vendored semantics (`Miri.lean` + `Miri/**`).
miri_files = [vendor / "Miri.lean"] + sorted(p for p in (vendor / "Miri").rglob("*") if p.is_file())
manifest = [{"path": p.relative_to(vendor).as_posix(), "sha256": sha256(p)} for p in miri_files]
manifest_sha256 = hashlib.sha256(
    "".join(f"{row['sha256']}  {row['path']}\n" for row in manifest).encode("utf-8")
).hexdigest()
if len(manifest) != EXPECTED["file_count"] or tree.get("file_count") != EXPECTED["file_count"]:
    fail(f"vendored Miri file count {len(manifest)} (pinned {tree.get('file_count')}) != {EXPECTED['file_count']}")
if tree.get("files") != manifest:
    fail("vendored Miri SHA-256 manifest does not match UPSTREAM_PIN.json")
if manifest_sha256 != EXPECTED["manifest_sha256"] or tree.get("manifest_sha256") != EXPECTED["manifest_sha256"]:
    fail(f"manifest_sha256 {manifest_sha256} does not match the pinned digest")
for row in aux:
    if sha256(vendor / row["path"]) != row["sha256"]:
        fail(f"SHA-256 mismatch for vendored file {row['path']}")

# Upstream git object ids, recomputed from bytes and modes.
objects = pin.get("upstream_git_objects", {})
expected_object_paths = sorted(["Miri", "Miri.lean"] + [row["path"] for row in aux])
if sorted(objects) != expected_object_paths:
    fail(f"upstream_git_objects must cover exactly {expected_object_paths}")
if objects["Miri"] != EXPECTED["miri_tree_sha1"] or objects["Miri.lean"] != EXPECTED["miri_root_blob_sha1"]:
    fail("pinned upstream git object ids for Miri/ or Miri.lean changed")
for rel, expected in sorted(objects.items()):
    path = vendor / rel
    actual = git_tree_sha1(path) if path.is_dir() else git_blob_sha1(path.read_bytes())
    if actual != expected:
        fail(f"git object id of lean-miri/vendor/{rel} is {actual}, upstream is {expected}")

print(
    f"Verified UPSTREAM_PIN.json: commit={EXPECTED['commit'][:12]}, files={len(manifest)}+{len(aux)}, "
    f"manifest_sha256={manifest_sha256}, Miri tree={objects['Miri']}"
)
PY

echo "=== [2/4] Running upstream semantic-source lint (check_semantic_sources.py) ==="
python3 lean-miri/vendor/tools/check_semantic_sources.py --root lean-miri/vendor

echo "=== [3/4] Verifying two-way module isolation (vendor/Miri and trusted/lean vs LeanMiriSpec) ==="
python3 - <<'PY'
import pathlib
import re
import sys


CHAR_LIT_RE = re.compile(r"'(?:\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\.|[^'\\\n])'")
RAW_STR_RE = re.compile(r'r(#*)"[\s\S]*?"\1')


def code_only(text):
    """Blank out comments (nested `/- -/`, `--`), regular/raw strings, and Lean char literals."""
    out = list(text)
    pos, depth, in_string = 0, 0, False
    while pos < len(text):
        if depth:
            if text.startswith("/-", pos):
                depth += 1
                out[pos:pos + 2] = "  "
                pos += 2
            elif text.startswith("-/", pos):
                depth -= 1
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif in_string:
            if text[pos] == "\\" and pos + 1 < len(text):
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] == '"':
                    in_string = False
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif text.startswith("/-", pos):
            depth = 1
            out[pos:pos + 2] = "  "
            pos += 2
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            end = len(text) if end < 0 else end
            out[pos:end] = " " * (end - pos)
            pos = end
        elif (
            text[pos] == "r"
            and pos + 1 < len(text)
            and text[pos + 1] in '#"'
            and (pos == 0 or (not text[pos - 1].isalnum() and text[pos - 1] not in "_'»"))
        ):
            m = RAW_STR_RE.match(text, pos)
            if m:
                for idx in range(pos, m.end()):
                    if out[idx] != "\n":
                        out[idx] = " "
                pos = m.end()
            else:
                pos += 1
        elif text[pos] == "'" and (
            pos == 0 or (not text[pos - 1].isalnum() and text[pos - 1] not in "_'»")
        ):
            m = CHAR_LIT_RE.match(text, pos)
            if m:
                span_len = m.end() - pos
                out[pos:m.end()] = " " * span_len
                pos = m.end()
            else:
                pos += 1
        elif text[pos] == '"':
            in_string = True
            out[pos] = " "
            pos += 1
        else:
            pos += 1
    return "".join(out)


# `import` is a header-only keyword, so every occurrence in code is an import,
# including `public import`, `meta import`, `import all`, and several imports
# on one line.
IMPORT_RE = re.compile(r"(?<![\w.'])(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_«][\w.'«»]*)")


def imports(path):
    return [m.group(1).replace("«", "").replace("»", "") for m in IMPORT_RE.finditer(code_only(path.read_text(encoding="utf-8")))]


def check(files, forbidden, label):
    for path in files:
        for module in imports(path):
            for root in forbidden:
                if module == root or module.startswith(root + "."):
                    print(f"ERROR: {label} file {path} imports {module}", file=sys.stderr)
                    sys.exit(1)


vendor = pathlib.Path("lean-miri/vendor")
vendor_files = [vendor / "Miri.lean"] + sorted((vendor / "Miri").rglob("*.lean"))
trusted_files = sorted(pathlib.Path("trusted/lean").rglob("*.lean"))
spec_files = sorted(pathlib.Path("lean-miri/lean").rglob("*.lean"))
correspondence_files = [
    p for p in spec_files if p != pathlib.Path("lean-miri/lean/LeanMiriSpec/Audit.lean")
]
check(vendor_files, ("LeanMiriSpec", "Trusted", "Anneal"), "vendored")
check(trusted_files, ("LeanMiriSpec", "Miri"), "trusted")
check(correspondence_files, ("Lean",), "non-audit LeanMiriSpec")
if not any(m == "Miri" or m.startswith("Miri.") for p in spec_files for m in imports(p)):
    print("ERROR: no LeanMiriSpec file imports Miri", file=sys.stderr)
    sys.exit(1)

# LeanMiriSpec/Audit.lean walks only the modules it imports (plus itself), and
# the build elaborates only the modules the root imports. Every `.lean` file
# under `lean-miri/lean` outside `LeanMiriSpec.lean` must reside under
# `LeanMiriSpec/`, be imported directly by both `LeanMiriSpec.lean` and
# `LeanMiriSpec/Audit.lean`, and `LeanMiriSpec.lean` itself must contain only
# `import` statements (no declarations outside `Audit.lean`'s import graph).
spec_root = pathlib.Path("lean-miri/lean")
root_file = spec_root / "LeanMiriSpec.lean"
if not root_file.is_file():
    print("ERROR: lean-miri/lean/LeanMiriSpec.lean is missing", file=sys.stderr)
    sys.exit(1)
stray_files = [
    str(p)
    for p in spec_files
    if p != root_file
    and not (p.relative_to(spec_root).parts[0] == "LeanMiriSpec" and len(p.relative_to(spec_root).parts) > 1)
]
if stray_files:
    print(f"ERROR: stray .lean files outside lean-miri/lean/LeanMiriSpec/: {stray_files}", file=sys.stderr)
    sys.exit(1)
spec_modules = {
    ".".join(p.relative_to(spec_root).with_suffix("").parts)
    for p in spec_files
    if p != root_file
}
for importer, required in (
    (spec_root / "LeanMiriSpec/Audit.lean", spec_modules - {"LeanMiriSpec.Audit"}),
    (root_file, spec_modules),
):
    missing = sorted(required - set(imports(importer)))
    if missing:
        print(f"ERROR: {importer} does not import LeanMiriSpec modules {missing}", file=sys.stderr)
        sys.exit(1)
root_non_import = IMPORT_RE.sub("", code_only(root_file.read_text(encoding="utf-8"))).strip()
if root_non_import:
    print(
        f"ERROR: {root_file} must contain only `import` statements (found: {root_non_import[:80]!r})",
        file=sys.stderr,
    )
    sys.exit(1)

print(
    f"Module isolation verified across {len(vendor_files)} Miri files, "
    f"{len(trusted_files)} Trusted files, and {len(spec_files)} LeanMiriSpec files."
)
PY

echo "=== [4/4] Scanning lean-miri/lean for proof-hygiene escape hatches ==="
python3 - <<'PY'
import pathlib
import re
import sys

CHAR_LIT_RE = re.compile(r"'(?:\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\.|[^'\\\n])'")
RAW_STR_RE = re.compile(r'r(#*)"[\s\S]*?"\1')


def code_only_char_aware(text):
    """Blank out comments, regular/raw string literals, and Lean character literals (`'\"'`, etc.)."""
    out = list(text)
    pos, depth, in_string = 0, 0, False
    while pos < len(text):
        if depth:
            if text.startswith("/-", pos):
                depth += 1
                out[pos:pos + 2] = "  "
                pos += 2
            elif text.startswith("-/", pos):
                depth -= 1
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif in_string:
            if text[pos] == "\\" and pos + 1 < len(text):
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] == '"':
                    in_string = False
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif text.startswith("/-", pos):
            depth = 1
            out[pos:pos + 2] = "  "
            pos += 2
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            end = len(text) if end < 0 else end
            out[pos:end] = " " * (end - pos)
            pos = end
        elif (
            text[pos] == "r"
            and pos + 1 < len(text)
            and text[pos + 1] in '#"'
            and (pos == 0 or (not text[pos - 1].isalnum() and text[pos - 1] not in "_'»"))
        ):
            m = RAW_STR_RE.match(text, pos)
            if m:
                for idx in range(pos, m.end()):
                    if out[idx] != "\n":
                        out[idx] = " "
                pos = m.end()
            else:
                pos += 1
        elif text[pos] == "'" and (
            pos == 0 or (not text[pos - 1].isalnum() and text[pos - 1] not in "_'»")
        ):
            m = CHAR_LIT_RE.match(text, pos)
            if m:
                out[pos:m.end()] = " " * (m.end() - pos)
                pos = m.end()
            else:
                pos += 1
        elif text[pos] == '"':
            in_string = True
            out[pos] = " "
            pos += 1
        else:
            pos += 1
    return "".join(out)


# The kernel-level audit in LeanMiriSpec/Audit.lean is authoritative; this scan
# rejects constructs that could hide unsoundness from it or from reviewers.
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|native_decide|axiom|opaque|unsafe|implemented_by|extern|"
    r"ofReduceBool|trustCompiler|skipKernelTC)\b|\+native\b|@\[\s*csimp"
)
METAPROG_RE = re.compile(r"\b(?:elab|macro|elab_rules|macro_rules|syntax)\b")
found = []
files = sorted(pathlib.Path("lean-miri/lean").rglob("*.lean"))
audit_file = pathlib.Path("lean-miri/lean/LeanMiriSpec/Audit.lean")
for path in files:
    stripped = code_only_char_aware(path.read_text(encoding="utf-8")).replace("«", " ").replace("»", " ")
    for match in FORBIDDEN.finditer(stripped):
        line = stripped.count("\n", 0, match.start()) + 1
        found.append(f"{path}:{line}: forbidden construct {match.group()!r}")
    if path != audit_file:
        for match in METAPROG_RE.finditer(stripped):
            line = stripped.count("\n", 0, match.start()) + 1
            found.append(f"{path}:{line}: metaprogramming construct {match.group()!r} outside Audit.lean")
if found:
    print("\n".join(found), file=sys.stderr)
    sys.exit(1)
print(f"Proof-hygiene scan passed across {len(files)} LeanMiriSpec files.")
PY

echo "Clean-room audit passed."
