#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Clean-room integrity, semantic-source lint, and module-isolation audit for the
# vendored `proofs-rs/lean-miri` formalization (`Miri`) and its correspondence
# bridge (`LeanMiriSpec`).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

echo "=== [1/3] Verifying lean-miri/UPSTREAM_PIN.json & vendored Miri SHA-256 manifest ==="
python3 - <<'PY'
import hashlib
import json
import pathlib
import sys

pin_path = pathlib.Path("lean-miri/UPSTREAM_PIN.json")
if not pin_path.is_file():
    print("ERROR: lean-miri/UPSTREAM_PIN.json is missing", file=sys.stderr)
    sys.exit(1)

pin = json.loads(pin_path.read_text(encoding="utf-8"))

expected_repo = "https://github.com/proofs-rs/lean-miri.git"
expected_commit = "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a"
expected_miri_commit = "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
expected_rustc_commits = {
    "8144389c895da997dbdecaa635e41d6a50be6ffd",
    "8144389c895da997dbdecaa635e44d6a50be6ffd",
}

if pin.get("repository") != expected_repo:
    print(f"ERROR: unexpected repository {pin.get('repository')!r}", file=sys.stderr)
    sys.exit(1)
if pin.get("commit") != expected_commit:
    print(f"ERROR: unexpected commit {pin.get('commit')!r}", file=sys.stderr)
    sys.exit(1)

upstream_pins = pin.get("upstream_pins", {})
if upstream_pins.get("miri_commit") != expected_miri_commit:
    print(f"ERROR: unexpected miri_commit {upstream_pins.get('miri_commit')!r}", file=sys.stderr)
    sys.exit(1)
if upstream_pins.get("rustc_commit") not in expected_rustc_commits:
    print(f"ERROR: unexpected rustc_commit {upstream_pins.get('rustc_commit')!r}", file=sys.stderr)
    sys.exit(1)

vendor_dir = pathlib.Path("lean-miri/vendor")
miri_pin_file = (vendor_dir / "upstream/.pins/miri.commit").read_text(encoding="utf-8").strip()
rustc_pin_file = (vendor_dir / "upstream/.pins/rustc.commit").read_text(encoding="utf-8").strip()
if miri_pin_file != expected_miri_commit:
    print(f"ERROR: vendor miri.commit mismatch: {miri_pin_file!r}", file=sys.stderr)
    sys.exit(1)
if rustc_pin_file not in expected_rustc_commits:
    print(f"ERROR: vendor rustc.commit mismatch: {rustc_pin_file!r}", file=sys.stderr)
    sys.exit(1)

source_lock_path = vendor_dir / "upstream/source-lock.json"
actual_lock_sha256 = hashlib.sha256(source_lock_path.read_bytes()).hexdigest()
if upstream_pins.get("source_lock_sha256") != actual_lock_sha256:
    print("ERROR: upstream/source-lock.json SHA-256 mismatch", file=sys.stderr)
    sys.exit(1)

miri_root = vendor_dir / "Miri.lean"
if not miri_root.is_file():
    print("ERROR: lean-miri/vendor/Miri.lean is missing", file=sys.stderr)
    sys.exit(1)

miri_files = sorted((vendor_dir / "Miri").rglob("*"))
actual_files = [miri_root] + [f for f in miri_files if f.is_file()]
actual_manifest = []
for f in actual_files:
    rel = f.relative_to(vendor_dir).as_posix()
    digest = hashlib.sha256(f.read_bytes()).hexdigest()
    actual_manifest.append({"path": rel, "sha256": digest})

manifest_lines = "".join(f"{row['sha256']}  {row['path']}\n" for row in actual_manifest)
actual_manifest_sha256 = hashlib.sha256(manifest_lines.encode("utf-8")).hexdigest()

vendor_tree = pin.get("vendor_tree", {})
if vendor_tree.get("file_count") != len(actual_manifest):
    print(
        f"ERROR: vendor file count {len(actual_manifest)} != pinned {vendor_tree.get('file_count')}",
        file=sys.stderr,
    )
    sys.exit(1)
if vendor_tree.get("files") != actual_manifest:
    print("ERROR: vendored Miri file manifest does not match UPSTREAM_PIN.json", file=sys.stderr)
    sys.exit(1)
if vendor_tree.get("manifest_sha256") != actual_manifest_sha256:
    print(
        f"ERROR: manifest_sha256 {actual_manifest_sha256} != pinned {vendor_tree.get('manifest_sha256')}",
        file=sys.stderr,
    )
    sys.exit(1)

print(
    f"Verified UPSTREAM_PIN.json: commit={expected_commit[:12]}, "
    f"files={len(actual_manifest)}, manifest_sha256={actual_manifest_sha256}"
)
PY

echo "=== [2/3] Running upstream semantic-source lint (check_semantic_sources.py) ==="
python3 lean-miri/vendor/tools/check_semantic_sources.py

echo "=== [3/3] Verifying two-way module isolation (vendor/Miri and trusted/lean vs LeanMiriSpec) ==="
python3 - <<'PY'
import pathlib
import re
import sys

import_re = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)

vendor_dir = pathlib.Path("lean-miri/vendor")
vendor_lean_files = [vendor_dir / "Miri.lean"] + sorted((vendor_dir / "Miri").rglob("*.lean"))
for f in vendor_lean_files:
    text = f.read_text(encoding="utf-8")
    for match in import_re.finditer(text):
        mod = match.group(1)
        if mod == "LeanMiriSpec" or mod.startswith("LeanMiriSpec."):
            print(f"ERROR: vendored file {f} imports {mod}", file=sys.stderr)
            sys.exit(1)
        if mod == "Trusted" or mod.startswith("Trusted."):
            print(f"ERROR: vendored file {f} imports {mod}", file=sys.stderr)
            sys.exit(1)

trusted_dir = pathlib.Path("trusted/lean")
trusted_lean_files = sorted(trusted_dir.rglob("*.lean"))
for f in trusted_lean_files:
    text = f.read_text(encoding="utf-8")
    for match in import_re.finditer(text):
        mod = match.group(1)
        if mod == "LeanMiriSpec" or mod.startswith("LeanMiriSpec."):
            print(f"ERROR: trusted file {f} imports {mod}", file=sys.stderr)
            sys.exit(1)
        if mod == "Miri" or mod.startswith("Miri."):
            print(f"ERROR: trusted file {f} imports {mod}", file=sys.stderr)
            sys.exit(1)

print(
    f"Module isolation verified across {len(vendor_lean_files)} Miri files and "
    f"{len(trusted_lean_files)} Trusted files."
)
PY

echo "Clean-room audit passed."
