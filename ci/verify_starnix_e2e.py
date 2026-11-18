#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check the production Starnix proof and fresh implementation mutations.

Source hashes bind this test to the original ten-file Fuchsia compilation.
The witness producer is untrusted: its output must first prove actual source
executions. A separate check then applies the fixed byte-reversal endpoints.
"""

import argparse
import base64
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request


# Retain raw streams before interpreting a receipt. A compiler crash,
# timeout, or invalid generator output must not count as proof rejection.
def checked_command(command, directory, log_prefix):
    with log_prefix.with_suffix(".stdout").open("wb") as stdout:
        with log_prefix.with_suffix(".stderr").open("wb") as stderr:
            result = subprocess.run(command, cwd=directory, stdout=stdout,
                                    stderr=stderr, timeout=600, check=False)
    return result.returncode


def verification(arguments, request, artifacts, log_prefix, expected):
    # When `--rustc-version` is declared, the CLI checks `--rustc` against
    # `--rustc-version` before capture and the capture's compiler after it.
    command = [str(arguments.cli), "verify", "--request", str(request),
               "--capture", str(arguments.capture), "--sysroot", str(arguments.sysroot),
               "--lean", str(arguments.lean), "--artifacts", str(artifacts)]
    if arguments.rustc_version is not None:
        command.extend(["--rustc", str(arguments.rustc),
                        "--rustc-version", arguments.rustc_version])
    code = checked_command(command, request.parent, log_prefix)
    output = json.loads(log_prefix.with_suffix(".stdout").read_text())
    if output.get("status") != expected or code != (0 if expected.endswith("verified") else 1):
        raise RuntimeError(f"unexpected {log_prefix.name}: exit {code}, "
                           f"{json.dumps(output)[:2500]}")
    return output


def sources(arguments, fixture, destination):
    pin = json.loads((fixture / "source.json").read_text())
    destination.mkdir()
    # Both downloads and local caches must supply the same original bytes.
    # A cache is a transport choice, not authority to change the workload.
    for name, expected in pin["files"].items():
        if arguments.source_dir:
            data = (arguments.source_dir / name).read_bytes()
        else:
            url = ("https://fuchsia.googlesource.com/fuchsia/+/"
                   f"{pin['revision']}/{pin['source_path']}/{name}?format=TEXT")
            for attempt in range(3):
                try:
                    with urllib.request.urlopen(url, timeout=60) as response:
                        data = base64.b64decode(response.read(), validate=False)
                    break
                except Exception:
                    if attempt == 2:
                        raise
                    time.sleep(1 << attempt)
        actual = hashlib.sha256(data).hexdigest()
        if actual != expected:
            raise RuntimeError(f"pinned source mismatch: {name}: {actual}")
        (destination / name).write_bytes(data)
    return pin


def mutate(path, kind):
    text = path.read_text()
    signature = "pub fn apply_endianness(to_be: bool, width: DataWidth, value: u64) -> u64"
    if text.count(signature) != 1:
        raise RuntimeError("production function signature changed")
    start = text.index("{", text.index(signature))
    # The hash-pinned function is a top-level item. Its inner closing braces
    # are indented; the first column-zero closing brace is its exact end.
    end = text.index("\n}", start) + 2
    if kind == "zero":
        replacement = "{\n    0\n}"
    else:
        replacement = """{
    match width {
        DataWidth::U8 => value & 0xff,
        DataWidth::U16 => value & 0xffff,
        DataWidth::U32 => value & 0xffff_ffff,
        DataWidth::U64 => value,
    }
}"""
    path.write_text(text[:start] + replacement + text[end:])


def execution_request(request_path):
    """Check the generated witnesses without assuming byte-reversal results."""
    request = json.loads(request_path.read_text())
    proof = request["proof"]
    fixed_claim_modules = {
        "ProductionClaims", "ProductionEndpoints", "Proof", "Spec",
    }
    proof["sources"] = [source for source in proof["sources"]
                        if source["module"] not in fixed_claim_modules]
    proof["sources"] += [
        {"module": "ExecutionSpec", "path": "ExecutionSpec.lean",
         "role": "specification"},
        {"module": "ExecutionProof", "path": "ExecutionProof.lean", "role": "proof"},
    ]
    proof["specification"] = "ExecutionSpec.specs"
    proof["theorem"] = "ExecutionProof.verify"
    destination = request_path.with_name("execution-request.json")
    destination.write_text(json.dumps(request, indent=2) + "\n")
    return destination


def run(arguments, work):
    repository = Path(__file__).resolve().parents[1]
    fixture = repository / "trusted/cargo-anneal/tests/fixtures/starnix"
    project = work / "production"
    project.mkdir()
    pin = sources(arguments, fixture, project / "source")
    shutil.copytree(fixture / "proof", project / "proof")
    shutil.copyfile(fixture / "request.json", project / "request.json")
    fixed_sources = {path.name: path.read_bytes()
                     for path in (project / "proof").glob("*.lean")
                     if path.name != "ProductionSteps.lean"}
    start = time.monotonic()
    baseline = verification(arguments, project / "request.json", work / "baseline-artifacts",
                            work / "baseline", "selected_unit_verified")
    if len(baseline["sources"]) != 10 or len(baseline["selected"]) != 1:
        raise RuntimeError("production source/selection inventory changed")
    # When `--rustc-version` is declared, the receipt must report that exact
    # compiler and the SHA-256 digest of the probed `--rustc` binary.
    compiler = baseline["compiler"]
    if not compiler.get("mir_dialect"):
        raise RuntimeError(f"receipt missing compiler mir_dialect: {compiler}")
    if arguments.rustc_version is not None:
        if arguments.rustc_version not in (compiler["mir_dialect"], compiler["commit"]):
            raise RuntimeError(f"receipt compiler differs from --rustc-version: {compiler}")
        expected_rustc_sha = hashlib.sha256(arguments.rustc.read_bytes()).hexdigest()
        if baseline.get("rustc_binary_sha256") != expected_rustc_sha:
            raise RuntimeError(
                f"receipt rustc_binary_sha256 {baseline.get('rustc_binary_sha256')} "
                f"!= {expected_rustc_sha}")
    elif baseline.get("rustc_binary_sha256") is not None:
        raise RuntimeError(
            "receipt unexpectedly populated rustc_binary_sha256 without --rustc-version: "
            f"{baseline.get('rustc_binary_sha256')}")
    # Positively exercise the same candidate producer used for mutations.
    # Exact byte equality reuses the baseline's successful kernel check and
    # prevents an invalid-Lean producer from satisfying only negative cases.
    regenerated = work / "baseline-regenerated.lean"
    generated = checked_command(
        [sys.executable, str(project / "proof/generate_steps.py"),
         str(work / "baseline-artifacts/capture/capture.json"), str(regenerated)],
        project, work / "baseline-generator")
    if generated or regenerated.read_bytes() != (project / "proof/ProductionSteps.lean").read_bytes():
        raise RuntimeError("regenerated baseline differs from its verified witnesses")
    results = {"baseline": {"status": baseline["status"],
                             "regenerated_witnesses_match": True,
                             "request_sha256": baseline["request_sha256"],
                             "capture_sha256": baseline["capture_sha256"],
                             "mir_dialect": compiler["mir_dialect"],
                             "timing_ms": baseline["timing_ms"]}}
    # Zero challenges a nontrivial output; masked identity challenges byte
    # reversal while preserving the requested width. Reusing the complete
    # source tree keeps each mutation in its production compilation context.
    for kind in ["zero", "masked-identity"]:
        candidate = work / kind
        shutil.copytree(project, candidate)
        mutate(candidate / "source/api.rs", kind)
        stale_artifacts = work / f"{kind}-original-witnesses"
        verification(arguments, candidate / "request.json", stale_artifacts,
                     work / f"{kind}-stale", "proof_failed")
        # Refresh candidates against the changed AST, then positively check
        # that exact module. Syntax, import, or transition failures must stop
        # the test before it can credit rejection of the fixed property.
        generated = checked_command(
            [sys.executable, str(candidate / "proof/generate_steps.py"),
             str(stale_artifacts / "capture/capture.json"),
             str(candidate / "proof/ProductionSteps.lean")],
            candidate, work / f"{kind}-generator")
        if generated:
            raise RuntimeError(f"candidate witness producer failed for {kind}")
        if any((candidate / "proof" / name).read_bytes() != contents
               for name, contents in fixed_sources.items()):
            raise RuntimeError(f"fixed proof sources changed for {kind}")
        witnesses = candidate / "proof/ProductionSteps.lean"
        witness_sha256 = hashlib.sha256(witnesses.read_bytes()).hexdigest()
        checked_execution = verification(
            arguments, execution_request(candidate / "request.json"),
            work / f"{kind}-checked-execution", work / f"{kind}-execution",
            "selected_unit_verified")
        if hashlib.sha256(witnesses.read_bytes()).hexdigest() != witness_sha256:
            raise RuntimeError(f"checked witnesses changed for {kind}")
        rejected = verification(arguments, candidate / "request.json",
                                work / f"{kind}-fresh-witnesses",
                                work / f"{kind}-fresh", "proof_failed")
        if hashlib.sha256(witnesses.read_bytes()).hexdigest() != witness_sha256:
            raise RuntimeError(f"checked witnesses changed for {kind}")
        if rejected.get("phase") != "audit":
            raise RuntimeError(f"fixed property did not reach proof checking for {kind}")
        results[kind] = {"status": rejected["status"],
                         "phase": rejected["phase"],
                         "fresh_witnesses": True,
                         "execution_status": checked_execution["status"],
                         "witness_sha256": witness_sha256}
    # Completion requires both positive execution checks and rejection of the
    # unchanged fixed property. Earlier logs alone establish neither outcome.
    summary = {"source_revision": pin["revision"], "results": results,
               "elapsed_seconds": round(time.monotonic() - start, 3)}
    (work / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


def main():
    import os
    repo_root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cli", type=Path,
        default=os.environ.get("ANNEAL_CLI") or os.environ.get("ANNEAL_MVP_CLI") or (repo_root / "target/debug/cargo-anneal"))
    parser.add_argument(
        "--capture", type=Path,
        default=os.environ.get("ANNEAL_CAPTURE") or os.environ.get("ANNEAL_MVP_CAPTURE") or (repo_root / "target/debug/anneal-rustc-capture"))
    parser.add_argument(
        "--sysroot", type=Path,
        default=os.environ.get("ANNEAL_SYSROOT") or os.environ.get("ANNEAL_MVP_SYSROOT") or os.environ.get("ANNEAL_TEST_RUST_SYSROOT"))
    parser.add_argument(
        "--lean", type=Path,
        default=os.environ.get("ANNEAL_LEAN") or os.environ.get("ANNEAL_MVP_LEAN"))
    parser.add_argument(
        "--rustc", type=Path, default=os.environ.get("ANNEAL_RUSTC") or None,
        help="Compiler checked against --rustc-version (default: SYSROOT/bin/rustc)")
    parser.add_argument(
        "--rustc-version", default=os.environ.get("ANNEAL_RUSTC_VERSION") or None,
        help="Declared compiler: a MIR dialect such as V2026_10_22_R7189d39d9 "
             "or the full commit")
    parser.add_argument("--source-dir", type=Path,
                        help="Existing pinned core/src; otherwise fetch hash-pinned files")
    parser.add_argument("--artifacts-dir", type=Path,
                        help="New directory retaining complete test evidence")
    arguments = parser.parse_args()
    for name in ["cli", "capture", "sysroot", "lean"]:
        if getattr(arguments, name) is None:
            option = name.replace("_", "-")
            parser.error(f"the following arguments are required: --{option}")
    if arguments.rustc is not None and arguments.rustc_version is None:
        parser.error("the following arguments are required: --rustc-version (required with --rustc)")
    if arguments.rustc_version is not None and arguments.rustc is None:
        arguments.rustc = Path(arguments.sysroot) / "bin/rustc"
    for name in ["cli", "capture", "sysroot", "lean", "rustc", "source_dir"]:
        path = getattr(arguments, name)
        if path is not None:
            setattr(arguments, name, Path(path).resolve(strict=True))
    # Own a fresh private evidence directory so an old successful receipt
    # cannot satisfy this run and exported source/log bytes stay private.
    if arguments.artifacts_dir:
        arguments.artifacts_dir.mkdir(mode=0o700)
        run(arguments, arguments.artifacts_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="anneal-starnix-") as directory:
            run(arguments, Path(directory))


if __name__ == "__main__":
    main()
