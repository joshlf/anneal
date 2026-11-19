"""Bounded fixtures for the public gate and the independently callable audit layer."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import subprocess
import sys
import tempfile
import time
import tomllib
import traceback
from unittest.mock import patch

sys.dont_write_bytecode = True


def self_test(checkout: Path, lean: Path | None) -> int:
    spec = importlib.util.spec_from_file_location("boundary_runner", checkout / "trusted/audit/check_trusted.py")
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    suite = Path(tempfile.mkdtemp(prefix="anneal-trusted-tests-"))
    started, passed, sequence = time.monotonic(), [], 0
    disposable = []

    def check_budget():
        if time.monotonic() - started > 1500:
            raise AssertionError("self-test exceeded twenty-five-minute envelope")
        if sum(p.stat().st_size for p in suite.rglob("*") if p.is_file()) > runner.MAX_BYTES:
            raise AssertionError("self-test exceeded 512 MiB retained envelope")

    def fixture(source=None):
        nonlocal sequence
        check_budget()
        sequence += 1
        root = suite / f"fixture-{sequence:03d}"
        (root / "trusted/audit").mkdir(parents=True)
        (root / "trusted/lean").mkdir(parents=True)
        for name in ("foundation-lock.json", "lean-toolchain"):
            shutil.copyfile(checkout / "trusted/lean" / name, root / "trusted/lean" / name)
        for name in ("check_trusted.py", "TrustedBoundary.lean"):
            shutil.copyfile(checkout / "trusted/audit" / name, root / "trusted/audit" / name)
        (root / "trusted/lean/Trusted.lean").write_text(source if source is not None else header)
        return root

    def checked(root, *, expected=None, phase=None, executed=None, check_downstream=False):
        checker = runner.Checker(root, lean, temp_parent=suite, fast=("--fast" in sys.argv))
        try:
            result = checker.run(check_downstream=check_downstream)
        except runner.Failure as error:
            if expected is None or error.code != expected or phase and error.phase != phase:
                raise AssertionError(f"unexpected {error.code}/{error.phase}: {error}; {checker.stage}") from error
            if executed is not None:
                assert checker.execution_began == executed
            result = error
        else:
            assert expected is None, f"expected rejection, got success: {checker.stage}"
        disposable.append(checker.stage)  # Retain raw evidence until the group's assertions pass.
        return result

    def done(label):
        check_budget()
        passed.append(label)
        print(f"  PASS {label}", flush=True)
        for path in disposable:
            shutil.rmtree(path)
        disposable.clear()

    header = "prelude\nimport Init.Core\n"
    try:
        report = checked(fixture())
        assert report["kernelDeclarations"] == 0 and report["axioms"] == [] and report["replay"]
        done("empty inventory, exact compiled foundation DAG, replay")

        positive = (checkout / "tests/trusted-boundary/positive.lean").read_text()
        root = fixture(positive)
        # Hostile ambient search paths and stale outputs must be irrelevant.
        stale = suite / "stale"
        stale.mkdir()
        (stale / "Trusted.olean").write_bytes(b"not an olean")
        with patch.dict(os.environ, {"LEAN_PATH": str(stale), "LEAN_SYSROOT": str(stale)}):
            report = checked(root)
        declarations = {d["name"]: d for d in report["declarations"]}
        assert report["kernelDeclarations"] == len(declarations) > 30
        helper = next(n for n in declarations if n.startswith("_private.") and n.endswith(".Outside.helper"))
        assert helper in declarations["Outside.sealed"]["dependencies"]
        assert declarations["Outside.sealed"]["kind"] == "opaque"
        assert "Outside.Box.rec" in declarations and "Outside.Indexed.rec" in declarations
        assert any(n.startswith("Outside.Tree") for n in declarations)
        assert any("instWrap" in n for n in declarations["Outside.inferred"]["dependencies"])
        # Elaboration reduces this coercion dictionary projection to Box.value.
        assert "Outside.Box.value" in declarations["Outside.coerced"]["dependencies"]
        assert any("instCoe" in n for n in declarations)
        assert all(d["module"] == "Trusted" for d in declarations.values())
        assert set(report["axioms"]) == {"Classical.choice", "Quot.sound", "propext"}
        done("private/opaque/data/mutual/nested/matcher/typeclass/coercion, module ownership, ambient paths")

        # Lock-only growth must affect parser, audit and replay roots consistently.
        root = fixture(header + "import Init.Data.Zero\ndef usesExtra (n : Nat) : Nat := npowRec n 2\n")
        lockpath = root / "trusted/lean/foundation-lock.json"
        lock = json.loads(lockpath.read_text())
        executable = (lean or Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean").resolve()
        prefix = executable.parent.parent
        extra = "Init.Data.Zero"
        lock["modules"][extra] = {
            "sourceSha256": runner.digest(prefix / "src/lean/Init/Data/Zero.lean"),
            "parts": {part: runner.digest(prefix / "lib/lean" / ("Init/Data/Zero." + part))
                      if (prefix / "lib/lean" / ("Init/Data/Zero." + part)).exists() else None
                      for part in runner.PARTS}}
        lock["graph"][extra] = [{"module": "Init.Tactics", "importAll": False, "isExported": True, "isMeta": False}]
        lockpath.write_text(json.dumps(lock))
        report = checked(root)
        assert extra in report["graph"] and "npowRec" in next(d["dependencies"] for d in report["declarations"] if d["name"] == "usesExtra")
        done("reviewed lock-only foundation growth and permitted standard axiom union")

        # Verify standard Init + Std, deriving, and coinductive_fixpoint are admitted and replayed.
        stdlib_pos = (
            "import Std.Data.HashMap\n"
            "structure PairBox where\n  a : Nat\n  b : Nat\nderiving DecidableEq, BEq, Repr, Inhabited\n"
            "def AlwaysZero (n : Nat) : Prop :=\n  n = 0 ∧ AlwaysZero n\ncoinductive_fixpoint\n"
        )
        stdlib_report = checked(fixture(stdlib_pos))
        assert stdlib_report["replay"] is True and stdlib_report["kernelDeclarations"] > 5

        # Each source rejection must happen before target compilation.
        negative_sources = {
            "Lean compiler import": "import Lean\ndef x : Nat := 0\n",
            "foreign namespace spoof": header + "import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n",
            "Lake import": "import Lake\n",
            "module header": "module\nprelude\nimport Init.Core\n",
            "meta import": "module\nprelude\nmeta import Init.Core\n",
            "direct meta import": "prelude\nmeta import Init.Core\n",
            "direct all import": "prelude\nimport all Init.Core\n",
            "public import": "prelude\npublic import Init.Core\n",
            "nested unsafe": header + "open Nat in\nunsafe def x : Nat := 0\n",
            "term unsafe generated hook": header + "def generatedUnsafe : Nat := unsafe 0\n",
            "mutual unsafe": header + "mutual\n unsafe def x : Nat := 0\nend\n",
            "nested forbidden command": header + "open Nat in\n#eval 0\n",
            "nested attribute": header + "structure X where\n @[extern \"foreign\"] x : Nat\n",
            "implemented_by": header + "@[implemented_by other] def x : Nat := 0\n",
            "attribute removal": header + "attribute [-extern] Nat.add\n",
            "unapproved deriving": header + "structure X where\n x : Nat\nderiving CustomUnsafeHandler\n",
            "elab command": "elab \"bad\" : command => pure ()\n",
            "set_option wrapper": header + "set_option debug.skipKernelTC true in\ndef x : Nat := 0\n",
            "axiom outside Assumptions": header + "axiom forbidden_ax : True\n",
            "custom macro": header + "macro \"x\" : term => `(0)\n",
            "native shortcut": header + "theorem x : True := by native_decide\n",
            "native decide config": header + "theorem x : True := by decide +native\n",
            "by_elab": header + "def x : Nat := by_elab return Lean.mkNatLit 0\n",
            "malformed recovery": header + "def broken : :=\n",
        }
        sentinel = suite / "must-not-exist"
        negative_sources["evaluation sentinel"] = header + f'#eval IO.FS.writeFile "{sentinel}" "executed"\n'
        for label, source in negative_sources.items():
            checked(fixture(source), expected=1, phase="preflight", executed=False)
            assert not sentinel.exists()
        done("parsed policy negatives, recursive wrappers/attributes, parser recovery, no eval sentinel")

        checked(fixture(header + "theorem bad : False := by sorry\n"), expected=1, phase="audit", executed=True)
        checked(fixture(header + "theorem bad : False := sorryAx False true\n"), expected=1, phase="audit", executed=True)
        root = fixture()
        (root / "trusted/lean/Trusted").mkdir()
        (root / "trusted/lean/Trusted/Unused.lean").write_text(header + "theorem unreferenced : False := by sorry\n")
        checked(root, expected=1, phase="audit", executed=True)
        done("sorry/direct sorryAx and unused module audited from complete inventory")

        root = fixture(header + "import Trusted.Other\n")
        (root / "trusted/lean/Trusted").mkdir()
        (root / "trusted/lean/Trusted/Other.lean").write_text(header + "import Trusted\n")
        checked(root, expected=1, phase="preflight", executed=False)
        done("source import cycle")

        for change in ("symlink", "compiled source artifact", "foundation digest", "unexpected companion"):
            root = fixture()
            if change == "symlink":
                (root / "trusted/lean/Alias.lean").symlink_to(root / "trusted/lean/Trusted.lean")
                phase, code = "snapshot", 1
            elif change == "compiled source artifact":
                (root / "trusted/lean/Trusted.olean").write_bytes(b"stale")
                phase, code = "snapshot", 1
            else:
                lockpath = root / "trusted/lean/foundation-lock.json"
                lock = json.loads(lockpath.read_text())
                part = "olean" if change == "foundation digest" else "olean.private"
                lock["modules"]["Init.Prelude"]["parts"][part] = "0" * 64 if part == "olean" else None
                lockpath.write_text(json.dumps(lock))
                phase, code = "foundation", 2
            checked(root, expected=code, phase=phase, executed=False)
        root = fixture()
        entries = sorted(p.name for p in (root / "trusted/lean").iterdir()) + ["trusted.lean"]
        with patch.object(runner.os, "walk", return_value=iter([(str(root / "trusted/lean"), [], entries)])):
            try:
                runner.snapshot(root / "trusted/lean")
            except runner.Failure as error:
                assert error.code == 1 and "case-colliding" in str(error)
            else:
                raise AssertionError("case-colliding discovery observation was accepted")
        done("symlinks/stale outputs/foundation bytes and deterministic case-collision observation")

        root = fixture()
        def incomplete_walk(_root, **options):
            options["onerror"](PermissionError("fixture unreadable nested directory"))
            return iter(())
        with patch.object(runner.os, "walk", side_effect=incomplete_walk):
            try:
                runner.snapshot(root / "trusted/lean")
            except runner.Failure as error:
                assert error.code == 2 and "incomplete" in str(error)
            else:
                raise AssertionError("incomplete directory traversal established an inventory")
        done("directory observation failure is distinct from an empty inventory")

        # Verify the axiom inventory layer directly, including an unused axiom, and graphTests.
        root = fixture()
        checker = runner.Checker(root, lean, temp_parent=suite)
        checker.tool_admission()
        imports = [{"module": "Init.Core", "importAll": False, "isExported": True, "isMeta": False}]
        setup = checker.inspect("setup", module="Trusted", imports=imports)
        setup_path = checker.stage / "axiom.setup.json"
        setup_path.write_text(json.dumps(setup))
        unchecked = checker.stage / "UnusedAxiom.lean"
        unchecked.write_text(header + "namespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n")
        output = checker.stage / "Trusted.olean"
        checker.process("axiom-fixture", ["-j1", "-M768", "-t0", "--setup", str(setup_path), "-o", str(output), str(unchecked)])
        checker.artifacts["Trusted"] = [[str(output)], []]
        checker.graph["Trusted"] = imports
        try:
            checker.inspect("audit", trusted=["Trusted"])
        except runner.Failure as error:
            assert error.code == 1 and "Trusted axiom AnyNamespace.unused" in str(error)
        else:
            raise AssertionError("unused compiled axiom escaped whole inventory audit")
        graph_report = checker.inspect("graph-tests")
        assert graph_report == {"graphTests": True}
        shutil.rmtree(checker.stage)
        done("unused compiled axiom and independent recursor-rule/opaque/parent/foreign/statement-origin graph oracles")

        # Complete final rediscovery must detect names/kinds, not just old hashes.
        root = fixture()
        checker = runner.Checker(root, lean, temp_parent=suite)
        checker.tool_admission()
        original = root / "trusted/lean/Trusted.lean"
        policy = root / "trusted/lean/foundation-lock.json"
        tool = root / "trusted/audit/TrustedBoundary.lean"
        original_bytes, policy_bytes, tool_bytes = original.read_bytes(), policy.read_bytes(), tool.read_bytes()
        changes = [
            lambda: (root / "trusted/lean/New.lean").write_text(header),
            lambda: original.unlink(),
            lambda: original.rename(root / "trusted/lean/Renamed.lean"),
            lambda: original.write_text(header + "def changed : Nat := 1\n"),
            lambda: policy.write_text("{}"),
            lambda: tool.write_text("changed inspector"),
        ]
        for change in changes:
            change()
            try:
                checker.freshness()
            except runner.Failure as error:
                assert error.code == 2 and error.phase == "freshness"
            else:
                raise AssertionError("changed complete input inventory was accepted")
            for extra in (root / "trusted/lean/New.lean", root / "trusted/lean/Renamed.lean"):
                if extra.exists():
                    extra.unlink()
            original.write_bytes(original_bytes)
            policy.write_bytes(policy_bytes)
            tool.write_bytes(tool_bytes)
        staged_source = checker.source_copy / "Trusted.lean"
        # Staged inputs are read-only (Group 18); model a child that defeats the mode bits.
        staged_source.chmod(0o644)
        staged_source.write_text(header + "def changedInStage : Nat := 9\n")
        try:
            checker.freshness()
        except runner.Failure as error:
            assert error.code == 2 and "staged Trusted" in str(error)
        else:
            raise AssertionError("changed staged source was accepted")
        staged_source.write_bytes(original_bytes)
        artifact = Path(next(p for p in checker.expected_artifacts if p.endswith(".olean.private")))
        artifact.write_bytes(b"truncated")
        try:
            checker.freshness()
        except runner.Failure as error:
            assert error.code == 2 and "artifact changed" in str(error)
        else:
            raise AssertionError("truncated staged artifact was accepted")
        shutil.rmtree(checker.stage)
        done("complete source/policy/tool rediscovery and staged-artifact freshness")

        # Status-sensitive subprocess/protocol seam; no production identity override.
        for behavior in ("nonzero", "empty", "malformed", "wrong-shape", "invalid-success-schema", "invalid-audit-count",
                         "signal", "timeout", "policy-exit1", "policy-exit2", "policy-signal", "policy-budget"):
            root = fixture()
            fake = root / "fake-lean"
            policy = "from pathlib import Path\nPath(sys.argv[-1]).write_text('{\"ok\":false,\"category\":\"policy\",\"message\":\"fixture policy\"}')\n"
            body = {"nonzero": "raise SystemExit(7)", "empty": "pass",
                    "malformed": "from pathlib import Path\nPath(sys.argv[-1]).write_text('not-json')",
                    "wrong-shape": "from pathlib import Path\nPath(sys.argv[-1]).write_text('[]')",
                    "invalid-success-schema": "from pathlib import Path\nPath(sys.argv[-1]).write_text('{\"ok\":true,\"result\":{\"graph\":[]}}')",
                    "invalid-audit-count": "from pathlib import Path\nPath(sys.argv[-1]).write_text('{\"ok\":true,\"result\":{\"graph\":{},\"declarations\":[],\"kernelDeclarations\":1,\"compilerOnlyNames\":0,\"reachableDeclarations\":1,\"axioms\":[],\"replay\":true}}')",
                    "signal": "import signal\nos.kill(os.getpid(), signal.SIGTERM)", "timeout": "pass",
                    "policy-exit1": policy + "raise SystemExit(1)",
                    "policy-exit2": policy + "raise SystemExit(2)",
                    "policy-signal": policy + "import signal\nos.kill(os.getpid(), signal.SIGTERM)",
                    "policy-budget": policy + "raise SystemExit(1)"}[behavior]
            fake.write_text(f"#!{sys.executable}\nimport sys,os\n{body}\n")
            fake.chmod(0o700)
            checker = runner.Checker(root, fake, temp_parent=suite)
            checker.prefix, checker.foundation, checker.lock, checker.inspector = root, [], {"axioms": []}, root / "unused"
            try:
                if behavior == "timeout":
                    with patch.object(runner.subprocess, "run", side_effect=subprocess.TimeoutExpired([str(fake)], 60)):
                        checker.inspect("foundation")
                elif behavior == "policy-budget":
                    with patch.object(checker, "budget", side_effect=runner.Failure(2, "budget", "fixture envelope failure")):
                        checker.inspect("foundation")
                elif behavior == "invalid-audit-count":
                    checker.inspect("audit", trusted=["Trusted"])
                else:
                    checker.inspect("foundation")
            except runner.Failure as error:
                assert error.code == (1 if behavior == "policy-exit1" else 2)
                statuses = list(checker.stage.glob("*.status.json"))
                assert len(statuses) == 1
                status = json.loads(statuses[0].read_text())
                assert status["timeout"] == (behavior == "timeout")
                if behavior == "nonzero":
                    assert status["returncode"] == 7
                if behavior == "signal":
                    assert status["returncode"] < 0
            else:
                raise AssertionError(f"bad producer {behavior} established success")
            shutil.rmtree(checker.stage)
        done("nonzero/empty/malformed/signalled/timed-out producers cannot establish success")

        # Group 12: Downstream Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation
        # and file-local test-axiom enforcement.
        def setup_downstream_fixture(claim_source: str, test_a_source: str | None = None, test_b_source: str | None = None):
            root = fixture(header + "def TrustedClaim : Prop := True\n")
            (root / "theory").mkdir()
            (root / "examples").mkdir()
            (root / "tests").mkdir()
            (root / "theory/Anneal.lean").write_text(
                "prelude\nimport Trusted\nnamespace Anneal\ndef UntrustedProp : Prop := True\ntheorem witness : TrustedClaim := True.intro\nend Anneal\n"
            )
            (root / "examples/lean-toolchain").write_text(runner.TOOLCHAIN + "\n")
            (root / "examples/lakefile.toml").write_text('name = "AnnealExamples"\ndefaultTargets = ["Smoke"]\n')
            (root / "examples/Smoke.lean").write_text(
                "prelude\nimport Anneal\nnamespace AnnealExamples\ntheorem ex : TrustedClaim := Anneal.witness\nend AnnealExamples\n"
            )
            (root / "tests/Smoke.lean").write_text(claim_source)
            targets = [
                ("Anneal", "theory/Anneal.lean", ["Trusted"], "theory"),
                ("Smoke", "examples/Smoke.lean", ["Anneal"], "examples"),
                ("SmokeTest", "tests/Smoke.lean", ["Anneal"], "claim"),
            ]
            if test_a_source is not None:
                (root / "tests/TestA.lean").write_text(test_a_source)
                targets.append(("TestA", "tests/TestA.lean", ["Anneal"], "test"))
            if test_b_source is not None:
                (root / "tests/TestB.lean").write_text(test_b_source)
                targets.append(("TestB", "tests/TestB.lean", ["Anneal", "TestA"], "test"))
            return root, targets

        # 12a. Valid claim: `ci.type` uses `TrustedClaim` (from `Trusted`), `ci.value?` uses `Anneal.witness` (from `theory/`),
        # plus a valid file-local test axiom in `TestA`.
        root, targets = setup_downstream_fixture(
            "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
            test_a_source="prelude\nimport Anneal\n-- anneal-audit: policy=file-local-axioms\naxiom local_ax : TrustedClaim\ntheorem uses_local : TrustedClaim := local_ax\n",
        )
        with patch.object(runner, "DOWNSTREAM_TARGETS", targets):
            ds = checked(root, check_downstream=True)["downstream"]
            assert ds["replay"] is True and ds["claimTheoremsChecked"] == 1 and ds["localTestAxioms"] == 1

        # 12b. Invalid claim: `ci.type` references `Anneal.UntrustedProp` through a local definition `myClaim`.
        root, targets = setup_downstream_fixture(
            "prelude\nimport Anneal\ndef myClaim : Prop := Anneal.UntrustedProp\ntheorem leaked_stmt : myClaim := True.intro\n"
        )
        with patch.object(runner, "DOWNSTREAM_TARGETS", targets):
            err = checked(root, expected=1, phase="downstream-audit", executed=True, check_downstream=True)
            assert "theorem statement of leaked_stmt depends on untrusted theory declaration Anneal.UntrustedProp" in str(err)

        # 12c. Invalid cross-file test axiom: `TestB` uses `local_ax` declared in `TestA`.
        root, targets = setup_downstream_fixture(
            "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
            test_a_source="prelude\nimport Anneal\n-- anneal-audit: policy=file-local-axioms\naxiom local_ax : TrustedClaim\n",
            test_b_source="prelude\nimport Anneal\nimport TestA\n-- anneal-audit: policy=file-local-axioms\ntheorem cross_file : TrustedClaim := local_ax\n",
        )
        with patch.object(runner, "DOWNSTREAM_TARGETS", targets):
            err = checked(root, expected=1, phase="downstream-audit", executed=True, check_downstream=True)
            assert "depends on foreign axiom local_ax from TestA" in str(err)
        done("statement (ci.type) vs. proof (ci.value?) origin separation and file-local test-axiom boundary")

        # Group 13: Cargo workspace DAG boundary for `trusted/rustc-capture`.
        root = fixture()
        shutil.copyfile(checkout / "Cargo.toml", root / "Cargo.toml")
        for member in tomllib.loads((checkout / "Cargo.toml").read_text())["workspace"]["members"]:
            (root / member).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(checkout / member / "Cargo.toml", root / member / "Cargo.toml")
        assert set(runner.check_cargo_boundary(root)) == {"Cargo.toml", "trusted/rustc-capture/Cargo.toml"}
        # Adding a dependency from `trusted/rustc-capture` onto `cargo-anneal` must fail with code 1.
        (root / "trusted/rustc-capture/Cargo.toml").write_text(
            '[package]\nname = "anneal-rustc-capture"\nversion = "0.1.0"\nedition = "2024"\n[dependencies]\ncargo-anneal = { path = "../../crates/cargo-anneal" }\n'
        )
        err = checked(root, expected=1, phase="cargo-boundary", executed=False)
        assert "depends on untrusted workspace crate cargo-anneal" in str(err)
        done("Cargo workspace DAG boundary rejects trusted/rustc-capture -> crates/* dependency")

        # Group 14: Cryptographic `CaptureManifest.json` handshake and compilation-completion check.
        manifest_dir = suite / "manifest-fixture"
        (manifest_dir / "src").mkdir(parents=True)
        (manifest_dir / "Mir").mkdir(parents=True)
        rs_file = manifest_dir / "src/lib.rs"
        mir_file = manifest_dir / "Mir/Foo.lean"
        rs_file.write_text("pub fn foo() {}\n")
        mir_file.write_text("def claim : Prop := True\n")
        manifest_path = manifest_dir / "CaptureManifest.json"
        valid_manifest = {
            "schema": 1,
            "compilation_succeeded": True,
            "rust_sources": [["src/lib.rs", runner.digest(rs_file)]],
            "targets": [{
                "def_id": "crate::foo",
                "mir_module_path": "Mir/Foo.lean",
                "mir_module_sha256": runner.digest(mir_file),
            }],
        }
        manifest_path.write_text(json.dumps(valid_manifest))
        assert runner.verify_capture_manifest(manifest_path, manifest_dir)["compilation_succeeded"] is True
        # Incomplete compilation must fail with code 1.
        manifest_path.write_text(json.dumps({**valid_manifest, "compilation_succeeded": False}))
        try:
            runner.verify_capture_manifest(manifest_path, manifest_dir)
        except runner.Failure as error:
            assert error.code == 1 and error.phase == "manifest" and "compilation_succeeded" in str(error)
        else:
            raise AssertionError("manifest with compilation_succeeded=False was accepted")
        # Tampering with `Mir/Foo.lean` on disk must fail with code 1.
        manifest_path.write_text(json.dumps(valid_manifest))
        mir_file.write_text("def claim : Prop := True -- tampered\n")
        try:
            runner.verify_capture_manifest(manifest_path, manifest_dir)
        except runner.Failure as error:
            assert error.code == 1 and error.phase == "manifest" and "Mir module digest mismatch" in str(error)
        else:
            raise AssertionError("tampered Mir/Foo.lean was accepted")
        shutil.rmtree(manifest_dir)
        done("CaptureManifest.json compilation_succeeded and SHA-256 integrity checks")

        # Group 15: Fast incremental mode (--fast) cold populate, warm hit, and
        # edit invalidation.
        root, targets = setup_downstream_fixture(
            "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n",
            test_a_source="prelude\nimport Anneal\n-- anneal-audit: policy=file-local-axioms\naxiom local_ax : TrustedClaim\ntheorem uses_local : TrustedClaim := local_ax\n",
        )
        try:
            runner.Checker(root, lean, temp_parent=suite, fast=True, cache_dir=root / "inside-cache")
        except runner.Failure as error:
            assert error.code == 2 and error.phase == "admission" and "outside checkout" in str(error)
        else:
            raise AssertionError("cache_dir inside checkout was accepted")
        fast_cache = suite / "fast-cache"
        with patch.object(runner, "DOWNSTREAM_TARGETS", targets):
            # 15a. Cold run populates .olean and inspection caches without
            # spawning setup subprocesses.
            cold_checker = runner.Checker(root, lean, temp_parent=suite, fast=True, cache_dir=fast_cache)
            disposable.append(cold_checker.stage)
            cold_report = cold_checker.run(check_downstream=True)
            assert cold_report["replay"] is True and cold_report["downstream"]["claimTheoremsChecked"] == 1
            cold_statuses = [p.name for p in sorted(cold_checker.stage.glob("*.status.json"))]
            assert not any(name.endswith("-setup.status.json") for name in cold_statuses)
            assert any(name.endswith("-compile-SmokeTest.status.json") for name in cold_statuses)
            assert (fast_cache / "olean").is_dir() and (fast_cache / "inspect").is_dir()

            # 15b. Warm no-op run hits all .olean and inspection caches so only
            # version and prefix subprocesses execute.
            warm_checker = runner.Checker(root, lean, temp_parent=suite, fast=True, cache_dir=fast_cache)
            disposable.append(warm_checker.stage)
            warm_report = warm_checker.run(check_downstream=True)
            assert warm_report == cold_report
            warm_statuses = [p.name for p in sorted(warm_checker.stage.glob("*.status.json"))]
            assert warm_statuses == ["001-version.status.json", "002-prefix.status.json"]

            # 15c. Editing one downstream file invalidates only that module and
            # downstream-audit.
            (root / "tests/Smoke.lean").write_text(
                "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n"
                "theorem second_claim : TrustedClaim := Anneal.witness\n"
            )
            edit_checker = runner.Checker(root, lean, temp_parent=suite, fast=True, cache_dir=fast_cache)
            disposable.append(edit_checker.stage)
            edit_report = edit_checker.run(check_downstream=True)
            assert edit_report["downstream"]["claimTheoremsChecked"] == 2
            edit_statuses = [p.name for p in sorted(edit_checker.stage.glob("*.status.json"))]
            assert any(name.endswith("-compile-SmokeTest.status.json") for name in edit_statuses)
            assert not any(name.endswith("-compile-Trusted.status.json") for name in edit_statuses)
            assert not any(name.endswith("-compile-Anneal.status.json") for name in edit_statuses)
            assert not any(name.endswith("-audit.status.json") and not name.endswith("-downstream-audit.status.json")
                           for name in edit_statuses)

            # 15d. Editing a downstream file to introduce a policy violation is
            # rejected in --fast mode.
            (root / "tests/Smoke.lean").write_text(
                "prelude\nimport Anneal\ndef badClaim : Prop := Anneal.UntrustedProp\n"
                "theorem bad_thm : badClaim := True.intro\n"
            )
            bad_checker = runner.Checker(root, lean, temp_parent=suite, fast=True, cache_dir=fast_cache)
            disposable.append(bad_checker.stage)
            try:
                bad_checker.run(check_downstream=True)
            except runner.Failure as error:
                assert error.code == 1 and error.phase == "downstream-audit"
                assert "theorem statement of bad_thm depends on untrusted theory declaration Anneal.UntrustedProp" in str(error)
            else:
                raise AssertionError("policy violation after downstream edit was accepted in --fast mode")
        shutil.rmtree(fast_cache, ignore_errors=True)
        done("fast incremental mode (--fast) cold populate, warm hit, and edit invalidation")

        # Group 16: Per-toolchain lock directory (trusted/lean/locks/foundation-lock-<ver>.json)
        # resolution and snapshot validation.
        root = fixture()
        (root / "trusted/lean/locks").mkdir(parents=True, exist_ok=True)
        shutil.copyfile(
            checkout / "trusted/lean/locks/foundation-lock-v4.34.1.json",
            root / "trusted/lean/locks/foundation-lock-v4.34.1.json",
        )
        # Even when fallback foundation-lock.json is removed, tool_admission() resolves
        # locks/foundation-lock-v4.34.1.json from lean-toolchain.
        (root / "trusted/lean/foundation-lock.json").unlink()
        ver_checker = runner.Checker(root, lean, temp_parent=suite)
        disposable.append(ver_checker.stage)
        ver_report = ver_checker.run()
        assert ver_report["replay"] is True
        assert ver_checker.lock_path.name == "foundation-lock-v4.34.1.json"
        # An unexpected file under locks/ must be rejected in snapshot.
        (root / "trusted/lean/locks/unexpected.txt").write_text("bad\n")
        checked(root, expected=1, phase="snapshot", executed=False)
        done("per-toolchain lock directory resolution and snapshot validation")

        # Group 17: Provisional native_decide (--allow-provisional-native) in verify-audit.
        # Verify that `Proof.*` modules using `native_decide` are rejected when
        # `--allow-provisional-native=false` and classified as `ProvisionalNative`
        # when `--allow-provisional-native=true`, while `Specs.*` modules using
        # `native_decide` are always rejected.
        prov_checker = runner.Checker(fixture(), lean, temp_parent=suite)
        prov_checker.tool_admission()
        proof_src = prov_checker.stage / "ProofNative.lean"
        proof_src.write_text("prelude\nimport Init.Core\ntheorem verified : True := by native_decide\n")
        spec_src = prov_checker.stage / "SpecNative.lean"
        spec_src.write_text("prelude\nimport Init.Core\ntheorem spec_bad : True := by native_decide\n")
        # 17a. Default preflight (allowProvisionalNative=false) rejects Proof.Demo.foo with native_decide.
        try:
            prov_checker.inspect("preflight", sources=[("Proof.Demo.foo", str(proof_src))])
        except runner.Failure as error:
            assert error.code == 1 and "nativeDecide" in str(error) and "--provisional" in str(error)
        else:
            raise AssertionError("Proof.Demo.foo with native_decide was accepted without --allow-provisional-native")
        # 17b. With allowProvisionalNative=True, Proof.Demo.foo with native_decide is permitted in preflight.
        prov_res = prov_checker.inspect(
            "preflight",
            sources=[("Proof.Demo.foo", str(proof_src))],
            allowProvisionalNative=True,
        )
        assert [h["module"] for h in prov_res["headers"]] == ["Proof.Demo.foo"]
        # 17c. Even with allowProvisionalNative=True, Specs.Demo.foo with native_decide is rejected.
        try:
            prov_checker.inspect(
                "preflight",
                sources=[("Specs.Demo.foo", str(spec_src))],
                allowProvisionalNative=True,
            )
        except runner.Failure as error:
            assert error.code == 1 and "nativeDecide" in str(error)
        else:
            raise AssertionError("Specs.Demo.foo with native_decide was accepted under allowProvisionalNative=True")
        shutil.rmtree(prov_checker.stage)
        done("provisional native_decide rejected by default and scoped to Proof.* in preflight")

        # Group 18: S0-S3 waiver pins (`waiver-pin`), annotated-claim non-vacuity
        # (`vacuity-audit`), read-only staged inputs, and `--base-snapshot` TCB drift.
        def lean_pinned(doc_lines, decl):
            body = "\n".join(doc_lines)
            name = decl.split()[1]
            tag = runner.compute_lean_decl_pins(f"/--\n{body}\n-/\n{decl}")[name]
            return f"/--\n{body}\n{tag}\n-/\n{decl}"

        def expect_failure(action, code, phase, *needles):
            try:
                action()
            except runner.Failure as error:
                assert error.code == code and error.phase == phase, (error.code, error.phase, str(error))
                for needle in needles:
                    assert needle in str(error), (needle, str(error))
                return error
            raise AssertionError(f"expected {code}/{phase} rejection, got success")

        pinned = lean_pinned(["Pinned layout constant.", "anneal:pinned_compiler_coupled rustc 1.90 layout"],
                             "def pinnedMagic : Nat := 7\n")
        vacuous = ("/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n"
                   "theorem vacuousClaim (n : Nat) (h : 0 = 1) : n = n := rfl\n")
        # 18a. A pinned waiver and an unannotated smoke lemma in a staged Trusted source pass.
        report = checked(fixture(header + pinned + "theorem trivial_witness : True := trivial\n"))
        assert report["waiverVacuityAudit"]["trusted"] == {"leanFiles": 1, "rustFiles": 0}
        # 18b. Unpinned / drifted / malformed / dangling / unauditable waivers and an annotated
        # vacuous claim in staged Trusted sources are rejected before any compilation.
        for subrule, source in {
            "unpinned_waiver": "/-- anneal:documented_intent kept for ABI parity -/\ndef unpinnedMagic : Nat := 7\n",
            "drifted_waiver_pin": pinned.replace(":= 7", ":= 8"),
            "malformed_waiver_pin": pinned.replace("pin:sha256:", "pin:sha256:zz", 1),
            "dangling_waiver": "/-! anneal:documented_intent module-wide -/\ndef x : Nat := 0\n",
            "invalid_waiver_syntax": "/-- anneal:trusted reason = -/\ndef y : Nat := 0\n",
        }.items():
            err = checked(fixture(header + source), expected=1, phase="waiver-pin", executed=False)
            assert f"[{subrule}]" in str(err) and "trusted/lean/Trusted.lean" in str(err), str(err)
        err = checked(fixture(header + vacuous), expected=1, phase="vacuity-audit", executed=False)
        assert "[syntactic_contradiction_hypothesis]" in str(err), str(err)
        # `cmd in decl` is one command: a `set_option ... in` prefix added above a pinned
        # declaration's docstring drifts its pin (the prefix is part of the pin pre-image).
        err = checked(fixture(header + "set_option maxHeartbeats 1 in\n" + pinned), expected=1,
                      phase="waiver-pin", executed=False)
        assert "[drifted_waiver_pin]" in str(err), str(err)
        err_unann = checked(
            fixture(header + "theorem unannotatedVac (n : Nat) (h : 0 = 1) : n = 99 := by omega\n"),
            expected=1,
            phase="vacuity-audit",
            executed=False,
        )
        assert "[syntactic_contradiction_hypothesis]" in str(err_unann), str(err_unann)
        err_in_meta = checked(
            fixture(
                header
                + "/- Kind: safety\nWitness: universal\nAssumes: S0 -/\n"
                + "set_option maxHeartbeats 200000 in\n"
                + "theorem vacuousIn (n : Nat) : n = n := rfl\n"
            ),
            expected=1,
            phase="vacuity-audit",
            executed=False,
        )
        assert "[trivial_conclusion]" in str(err_in_meta), str(err_in_meta)
        err_paren_eq = checked(
            fixture(
                header
                + "/-- Kind: safety\nWitness: universal\nAssumes: S0 -/\n"
                + "theorem vacParen (x y : Nat) : (True ∧ x = x) ∧ (x == y) = (x == y) := ⟨⟨trivial, rfl⟩, rfl⟩\n"
            ),
            expected=1,
            phase="vacuity-audit",
            executed=False,
        )
        assert "[trivial_conclusion]" in str(err_paren_eq), str(err_paren_eq)

        # 18c. trusted/rustc-capture Rust sources: an unpinned `///` waiver and an escaped
        # `#[doc = "anneal\x3a..."]` directive are rejected; the pinned item passes the audit.
        rs_item = "/// anneal:documented_intent kept for FFI parity\npub fn ffi_magic() -> u32 { 7 }\n"
        rs_tag = next(iter(runner.compute_rust_item_pins(rs_item).values()))
        rs_pinned = rs_item.replace("\npub fn", f"\n/// {rs_tag}\npub fn", 1)
        for rs_source, needle in ((rs_item, "[unpinned_waiver]"),
                                  ('#[doc = "anneal\\x3adocumented_intent hidden"]\npub fn g() {}\n', "[unpinned_waiver]")):
            root = fixture()
            (root / "trusted/rustc-capture/src").mkdir(parents=True)
            (root / "trusted/rustc-capture/src/lib.rs").write_text(rs_source)
            err = checked(root, expected=1, phase="waiver-pin", executed=False)
            assert needle in str(err) and "trusted/rustc-capture/src/lib.rs" in str(err), str(err)
        (root / "trusted/rustc-capture/src/lib.rs").write_text(rs_pinned)
        assert runner.audit_waivers_and_vacuity(runner.rustc_capture_sources(root), vacuity=False) == {
            "leanFiles": 0, "rustFiles": 1}

        # 18d. DOWNSTREAM_TARGETS: staged downstream copies are read-only and audited before
        # downstream compilation (unpinned waiver in the claim module, vacuous annotated test).
        for claim_extra, test_a, phase, needle in (
            ("/-- anneal:documented_intent smoke -/\ndef smokeMagic : Nat := 1\n", None, "waiver-pin", "[unpinned_waiver]"),
            ("", "prelude\nimport Anneal\n" + vacuous, "vacuity-audit", "[syntactic_contradiction_hypothesis]"),
        ):
            root, targets = setup_downstream_fixture(
                "prelude\nimport Anneal\ntheorem valid_claim : TrustedClaim := Anneal.witness\n" + claim_extra,
                test_a_source=test_a,
            )
            with patch.object(runner, "DOWNSTREAM_TARGETS", targets):
                ds_checker = runner.Checker(root, lean, temp_parent=suite, fast=("--fast" in sys.argv))
                disposable.append(ds_checker.stage)
                expect_failure(lambda: ds_checker.run(check_downstream=True), 1, phase, needle)
            staged_downstream = [p for p in (ds_checker.stage / "downstream-source").rglob("*") if p.is_file()]
            assert staged_downstream and all(stat.S_IMODE(p.stat().st_mode) == 0o444 for p in staged_downstream)
            assert not any(name.endswith("-compile-SmokeTest.status.json")
                           for name in (p.name for p in ds_checker.stage.glob("*.status.json")))

        # 18e. CaptureManifest.json: Rust sources and Mir/<Item>.lean targets are audited after
        # their digests match.
        manifest_dir = suite / "manifest-waiver-fixture"
        (manifest_dir / "src").mkdir(parents=True)
        (manifest_dir / "Mir").mkdir(parents=True)
        rs_file, mir_file = manifest_dir / "src/lib.rs", manifest_dir / "Mir/Foo.lean"
        manifest_path = manifest_dir / "CaptureManifest.json"

        def write_manifest(rs_text, mir_text):
            rs_file.write_text(rs_text)
            mir_file.write_text(mir_text)
            manifest_path.write_text(json.dumps({
                "schema": 1, "compilation_succeeded": True,
                "rust_sources": [["src/lib.rs", runner.digest(rs_file)]],
                "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Foo.lean",
                             "mir_module_sha256": runner.digest(mir_file)}],
            }))

        write_manifest(rs_pinned, "def claim : Prop := True\n")
        assert runner.verify_capture_manifest(manifest_path, manifest_dir)["compilation_succeeded"] is True
        write_manifest(rs_item, "def claim : Prop := True\n")
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "waiver-pin",
                       "src/lib.rs", "[unpinned_waiver]")
        write_manifest(rs_pinned, vacuous)
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "vacuity-audit",
                       "Mir/Foo.lean", "[syntactic_contradiction_hypothesis]")
        write_manifest(rs_pinned, "theorem unannotatedMirVac (n : Nat) (h : False) : n = 0 := False.elim h\n")
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "vacuity-audit",
                       "Mir/Foo.lean", "[syntactic_contradiction_hypothesis]")
        escape_rs = suite / "escape.rs"
        escape_rs.write_text("pub fn f() {}\n")
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [["../escape.rs", runner.digest(escape_rs)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Foo.lean",
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "manifest",
                       "escapes checkout")
        # rustc-capture keeps absolute paths for primary-package sources outside its working
        # directory: those are digest-checked as recorded, while Mir targets must be relative.
        mir_file.write_text("def claim : Prop := True\n")
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [[str(escape_rs.resolve()), runner.digest(escape_rs)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Foo.lean",
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        assert runner.verify_capture_manifest(manifest_path, manifest_dir)["compilation_succeeded"] is True
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [["src/lib.rs", runner.digest(rs_file)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": str(mir_file.resolve()),
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "manifest",
                       "mir_module_path escapes checkout")
        # Non-.rs Rust source files (e.g. `include!("waivers.inc")`) in `rust_sources` are still
        # audited as Rust, and non-.lean or symlinked `mir_module_path` entries are rejected.
        inc_file = manifest_dir / "src/waivers.inc"
        inc_file.write_text('/// anneal:trusted reason = "unpinned include"\npub unsafe fn bad() {}\n')
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [["src/waivers.inc", runner.digest(inc_file)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Foo.lean",
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "waiver-pin",
                       "src/waivers.inc", "[unpinned_waiver]")
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [["src/lib.rs", runner.digest(rs_file)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Foo.rs",
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "manifest",
                       "must be a .lean file")
        mir_link = manifest_dir / "Mir/Link.lean"
        mir_link.symlink_to(mir_file)
        manifest_path.write_text(json.dumps({
            "schema": 1, "compilation_succeeded": True,
            "rust_sources": [["src/lib.rs", runner.digest(rs_file)]],
            "targets": [{"def_id": "crate::ffi_magic", "mir_module_path": "Mir/Link.lean",
                         "mir_module_sha256": runner.digest(mir_file)}],
        }))
        expect_failure(lambda: runner.verify_capture_manifest(manifest_path, manifest_dir), 1, "manifest",
                       "regular file")
        mir_link.unlink()
        escape_rs.unlink()
        shutil.rmtree(manifest_dir)

        # 18f. Staged inspector and Trusted source copies are read-only (0444) from admission on.
        ro_checker = runner.Checker(fixture(), lean, temp_parent=suite)
        disposable.append(ro_checker.stage)
        ro_checker.tool_admission()
        staged_inputs = [ro_checker.inspector, *(p for p in ro_checker.source_copy.rglob("*") if p.is_file())]
        assert len(staged_inputs) >= 2 and all(stat.S_IMODE(p.stat().st_mode) == 0o444 for p in staged_inputs)
        if os.geteuid() != 0:
            try:
                (ro_checker.source_copy / "Trusted.lean").write_text(header + "def tampered : Nat := 1\n")
            except PermissionError:
                pass
            else:
                raise AssertionError("staged Trusted source copy was writable")
        runner.make_tree_writable(ro_checker.stage)
        assert all(p.stat().st_mode & stat.S_IWUSR for p in staged_inputs)

        # 18g. --base-snapshot: identical TCB passes; drift, additions, writable snapshots fail;
        # explicitly expected drift passes.
        root = fixture(header + pinned)
        snap = suite / "base-snapshot"
        for rel, path in runner.tcb_snapshot_files(root).items():
            (snap / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, snap / rel)
            (snap / rel).chmod(0o444)
        base_checker = runner.Checker(root, lean, temp_parent=suite, fast=("--fast" in sys.argv), base_snapshot=snap)
        disposable.append(base_checker.stage)
        assert len(base_checker.run()["baseSnapshotSha256"]) == 64
        (root / "trusted/lean/Trusted.lean").write_text(header + pinned + "def drifted : Nat := 1\n")
        drift_checker = runner.Checker(root, lean, temp_parent=suite, base_snapshot=snap)
        disposable.append(drift_checker.stage)
        expect_failure(drift_checker.run, 1, "base-snapshot", "changed: trusted/lean/Trusted.lean")
        assert drift_checker.execution_began is False and not list(drift_checker.stage.glob("*.status.json"))
        (root / "trusted/lean/Trusted/Extra.lean").parent.mkdir(parents=True)
        (root / "trusted/lean/Trusted/Extra.lean").write_text(header)
        expect_failure(lambda: runner.verify_base_snapshot(root, snap, ("trusted/lean/Trusted.lean",)),
                       1, "base-snapshot", "absent from base snapshot: trusted/lean/Trusted/Extra.lean")
        shutil.rmtree(root / "trusted/lean/Trusted")
        (root / "trusted/lean/RogueTop.lean").write_text(header)
        expect_failure(lambda: runner.verify_base_snapshot(root, snap, ("trusted/lean/Trusted.lean",)),
                       1, "base-snapshot", "absent from base snapshot: trusted/lean/RogueTop.lean")
        (root / "trusted/lean/RogueTop.lean").unlink()
        assert set(runner.verify_base_snapshot(root, snap, ("trusted/lean/Trusted.lean",))) == set(
            runner.tcb_snapshot_files(snap))
        (snap / "trusted/lean/lean-toolchain").chmod(0o644)
        expect_failure(lambda: runner.verify_base_snapshot(root, snap, ("trusted/lean/Trusted.lean",)),
                       2, "base-snapshot", "not read-only")
        shutil.rmtree(snap)
        done("waiver pins, annotated-claim vacuity, read-only staged inputs, and --base-snapshot TCB drift")

        # Group 19: pre-execution toolchain admission (the struct-free ELF64 parser and the
        # DT_NEEDED x DT_RUNPATH / DT_RPATH analysis of `lean_release_findings`), the root
        # manifest, and the Lean-child environment. Pure Python: nothing is executed.
        def elf64(needed, runpath=(), *, rpath=(), rpath_tag=29, unterminated=False, extra_dyn=()):
            """Minimal ELF64 LE ET_DYN image (EM_BPF, so it can never run): one PT_LOAD over
            the file, a PT_DYNAMIC with DT_NEEDED*, [DT_RPATH], [DT_RUNPATH/DT_RPATH],
            DT_STRTAB, DT_STRSZ, DT_NULL."""
            strtab, dyn = bytearray(b"\0"), []
            for name in needed:
                dyn.append((1, len(strtab)))
                strtab += name.encode() + b"\0"
            for tag, val_str in extra_dyn:
                dyn.append((tag, len(strtab)))
                strtab += val_str.encode() + b"\0"
            if rpath:
                dyn.append((15, len(strtab)))
                strtab += ":".join(rpath).encode() + b"\0"
            if runpath:
                dyn.append((rpath_tag, len(strtab)))
                strtab += ":".join(runpath).encode() + b"\0"
            if unterminated:
                del strtab[-1]
            dyn_off, slots = 64 + 2 * 56, len(dyn) + 3
            str_off = dyn_off + 16 * slots
            total = str_off + len(strtab)
            dyn += [(5, str_off), (10, len(strtab)), (0, 0)]
            ehdr = struct.pack("<4sBBBBB7sHHIQQQIHHHHHH", b"\x7fELF", 2, 1, 1, 0, 0, bytes(7), 3, 247, 1, 0,
                               64, 0, 0, 64, 56, 2, 64, 0, 0)
            load = struct.pack("<IIQQQQQQ", 1, 4, 0, 0, 0, total, total, 0x1000)
            dynamic = struct.pack("<IIQQQQQQ", 2, 6, dyn_off, dyn_off, dyn_off, 16 * slots, 16 * slots, 8)
            return ehdr + load + dynamic + b"".join(struct.pack("<qQ", t, v) for t, v in dyn) + bytes(strtab)

        prefix = suite / "toolchain-fixture"
        for directory in (prefix, prefix / "bin", prefix / "lib", prefix / "lib/lean"):
            directory.mkdir(exist_ok=True)
            directory.chmod(0o755)

        def install(bin_lean, extra=None):
            images = {"bin/lean": bin_lean,
                      "bin/lake": elf64(["libleanshared.so", "libc.so.6"], ["$ORIGIN/../lib", "$ORIGIN/../lib/lean"]),
                      "lib/lean/libleanshared.so": elf64(["libc.so.6"], ["$ORIGIN/..", "$ORIGIN"])}
            images.update(extra or {})
            for rel, data in images.items():
                (prefix / rel).write_bytes(data)
                (prefix / rel).chmod(0o755 if rel.startswith("bin/") else 0o644)
            return {"files": {rel: runner.digest(prefix / rel) for rel in images}}

        def expect_finding(release, needle, absent=()):
            problems = runner.lean_release_findings(prefix, release)
            assert any(needle in p for p in problems), (needle, problems)
            assert not any(bad in p for bad in absent for p in problems), (absent, problems)

        clean = install(elf64(["libleanshared.so", "libc.so.6"], ["$ORIGIN/../lib", "${ORIGIN}/../lib/lean"]))
        assert runner.lean_release_findings(prefix, clean) == [], runner.lean_release_findings(prefix, clean)
        assert runner.elf_dynamic_entries(prefix / "bin/lean") == (
            ("libleanshared.so", "libc.so.6"), ((29, ("$ORIGIN/../lib", "${ORIGIN}/../lib/lean")),))
        assert runner.elf_dynamic_info(prefix / "bin/lean") == (
            ("libleanshared.so", "libc.so.6"), ("$ORIGIN/../lib", "${ORIGIN}/../lib/lean"))
        # An honored DT_RPATH (no DT_RUNPATH next to it) is inherited by the system libraries'
        # dependencies and searched by glibc-internal dlopen (`libgcc_s.so.1`, NSS modules):
        # rejected even without a shadowed DT_NEEDED soname; an ignored one is accepted.
        (prefix / "lib/libgcc_s.so.1").write_bytes(b"\x7fELF-planted-libgcc_s")
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib", "$ORIGIN/../lib/lean"], rpath_tag=15)),
                       "bin/lean: DT_RPATH without DT_RUNPATH is unsupported", absent=("RUNPATH shadowing",))
        ignored = install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], rpath=["$ORIGIN/../lib"]))
        assert runner.lean_release_findings(prefix, ignored) == [], runner.lean_release_findings(prefix, ignored)
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"]),
                               {"lib/lean/libleanshared.so": elf64(["libc.so.6"], ["$ORIGIN/..", "$ORIGIN"], rpath_tag=15)}),
                       "lib/lean/libleanshared.so: DT_RPATH without DT_RUNPATH is unsupported")
        (prefix / "lib/libgcc_s.so.1").unlink()
        # glibc `fillin_rpath` / `is_dst` semantics and generic DT_NEEDED x DT_RUNPATH shadowing.
        (prefix / "lib/libz.so.1").write_bytes(b"\x7fELF-planted-zlib")
        for needed, runpath, needle in (
            (["libleanshared.so"], ["$ORIGIN/../lib/lean", ""], "bin/lean: empty DT_RUNPATH/DT_RPATH component"),
            (["libleanshared.so"], ["$LIB/x"], "bin/lean: unsupported DT_RUNPATH entry '$LIB/x'"),
            (["libleanshared.so"], ["$ORIGINX/../lib/lean"], "bin/lean: unsupported DT_RUNPATH entry '$ORIGINX/../lib/lean'"),
            (["libleanshared.so"], ["$ORIGIN/../.."], "bin/lean: DT_RUNPATH entry '$ORIGIN/../..' resolves outside"),
            (["$ORIGIN/evil.so"], ["$ORIGIN/../lib/lean"], "bin/lean: DT_NEEDED entry '$ORIGIN/evil.so' is a path"),
            (["libz.so.1"], ["$ORIGIN/../lib"], "RUNPATH shadowing: bin/lean needs 'libz.so.1'"),
        ):
            expect_finding(install(elf64(needed, runpath)), needle)
        (prefix / "lib/libz.so.1").unlink()
        # World-writable search directory, unparseable pinned ELF, planted companion, digest drift.
        (prefix / "lib/extra").mkdir()
        (prefix / "lib/extra").chmod(0o777)
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean", "$ORIGIN/../lib/extra"])),
                       "bin/lean: DT_RUNPATH search directory lib/extra is world-writable or not a directory")
        (prefix / "lib/extra/sub").mkdir()
        (prefix / "lib/extra/sub").chmod(0o755)
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean", "$ORIGIN/../lib/extra/sub"])),
                       "bin/lean: DT_RUNPATH search directory lib/extra/sub is world-writable or not a directory")
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean", "$ORIGIN/../lib/extra/missing"])),
                       "bin/lean: DT_RUNPATH search directory lib/extra/missing is world-writable or not a directory")
        shutil.rmtree(prefix / "lib/extra")
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], extra_dyn=[(0x7FFFFFFD, "libaux.so")])),
                       "cannot parse the ELF dynamic section of bin/lean: unsupported ELF dynamic filter tag (DT_AUXILIARY/DT_FILTER)")
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], extra_dyn=[(0x6FFFFEFC, "libaudit.so")])),
                       "cannot parse the ELF dynamic section of bin/lean: unsupported ELF dynamic audit tag (DT_AUDIT/DT_DEPAUDIT)")
        ext_sym = suite / "ext-sym-to-prefix"
        os.symlink(os.path.realpath(prefix), ext_sym)
        expect_finding(install(elf64(["libleanshared.so"], [str(ext_sym / "lib/lean")])),
                       "bin/lean: DT_RUNPATH entry")
        ext_sym.unlink()
        sym_anc = suite / "sym-anc"
        os.symlink(suite, sym_anc)
        anc_release = install(elf64(["libleanshared.so"], [os.path.realpath(prefix) + "/lib/lean", "$ORIGIN/../lib/lean"]))
        assert runner.lean_release_findings(sym_anc / "toolchain-fixture", anc_release) == [], \
            runner.lean_release_findings(sym_anc / "toolchain-fixture", anc_release)
        sym_anc.unlink()
        ww_anc = suite / "ww-anc-no-sticky"
        ww_anc.mkdir()
        ww_tc = ww_anc / "tc"
        ww_tc.mkdir()
        ww_anc.chmod(0o777)  # no S_ISVTX: allows rename-swap of `tc`
        ww_tc.chmod(0o755)
        ww_problems = runner.lean_release_findings(ww_tc, anc_release)
        assert any("without root/owner sticky protection" in p for p in ww_problems), ww_problems
        os.symlink(os.path.realpath(prefix).rsplit("/", 1)[0], ww_anc / "sym-to-safe")
        ww_sym_problems = runner.lean_release_findings(
            ww_anc / "sym-to-safe" / os.path.basename(os.path.realpath(prefix)), anc_release
        )
        assert any("without root/owner sticky protection" in p for p in ww_sym_problems), ww_sym_problems
        ww_anc.chmod(0o755)
        shutil.rmtree(ww_anc)
        prefix.chmod(0o777)
        expect_finding(clean, "toolchain root is world-writable")
        prefix.chmod(0o755)
        expect_finding(install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"], unterminated=True)),
                       "cannot parse the ELF dynamic section of bin/lean: unterminated")
        release = install(elf64(["libleanshared.so"], ["$ORIGIN/../lib/lean"]))
        (prefix / "lib/lean/libleanshared_evil.so").write_bytes(b"evil")
        (prefix / "lib/lean/libleanshared_evil.so").chmod(0o644)
        expect_finding(release, "unpinned toolchain file added: lib/lean/libleanshared_evil.so")
        (prefix / "lib/lean/libleanshared_evil.so").unlink()
        (prefix / "bin/lake").write_bytes(b"#!/bin/sh\n")
        expect_finding(release, "SHA-256 mismatch for bin/lake")
        shutil.rmtree(prefix)
        # Root manifest: exact SHA-256 coverage, fail-closed on drift, and no silent shrinking
        # (a deleted manifest or a deleted line for a required input is rejected).
        mroot = suite / "root-manifest-fixture"
        (mroot / "trusted").mkdir(parents=True)
        (mroot / "covered.txt").write_text("covered\n")
        (mroot / runner.ROOT_MANIFEST_RELPATH).write_text(
            f"# fixture\n{runner.digest(mroot / 'covered.txt')}  covered.txt\n")
        assert runner.verify_root_manifest(mroot)["coveredFiles"] == 1
        (mroot / "covered.txt").write_text("drifted\n")
        expect_failure(lambda: runner.verify_root_manifest(mroot), 1, runner.ROOT_MANIFEST_PHASE,
                       "SHA-256 mismatch for covered.txt")
        (mroot / "covered.txt").write_text("covered\n")
        (mroot / "flake.lock").write_text("{}\n")
        expect_failure(lambda: runner.verify_root_manifest(mroot), 1, runner.ROOT_MANIFEST_PHASE,
                       "flake.lock is present but not covered")
        (mroot / runner.ROOT_MANIFEST_RELPATH).unlink()
        expect_failure(lambda: runner.verify_root_manifest(mroot), 1, runner.ROOT_MANIFEST_PHASE,
                       "trusted/root-manifest.sha256 is missing, but the checkout carries flake.lock")
        (mroot / "flake.lock").unlink()
        assert runner.verify_root_manifest(mroot) == {}  # marker-free fixture without a manifest
        shutil.rmtree(mroot)
        # Lean children never inherit loader variables or glibc's secure-execution variables.
        with patch.dict(os.environ, {"LD_PRELOAD": str(suite / "evil.so"), "GCONV_PATH": str(suite),
                                     "GLIBC_TUNABLES": "glibc.rtld.optional_static_tls=1", "TMPDIR": str(suite)}):
            env_checker = runner.Checker(fixture(), lean, temp_parent=suite)
        disposable.append(env_checker.stage)
        assert not {k for k in env_checker.environment
                    if k.startswith(("LD_", "DYLD_")) or k in runner.GLIBC_UNSECURE_ENVVARS}, env_checker.environment
        assert env_checker.environment.get("TMPDIR") == str(suite)
        # Positive control: the installed locked release itself is admitted.
        live_prefix = (lean or Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean").resolve().parent.parent
        if (live_prefix.name == runner.LOCKED_LEAN_RELEASE["directory"]
                and runner._host_platform() == runner.LOCKED_LEAN_RELEASE["platform"]):
            assert runner.lean_release_findings(live_prefix) == [], runner.lean_release_findings(live_prefix)
        done("pre-execution toolchain admission (DT_NEEDED x DT_RUNPATH/DT_RPATH), root manifest, Lean-child env")
    except BaseException as error:
        (suite / "failure.traceback").write_text(traceback.format_exc())
        print(f"SELF-TEST FAILED: {error}\nPreserved fixture sources/raw logs: {suite}", file=sys.stderr)
        return 2
    print(f"PASS: {len(passed)} fixture groups in {time.monotonic() - started:.1f}s; sequential, no research builds")
    shutil.rmtree(suite)
    return 0
