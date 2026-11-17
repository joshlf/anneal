"""Bounded fixtures for the public gate and the independently callable audit layer."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
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

        # Group 19: Independent MIR fault-site census, unified 12-class PROPERTY_REGISTRY,
        # cross-language source pins, 4+2 false-proof mutation probes, and --audit-fault-coverage.
        # 19a. All 4+2 false-proof mutation probes pass when intact and fail closed when compromised.
        fc_report = checked(fixture())["faultCoverageAudit"]
        assert fc_report["faultClasses"] == 12 and fc_report["propertyRegistryVerified"] == 12
        assert fc_report["probesPassed"] == list(runner.ALL_FALSE_PROOF_PROBES)
        for probe_name in runner.FAULT_MUTATION_PROBES:
            probe_rep = runner.run_false_proof_probe(probe_name)
            assert probe_rep["passed"] is True
            assert probe_rep["baseline_discharged"] == probe_rep["census"]
            assert probe_rep["baseline_verdict"]["verdict"] == "VERIFIED"
            assert probe_rep["mutant_verdict"]["verdict"] == "UNKNOWN(UNMAPPED_FAULT_SITE)"
            assert probe_rep["mutant_verdict"]["missing_sites"] == probe_rep["expected_missing_sites"]
        reg_probe = runner.run_property_registry_unemitted_probe()
        assert reg_probe["passed"] is True
        assert reg_probe["witnessClasses"] == list(runner.MIR_FAULT_CLASSES)
        assert reg_probe["perClassFailClosed"] == {cls: True for cls in runner.MIR_FAULT_CLASSES}
        assert runner.run_callee_coordinate_mask_probe()["passed"] is True
        # The probe baselines are the real obligation emitter: an emitter that silently drops
        # any single fault class (e.g. `bounds_check`, never reached by the four mutation
        # bodies) fails the gate instead of passing `baseline == census` by construction.
        real_emit = runner.emit_mir_obligation_fault_sites
        for dropped in runner.MIR_FAULT_CLASSES:
            with patch.object(runner, "emit_mir_obligation_fault_sites",
                              lambda body, d=dropped: [s for s in real_emit(body) if s.fault_class != d]):
                expect_gate_failure = False
                try:
                    runner.run_false_proof_mutation_probes()
                except runner.Failure as error:
                    expect_gate_failure = error.phase == "fault-coverage"
                assert expect_gate_failure, f"lossy emitter dropping `{dropped}` passed the probes"
        with patch.object(runner, "emit_mir_obligation_fault_sites",
                          lambda body: [s for s in real_emit(body) if s.fault_class != "bounds_check"]):
            checked(fixture(), expected=1, phase="fault-coverage", executed=False)
        bad_reg = {k: dict(v) for k, v in runner.PROPERTY_REGISTRY.items()}
        bad_reg["tree_borrows_violation"]["status"] = runner.PROPERTY_STATUS_UNEMITTED_GAP
        with patch.object(runner, "PROPERTY_REGISTRY", bad_reg):
            checked(fixture(), expected=1, phase="fault-coverage", executed=False)

        # 19b. Strict census_lean_mir_module lexer traps, malformed/shadowed/truncated Mir,
        # OOB CFG targets, and RigidTy.param call-constant checks.
        valid_mir_mod = (
            "import Trusted\n"
            "namespace Mir.Demo.«item_1»\n"
            "-- comment with fake def body : CapturedMir := { basicBlocks := List.nil }\n"
            "/- nested /- comment \"unclosed -/ -/\n"
            "def emptyLayoutTable : LayoutTable := { entries := List.nil }\n"
            "def «body» : CapturedMir :=\n"
            "  { defPath := \"demo::item_1\"\n"
            "  , phase := MirPhaseTag.runtimePostCleanup\n"
            "  , role := ContractRole.subject\n"
            "  , argCount := 0\n"
            "  , localDecls := List.nil\n"
            "  , basicBlocks :=\n"
            "      (List.cons\n"
            "        { statements :=\n"
            "            (List.cons\n"
            "              { kind := (StatementKind.storageLive 1), span := \"src/lib.rs:1:1\" }\n"
            "              List.nil)\n"
            "        , terminator := { kind := TerminatorKind.return_, span := \"src/lib.rs:2:1\" }\n"
            "        , isCleanup := false\n"
            "        }\n"
            "        List.nil)\n"
            "  , fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := FieldsShape.primitive, variants := VariantsShape.empty, isUninhabited := false }, mode := AbiPassMode.ignore }, conv := CallConv.rust, canUnwind := false }\n"
            "  , layouts := emptyLayoutTable\n"
            "  , allocations := List.nil\n"
            "  }\n"
            "end Mir.Demo.«item_1»\n"
        )
        expected_sites = [
            runner.FaultSite(0, 0, "storage_live_protected"),
            runner.FaultSite(0, 1, "tree_borrows_violation"),
            runner.FaultSite(0, 1, "uninit_read"),
            runner.FaultSite(0, 1, "call_abi_mismatch"),
        ]
        assert runner.census_lean_mir_module(valid_mir_mod) == expected_sites
        assert runner.emit_mir_obligation_fault_sites(
            runner.parse_lean_mir_module_body_strict(valid_mir_mod)
        ) == expected_sites
        for bad_mir in (
            valid_mir_mod + "/- unclosed comment",
            valid_mir_mod.replace('"demo::item_1"', '"unclosed'),
            valid_mir_mod.replace("«body»", "«unclosed\nbody»"),
            valid_mir_mod.replace("import Trusted", "import Trusted.Rustc.V2026_08_01.MirAst"),
            valid_mir_mod.replace("def «body» : CapturedMir :=", "def StatementKind.nop : Nat := 0\ndef «body» : CapturedMir :="),
            valid_mir_mod.replace("end Mir.Demo.«item_1»", ""),
            valid_mir_mod.replace("allocations := List.nil\n  }", "allocations := List.nil\n  } |> id"),
            valid_mir_mod.replace("basicBlocks :=", "basicBlocks := externalBlocks --"),
        ):
            try:
                runner.census_lean_mir_module(bad_mir)
            except runner.CensusScanError:
                pass
            else:
                raise AssertionError(f"bad Mir module was accepted: {bad_mir[:80]!r}")
            assert runner.reconcile_lean_mir_coverage(bad_mir, expected_sites)["is_verified"] is False

        oob_body = runner.parse_lean_mir_module_body_strict(
            valid_mir_mod.replace("TerminatorKind.return_", "(TerminatorKind.goto 5)")
        )
        assert runner.cfg_targets_in_bounds(oob_body) is False
        oob_batch = runner.reconcile_multi_item_coverage(
            [{"def_path": "demo::item_1", "body": oob_body, "discharged": runner.census_mir_fault_sites(oob_body)}]
        )
        assert oob_batch["is_verified"] is False and any("cfgTargetsInBounds" in r for r in oob_batch["reasons"])

        param_call_mod = valid_mir_mod.replace(
            "TerminatorKind.return_",
            "(TerminatorKind.call (Operand.constant { ty := { kind := (RigidTy.param 0 \"T\"), layoutIdx := 0 }, val := ConstValue.zeroSized }) List.nil { local_ := 0, projection := List.nil } (Option.some 0) UnwindAction.continue_)",
        )
        param_body = runner.parse_lean_mir_module_body_strict(param_call_mod)
        assert runner.body_has_no_param_call_const(param_body) is False
        param_batch = runner.reconcile_multi_item_coverage(
            [{"def_path": "demo::item_1", "body": param_body, "discharged": runner.census_mir_fault_sites(param_body)}],
            {"inline_callees": [], "external_callees": [], "allow_unresolved_indirect_calls": True},
        )
        assert param_batch["is_verified"] is False and any("bodyHasNoParamCallConst" in r for r in param_batch["reasons"])

        # 19c. Cross-language Terminators.lean & FaultSiteCensus.lean source-pin drift fails closed.
        assert runner.check_fault_census_source_pins(checkout) == {
            "terminators": True,
            "faultSiteCensus": True,
        }
        # Pins are mandatory as soon as a tree ships any census theory; only bare fixture
        # trees (no `Anneal.FaultSiteCensus` import, neither pinned file) may skip them.
        assert runner.fault_census_source_pins_required(checkout) is True
        bare = fixture()
        assert runner.fault_census_source_pins_required(bare) is False
        (bare / "theory").mkdir()
        (bare / "theory/Anneal.lean").write_text("prelude\nimport Trusted\n")
        assert runner.fault_census_source_pins_required(bare) is False
        (bare / "theory/Anneal.lean").write_text("import Trusted\nimport Anneal.FaultSiteCensus\n")
        assert runner.fault_census_source_pins_required(bare) is True
        expect_failure(lambda: runner.audit_checkout_fault_coverage_gate(bare, require_source_pins=True),
                       1, "fault-coverage", "could not run")
        checked(bare, expected=1, phase="fault-coverage", executed=False)
        (bare / "theory/Anneal.lean").write_text("prelude\nimport Trusted\n")
        (bare / "theory/Anneal").mkdir()
        shutil.copyfile(checkout / "theory/Anneal/FaultSiteCensus.lean", bare / "theory/Anneal/FaultSiteCensus.lean")
        assert runner.fault_census_source_pins_required(bare) is True
        checked(bare, expected=1, phase="fault-coverage", executed=False)
        shutil.rmtree(bare)
        term_rel = Path("trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean")
        root = fixture()
        (root / term_rel).parent.mkdir(parents=True, exist_ok=True)
        (root / term_rel).write_text(
            (checkout / term_rel).read_text().replace(
                '"core::intrinsics::exact_div"', '"core::intrinsics::drifted_exact_div"', 1
            )
        )
        expect_failure(lambda: runner.check_fault_census_source_pins(root), 1, "fault-coverage", "Terminators.lean")
        shutil.rmtree(root)

        fsc_rel = Path("theory/Anneal/FaultSiteCensus.lean")
        root = fixture()
        (root / fsc_rel).parent.mkdir(parents=True, exist_ok=True)
        (root / fsc_rel).write_text(
            (checkout / fsc_rel).read_text().replace(
                "| .arithOverflow => \"arith_overflow\"",
                "| .arithOverflow => \"drifted_overflow\"",
                1,
            )
        )
        checked(root, expected=1, phase="fault-coverage", executed=False)

        # 19d. --audit-fault-coverage workspace & CaptureManifest.json positive and negative checks.
        # The FaultCensus receipt is cargo-anneal output, i.e. untrusted input: its discharged
        # sites must equal the independent Python obligation emitter, and its callee closure
        # must agree with `Obligations/<Item>.lean` and the `Verify/<Item>.lean` surface.
        ws_dir = suite / "fc-workspace"
        gen_dir = ws_dir / ".anneal/generated"
        for sub in ("Mir/Demo", "FaultCensus/Demo", "Obligations/Demo", "Verify/Demo"):
            (gen_dir / sub).mkdir(parents=True, exist_ok=True)
        (ws_dir / "src").mkdir(parents=True, exist_ok=True)
        rs_ws = ws_dir / "src/lib.rs"
        rs_ws.write_text("pub fn item_1() {}\nfn helper() {}\n")
        mir_ws = gen_dir / "Mir/Demo/item_1.lean"
        mir_ws.write_text(valid_mir_mod)
        # Inline callee bodies are captured with `ContractRole.subject` but never get their
        # own receipt or `Verify/` module; they must not be mistaken for unaudited subjects.
        helper_ws = gen_dir / "Mir/Demo/helper.lean"
        helper_ws.write_text(valid_mir_mod.replace("item_1", "helper"))
        ob_ws = gen_dir / "Obligations/Demo/item_1.lean"
        ob_nil = ("import Trusted\nimport Mir.Demo.item_1\nnamespace Obligations.Demo.item_1\n"
                  "def defaultCallees : List CapturedMir := .nil\nend Obligations.Demo.item_1\n")
        ob_ws.write_text(ob_nil)
        ver_ws = gen_dir / "Verify/Demo/item_1.lean"
        ver_claim = ("import Trusted\nimport Mir.Demo.item_1\nimport Obligations.Demo.item_1\n"
                     "namespace Verify.Demo.item_1\n"
                     "theorem verified : Trusted.VerificationResult.VerificationResult Obligations.Demo.item_1.claim :=\n"
                     "  Proof.Demo.item_1.verified\nend Verify.Demo.item_1\n")
        ver_ws.write_text(ver_claim)
        fc_ws = gen_dir / "FaultCensus/Demo/item_1.json"
        valid_receipt = {
            "def_path": "demo::item_1",
            "mir_module_sha256": runner.digest(mir_ws),
            "census_sites": [s.to_dict() for s in expected_sites],
            "discharged_sites": [s.to_dict() for s in expected_sites],
            "callee_closure": {
                "inline_callees": [],
                "external_callees": [],
                "allow_unresolved_indirect_calls": False,
            },
            "reconciliation_verdict": "VERIFIED",
            "is_verified": True,
            "reasons": [],
        }

        def write_receipt(**overrides):
            fc_ws.write_text(json.dumps({**valid_receipt, **overrides}, indent=2))

        def closure(inline=(), external=(), unresolved=False):
            return {"inline_callees": list(inline), "external_callees": list(external),
                    "allow_unresolved_indirect_calls": unresolved}

        write_receipt()
        ws_manifest = ws_dir / "CaptureManifest.json"
        ws_manifest.write_text(json.dumps({
            "schema": 1,
            "compilation_succeeded": True,
            "rust_sources": [["src/lib.rs", runner.digest(rs_ws)]],
            "targets": [{
                "def_id": "demo::helper",
                "mir_module_path": ".anneal/generated/Mir/Demo/helper.lean",
                "mir_module_sha256": runner.digest(helper_ws),
            }, {
                "def_id": "demo::item_1",
                "mir_module_path": ".anneal/generated/Mir/Demo/item_1.lean",
                "mir_module_sha256": runner.digest(mir_ws),
            }],
        }))
        assert runner.audit_fault_coverage(ws_dir)["receiptsAudited"] == 1
        assert runner.audit_fault_coverage(ws_manifest)["targets"] == 2

        # Negative 1: Omitted or unbacked discharged sites fail closed against the independent
        # emitter (a receipt can no longer certify `discharged_sites := census_sites`).
        write_receipt(discharged_sites=[s.to_dict() for s in expected_sites[:-1]])
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "independent obligation emitter")
        expect_failure(lambda: runner.verify_capture_manifest(ws_manifest, ws_dir), 1, "fault-coverage", "independent obligation emitter")
        write_receipt(discharged_sites=[s.to_dict() for s in expected_sites]
                      + [{"block_idx": 7, "stmt_idx": 0, "fault_class": "arith_overflow"}])
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "independent obligation emitter")
        real_emit = runner.emit_mir_obligation_fault_sites
        with patch.object(runner, "emit_mir_obligation_fault_sites",
                          lambda body: [s for s in real_emit(body) if s.fault_class != "call_abi_mismatch"]):
            write_receipt(discharged_sites=[s.to_dict() for s in expected_sites if s.fault_class != "call_abi_mismatch"])
            expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "call_abi_mismatch")

        # Negative 2: Stale/truncated census_sites in FaultCensus/<Item>.json fails closed.
        write_receipt(census_sites=[s.to_dict() for s in expected_sites[:-1]])
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "stale or tampered")

        # Negative 3: SHA-256 mismatch in FaultCensus/<Item>.json fails closed.
        write_receipt(mir_module_sha256="0" * 64)
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "SHA-256 mismatch")

        # Negative 4: Unverified verdict in FaultCensus/<Item>.json fails closed.
        write_receipt(is_verified=False, reconciliation_verdict="UNKNOWN(UNMAPPED_FAULT_SITE)")
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "not VERIFIED")

        # Negative 5: Unemitted registry class fails closed.
        write_receipt()
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir, registry=bad_reg), 1, "fault-coverage", "tree_borrows_violation")

        # Negative 6: Missing subject receipt fails closed (via manifest, workspace, and generated dir).
        fc_ws.unlink()
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "missing FaultCensus receipt")
        expect_failure(lambda: runner.audit_fault_coverage(ws_manifest), 1, "fault-coverage", "missing FaultCensus receipt")
        expect_failure(lambda: runner.audit_fault_coverage(gen_dir), 1, "fault-coverage", "no `FaultCensus/<Item>.json` receipts")
        write_receipt()

        # Negative 7: Orphan receipt without matching Mir/<Item>.lean fails closed.
        orphan_fc = gen_dir / "FaultCensus/Demo/orphan.json"
        orphan_fc.write_text(json.dumps(valid_receipt))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "orphan FaultCensus receipt")
        orphan_fc.unlink()

        # Negative 8: Unlisted inline callee in Obligations defaultCallees fails closed.
        ob_ws.write_text(ob_nil.replace(":= .nil", ":= [Mir.Demo.item_1.body]"))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "missing from FaultCensus `callee_closure.inline_callees`")
        ob_ws.write_text(ob_nil.replace(":= .nil", ":= [Mir.Demo.helper.body]"))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "missing from FaultCensus `callee_closure.inline_callees`")
        write_receipt(callee_closure=closure(inline=["demo::helper"]))
        assert runner.audit_fault_coverage(ws_dir)["receiptsAudited"] == 1
        ob_ws.write_text(ob_nil)

        # Negative 9: A tampered callee closure is never taken at face value.
        write_receipt(callee_closure=closure(inline=["demo::helper"]))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "never installs")
        write_receipt(callee_closure=closure(unresolved=True))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "allow_unresolved_indirect_calls")
        write_receipt(callee_closure=closure(external=["demo::ghost"]))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "non-modular")
        write_receipt()

        # Negative 10: Missing, shadowed, modified, or extended `defaultCallees` tables fail closed.
        for bad_ob, needle in (
            (ob_nil.replace("def defaultCallees : List CapturedMir := .nil\n", ""), "missing `def defaultCallees"),
            (ob_nil.replace("def defaultCallees", "abbrev defaultCallees"), "via `abbrev`"),
            (ob_nil.replace("def defaultCallees", "private def defaultCallees"), "modifier"),
            (ob_nil.replace("def defaultCallees", "def Evil.defaultCallees"), "qualified"),
            (ob_nil.replace(": List CapturedMir :=", ": List Nat :="), "malformed `def defaultCallees` header"),
            (ob_nil.replace(":= .nil", ":= [] ++ [Mir.Demo.helper.body]"), "trailing token"),
            (ob_nil.replace("namespace Obligations.Demo.item_1\n", "namespace Obligations.Demo.item_1\nnamespace Evil\nend Evil\n"), "unexpected `namespace Evil`"),
            (ob_nil.replace("import Mir.Demo.item_1\n", "import Mir.Demo.item_1\nimport Obligations.Demo.item_1\n"), "self-imports"),
        ):
            ob_ws.write_text(bad_ob)
            expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", needle)
        ob_ws.unlink()
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "missing Obligations module")
        ob_ws.write_text(ob_nil)

        # Negative 11: Missing or non-canonical `Verify/<Item>.lean` fails closed.
        for bad_ver, needle in (
            ("import Trusted\nnamespace Verify.Demo.item_1\ntheorem verified : True := trivial\nend Verify.Demo.item_1\n", "non-canonical"),
            (ver_claim.replace("theorem verified", "axiom verified"), "via `axiom`"),
            (ver_claim + "namespace Verify.Demo.item_1\ntheorem verified : True := trivial\nend Verify.Demo.item_1\n", "exactly one"),
            # Verify-surface smuggling (ported from the Rust certificate inspector, plus
            # certificate-type shadowing): axioms, notation, `@[instance]`, spec instances,
            # foreign imports, and local re-definitions of the certificate types.
            (ver_claim.replace("theorem verified", "axiom evil : False\ntheorem verified"), "disallowed top-level `axiom`"),
            (ver_claim.replace("theorem verified", "notation \"ok\" => True\ntheorem verified"), "disallowed top-level `notation`"),
            (ver_claim.replace("theorem verified", "@[instance] def evilProof : Nat := 0\ntheorem verified"), "`@[instance]`"),
            (ver_claim.replace("theorem verified", "instance : ItemSpec \"demo::item_1\" := sorry\ntheorem verified"), "specification class"),
            (ver_claim.replace("theorem verified", "instance evil : Inhabited Nat := ⟨0⟩\ntheorem verified"), "non-`*ItemProof` `instance`"),
            (ver_claim.replace("import Trusted\n", "import Trusted\nimport Assumptions.Demo.other\n"), "disallowed `import Assumptions.Demo.other`"),
            (ver_claim.replace("import Trusted\n", "import Trusted\nimport Evil\n"), "disallowed `import Evil`"),
            (ver_claim.replace("theorem verified", "def VerificationResult (_ : Nat) : Prop := True\ntheorem verified"), "shadows or escapes"),
            (ver_claim.replace("theorem verified", "def Obligations.Demo.item_1.claim : Nat := 0\ntheorem verified"), "shadows or escapes"),
        ):
            ver_ws.write_text(bad_ver)
            expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", needle)
        ver_ws.unlink()
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "Verify")
        expect_failure(lambda: runner.audit_fault_coverage(ws_manifest), 1, "fault-coverage", "Verify")

        # 19e. External callees are honoured only for an independently derived modular surface
        # backed by `externalSpecCallContract` targets or imported sibling obligations, and
        # unresolved indirect calls only for an assumed (`spec(trusted)` / UB-exception) body.
        ver_ws.write_text(ver_claim.replace(
            "VerificationResult.VerificationResult Obligations.Demo.item_1.claim",
            "VerificationResult.ModularVerificationResult Obligations.Demo.item_1.modularClaim"))
        ob_ws.write_text(ob_nil.replace(
            "end Obligations.Demo.item_1",
            "def externalCallContract_ext : MirCallContract :=\n"
            "  externalSpecCallContract \"demo::ext\" Mir.Demo.helper.body (fun _ => True) (fun _ _ => True)\n"
            "end Obligations.Demo.item_1"))
        write_receipt(callee_closure=closure(external=["demo::ext"]))
        assert runner.audit_fault_coverage(ws_dir)["receiptsAudited"] == 1
        write_receipt(callee_closure=closure(external=["demo::ext", "demo::ghost"]))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "backed by neither")
        write_receipt(callee_closure=closure(external=["demo::ext"], unresolved=True))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "allow_unresolved_indirect_calls")
        ob_ws.write_text(ob_nil.replace("import Mir.Demo.item_1\n", "import Mir.Demo.item_1\nimport Obligations.Demo.helper\n"))
        write_receipt(callee_closure=closure(external=["demo::helper"]))
        assert runner.audit_fault_coverage(ws_dir)["receiptsAudited"] == 1
        ob_ws.write_text(ob_nil.replace("import Mir.Demo.item_1\n", "import Mir.Demo.item_1\nimport Obligations.Demo.missing\n"))
        expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "Mir/Demo/missing.lean")
        ob_ws.write_text(ob_nil)
        ver_trusted = ver_claim.replace(
            "import Obligations.Demo.item_1\n", "import Obligations.Demo.item_1\nimport Assumptions.Demo.item_1\n"
        ).replace("Proof.Demo.item_1.verified", "Assumptions.Demo.item_1.rust_trusted_contract")
        ver_ws.write_text(ver_trusted)
        write_receipt(callee_closure=closure(external=["demo::anything"], unresolved=True))
        assert runner.audit_fault_coverage(ws_dir)["receiptsAudited"] == 1
        assert runner.audit_fault_coverage(ws_manifest)["targets"] == 2
        # The subject counts as assumed only for the exact generated `spec(trusted)`
        # certificate: a wrapped proof term, or one without `import Assumptions.<Item>`,
        # does not relax the closure.
        for not_assumed in (
            ver_trusted.replace("Assumptions.Demo.item_1.rust_trusted_contract",
                                "(fun h => h) Assumptions.Demo.item_1.rust_trusted_contract"),
            ver_trusted.replace("import Assumptions.Demo.item_1\n", ""),
            ver_trusted.replace("Assumptions.Demo.item_1.rust_trusted_contract",
                                "Proof.Demo.item_1.verified -- Assumptions.Demo.item_1.rust_trusted_contract"),
        ):
            ver_ws.write_text(not_assumed)
            expect_failure(lambda: runner.audit_fault_coverage(ws_dir), 1, "fault-coverage", "allow_unresolved_indirect_calls")
        shutil.rmtree(ws_dir)
        done("fault-site census, 12-class PropertyRegistry, source pins, 4+2 false-proof mutation probes, and --audit-fault-coverage")
    except BaseException as error:
        (suite / "failure.traceback").write_text(traceback.format_exc())
        print(f"SELF-TEST FAILED: {error}\nPreserved fixture sources/raw logs: {suite}", file=sys.stderr)
        return 2
    print(f"PASS: {len(passed)} fixture groups in {time.monotonic() - started:.1f}s; sequential, no research builds")
    shutil.rmtree(suite)
    return 0
