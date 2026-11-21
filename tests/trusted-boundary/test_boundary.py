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

    def fixture(source=None, *, retain=False):
        nonlocal sequence
        check_budget()
        sequence += 1
        root = suite / f"fixture-{sequence:03d}"
        (root / "trusted/audit").mkdir(parents=True)
        (root / "trusted/lean").mkdir(parents=True)
        for name in ("foundation-lock.json", "lean-toolchain"):
            shutil.copyfile(checkout / "trusted/lean" / name, root / "trusted/lean" / name)
        # `Checker` requires the compiled-environment auditor unconditionally: a fixture without it
        # fails admission, so every fixture carries the checked-out source.
        for name in ("check_trusted.py", "TrustedBoundary.lean", "OleanEnvAuditor.lean"):
            shutil.copyfile(checkout / "trusted/audit" / name, root / "trusted/audit" / name)
        (root / "trusted/lean/Trusted.lean").write_text(source if source is not None else header)
        if not retain:
            disposable.append(root)
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
            if path.exists():
                runner.make_tree_writable(path)
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
        # The compiled-environment auditor ran on the same artifacts and audited every declaration.
        olean = report["oleanAudit"]
        assert olean["auditor"] == "OleanEnvAuditor" and olean["replay"] is True and olean["modules"] == ["Trusted"]
        assert olean["auditedDeclarations"] >= report["kernelDeclarations"] and olean["intrinsicTagsChecked"] > 0
        assert olean["kernelTagConfirmations"] > 0 and set(olean["axioms"]) == set(report["axioms"])
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
        staged_inputs = [ro_checker.inspector, ro_checker.olean_auditor,
                         *(p for p in ro_checker.source_copy.rglob("*") if p.is_file())]
        assert len(staged_inputs) >= 3 and all(stat.S_IMODE(p.stat().st_mode) == 0o444 for p in staged_inputs)
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

        # Groups 19-27: Episode 1 compiled-environment auditor (OleanEnvAuditor). Attack modules are
        # compiled directly (no preflight), exactly as a hostile build would hand them over, and the
        # auditor must reject them from the compiled artifacts alone.
        def olean_checker():
            ol = runner.Checker(fixture(retain=True), lean, temp_parent=suite)
            ol.tool_admission()  # Its stage spans Groups 19-27 and is removed after Group 27.
            return ol

        def olean_module(ol, name, source, imports, *, module_file=False, flags=()):
            rel = name.replace(".", "/")
            src = ol.stage / "olean-src" / (rel + ".lean")
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text(source)
            out = ol.stage / "olean-lib" / (rel + ".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            edges = [{"module": m, "importAll": False, "isExported": True, "isMeta": False} for m in imports]
            setup = {"name": name, "isModule": module_file, "imports": edges, "importArts": dict(ol.artifacts),
                     "dynlibs": [], "plugins": [], "options": {}}
            setup_path = ol.stage / f"{name}.olean-fixture.setup.json"
            setup_path.write_text(json.dumps(setup))
            ol.process("olean-fixture-" + name, ["-j1", "-M4096", "-t0", *flags, "--setup", str(setup_path),
                                                  "-o", str(out), str(src)])
            parts = {}
            for part in runner.PARTS:
                artifact = out.with_name(out.name[:-5] + part)
                if artifact.exists():
                    parts[part] = str(artifact)
                    ol.expected_artifacts[str(artifact)] = runner.digest(artifact)
            ol.artifacts[name] = [[parts[p] for p in runner.PARTS[:3] if p in parts],
                                  [parts[p] for p in runner.PARTS[3:] if p in parts]]
            ol.graph[name] = edges
            return parts

        def olean_reject(ol, names, *needles, **extra):
            try:
                ol.olean_audit("olean-audit", scope="fixture", roots=names, modules=names,
                               maxReportedViolations=200, **extra)
            except runner.Failure as error:
                assert error.code == 1 and error.phase == "olean-audit", (error.code, error.phase, str(error))
                for needle in needles:
                    assert needle in str(error), (needle, str(error))
                return str(error)
            raise AssertionError(f"compiled-environment audit accepted {names} {extra}")

        def olean_accept(ol, names, **extra):
            return ol.olean_audit("olean-audit", scope="fixture", roots=names, modules=names, **extra)

        def olean_raw(ol, names, **extra):
            """Diagnostic run outside the trust gate (no result-schema gate) to observe verdicts."""
            request = {"mode": "olean-audit", "sysroot": str(ol.prefix), "artifacts": sorted(ol.artifacts.items()),
                       "foundation": ol.foundation, "graph": ol.graph, "axioms": ol.lock["axioms"],
                       "roots": names, "modules": names, "scope": "diagnostic", "maxReportedViolations": 200, **extra}
            raw = ol.stage / f"olean-raw-{len(list(ol.stage.glob('olean-raw-*.request.json')))}.request.json"
            res = raw.with_name(raw.name.replace(".request.json", ".response.json"))
            raw.write_text(json.dumps(request))
            try:
                ol.process("olean-diagnostic", ["-j1", "--run", str(ol.olean_auditor), str(raw), str(res)])
            except runner.Failure:
                pass
            return json.loads(res.read_text())

        prelude_init = "prelude\nimport Init\n"

        # Group 19: positive control (inductives, structures, matchers, sparse casesOn, noConfusion,
        # well-founded and structural recursion), the `--audit-olean` request API, and cache trust.
        ol = olean_checker()
        clean_source = prelude_init + (
            "inductive Color where\n  | red | green | blue\nderiving DecidableEq\n"
            "structure Pt where\n  x : Nat\n  y : Nat\nderiving DecidableEq\n"
            "inductive Vec (α : Type) : Nat → Type where\n  | nil : Vec α 0\n  | cons : α → Vec α n → Vec α (n + 1)\n"
            "def Color.next : Color → Color\n  | .red => .green\n  | .green => .blue\n  | .blue => .red\n"
            "def isRed : Color → Bool\n  | .red => true\n  | _ => false\n"
            "def ack : Nat → Nat → Nat\n  | 0, n => n + 1\n  | m + 1, 0 => ack m 1\n"
            "  | m + 1, n + 1 => ack m (ack (m + 1) n)\ntermination_by m n => (m, n)\n"
            "def sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + sumTo n\n"
            "theorem vcons_head {α : Type} {n : Nat} (a b : α) (v w : Vec α n)\n"
            "    (h : Vec.cons a v = Vec.cons b w) : a = b := by injection h\n"
            "theorem red_ne_green : Color.red ≠ Color.green := by decide\n")
        olean_module(ol, "OlClean", clean_source, ["Init"])
        clean_src = str(ol.stage / "olean-src/OlClean.lean")
        clean = olean_accept(ol, ["OlClean"], sources=[("OlClean", clean_src)])
        assert clean["replay"] is True and clean["auditedDeclarations"] > 20 and clean["codegenCompanions"] >= 1
        assert clean["intrinsicTagsChecked"] > 0 and clean["kernelTagConfirmations"] > 0 and clean["irDeclarationsChecked"] > 0
        api = ol.audit_olean_request({"roots": ["OlClean"], "modules": ["OlClean"], "artifacts": [],
                                      "sources": [["OlClean", clean_src]], "scope": "api"})
        assert api["scope"] == "api" and api["auditedDeclarations"] == clean["auditedDeclarations"]
        # A fresh Checker calling `--audit-olean` without optional `graph` must succeed, while
        # attempting to override the locked foundation DAG or pass a symlinked parent dir via
        # `--fast` cache must fail closed.
        clean_parts = ol.artifacts["OlClean"]
        fresh_cache = suite / "olean-api-cache"
        fresh_ol = runner.Checker(fixture(), lean, temp_parent=suite, fast=True, cache_dir=fresh_cache)
        disposable.append(fresh_ol.stage)
        fresh_ol.tool_admission()
        fresh_verdict = fresh_ol.audit_olean_request({
            "roots": ["OlClean"], "modules": ["OlClean"],
            "artifacts": [["OlClean", clean_parts]],
            "sources": [["OlClean", clean_src]], "scope": "fresh-no-graph",
        })
        assert fresh_verdict["replay"] is True and fresh_verdict["auditedDeclarations"] == clean["auditedDeclarations"]
        sym_parent = suite / "olean-sym-parent"
        sym_parent.symlink_to(ol.stage / "olean-lib")
        sym_olean = str(sym_parent / "OlClean.olean")
        fresh_ol2 = runner.Checker(fixture(), lean, temp_parent=suite, fast=True, cache_dir=fresh_cache)
        disposable.append(fresh_ol2.stage)
        fresh_ol2.tool_admission()
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlClean"], "modules": ["OlClean"],
            "artifacts": [["OlClean", [[sym_olean], []]]],
            "sources": [["OlClean", clean_src]], "scope": "fresh-no-graph",
        }), 1, "olean-audit", "moduleProvenanceSpoofed")
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlClean"], "modules": ["OlClean"],
            "artifacts": [["OlClean", clean_parts]],
            "graph": {"Init.Prelude": [{"module": "Fake", "importAll": False, "isExported": True, "isMeta": False}]},
        }), 1, "olean-audit", "locked foundation DAG")
        # `--fast` cache must never return a hit when an artifact path mismatches its module name
        # (even with identical basename and bytes), omits an on-disk companion, swaps olean/IR
        # slots, or splits companion base directories.
        olean_module(ol, "OlSub.Mod", "prelude\nimport Init.Prelude\ndef x : Nat := 1\n", ["Init.Prelude"])
        sub_parts = ol.artifacts["OlSub.Mod"]
        sub_verdict = fresh_ol2.audit_olean_request({
            "roots": ["OlSub.Mod"], "modules": ["OlSub.Mod"],
            "artifacts": [["OlSub.Mod", sub_parts]], "scope": "sub-cache",
        })
        assert sub_verdict["replay"] is True and sub_verdict["modules"] == ["OlSub.Mod"]
        wrong_dir = suite / "olean-wrong-dir/NotSub"
        wrong_dir.mkdir(parents=True)
        wrong_olean = wrong_dir / "Mod.olean"
        shutil.copyfile(sub_parts[0][0], wrong_olean)
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlSub.Mod"], "modules": ["OlSub.Mod"],
            "artifacts": [["OlSub.Mod", [[str(wrong_olean)], []]]], "scope": "sub-cache",
        }), 1, "olean-audit", "moduleProvenanceSpoofed", "does not match the module name")
        omit_dir = suite / "olean-omit-dir/OlSub"
        omit_dir.mkdir(parents=True)
        omit_olean = omit_dir / "Mod.olean"
        shutil.copyfile(sub_parts[0][0], omit_olean)
        (omit_dir / "Mod.olean.private").write_bytes(b"omitted companion")
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlSub.Mod"], "modules": ["OlSub.Mod"],
            "artifacts": [["OlSub.Mod", [[str(omit_olean)], []]]], "scope": "sub-cache",
        }), 1, "olean-audit", "missingPrivateArtifact", "exists but was omitted")
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlSub.Mod"], "modules": ["OlSub.Mod"],
            "artifacts": [["OlSub.Mod", [[], [sub_parts[0][0]]]]], "scope": "sub-cache",
        }), 1, "olean-audit", "missingPrivateArtifact")
        olean_module(ol, "OlFastMod", "module\nprelude\npublic import Init.Prelude\npublic def y : Nat := 1\n",
                     ["Init.Prelude"], module_file=True)
        fm_parts = ol.artifacts["OlFastMod"]
        fm_verdict = fresh_ol2.audit_olean_request({
            "roots": ["OlFastMod"], "modules": ["OlFastMod"],
            "artifacts": [["OlFastMod", fm_parts]], "scope": "fm-cache",
        })
        assert fm_verdict["replay"] is True
        split_dir = suite / "olean-split-base"
        split_dir.mkdir()
        split_priv = split_dir / "OlFastMod.olean.private"
        shutil.copyfile(fm_parts[0][2], split_priv)
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlFastMod"], "modules": ["OlFastMod"],
            "artifacts": [["OlFastMod", [[fm_parts[0][0], fm_parts[0][1], str(split_priv)], fm_parts[1]]]],
            "scope": "fm-cache",
        }), 1, "olean-audit", "moduleProvenanceSpoofed", "canonical companions")
        # `--fast` cache-key sensitivity for constructive policy (`allowClassicalChoice` & `constructiveModules`).
        olean_module(ol, "OlFastChoice", prelude_init + "noncomputable def fcChoice : Nat := Classical.choice ⟨0⟩\n",
                     ["Init"])
        fc_parts = ol.artifacts["OlFastChoice"]
        ok_fc = fresh_ol2.audit_olean_request({
            "roots": ["OlFastChoice"], "modules": ["OlFastChoice"],
            "artifacts": [["OlFastChoice", fc_parts]],
            "allowClassicalChoice": True, "scope": "ep2-cache-key",
        })
        assert "Classical.choice" in ok_fc["axioms"], ok_fc
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlFastChoice"], "modules": ["OlFastChoice"],
            "artifacts": [["OlFastChoice", fc_parts]],
            "allowClassicalChoice": False, "scope": "ep2-cache-key",
        }), 1, "olean-audit", "Classical.choice")
        expect_failure(lambda: fresh_ol2.audit_olean_request({
            "roots": ["OlFastChoice"], "modules": ["OlFastChoice"],
            "artifacts": [["OlFastChoice", fc_parts]],
            "constructiveModules": ["OlFastChoice"], "scope": "ep2-cache-key",
        }), 1, "olean-audit", "Classical.choice")
        shutil.rmtree(wrong_dir.parent, ignore_errors=True)
        shutil.rmtree(omit_dir.parent, ignore_errors=True)
        shutil.rmtree(split_dir, ignore_errors=True)
        shutil.rmtree(fresh_cache, ignore_errors=True)
        sym_parent.unlink()
        expect_failure(lambda: ol.olean_audit("olean-audit", scope="fixture", roots=["Init.Prelude"], modules=[]),
                       1, "olean-audit", "no audited modules")
        # A caller can neither supply nor name `Trusted` modules in any field: a forged `Trusted`
        # redefining `VerificationResult` or relaxing local axioms would compromise claims.
        for spoof in ({"roots": ["OlClean"], "modules": ["OlClean", "Trusted"], "artifacts": []},
                      {"roots": ["Trusted.Fake"], "modules": ["Trusted.Fake"],
                       "artifacts": [["Trusted.Fake", clean_parts]]},
                      {"roots": ["OlClean"], "modules": ["OlClean"], "artifacts": [],
                       "localAxiomModules": ["Trusted"]},
                      {"roots": ["OlClean"], "modules": ["OlClean"], "artifacts": [],
                       "sources": [["Trusted", clean_src]]}):
            expect_failure(lambda: ol.audit_olean_request(spoof), 1, "olean-audit",
                           "moduleProvenanceSpoofed", "Trusted modules")
        # After `run()`, requests are audited together with the checker's own `Trusted` artifacts,
        # and repeated `audit_olean_request` calls must not pollute `Checker` state.
        api_ol = runner.Checker(fixture(header + "def VerificationResult (p : Prop) : Prop := p\n"), lean,
                                temp_parent=suite)
        disposable.append(api_ol.stage)
        api_ol.run()
        olean_module(api_ol, "OlApiClaim", "prelude\nimport Trusted\n"
                     "theorem verified : VerificationResult True := True.intro\n", ["Trusted"])
        api_claim_parts = api_ol.artifacts.pop("OlApiClaim")
        api_claim_edges = api_ol.graph.pop("OlApiClaim")
        for _ in range(2):
            api_claim = api_ol.audit_olean_request({
                "roots": ["OlApiClaim"], "modules": ["OlApiClaim"],
                "artifacts": [["OlApiClaim", api_claim_parts]],
                "graph": {"OlApiClaim": api_claim_edges},
            })
            assert api_claim["modules"] == ["OlApiClaim", "Trusted"] and api_claim["replay"] is True, api_claim
        expect_failure(lambda: ol.audit_olean_request({"roots": ["OlClean"], "modules": ["OlClean"], "artifacts": [],
                                                       "allowProvisionalNative": True}),
                       2, "olean-audit", "malformed --audit-olean request")
        expect_failure(lambda: ol.audit_olean_request({"roots": ["OlClean"], "modules": ["OlClean"], "artifacts": [],
                                                       "sources": [["OlClean", clean_src], ["OlClean", clean_src]]}),
                       2, "olean-audit", "malformed --audit-olean sources")
        bad_hb = olean_raw(ol, ["OlClean"], nativeHeartbeats=0)
        assert bad_hb["ok"] is False and "nativeHeartbeats" in bad_hb["message"], bad_hb
        bad_graph = olean_raw(ol, ["OlClean"], graph={"OlClean": ol.graph["OlClean"]})
        assert bad_graph["ok"] is False and "foundation module missing" in bad_graph["message"], bad_graph
        cache_probe = suite / "cache-probe"
        cache_probe.write_text("{}")
        cache_probe.chmod(0o644)
        assert runner._trusted_cache_file(cache_probe)
        cache_probe.chmod(0o664)
        assert not runner._trusted_cache_file(cache_probe)
        cache_probe.unlink()
        # `_restore_cached_module` must also refuse world/group-writable cache entries.
        bad_cache = suite / "bad-olean-cache"
        bad_entry = bad_cache / "olean" / "badkey"
        bad_entry.mkdir(parents=True)
        (bad_entry / "artifact.olean").write_bytes(b"tampered")
        (bad_entry / "artifact.olean").chmod(0o666)
        (bad_entry / "meta.json").write_text(json.dumps({"olean": runner.digest(bad_entry / "artifact.olean")}))
        (bad_entry / "meta.json").chmod(0o666)
        bad_rc = runner.Checker(fixture(), lean, temp_parent=suite, fast=True, cache_dir=bad_cache)
        disposable.append(bad_rc.stage)
        assert not bad_rc._restore_cached_module("BadMod", "badkey", bad_rc.stage / "BadMod.olean")
        shutil.rmtree(bad_cache, ignore_errors=True)
        # Symlinked or world-writable `cache/inspect` directories must never be read or written.
        sym_cache = suite / "sym-inspect-cache"
        sym_target = suite / "sym-inspect-target"
        sym_cache.mkdir(mode=0o700)
        sym_target.mkdir(mode=0o700)
        (sym_cache / "inspect").symlink_to(sym_target)
        assert not runner._ensure_trusted_cache_dir(sym_cache, sym_cache / "inspect")
        (sym_target / "probe.json").write_text("{}")
        assert not runner._trusted_cache_tree(sym_cache, sym_cache / "inspect" / "probe.json")
        ww_cache = suite / "ww-inspect-cache"
        (ww_cache / "inspect").mkdir(parents=True)
        (ww_cache / "inspect").chmod(0o777)
        (ww_cache / "inspect" / "probe.json").write_text("{}")
        assert not runner._trusted_cache_tree(ww_cache, ww_cache / "inspect" / "probe.json")
        assert not runner._ensure_trusted_cache_dir(ww_cache, ww_cache / "inspect")
        shutil.rmtree(sym_cache, ignore_errors=True)
        shutil.rmtree(sym_target, ignore_errors=True)
        shutil.rmtree(ww_cache, ignore_errors=True)
        done("compiled-environment auditor: 0-FP positive control, --audit-olean API, cache trust")

        # Group 20: artifact completeness and all-parts provenance. A `module` file's private axiom
        # lives only in `.olean.private`; omitted, deleted, reordered, or symlinked companions and
        # toolchain-named artifacts are rejected.
        mod_header = "module\nprelude\npublic import Init.Core\n"
        olean_module(ol, "OlMod", mod_header + "private axiom hiddenBackdoor : False\n"
                     "public theorem sneaky : True := hiddenBackdoor.elim\n", ["Init.Core"], module_file=True)
        olean_reject(ol, ["OlMod"], "[unapprovedAxiom]", "hiddenBackdoor")
        mod_parts = olean_module(ol, "OlModClean", mod_header + "public def pubFn (n : Nat) : Nat := n + 1\n"
                                 "def privFn (n : Nat) : Nat := n + 2\ntheorem privFn_eq : privFn 0 = 2 := rfl\n",
                                 ["Init.Core"], module_file=True)
        assert set(mod_parts) == set(runner.PARTS)
        olean_accept(ol, ["OlModClean"])
        genuine = [list(g) for g in ol.artifacts["OlModClean"]]
        ol.artifacts["OlModClean"] = [[genuine[0][0]], genuine[1]]
        olean_reject(ol, ["OlModClean"], "[missingPrivateArtifact]", "exists but was omitted")
        ol.artifacts["OlModClean"] = [[genuine[0][0], genuine[0][2], genuine[0][1]], genuine[1]]
        olean_reject(ol, ["OlModClean"], "[moduleProvenanceSpoofed]", "canonical companions")
        ol.artifacts["OlModClean"] = [genuine[0], []]
        olean_reject(ol, ["OlModClean"], "[missingPrivateArtifact]")
        evil = ol.stage / "evil-artifacts"
        evil.mkdir()
        for part in runner.PARTS:
            (evil / f"OlModClean.{part}").symlink_to(mod_parts[part])
        ol.artifacts["OlModClean"] = [[str(evil / f"OlModClean.{p}") for p in runner.PARTS[:3]],
                                      [str(evil / f"OlModClean.{p}") for p in runner.PARTS[3:]]]
        olean_reject(ol, ["OlModClean"], "[moduleProvenanceSpoofed]", "resolves to")
        split = ol.stage / "split-artifacts"
        split.mkdir()
        for part in runner.PARTS:
            shutil.copyfile(mod_parts[part], split / f"OlModClean.{part}")
        (split / "OlModClean.olean.private").unlink()
        (split / "OlModClean.olean.private").symlink_to(ol.artifacts["OlMod"][0][2])
        ol.artifacts["OlModClean"] = [[str(split / f"OlModClean.{p}") for p in runner.PARTS[:3]],
                                      [str(split / f"OlModClean.{p}") for p in runner.PARTS[3:]]]
        olean_reject(ol, ["OlModClean"], "[moduleProvenanceSpoofed]", "OlModClean.olean.private")
        for part in ("ir", "ir.sig"):
            Path(mod_parts[part]).unlink()
        ol.artifacts["OlModClean"] = [genuine[0], []]
        olean_reject(ol, ["OlModClean"], "[missingPrivateArtifact]", "module-system file")
        del ol.artifacts["OlModClean"]  # Its IR is gone; every audited artifact entry must be intact.
        olean_module(ol, "OlUsesZero", "prelude\nimport Init.Data.Zero\ndef usesZero : Nat := 0\n", ["Init.Data.Zero"])
        spoof = ol.stage / "toolchain-spoof/Init/Data"
        spoof.mkdir(parents=True)
        zero_parts = [[], []]
        for part in runner.PARTS:
            shutil.copyfile(ol.prefix / "lib/lean/Init/Data" / f"Zero.{part}", spoof / f"Zero.{part}")
            zero_parts[0 if part.startswith("olean") else 1].append(str(spoof / f"Zero.{part}"))
        ol.artifacts["Init.Data.Zero"] = zero_parts
        olean_reject(ol, ["OlUsesZero"], "[moduleProvenanceSpoofed]", "toolchain-named module")
        del ol.artifacts["Init.Data.Zero"]
        # Standalone `OleanEnvAuditor` must also refuse a spoofed `Init.Core` passed via `foundation`
        # + `artifacts` (whose bytes/parts do not match `<sysroot>/lib/lean/Init/Core.*`).
        fspoof = ol.stage / "foundation-spoof"
        (fspoof / "Init").mkdir(parents=True)
        (fspoof / "Init/Core.lean").write_text("prelude\ninductive MyFalse : Prop\naxiom propext : MyFalse\n")
        fsp_setup = fspoof / "InitCore.setup.json"
        fsp_setup.write_text(json.dumps({"name": "Init.Core", "isModule": False, "imports": [],
                                         "importArts": {}, "dynlibs": [], "plugins": [], "options": {}}))
        ol.process("olean-fixture-InitCoreSpoof", ["-j1", "-M2048", "-t0", "--setup", str(fsp_setup),
                                                   "-o", str(fspoof / "Init/Core.olean"), str(fspoof / "Init/Core.lean")])
        (fspoof / "OlSpoofVic.lean").write_text("prelude\nimport Init.Core\ntheorem provenFalse : MyFalse := propext\n")
        fsp_setup2 = fspoof / "OlSpoofVic.setup.json"
        fsp_setup2.write_text(json.dumps({
            "name": "OlSpoofVic", "isModule": False,
            "imports": [{"module": "Init.Core", "importAll": False, "isExported": True, "isMeta": False}],
            "importArts": {"Init.Core": [[str(fspoof / "Init/Core.olean")], []]},
            "dynlibs": [], "plugins": [], "options": {},
        }))
        ol.process("olean-fixture-OlSpoofVic", ["-j1", "-M2048", "-t0", "--setup", str(fsp_setup2),
                                                "-o", str(fspoof / "OlSpoofVic.olean"), str(fspoof / "OlSpoofVic.lean")])
        fsp_req = {"mode": "olean-audit", "sysroot": str(ol.prefix), "foundation": ["Init.Core"],
                   "artifacts": [["Init.Core", [[str(fspoof / "Init/Core.olean")], []]],
                                 ["OlSpoofVic", [[str(fspoof / "OlSpoofVic.olean")], []]]],
                   "roots": ["OlSpoofVic"], "modules": ["OlSpoofVic"],
                   "axioms": [["propext", "Init.Core"]], "scope": "foundation-spoof"}
        fsp_raw = ol.stage / "olean-raw-foundation-spoof.request.json"
        fsp_res = ol.stage / "olean-raw-foundation-spoof.response.json"
        fsp_raw.write_text(json.dumps(fsp_req))
        try:
            ol.process("olean-diagnostic", ["-j1", "--run", str(ol.olean_auditor), str(fsp_raw), str(fsp_res)])
        except runner.Failure:
            pass
        fsp_verdict = json.loads(fsp_res.read_text())
        assert fsp_verdict["ok"] is False and "[moduleProvenanceSpoofed]" in fsp_verdict["message"], fsp_verdict
        olean_accept(ol, ["OlUsesZero"])
        done("hidden private axiom, omitted/reordered/deleted companions, split-part and toolchain/foundation provenance spoofing")

        # Group 21: `partial`, `unsafe`, and forged `_unsafe_rec` code-generation companions (a
        # sibling replaces the compiled code of its parent with no attribute), including a stdlib
        # parent, an opaque parent, and a structurally recursive (non-partial) forged sibling; plus
        # the source-level identifier rule.
        rec_source = prelude_init + (
            "partial def loopy (n : Nat) : Nat := loopy (n + 1)\n"
            "unsafe def danger (n : Nat) : Nat := n\n"
            "def victim._unsafe_rec (n : Nat) : Nat := n + 1\ndef victim (n : Nat) : Nat := n\n"
            "def Bool.xor._unsafe_rec (a _b : Bool) : Bool := a\n"
            "opaque op : Nat → Nat\ndef op._unsafe_rec (n : Nat) : Nat := n\n"
            "noncomputable def selfRec._unsafe_rec : Nat → Nat\n  | 0 => 0\n  | n + 1 => selfRec._unsafe_rec n + 2\n"
            "noncomputable def selfRec (n : Nat) : Nat := n\n")
        olean_module(ol, "OlRec", rec_source, ["Init"])
        olean_reject(ol, ["OlRec"], "[partialOrUnsafeRecDependency] loopy", "[unsafeDeclaration] danger",
                     "[compilerOverrideAttribute] victim._unsafe_rec", "[compilerOverrideAttribute] Bool.xor._unsafe_rec",
                     "[compilerOverrideAttribute] op._unsafe_rec", "[compilerOverrideAttribute] selfRec._unsafe_rec",
                     "unsafe_rec_sibling", "[sourceForbiddenIdentifier]",
                     sources=[("OlRec", str(ol.stage / "olean-src/OlRec.lean"))])
        # Reaching an `Init` `partial def` (opaque + partial `_unsafe_rec` sibling) must be caught
        # in the dependency closure, and `Char` literals `'"'` or interpolated strings `s!"..."`
        # must not blind the source-level `_unsafe_rec` identifier scanner.
        olean_module(ol, "OlStdPartial", "prelude\nimport Init.Prelude\n"
                     "def callsStdPartial (s : Lean.Syntax) : Option Lean.SourceInfo := Lean.Syntax.getHeadInfo? s\n",
                     ["Init.Prelude"])
        olean_reject(ol, ["OlStdPartial"], "[partialOrUnsafeRecDependency] Lean.Syntax.getHeadInfo?")
        olean_module(ol, "OlScanBlind", prelude_init + (
            "def quoteChar : Char := '\"'\n"
            "def after_char_unsafe_rec (n : Nat) : Nat := n\n"
            "def interpStr : String := s!\"{let inside_interp_unsafe_rec := 1; inside_interp_unsafe_rec}\"\n"),
            ["Init"])
        olean_reject(ol, ["OlScanBlind"], "[sourceForbiddenIdentifier] after_char_unsafe_rec",
                     "[sourceForbiddenIdentifier] inside_interp_unsafe_rec",
                     sources=[("OlScanBlind", str(ol.stage / "olean-src/OlScanBlind.lean"))])
        done("partial/unsafe declarations, stdlib partial closure, forged _unsafe_rec siblings, and hardened source scan")

        # Group 22: compiler overrides persisted in compiled artifacts: implemented_by, extern,
        # export, initialize, @[csimp] redirecting a stdlib function, @[scoped csimp], and an erased
        # @[local csimp] whose lemma is audited as an inventory root (sorry / custom axiom).
        override_source = prelude_init + (
            "def evilImpl (n : Nat) : Nat := n + 1000\n"
            "@[implemented_by evilImpl] def ib (n : Nat) : Nat := n\n"
            "@[extern \"anneal_fixture_c_fn\"] def ext (n : Nat) : Nat := n\n"
            "@[export anneal_fixture_sym] def exp (n : Nat) : Nat := n\n"
            "def evilAdd (_a _b : Nat) : Nat := 999\naxiom csimpAx : @Nat.add = @evilAdd\n"
            "@[csimp] theorem redirect : @Nat.add = @evilAdd := csimpAx\n"
            "def evilMul (_a _b : Nat) : Nat := 7\n"
            "namespace Scoped\n@[scoped csimp] theorem redirectMul : @Nat.mul = @evilMul := sorry\nend Scoped\n"
            "def evilSub (_a _b : Nat) : Nat := 5\n"
            "section\n@[local csimp] theorem redirectSub : @Nat.sub = @evilSub := sorry\n"
            "def localCaller (a b : Nat) : Nat := Nat.sub a b\nend\n"
            "initialize initFlag : Bool ← pure true\n")
        olean_module(ol, "OlOverride", override_source, ["Init"])
        olean_reject(ol, ["OlOverride"], "[compilerOverrideAttribute] ib", "implemented_by",
                     "[compilerOverrideAttribute] ext", "extern", "[compilerOverrideAttribute] exp", "export",
                     "[compilerOverrideAttribute] Nat.add", "csimp: Nat.add", "csimp: Nat.mul",
                     "[compilerOverrideAttribute] initFlag", "init", "[unapprovedAxiom] csimpAx",
                     "[sorryAxiomReached] sorryAx")
        done("implemented_by/extern/export/init and stdlib, scoped, and erased local csimp redirections")

        # Group 23: compiler state forged by a metaprogram (needs `import Lean`): a persisted csimp
        # entry reusing the genuine List.map triple, a @[cpass] installer, a constant folder, and
        # forged casesOn / sparseCasesOn / noConfusion compiler-intrinsic tags. A default audit
        # rejects any Lean-library module outright; an audit that admits the Lean library still
        # rejects every forged entry.
        forged_source = "prelude\nimport Init\nimport Lean\nopen Lean\n" + (
            "def victimF (n : Nat) : Nat := n\n"
            "run_cmd Lean.modifyEnv fun env => Lean.Compiler.LCNF.Simp.ConstantFold.folderExt.addEntry env "
            "{ declName := `victimF, folderDeclName := `forgedFolder, folder := fun _ => pure none }\n"
            "run_cmd Lean.Compiler.CSimp.ext.add "
            "{ fromDeclName := ``List.map, toDeclName := ``List.mapTR, thmName := ``List.map_eq_mapTR }\n"
            "def FakeT.casesOn (_n : Nat) : Nat := 1\n"
            "run_cmd Lean.modifyEnv (Lean.markAuxRecursor · ``FakeT.casesOn)\n"
            "def sparseFake (_n : Nat) : Nat := 1\n"
            "run_cmd Lean.modifyEnv (Lean.markSparseCasesOn · ``sparseFake)\n"
            "def ncFake (_n : Nat) : Nat := 1\n"
            "run_cmd Lean.modifyEnv (Lean.markNoConfusion · ``ncFake (.perCtor 1 0))\n"
            "run_cmd Lean.modifyEnv fun env => Lean.Compiler.LCNF.passManagerExt.addEntry env "
            "(`forgedInstaller, Lean.Compiler.LCNF.builtinPassManager)\n")
        olean_module(ol, "OlForged", forged_source, ["Init", "Lean"])
        olean_reject(ol, ["OlForged"], "[foreignModule] Lean")
        olean_reject(ol, ["OlForged"], "csimp: List.map", "cpass: compiler pass installer", "constant_fold: folder forgedFolder",
                     "casesOn_tag", "FakeT.casesOn", "sparse_casesOn_tag", "sparseFake", "noConfusion_tag", "ncFake",
                     toolchainRoots=["Init", "Std", "Lean"])
        # Forged `_sparseCasesOn` with `.default` BEFORE `.ctor` (compiled IR short-circuits to the
        # default branch even though per-ctor kernel equations hold), duplicate `.default`, and
        # forged IR calling toolchain `unsafeBaseIO` must all be rejected.
        forged_sem_source = "prelude\nimport Init\nimport Lean\n" + (
            "inductive FTwo where | a | b\n"
            "def FTwo._sparseCasesOn_rev.{u} {motive : FTwo → Sort u} (t : FTwo)\n"
            "    (dflt : motive t) (altA : motive .a) : motive t :=\n"
            "  FTwo.casesOn (motive := fun x => motive x → motive x) t (fun _ => altA) (fun d => d) dflt\n"
            "run_cmd Lean.modifyEnv (Lean.markSparseCasesOn · ``FTwo._sparseCasesOn_rev)\n"
            "def FTwo._sparseCasesOn_dupdef.{u} {motive : FTwo → Sort u} (t : FTwo)\n"
            "    (d1 : motive t) (d2 : motive t) : motive t := d1\n"
            "run_cmd Lean.modifyEnv (Lean.markSparseCasesOn · ``FTwo._sparseCasesOn_dupdef)\n"
            "def irUnsafeVictim (n : Nat) : Nat := n\n"
            "run_cmd Lean.modifyEnv fun env =>\n"
            "  let d := Lean.IR.Decl.fdecl ``irUnsafeVictim #[{ x := ⟨1⟩, borrow := false, ty := .object }] .object\n"
            "    (.vdecl ⟨2⟩ .object (.fap ``unsafeBaseIO #[.var ⟨1⟩]) (.ret (.var ⟨2⟩))) {}\n"
            "  Lean.IR.declMapExt.addEntry env d\n")
        olean_module(ol, "OlForgedSem", forged_sem_source, ["Init", "Lean"])
        olean_reject(ol, ["OlForgedSem"],
                     "FTwo._sparseCasesOn_rev", "constructor alternative appears after default alternative",
                     "FTwo._sparseCasesOn_dupdef", "duplicate default alternative",
                     "[unsafeDeclaration] unsafeBaseIO", "duplicate IR declaration entry",
                     toolchainRoots=["Init", "Std", "Lean"])
        # Forged LCNF compiler-extension state (ElimDeadBranches summary, baseExt/monoExt
        # duplicates, single uncompiled IR entry via `Lean.addDecl`, forged `_unsafe_rec`
        # companion on a non-recursive def, and non-Prop side binder in `_sparseCasesOn`).
        forged_lcnf_source = "prelude\nimport Init\nimport Lean\n" + (
            "inductive FSide where | a | b\n"
            "def FSide._sparseCasesOn_side.{u} {motive : FSide → Sort u} (t : FSide)\n"
            "    (_extra : Nat) (altA : motive .a) (altB : motive .b) : motive t :=\n"
            "  FSide.casesOn t altA altB\n"
            "run_cmd Lean.modifyEnv (Lean.markSparseCasesOn · ``FSide._sparseCasesOn_side)\n"
            "@[noinline] def fDeadFlag (b : Bool) : Bool := b\n"
            "run_cmd Lean.modifyEnv fun env =>\n"
            "  Lean.Compiler.LCNF.UnreachableBranches.addFunctionSummary env ``fDeadFlag (.ctor ``Bool.true #[])\n"
            "@[inline] def fBaseVictim (n : Nat) : Nat := n\n"
            "def fMonoVictim (n : Nat) : Nat := n\n"
            "def fEvilConst (_ : Nat) : Nat := 999\n"
            "run_cmd do\n"
            "  let env ← Lean.getEnv\n"
            "  let some eb := Lean.Compiler.LCNF.getDeclCore? env Lean.Compiler.LCNF.baseExt ``fEvilConst | throwError \"no b\"\n"
            "  let some em := Lean.Compiler.LCNF.getDeclCore? env Lean.Compiler.LCNF.monoExt ``fEvilConst | throwError \"no m\"\n"
            "  Lean.modifyEnv fun e =>\n"
            "    let e := Lean.Compiler.LCNF.baseExt.addEntry e { eb with name := ``fBaseVictim }\n"
            "    Lean.Compiler.LCNF.monoExt.addEntry e { em with name := ``fMonoVictim }\n"
            "run_cmd Lean.Elab.Command.liftCoreM do\n"
            "  let natTy := Lean.mkConst ``Nat\n"
            "  let fnTy := Lean.Expr.forallE `n natTy natTy .default\n"
            "  let idVal := Lean.Expr.lam `n natTy (.bvar 0) .default\n"
            "  Lean.addDecl (.defnDecl { name := `fGhost, levelParams := [], type := fnTy, value := idVal, hints := .abbrev, safety := .safe })\n"
            "  let env ← Lean.getEnv\n"
            "  let some tplIR := Lean.IR.findEnvDecl env ``fEvilConst | throwError \"no ir\"\n"
            "  let some tplSig := Lean.Compiler.LCNF.getSigCore? env Lean.Compiler.LCNF.impureSigExt ``fEvilConst | throwError \"no sig\"\n"
            "  let forgedIR := match tplIR with | .fdecl _ xs ty b info => .fdecl `fGhost xs ty b info | o => o\n"
            "  Lean.modifyEnv fun e =>\n"
            "    Lean.IR.declMapExt.addEntry (Lean.Compiler.LCNF.impureSigExt.addEntry e { tplSig with name := `fGhost }) forgedIR\n"
            "  let pName := `fNonRec\n"
            "  let recName := Lean.Name.str pName (\"_unsafe\" ++ \"_rec\")\n"
            "  let parentDecl := Lean.Declaration.defnDecl { name := pName, levelParams := [], type := fnTy, value := idVal, hints := .abbrev, safety := .safe }\n"
            "  Lean.addDecl parentDecl\n"
            "  let motive := Lean.Expr.lam `_ natTy natTy .default\n"
            "  let succCase := Lean.Expr.lam `_ natTy (Lean.Expr.app (Lean.mkConst recName) (Lean.mkConst ``Nat.zero)) .default\n"
            "  let body := Lean.mkApp4 (Lean.mkConst ``Nat.casesOn [.succ .zero]) motive (.bvar 0) (Lean.mkRawNatLit 999) succCase\n"
            "  Lean.addDecl (.mutualDefnDecl [{ name := recName, levelParams := [], type := fnTy, value := Lean.Expr.lam `n natTy body .default, hints := .opaque, safety := .partial }])\n"
            "  Lean.compileDecl parentDecl\n")
        olean_module(ol, "OlForgedLcnf", forged_lcnf_source, ["Init", "Lean"])
        olean_reject(ol, ["OlForgedLcnf"],
                     "FSide._sparseCasesOn_side", "side condition is not a Prop",
                     "fDeadFlag", "dead_branch_summary",
                     "fBaseVictim", "lcnf_ir_mismatch",
                     "fMonoVictim",
                     "fGhost", "IR body for definition without base-phase LCNF declaration",
                     "fNonRec", "does not use a recursion combinator",
                     toolchainRoots=["Init", "Std", "Lean"])
        # A forged companion whose parent merely mentions some `Lean.*` constant (or a bare
        # recursor) is not an equation-compiler companion: only well-founded / `brecOn` /
        # `Lean.Order` fixpoint encodings count as recursion combinators.
        forged_comp_source = "prelude\nimport Init\nimport Lean\nopen Lean\n" + (
            "def cNr (n : Nat) : Nat := n + Lean.Name.anonymous.hash.toNat * 0\n"
            "noncomputable def cNr2 (n : Nat) : Nat := Nat.rec n (fun _ ih => ih) 0\n"
            "run_cmd Elab.Command.liftCoreM do\n"
            "  for p in [`cNr, `cNr2] do\n"
            "    let c := p ++ Name.mkSimple (\"_unsafe\" ++ \"_rec\")\n"
            "    let ty ← mkArrow (mkConst ``Nat) (mkConst ``Nat)\n"
            "    let body := mkLambda `n .default (mkConst ``Nat)\n"
            "      (mkApp4 (mkConst ``Nat.rec [1]) (mkLambda `x .default (mkConst ``Nat) (mkConst ``Nat)) (mkNatLit 999)\n"
            "        (mkLambda `k .default (mkConst ``Nat) (mkLambda `ih .default (mkConst ``Nat) (mkApp (mkConst c) (mkBVar 1))))\n"
            "        (mkBVar 0))\n"
            "    addDecl (.mutualDefnDecl [{ name := c, levelParams := [], type := ty, value := body, hints := .opaque, safety := .partial }])\n")
        olean_module(ol, "OlForgedCompanion", forged_comp_source, ["Init", "Lean"])
        olean_reject(ol, ["OlForgedCompanion"], "cNr._unsafe_rec", "cNr2._unsafe_rec", "does not use a recursion combinator",
                     toolchainRoots=["Init", "Std", "Lean"])
        # B4 regressions: `LCNF.Specialize.specCacheExt` hijacking to a pure kernel def,
        # `ElimDeadBranches` forged summary on a non-trivial (`SimpleRet.other`) Bool function,
        # forged companion on a parent using `WellFounded.fix` with extra constants/literals, and
        # simultaneous 3-phase (`base`+`mono`+`IR`) forgery contradicting a simple kernel body.
        forged_b4_source = "prelude\nimport Init\nimport Lean\nopen Lean\n" + (
            "@[specialize, noinline] def b4Apply (f : Nat → Nat) (x : Nat) : Nat :=\n"
            "  match x with | 0 => f 0 | n + 1 => b4Apply f n + f (n + 1)\n"
            "@[noinline] def b4Inc (n : Nat) : Nat := n + 1\n"
            "@[noinline] def b4EvilSpec (_ : Nat) : Nat := 999\n"
            "run_cmd Elab.Command.liftCoreM <|\n"
            "  Lean.Compiler.LCNF.Specialize.cacheSpec (mkApp (mkConst ``b4Apply) (mkConst ``b4Inc)) ``b4EvilSpec\n"
            "@[noinline] def b4SpecVictim (x : Nat) : Nat := b4Apply b4Inc x\n"
            "@[noinline] def b4PredOther (n : Nat) : Bool := n == 0\n"
            "run_cmd modifyEnv fun env =>\n"
            "  Lean.Compiler.LCNF.UnreachableBranches.addFunctionSummary env ``b4PredOther (.ctor ``Bool.true #[])\n"
            "def b4WfTpl (n : Nat) : Nat := WellFounded.fix (r := (· < ·)) Nat.lt_wfRel.wf (fun k _ => k) n\n"
            "@[noinline] def b4ThreeDonor (_ : Nat) : Nat := 999\n"
            "run_cmd Elab.Command.liftCoreM do\n"
            "  let nat := mkConst ``Nat\n"
            "  let ty := mkForall `n .default nat nat\n"
            "  let pName := `b4WfSneaky\n"
            "  let recName := pName.str (\"_unsafe\" ++ \"_rec\")\n"
            "  let tplVal := (← getConstInfo ``b4WfTpl).value!\n"
            "  let pDecl := Declaration.defnDecl { name := pName, levelParams := [], type := ty, value := tplVal, hints := .abbrev, safety := .safe }\n"
            "  addDecl pDecl\n"
            "  let mot := mkLambda `k .default nat nat\n"
            "  let body := mkLambda `n .default nat (mkApp4 (mkConst ``Nat.casesOn [Level.one]) mot (mkBVar 0) (mkNatLit 999) (mkLambda `m .default nat (mkApp (mkConst recName) (mkBVar 0))))\n"
            "  addDecl (.mutualDefnDecl [{ name := recName, levelParams := [], type := ty, value := body, hints := .opaque, safety := .partial }])\n"
            "  compileDecl pDecl\n"
            "  addDecl (.defnDecl { name := `b4ThreeVictim, levelParams := [], type := ty, value := mkLambda `n .default nat (mkNatLit 1), hints := .abbrev, safety := .safe })\n"
            "  let env ← getEnv\n"
            "  let some bd := Lean.Compiler.LCNF.getDeclCore? env Lean.Compiler.LCNF.baseExt ``b4ThreeDonor | throwError \"no b\"\n"
            "  let some md := Lean.Compiler.LCNF.getDeclCore? env Lean.Compiler.LCNF.monoExt ``b4ThreeDonor | throwError \"no m\"\n"
            "  let some sg := Lean.Compiler.LCNF.getSigCore? env Lean.Compiler.LCNF.impureSigExt ``b4ThreeDonor | throwError \"no s\"\n"
            "  let some ir := Lean.IR.findEnvDecl env ``b4ThreeDonor | throwError \"no ir\"\n"
            "  let ir' := match ir with | .fdecl _ xs t b i => .fdecl `b4ThreeVictim xs t b i | o => o\n"
            "  modifyEnv fun e =>\n"
            "    let e := Lean.Compiler.LCNF.baseExt.addEntry e { bd with name := `b4ThreeVictim }\n"
            "    let e := Lean.Compiler.LCNF.monoExt.addEntry e { md with name := `b4ThreeVictim }\n"
            "    let e := Lean.Compiler.LCNF.impureSigExt.addEntry e { sg with name := `b4ThreeVictim }\n"
            "    Lean.IR.declMapExt.addEntry e ir'\n")
        olean_module(ol, "OlForgedB4", forged_b4_source, ["Init", "Lean"])
        olean_reject(ol, ["OlForgedB4"],
                     "b4EvilSpec", "specialize_cache",
                     "b4PredOther", "dead_branch_summary",
                     "b4WfSneaky._unsafe_rec", "absent from parent closure",
                     "b4ThreeVictim", "lcnf_ir_mismatch",
                     toolchainRoots=["Init", "Std", "Lean"])
        done("metaprogram-forged csimp/cpass/folder/LCNF/specCache/companion state, intrinsic tags, IR-unsafe, Lean library foreign")

        # Group 24: separate compilation (`-Dcompiler.postponeCompile=true`) of a `module` file
        # writes no IR for public or private functions.
        olean_module(ol, "OlPostponed", mod_header + "public def ppPublic (n : Nat) : Nat := n + 1\n"
                     "def ppPriv (n : Nat) : Nat := n + 2\n", ["Init.Core"], module_file=True,
                     flags=("-Dcompiler.postponeCompile=true",))
        olean_reject(ol, ["OlPostponed"], "[missingPrivateArtifact]", "[environmentLoadFailed]", "postponed")
        done("separate-compilation module files without IR")

        # Group 25: native evaluation. Trust-gating audits reject native_decide; a diagnostic
        # re-check refutes forged native axioms (including `_sunfold` steering and spoofed shapes)
        # by the kernel, confirms a genuine one, and never passes an axiom that stays provisional;
        # the gate rejects even kernel-confirmed native axioms (constraint 4).
        olean_module(ol, "OlNative", prelude_init + "theorem nd : (2 + 2 == 4) = true := by native_decide\n", ["Init"])
        olean_reject(ol, ["OlNative"], "[nativeDecideReached]")
        diag = olean_raw(ol, ["OlNative"], allowProvisionalNative=True)
        assert diag["ok"] is True and len(diag["result"]["kernelConfirmedNativeAxioms"]) == 1, diag
        expect_failure(lambda: ol.olean_audit("olean-audit", scope="fixture", roots=["OlNative"], modules=["OlNative"],
                                              allowProvisionalNative=True),
                       2, "olean-audit", "invalid compiled-environment audit observation")
        olean_module(ol, "OlForgedNative", prelude_init + (
            "def bad : Bool := false\ndef bad._sunfold : Bool := true\n"
            "axiom f1._native.native_decide.ax_1_1 : bad = true\n"
            "axiom f2._native.native_decide.ax_1_1 : (!true) = true\n"
            "axiom f3._native.native_decide.ax_1_1 : false = true\n"
            "axiom f4._native.native_decide.ax_1_1 : False\n"), ["Init"])
        olean_reject(ol, ["OlForgedNative"], "[nativeDecideReached] f1", "[unapprovedAxiom] f3", "[unapprovedAxiom] f4")
        diag = olean_raw(ol, ["OlForgedNative"], allowProvisionalNative=True)
        assert diag["ok"] is False and diag["category"] == "policy", diag
        for needle in ("[unapprovedAxiom] f1", "[unapprovedAxiom] f2", "[unapprovedAxiom] f3", "[unapprovedAxiom] f4"):
            assert needle in diag["message"], (needle, diag)
        olean_module(ol, "OlStuckNative", prelude_init + "opaque stuck : Bool\n"
                     "axiom f5._native.native_decide.ax_1_1 : stuck = true\n", ["Init"])
        diag = olean_raw(ol, ["OlStuckNative"], allowProvisionalNative=True)
        assert diag["ok"] is False and "provisionalNative" in diag["message"] and "f5" in diag["message"], diag
        done("native_decide rejection, kernel re-check of forged/_sunfold-steered native axioms, provisional never passes")

        # Group 26: statement-origin separation in the compiled environment: a claim statement that
        # unfolds (directly or via an intermediate examples/Specs module) into a forbidden theory
        # module is rejected; proof-only use is not; missing claimModules entries fail closed.
        olean_module(ol, "OlTheory", prelude_init + "def UntrustedProp : Prop := True\n", ["Init"])
        olean_module(ol, "OlSpecMod", "prelude\nimport OlTheory\ndef SpecProp : Prop := UntrustedProp\n", ["OlTheory"])
        olean_module(ol, "OlClaim", "prelude\nimport OlTheory\ndef myClaim : Prop := UntrustedProp\n"
                     "theorem leaked : myClaim := True.intro\n", ["OlTheory"])
        olean_module(ol, "OlClaimViaSpec", "prelude\nimport OlSpecMod\n"
                     "theorem leakedViaSpec : SpecProp := True.intro\n", ["OlSpecMod"])
        olean_module(ol, "OlClaimDef", "prelude\nimport OlTheory\n"
                     "def leakedDef : UntrustedProp := True.intro\n", ["OlTheory"])
        olean_module(ol, "OlClaimOk", "prelude\nimport OlTheory\n"
                     "theorem proofOnly : True := (fun (_ : UntrustedProp) => True.intro) True.intro\n", ["OlTheory"])
        olean_reject(ol, ["OlTheory", "OlClaim"], "[statementOriginLeak] leaked", "UntrustedProp",
                     claimModules=["OlClaim"], statementForbidden=["OlTheory"], statementUnfold=["OlClaim"])
        olean_reject(ol, ["OlTheory", "OlSpecMod", "OlClaimViaSpec"], "[statementOriginLeak] leakedViaSpec", "UntrustedProp",
                     claimModules=["OlClaimViaSpec"], statementForbidden=["OlTheory"],
                     statementUnfold=["OlClaimViaSpec", "OlSpecMod"])
        olean_reject(ol, ["OlTheory", "OlClaimDef"], "[statementOriginLeak] leakedDef", "UntrustedProp",
                     claimModules=["OlClaimDef"], statementForbidden=["OlTheory"], statementUnfold=["OlClaimDef"])
        olean_reject(ol, ["OlTheory"], "[missingDeclaration]", "MissingClaimMod",
                     claimModules=["MissingClaimMod"], statementForbidden=["OlTheory"])
        olean_accept(ol, ["OlTheory", "OlClaimOk"], claimModules=["OlClaimOk"], statementForbidden=["OlTheory"],
                     statementUnfold=["OlClaimOk"])
        done("compiled statement-origin separation (incl. Specs/examples and missing claimModules)")

        # Group 27: pure Lean 4 hardcoded compiler-intrinsic name spoofing (no `import Lean`, no
        # attributes, no axioms): redefining ConstantFold/ToLCNF built-in names in non-toolchain
        # modules causes compiled code to silently diverge from the kernel and must be rejected.
        olean_module(ol, "OlSpoofFold", "prelude\nimport Init.Core\n"
                     "def Nat.nextPowerOfTwo (_ : Nat) : Nat := 1000\n"
                     "def String.length (_ : String) : Nat := 1000\n"
                     "def victim : Nat := Nat.nextPowerOfTwo 3\n"
                     "theorem kernel_val : victim = 1000 := rfl\n", ["Init.Core"])
        olean_reject(ol, ["OlSpoofFold"], "[compilerOverrideAttribute] Nat.nextPowerOfTwo",
                     "[compilerOverrideAttribute] String.length", "compiler_intrinsic_name")
        olean_module(ol, "OlSpoofPrelude", "prelude\n"
                     "inductive PNat where | zero | succ (n : PNat)\n"
                     "def Empty.rec (x : PNat) (_y : PNat) : PNat := PNat.succ x\n", [])
        olean_reject(ol, ["OlSpoofPrelude"], "[compilerOverrideAttribute] Empty.rec", "compiler_intrinsic_name")
        # A fixed denylist cannot keep up with the names the code generator special-cases
        # (`LCNF.Types`/`ToImpureType` match `Void.nonemptyType`; `ExtractClosed` and
        # `SimpleGroundExpr` match `Array.emptyWithCapacity` and `Lean.Name.mkStr1`..): any
        # non-toolchain declaration reusing a name the pinned toolchain declares is rejected, even
        # when the declaring toolchain module is not imported.
        olean_module(ol, "OlSpoofToolchainName", "prelude\nimport Init.Prelude\n"
                     "def Void.nonemptyType : Nat := 0\n"
                     "def Lean.Compiler.LCNF.PassInstaller : Nat := 1\n", ["Init.Prelude"])
        olean_reject(ol, ["OlSpoofToolchainName"], "[compilerOverrideAttribute] Void.nonemptyType",
                     "[compilerOverrideAttribute] Lean.Compiler.LCNF.PassInstaller", "toolchain_name")
        # Source rule: a raw string `r"\"` has no escapes, and prefix `!` before `"{"` is not an
        # interpolated string, so neither may blind the scanner to a following `_unsafe_rec` ident.
        raw_src = "prelude\nimport Init\ndef rawS : String := r\"\\\"\ndef hiddenRaw._unsafe_rec (n : Nat) : Nat := n\n" \
                  "def rawT : String := \"x\"\n"
        olean_module(ol, "OlRawString", raw_src, ["Init"])
        olean_reject(ol, ["OlRawString"], "[sourceForbiddenIdentifier] hiddenRaw._unsafe_rec",
                     sources=[("OlRawString", str(ol.stage / "olean-src/OlRawString.lean"))])
        bang_src = "prelude\nimport Init.Notation\ninstance : Coe String Bool where coe _ := true\n" \
                   "def blindBang : Bool := !\"{\"\ndef hidden_unsafe_rec : Nat := 1\n"
        olean_module(ol, "OlBangString", bang_src, ["Init.Notation"])
        olean_reject(ol, ["OlBangString"], "[sourceForbiddenIdentifier] hidden_unsafe_rec",
                     sources=[("OlBangString", str(ol.stage / "olean-src/OlBangString.lean"))])
        # Spaced `s! "..."` and `println! "..."` interpolated strings with `'"'` inside `{...}`
        # must never desynchronize `scanIdents` or hide a subsequent `_unsafe_rec` identifier.
        interp_space_src = (
            "prelude\nimport Init\n"
            "def spacedS : String := s! \"{'\"'}\"\n"
            "def spacedP : IO Unit := println! \"{'\"'}\"\n"
            "def hiddenLocal : Nat := let my_unsafe_rec := 42; my_unsafe_rec\n"
            "-- \"\n"
        )
        olean_module(ol, "OlInterpSpace", interp_space_src, ["Init"])
        olean_reject(ol, ["OlInterpSpace"], "[sourceForbiddenIdentifier] my_unsafe_rec",
                     sources=[("OlInterpSpace", str(ol.stage / "olean-src/OlInterpSpace.lean"))])
        # `panic! "{"` is a plain string, but `<ident>!` makes the token scan read it as an
        # interpolated one; with quotes balanced by a trailing comment the scan stays "balanced"
        # while missing the local identifier. The string-unaware pass still sees it.
        panic_src = ("prelude\nimport Init\ndef panicS : String := panic! \"{\"\n"
                     "def panicHidden : Nat := let my_unsafe_rec := 1; my_unsafe_rec -- \"}\"\n")
        olean_module(ol, "OlPanicString", panic_src, ["Init"])
        olean_reject(ol, ["OlPanicString"], "[sourceForbiddenIdentifier] OlPanicString", "outside comments",
                     sources=[("OlPanicString", str(ol.stage / "olean-src/OlPanicString.lean"))])
        done("pure Lean 4 hardcoded compiler-intrinsic and toolchain-owned name spoofing, raw/bang-string source scan")

        # Group 28: `trusted/root-manifest.sha256` verification before any Lean child.
        root = fixture()
        pinned_input = root / "fixture-input.txt"
        pinned_input.write_text("pinned build input\n")
        manifest = root / "trusted/root-manifest.sha256"

        def write_manifest(entries):
            manifest.write_text("# fixture manifest\n\n" + "".join(f"{runner.digest(root / p)}  {p}\n" for p in entries))

        covered = ["fixture-input.txt", "trusted/audit/check_trusted.py", "trusted/audit/OleanEnvAuditor.lean"]
        write_manifest(covered)
        assert set(runner.verify_root_manifest(root)) == set(covered)
        pinned_input.write_text("drifted build input\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "drift: fixture-input.txt")
        err = checked(root, expected=1, phase="root-manifest", executed=False)
        assert "fixture-input.txt" in str(err)
        assert not any(p.name.endswith(".status.json") for d in disposable[-1:] for p in Path(d).glob("*"))
        pinned_input.unlink()
        pinned_input.symlink_to(root / "trusted/lean/lean-toolchain")
        write_manifest(["trusted/audit/check_trusted.py", "trusted/audit/OleanEnvAuditor.lean"])
        manifest.write_text(manifest.read_text() + f"{runner.digest(pinned_input)}  fixture-input.txt\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "symlink")
        pinned_input.unlink()
        pinned_input.write_text("pinned build input\n")
        write_manifest(["fixture-input.txt", "trusted/audit/check_trusted.py"])
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest",
                       "does not cover required TCB files: trusted/audit/OleanEnvAuditor.lean")
        write_manifest(covered)
        manifest.write_text(manifest.read_text() + "not a checksum line\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "malformed")
        write_manifest(covered)
        manifest.write_text(manifest.read_text() + f"{'0' * 64}  missing/file.txt\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "missing covered file")
        write_manifest(covered)
        manifest.write_text(manifest.read_text() + f"{runner.digest(pinned_input)}  ../escape\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "canonical relative path")
        manifest.unlink()
        assert runner.verify_root_manifest(root) is None
        (root / "flake.nix").write_text("{}\n")
        (root / "lakefile.toml").write_text("name = \"fixture\"\n")
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "missing trusted/root-manifest.sha256")
        # Deleting one repository marker (`flake.nix`) must not bypass root-manifest enforcement.
        (root / "flake.nix").unlink()
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "missing trusted/root-manifest.sha256")
        (root / "flake.nix").write_text("{}\n")
        # In a repository checkout (`flake.nix` + `lakefile.toml`), stripping root build files from
        # `trusted/root-manifest.sha256` must be rejected.
        write_manifest(covered)
        expect_failure(lambda: runner.verify_root_manifest(root), 1, "root-manifest", "Cargo.toml")
        # `tcb_snapshot_files` must include `trusted/root-manifest.sha256` when present, so
        # mutating a covered file and refreshing the manifest is still caught by `--base-snapshot`.
        assert "trusted/root-manifest.sha256" in runner.tcb_snapshot_files(root)
        snap28 = suite / "snap-manifest-28"
        for rel, src_p in runner.tcb_snapshot_files(root).items():
            dst = snap28 / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src_p, dst)
            dst.chmod(0o444)
        pinned_input.write_text("mutated with refreshed manifest\n")
        write_manifest(covered)
        expect_failure(lambda: runner.verify_base_snapshot(root, snap28),
                       1, "base-snapshot", "trusted/root-manifest.sha256")
        shutil.rmtree(snap28)
        done("root-manifest drift, symlink, missing-entry, malformed, base-snapshot, and missing-manifest rejection before Lean")

        # Group 29: Episode 2 constructive axiom policy (`allowClassicalChoice=False`,
        # `constructiveModules`), `--audit-olean` validation, and end-to-end 9-vector
        # (`V1`–`V7`, with `V8`–`V9` in Group 30) compiled-`.olean` checks.
        ol2 = ol
        olean_module(ol2, "OlEp2ConstructiveOk", prelude_init + (
            "theorem ep2_propext (p q : Prop) (h : p ↔ q) : p = q := propext h\n"
            "theorem ep2_quot : Quot.mk (fun (_ _ : Nat) => True) 0 = Quot.mk (fun (_ _ : Nat) => True) 1 :=\n"
            "  Quot.sound trivial\n"), ["Init"])
        olean_module(ol2, "OlEp2UsesChoice", prelude_init + (
            "noncomputable def ep2_choice : Nat := Classical.choice ⟨0⟩\n"), ["Init"])
        c_ok = olean_accept(ol2, ["OlEp2ConstructiveOk"], allowClassicalChoice=False)
        assert "Classical.choice" not in c_ok["axioms"] and c_ok["constructiveModulesChecked"] == 0, c_ok
        olean_reject(ol2, ["OlEp2UsesChoice"], "[unapprovedAxiom]", "Classical.choice",
                     allowClassicalChoice=False)
        c_mix = olean_accept(ol2, ["OlEp2ConstructiveOk", "OlEp2UsesChoice"],
                             constructiveModules=["OlEp2ConstructiveOk"])
        assert c_mix["constructiveModulesChecked"] == 1 and "Classical.choice" in c_mix["axioms"], c_mix
        olean_reject(ol2, ["OlEp2ConstructiveOk", "OlEp2UsesChoice"], "[unapprovedAxiom]", "Classical.choice",
                     constructiveModules=["OlEp2UsesChoice"])
        # Malformed `--audit-olean` constructive/specStrengthChecks fields and `Trusted` in `constructiveModules`.
        expect_failure(lambda: ol2.audit_olean_request({
            "roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
            "constructiveModules": ["Trusted"],
        }), 1, "olean-audit", "moduleProvenanceSpoofed", "Trusted modules")
        for bad_req, needle in (
            ({"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
              "allowClassicalChoice": "no"}, "malformed"),
            ({"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
              "specStrengthChecks": [{"kind": "unknownKind", "cert": "c"}]}, "unsupported"),
            ({"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
              "specStrengthChecks": [{"kind": "claim", "claim": "t"}]}, "malformed"),
            ({"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
              "specStrengthChecks": [{"kind": "itemSynth", "cert": "c"}]}, "malformed"),
        ):
            expect_failure(lambda req=bad_req: ol2.audit_olean_request(req), 2, "olean-audit", needle)
        # Vectors V1–V7 end-to-end on compiled `.olean`s.
        olean_module(ol2, "OlEp2V1", header + "theorem v1 : True := by sorry\n", ["Init.Core"])
        olean_reject(ol2, ["OlEp2V1"], "[sorryAxiomReached]")
        olean_module(ol2, "OlEp2V2", header + "theorem v2 : True := sorryAx True false\n", ["Init.Core"])
        olean_reject(ol2, ["OlEp2V2"], "[sorryAxiomReached]")
        olean_module(ol2, "OlEp2V3", prelude_init + (
            "axiom v3Cust : True\nprivate axiom v3Priv : True\n"
            "theorem v3t : True := by have _ := v3Cust; exact v3Priv\n"
            "def v3Tc : Bool := Lean.reduceBool true\n"), ["Init"])
        olean_reject(ol2, ["OlEp2V3"], "[unapprovedAxiom]", "v3Cust", "v3Priv", "[nativeDecideReached]")
        olean_module(ol2, "OlEp2V4", prelude_init + "theorem v4 : (1 + 1 == 2) = true := by native_decide\n", ["Init"])
        olean_module(ol2, "OlEp2V5Bad", header + "partial def v5p (n : Nat) : Nat := v5p (n + 1)\n", ["Init.Core"])
        olean_module(ol2, "OlEp2V5Ok", prelude_init + (
            "def v5gcd : Nat → Nat → Nat\n  | 0, b => b\n  | a + 1, b => v5gcd (b % (a + 1)) (a + 1)\n"
            "termination_by a _ => a\ndecreasing_by exact Nat.mod_lt b (Nat.succ_pos a)\n"), ["Init"])
        olean_module(ol2, "OlEp2V6", prelude_init + (
            "unsafe def v6u (n : Nat) : Nat := n\n"
            "def v6ib (n : Nat) : Nat := n + 1\n"
            "@[implemented_by v6ib] def v6f (n : Nat) : Nat := n\n"
            "@[extern \"ep2_c\"] def v6e (n : Nat) : Nat := n\n"
            "@[export ep2_x] def v6x (n : Nat) : Nat := n\n"
            "def v6cs1 (a : Nat) : Nat := a\ndef v6cs2 (a : Nat) : Nat := a\n"
            "@[csimp] theorem v6cs : @v6cs1 = @v6cs2 := rfl\n"
            "initialize v6i : Bool ← pure true\n"), ["Init"])
        olean_reject(ol2, ["OlEp2V4", "OlEp2V5Bad", "OlEp2V6"],
                     "[nativeDecideReached]", "v4",
                     "[partialOrUnsafeRecDependency]", "v5p",
                     "[unsafeDeclaration]", "v6u",
                     "[compilerOverrideAttribute]", "implemented_by", "extern", "export", "csimp", "init")
        olean_module(ol2, "OlEp2V7Th", header + "def Ep2ThProp : Prop := True\n", ["Init.Core"])
        olean_module(ol2, "OlEp2V7Leak", "prelude\nimport OlEp2V7Th\ntheorem v7l : Ep2ThProp := True.intro\n",
                     ["OlEp2V7Th"])
        olean_module(ol2, "OlEp2V7Ok", "prelude\nimport OlEp2V7Th\n"
                     "theorem v7ok : True := (fun (_ : Ep2ThProp) => True.intro) True.intro\n", ["OlEp2V7Th"])
        olean_reject(ol2, ["OlEp2V7Th", "OlEp2V7Leak"], "[statementOriginLeak]", "v7l",
                     claimModules=["OlEp2V7Leak"], statementForbidden=["OlEp2V7Th"], statementUnfold=["OlEp2V7Leak"])
        olean_accept(ol2, ["OlEp2V5Ok", "OlEp2V7Th", "OlEp2V7Ok"],
                     claimModules=["OlEp2V7Ok"], statementForbidden=["OlEp2V7Th"], statementUnfold=["OlEp2V7Ok"])
        done("Episode 2 constructive policy, --audit-olean validation, cache-key sensitivity, and V1-V7 compiled checks")

        # Group 30: End-to-end compiled-`.olean` Spec-Strength & Mutant-Kill Gates (`V8`, `V9`,
        # `R6`, `R7`, `R8`, `R11`, `A1-2`, `A1-4`, `A1-6`, `S3a/b`, `S5`, `A3-3a..e`, `A4-5`,
        # `A4-7`, `Classical.choice` certificate rejection, `--fast` cache sensitivity, and the
        # Episode 2 `B1` findings: theorem-headed major premises, kernel-native evaluators executing
        # audited code inside the auditor, and specification-library provenance).
        mir_stub = (
            "module\nprelude\npublic import Init\npublic section\n"
            "namespace Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "abbrev Value := Nat\n"
            "abbrev Memory := Nat\n"
            "abbrev ExternalCallHandler := Nat → Nat\n"
            "end Trusted.Rustc.V2026_06_01.MirSemantics\n")
        verif_stub = (
            "module\nprelude\npublic import Init\npublic import Trusted.Rustc.V2026_06_01.MirSemantics\npublic section\n"
            "namespace Trusted.VerificationResult\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "structure Claim where\n  pre : List Value → Prop\n  post : List Value → Value → Prop\n"
            "structure VerificationResult (c : Claim) : Prop where\n  ok : True\n"
            "structure StatefulClaim where\n  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "structure StatefulVerificationResult (c : StatefulClaim) : Prop where\n  ok : True\n"
            "structure TotalClaim where\n  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "structure TotalVerificationResult (c : TotalClaim) : Prop where\n  ok : True\n"
            "structure ModularClaim where\n  envAssumed : ExternalCallHandler → Prop\n"
            "  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "structure ModularVerificationResult (c : ModularClaim) : Prop where\n  ok : True\n"
            "class ItemSpec (defId : String) : Type 1 where\n  pre : List Value → Prop\n  post : List Value → Value → Prop\n"
            "class StatefulItemSpec (defId : String) : Type 1 where\n  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "class TotalItemSpec (defId : String) : Type 1 where\n  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "class ModularItemSpec (defId : String) : Type 1 where\n  envAssumed : ExternalCallHandler → Prop\n"
            "  pre : List Value → Memory → Prop\n  post : List Value → Memory → Value → Memory → Prop\n"
            "end Trusted.VerificationResult\n")
        spec_lib_stub = (
            "module\nprelude\npublic import Init\npublic import Trusted.VerificationResult\npublic section\n"
            "namespace Anneal.OleanSpecStrengthAuditor\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "inductive MutantCategory where\n"
            "  | wrongReturn | wrapOverflow | truncatedLength | swappedByteOrder\n"
            "  | offByOneScalar | wrongBranchTag | unpreservedFrame | custom (name : String)\n"
            "  deriving DecidableEq, BEq, Repr\n"
            "structure SpecStrengthCert {α : Type u} {β : Type v} (req : α → Prop) (ens : α → β → Prop) where\n"
            "  witnessInput : α\n  witnessValid : req witnessInput\n"
            "  referenceOutput : β\n  referenceAccepted : ens witnessInput referenceOutput\n"
            "  mutantOutput : β\n  mutantRejected : ¬ ens witnessInput mutantOutput\n"
            "structure NamedMutantKill {α : Type u} {β : Type v} (req : α → Prop) (ens : α → β → Prop) where\n"
            "  name : String\n  category : MutantCategory\n  input : α\n  inputValid : req input\n"
            "  referenceOutput : β\n  referenceAccepted : ens input referenceOutput\n"
            "  mutantOutput : β\n  mutantRejected : ¬ ens input mutantOutput\n"
            "structure MultiMutantSpecCert {α : Type u} {β : Type v} (req : α → Prop) (ens : α → β → Prop) where\n"
            "  kills : List (NamedMutantKill req ens)\n  nonEmpty : kills ≠ []\n"
            "@[expose] def MultiMutantSpecCert.coversCategory {α : Type u} {β : Type v} {req : α → Prop} {ens : α → β → Prop}\n"
            "    (c : MultiMutantSpecCert req ens) (cat : MutantCategory) : Bool :=\n"
            "  c.kills.any (fun k => k.category == cat)\n"
            "structure DeterministicSpecCert {α : Type u} {β : Type v} (req : α → Prop) (ens : α → β → Prop) where\n"
            "  witnessInput : α\n  witnessValid : req witnessInput\n"
            "  referenceOutput : β\n  referenceAccepted : ens witnessInput referenceOutput\n"
            "  mutantOutput : β\n  mutantDiffers : mutantOutput ≠ referenceOutput\n"
            "  realizable : ∀ x, req x → ∃ y, ens x y\n"
            "  uniqueOutput : ∀ x y₁ y₂, req x → ens x y₁ → ens x y₂ → y₁ = y₂\n"
            "structure InputSensitiveSpecCert {α : Type u} {β : Type v} (req : α → Prop) (ens : α → β → Prop) where\n"
            "  input₁ : α\n  input₂ : α\n  valid₁ : req input₁\n  valid₂ : req input₂\n"
            "  output₁ : β\n  output₂ : β\n  accepted₁ : ens input₁ output₁\n"
            "  accepted₂ : ens input₂ output₂\n"
            "  nonInterchangeable : ¬ ens input₁ output₂ ∨ ¬ ens input₂ output₁\n"
            "@[expose] def uncurryPre (pre : List Value → Memory → Prop) : (List Value × Memory) → Prop := fun p => pre p.1 p.2\n"
            "@[expose] def uncurryPost (post : List Value → Memory → Value → Memory → Prop) :\n"
            "    (List Value × Memory) → (Value × Memory) → Prop := fun p q => post p.1 p.2 q.1 q.2\n"
            "structure ModularSpecStrengthCert (envA : ExternalCallHandler → Prop)\n"
            "    (pre : List Value → Memory → Prop) (post : List Value → Memory → Value → Memory → Prop) where\n"
            "  envNonVacuous : ∃ h, envA h\n  specCert : SpecStrengthCert (uncurryPre pre) (uncurryPost post)\n"
            "structure ModularMultiMutantSpecCert (envA : ExternalCallHandler → Prop)\n"
            "    (pre : List Value → Memory → Prop) (post : List Value → Memory → Value → Memory → Prop) where\n"
            "  envNonVacuous : ∃ h, envA h\n  specCert : MultiMutantSpecCert (uncurryPre pre) (uncurryPost post)\n"
            "@[expose] def ModularMultiMutantSpecCert.coversCategory {envA pre post}\n"
            "    (c : ModularMultiMutantSpecCert envA pre post) (cat : MutantCategory) : Bool :=\n"
            "  c.specCert.coversCategory cat\n"
            "structure ModularDeterministicSpecCert (envA : ExternalCallHandler → Prop)\n"
            "    (pre : List Value → Memory → Prop) (post : List Value → Memory → Value → Memory → Prop) where\n"
            "  envNonVacuous : ∃ h, envA h\n  specCert : DeterministicSpecCert (uncurryPre pre) (uncurryPost post)\n"
            "structure ModularInputSensitiveSpecCert (envA : ExternalCallHandler → Prop)\n"
            "    (pre : List Value → Memory → Prop) (post : List Value → Memory → Value → Memory → Prop) where\n"
            "  envNonVacuous : ∃ h, envA h\n  specCert : InputSensitiveSpecCert (uncurryPre pre) (uncurryPost post)\n"
            "end Anneal.OleanSpecStrengthAuditor\n")
        olean_module(ol2, "Trusted.Rustc.V2026_06_01.MirSemantics", mir_stub, ["Init"], module_file=True)
        olean_module(ol2, "Trusted.VerificationResult", verif_stub, ["Init", "Trusted.Rustc.V2026_06_01.MirSemantics"], module_file=True)
        olean_module(ol2, "Anneal.OleanSpecStrengthAuditor", spec_lib_stub, ["Init", "Trusted.VerificationResult"], module_file=True)
        base_spec_mods = ["Trusted.Rustc.V2026_06_01.MirSemantics", "Trusted.VerificationResult",
                          "Anneal.OleanSpecStrengthAuditor"]

        # Clean claims & certificates (all 4 claim kinds + clean single item & modular synth).
        clean_spec_src = (
            "prelude\nimport Init\nimport Anneal.OleanSpecStrengthAuditor\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "open Trusted.VerificationResult\n"
            "open Anneal.OleanSpecStrengthAuditor\n"
            "set_option linter.defProp false\n"
            "def epPre (xs : List Value) : Prop := xs = [0] ∨ xs = [1]\n"
            "def epPost (xs : List Value) (r : Value) : Prop := match xs with | [a] => r = a + 10 | _ => False\n"
            "def epRely (h : ExternalCallHandler) : Prop := h 0 = 0\n"
            "def epClaim : Claim := { pre := epPre, post := epPost }\n"
            "theorem epClaim_ok : VerificationResult epClaim := ⟨trivial⟩\n"
            "def epStClaim : StatefulClaim := { pre := fun xs m => epPre xs ∧ m = 0, post := fun xs m r m' => epPost xs r ∧ m' = m }\n"
            "theorem epStClaim_ok : StatefulVerificationResult epStClaim := ⟨trivial⟩\n"
            "def epTotClaim : TotalClaim := { pre := fun xs m => epPre xs ∧ m = 0, post := fun xs m r m' => epPost xs r ∧ m' = m }\n"
            "theorem epTotClaim_ok : TotalVerificationResult epTotClaim := ⟨trivial⟩\n"
            "def epModClaim : ModularClaim := { envAssumed := epRely, pre := fun xs m => epPre xs ∧ m = 0, post := fun xs m r m' => epPost xs r ∧ m' = m }\n"
            "theorem epModClaim_ok : ModularVerificationResult epModClaim := ⟨trivial⟩\n"
            "def epMultiCert : MultiMutantSpecCert epPre epPost := {\n"
            "  kills := [\n"
            "    { name := \"k1\", category := .wrongReturn, input := [0], inputValid := Or.inl rfl,\n"
            "      referenceOutput := 10, referenceAccepted := rfl, mutantOutput := 0, mutantRejected := (by dsimp [epPost]; decide) },\n"
            "    { name := \"k2\", category := .offByOneScalar, input := [0], inputValid := Or.inl rfl,\n"
            "      referenceOutput := 10, referenceAccepted := rfl, mutantOutput := 11, mutantRejected := (by dsimp [epPost]; decide) },\n"
            "    { name := \"k3\", category := .custom \"ep2_tag\", input := [0], inputValid := Or.inl rfl,\n"
            "      referenceOutput := 10, referenceAccepted := rfl, mutantOutput := 99, mutantRejected := (by dsimp [epPost]; decide) }\n"
            "  ],\n  nonEmpty := (by intro h; nomatch h) }\n"
            "def epDetCert : DeterministicSpecCert epPre epPost := {\n"
            "  witnessInput := [0], witnessValid := Or.inl rfl, referenceOutput := 10, referenceAccepted := rfl,\n"
            "  mutantOutput := 11, mutantDiffers := (by decide),\n"
            "  realizable := fun xs h => (by rcases h with rfl | rfl <;> exact ⟨_, rfl⟩),\n"
            "  uniqueOutput := fun xs y₁ y₂ h h1 h2 => (by rcases h with rfl | rfl <;> exact h1.trans h2.symm) }\n"
            "def epInSensCert : InputSensitiveSpecCert epPre epPost := {\n"
            "  input₁ := [0], input₂ := [1], valid₁ := Or.inl rfl, valid₂ := Or.inr rfl,\n"
            "  output₁ := 10, output₂ := 11, accepted₁ := rfl, accepted₂ := rfl,\n"
            "  nonInterchangeable := Or.inl (by dsimp [epPost]; decide) }\n"
            "def epStMultiCert : MultiMutantSpecCert (uncurryPre epStClaim.pre) (uncurryPost epStClaim.post) := {\n"
            "  kills := [\n"
            "    { name := \"k1\", category := .wrongReturn, input := ([0], 0), inputValid := ⟨Or.inl rfl, rfl⟩,\n"
            "      referenceOutput := (10, 0), referenceAccepted := ⟨rfl, rfl⟩, mutantOutput := (0, 0),\n"
            "      mutantRejected := (by intro ⟨h, _⟩; dsimp [epStClaim, epPost] at h; exact absurd h (by decide)) }\n"
            "  ],\n"
            "  nonEmpty := (by intro h; nomatch h) }\n"
            "def epModMultiCert : ModularMultiMutantSpecCert epRely epModClaim.pre epModClaim.post := {\n"
            "  envNonVacuous := ⟨fun x => x, rfl⟩, specCert := epStMultiCert }\n"
            "def epModInSensCert : ModularInputSensitiveSpecCert epRely epModClaim.pre epModClaim.post := {\n"
            "  envNonVacuous := ⟨fun x => x, rfl⟩,\n"
            "  specCert := {\n"
            "    input₁ := ([0], 0), input₂ := ([1], 0), valid₁ := ⟨Or.inl rfl, rfl⟩, valid₂ := ⟨Or.inr rfl, rfl⟩,\n"
            "    output₁ := (10, 0), output₂ := (11, 0), accepted₁ := ⟨rfl, rfl⟩, accepted₂ := ⟨rfl, rfl⟩,\n"
            "    nonInterchangeable := Or.inl (by intro ⟨h, _⟩; dsimp [epModClaim, epPost] at h; exact absurd h (by decide)) } }\n"
            "instance epCleanItem : ItemSpec \"ep2::clean\" where pre := epPre; post := epPost\n"
            "instance epCleanStItem : StatefulItemSpec \"ep2::clean_st\" where pre := epStClaim.pre; post := epStClaim.post\n"
            "instance epCleanTotItem : TotalItemSpec \"ep2::clean_tot\" where pre := epTotClaim.pre; post := epTotClaim.post\n"
            "instance epCleanModItem : ModularItemSpec \"ep2::clean_mod\" where\n"
            "  envAssumed := epRely; pre := epModClaim.pre; post := epModClaim.post\n"
            "-- V8/V9/non-theorem/wrong-rely/classical canaries in the same module (audited per-check):\n"
            "def epVacClaim : Claim := { pre := fun _ => False, post := epPost }\n"
            "theorem epVacClaim_ok : VerificationResult epVacClaim := ⟨trivial⟩\n"
            "def epTrivClaim : Claim := { pre := epPre, post := fun _ _ => True }\n"
            "theorem epTrivClaim_ok : VerificationResult epTrivClaim := ⟨trivial⟩\n"
            "def epTrivCert := epMultiCert\n"
            "def epNotAThm : VerificationResult epClaim := ⟨trivial⟩\n"
            "def epWrongRelyCert : ModularMultiMutantSpecCert (fun _ => True) epModClaim.pre epModClaim.post := {\n"
            "  envNonVacuous := ⟨fun x => x, trivial⟩, specCert := epStMultiCert }\n"
            "noncomputable def epClassicalCert : MultiMutantSpecCert epPre epPost :=\n"
            "  let _ : Nat := Classical.choice ⟨0⟩\n  epMultiCert\n")
        olean_module(ol2, "OlEp2SpecClean", clean_spec_src, ["Init", "Anneal.OleanSpecStrengthAuditor"])
        clean_checks = [
            {"kind": "claim", "claim": "epClaim_ok", "cert": "epMultiCert",
             "requiredCategories": ["wrongReturn", "offByOneScalar"]},
            {"kind": "claim", "claim": "epClaim_ok", "cert": "epDetCert", "requireDeterministic": True},
            {"kind": "claim", "claim": "epClaim_ok", "cert": "epInSensCert", "requireInputSensitive": True},
            {"kind": "claim", "claim": "epStClaim_ok", "cert": "epStMultiCert", "requiredCategories": ["wrongReturn"]},
            {"kind": "claim", "claim": "epTotClaim_ok", "cert": "epStMultiCert", "requiredCategories": ["wrongReturn"]},
            {"kind": "claim", "claim": "epModClaim_ok", "cert": "epModMultiCert", "requiredCategories": ["wrongReturn"]},
            {"kind": "claim", "claim": "epModClaim_ok", "cert": "epModInSensCert", "requireInputSensitive": True},
            {"kind": "itemSynth", "defId": "ep2::clean", "cert": "epMultiCert",
             "requiredCategories": ["wrongReturn", "custom:ep2_tag"]},
            {"kind": "statefulItemSynth", "defId": "ep2::clean_st", "cert": "epStMultiCert",
             "requiredCategories": ["wrongReturn"]},
            {"kind": "totalItemSynth", "defId": "ep2::clean_tot", "cert": "epStMultiCert",
             "requiredCategories": ["wrongReturn"]},
            {"kind": "modularItemSynth", "defId": "ep2::clean_mod", "cert": "epModMultiCert",
             "requiredCategories": ["wrongReturn"]},
        ]
        sc_res = olean_accept(ol2, base_spec_mods + ["OlEp2SpecClean"],
                              constructiveModules=["Anneal.OleanSpecStrengthAuditor"],
                              specStrengthChecks=clean_checks)
        assert sc_res["specStrengthChecksPassed"] == len(clean_checks), sc_res
        assert sc_res["constructiveModulesChecked"] == 1, sc_res
        # Negative claim/cert checks: V8, V9, Classical.choice cert, R8 coverage gap, non-theorem, wrong rely, S5.
        # Batched with distinct `(tag, decl)` pairs so every single violation is verified explicitly.
        olean_reject(ol2, base_spec_mods + ["OlEp2SpecClean"],
                     "[specStrengthCertInvalidType] epMultiCert",
                     "[specStrengthCertInvalidType] epTrivCert",
                     "[unapprovedAxiom] Classical.choice",
                     "[specStrengthCoverageGap] epMultiCert",
                     "[specStrengthCertInvalidType] epNotAThm",
                     "[specStrengthCertInvalidType] epWrongRelyCert",
                     "[specStrengthCertInvalidType] epDetCert",
                     specStrengthChecks=[
                         {"kind": "claim", "claim": "epVacClaim_ok", "cert": "epMultiCert"},
                         {"kind": "claim", "claim": "epTrivClaim_ok", "cert": "epTrivCert"},
                         {"kind": "claim", "claim": "epClaim_ok", "cert": "epClassicalCert"},
                         {"kind": "claim", "claim": "epClaim_ok", "cert": "epMultiCert",
                          "requiredCategories": ["wrongReturn", "unpreservedFrame"]},
                         {"kind": "claim", "claim": "epNotAThm", "cert": "epMultiCert"},
                         {"kind": "claim", "claim": "epModClaim_ok", "cert": "epWrongRelyCert"},
                         {"kind": "claim", "claim": "epClaim_ok", "cert": "epDetCert", "requireInputSensitive": True},
                     ])

        # A1-4 (`sorry`-faked cert reports `sorryAxiomReached`, NOT `specStrengthCoverageGap`).
        olean_module(ol2, "OlEp2A14", (
            "prelude\nimport Init\nimport OlEp2SpecClean\n"
            "open Anneal.OleanSpecStrengthAuditor\n"
            "def a14SorryCert : MultiMutantSpecCert epPre epPost := by sorry\n"), ["Init", "OlEp2SpecClean"])
        a14_err = olean_reject(ol2, base_spec_mods + ["OlEp2SpecClean", "OlEp2A14"], "[sorryAxiomReached]",
                               specStrengthChecks=[{"kind": "claim", "claim": "epClaim_ok", "cert": "a14SorryCert",
                                                    "requiredCategories": ["unpreservedFrame"]}])
        assert "specStrengthCoverageGap" not in a14_err, a14_err

        # A3-3a..e (`_sunfold` spec-gate spoofs) + R7 / A1-2a..d / S3a/b shadowing in compiled `.olean`.
        shadow_src = (
            "prelude\nimport Init\nimport OlEp2SpecClean\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics\n"
            "open Trusted.VerificationResult\n"
            "open Anneal.OleanSpecStrengthAuditor\n"
            "def s3VacPre (_ : List Value) : Prop := False\n"
            "def s3VacPost (_ : List Value) (_ : Value) : Prop := True\n"
            "def s3VacClaim : Claim := { pre := s3VacPre, post := s3VacPost }\n"
            "theorem s3VacClaim_ok : VerificationResult s3VacClaim := ⟨trivial⟩\n"
            "def s3VacPre._sunfold : List Value → Prop := epPre\n"
            "def s3VacPost._sunfold : List Value → Value → Prop := epPost\n"
            "def s3WeakKills : List (NamedMutantKill epPre epPost) := epMultiCert.kills\n"
            "def s3WeakCert : MultiMutantSpecCert epPre epPost := { kills := s3WeakKills, nonEmpty := (by intro h; dsimp [s3WeakKills, epMultiCert] at h; nomatch h) }\n"
            "def s3WeakKills._sunfold : List (NamedMutantKill epPre epPost) :=\n"
            "  { name := \"f\", category := .unpreservedFrame, input := [0], inputValid := Or.inl rfl,\n"
            "    referenceOutput := 10, referenceAccepted := rfl, mutantOutput := 99, mutantRejected := (by dsimp [epPost]; decide) } :: epMultiCert.kills\n"
            "instance s3cStrong : ItemSpec \"ep2::s3c\" where pre := epPre; post := epPost\n"
            "def s3Hide : Type 1 := ItemSpec \"ep2::s3c\"\n"
            "def s3cShadow : s3Hide := { pre := fun _ => False, post := fun _ _ => True }\n"
            "def s3Hide._sunfold : Type 1 := PUnit\n"
            "def s3dFakeTy : Type := Unit\ndef s3dUnit : s3dFakeTy := ()\n"
            "def s3dFakeTy._sunfold : Type := SpecStrengthCert epPre epPost\n"
            "def s3eFakeTy : Prop := True\ntheorem s3eTriv : s3eFakeTy := trivial\n"
            "def s3eFakeTy._sunfold : Prop := VerificationResult epClaim\n"
            "instance r7S : ItemSpec \"ep2::r7\" where pre := epPre; post := epPost\n"
            "def r7W : ItemSpec \"ep2::r7\" := { pre := fun _ => False, post := fun _ _ => True }\n"
            "instance letS : ItemSpec \"ep2::let\" where pre := epPre; post := epPost\n"
            "def letW : (let T := ItemSpec \"ep2::let\"; T) := { pre := fun _ => False, post := fun _ _ => True }\n"
            "instance betaS : ItemSpec \"ep2::beta\" where pre := epPre; post := epPost\n"
            "def betaW : ((fun s => ItemSpec s) \"ep2::beta\") := { pre := fun _ => False, post := fun _ _ => True }\n"
            "instance projS : ItemSpec \"ep2::proj\" where pre := epPre; post := epPost\n"
            "abbrev ProjPair : Type 1 × Type := (ItemSpec \"ep2::proj\", Nat)\n"
            "def projW : ProjPair.1 := { pre := fun _ => False, post := fun _ _ => True }\n"
            "class SubChain extends ItemSpec \"ep2::sub\"\n"
            "instance subW : SubChain where pre := fun _ => False; post := fun _ _ => True\n"
            "instance subS : SubChain where pre := epPre; post := epPost\n"
            "def c_s3c := epMultiCert\ndef c_r7 := epMultiCert\ndef c_let := epMultiCert\n"
            "def c_beta := epMultiCert\ndef c_proj := epMultiCert\ndef c_sub := epMultiCert\n"
            "def plainNoInst : ItemSpec \"ep2::plain_no_inst\" := { pre := epPre, post := epPost }\n"
            "def c_plain := epMultiCert\n")
        olean_module(ol2, "OlEp2Shadow", shadow_src, ["Init", "OlEp2SpecClean"])
        shadow_mods = base_spec_mods + ["OlEp2SpecClean", "OlEp2Shadow"]
        olean_reject(ol2, shadow_mods,
                     "[specStrengthCertInvalidType] epMultiCert",
                     "[specStrengthCoverageGap] s3WeakCert",
                     "[specInstanceAmbiguous] c_s3c",
                     "[specStrengthCertInvalidType] s3dUnit",
                     "[specStrengthCertInvalidType] s3eTriv",
                     "[specInstanceAmbiguous] c_r7",
                     "[specInstanceAmbiguous] c_let",
                     "[specInstanceAmbiguous] c_beta",
                     "[specInstanceAmbiguous] c_proj",
                     "[specInstanceAmbiguous] SubChain.toItemSpec",
                     "[specStrengthCertMissing] plainNoInst",
                     specStrengthChecks=[
                         {"kind": "claim", "claim": "s3VacClaim_ok", "cert": "epMultiCert"},
                         {"kind": "claim", "claim": "epClaim_ok", "cert": "s3WeakCert",
                          "requiredCategories": ["unpreservedFrame"]},
                         {"kind": "itemSynth", "defId": "ep2::s3c", "cert": "c_s3c"},
                         {"kind": "claim", "claim": "epClaim_ok", "cert": "s3dUnit"},
                         {"kind": "claim", "claim": "s3eTriv", "cert": "epMultiCert"},
                         {"kind": "itemSynth", "defId": "ep2::r7", "cert": "c_r7"},
                         {"kind": "itemSynth", "defId": "ep2::let", "cert": "c_let"},
                         {"kind": "itemSynth", "defId": "ep2::beta", "cert": "c_beta"},
                         {"kind": "itemSynth", "defId": "ep2::proj", "cert": "c_proj"},
                         {"kind": "itemSynth", "defId": "ep2::sub", "cert": "c_sub"},
                         {"kind": "itemSynth", "defId": "ep2::plain_no_inst", "cert": "c_plain"},
                     ])

        # A1-3 (parameterized dependent-recursor / typeclass-gated shadow in compiled `.olean`).
        olean_module(ol2, "OlEp2A13", (
            "prelude\nimport Init\nimport OlEp2SpecClean\n"
            "open Trusted.VerificationResult\n"
            "instance a13S : ItemSpec \"ep2::a13\" where pre := epPre; post := epPost\n"
            "class A13Flag where ok : Bool\n"
            "instance : A13Flag where ok := true\n"
            "def a13Cond [f : A13Flag] : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec \"ep2::a13\") f.ok :=\n"
            "  match f with | ⟨false⟩ => PUnit.unit | ⟨true⟩ => { pre := fun _ => False, post := fun _ _ => True }\n"),
            ["Init", "OlEp2SpecClean"])
        olean_reject(ol2, base_spec_mods + ["OlEp2SpecClean", "OlEp2A13"], "[specInstanceAmbiguous] epMultiCert",
                     "a13Cond", specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::a13", "cert": "epMultiCert"}])

        # B1-1 (theorem-headed major premise). Lean's kernel δ-unfolds theorems exactly like
        # definitions; `Meta.whnf` never does. `thmWeak` needs no axiom and no native code, its type
        # is `Acc.rec … thmAcc`, and the kernel accepts it as `ItemSpec "ep2::thm"`. Both scanners
        # used to answer "not a candidate" and the gate certified the strong instance as unique.
        thm_ty = ("@Acc.rec Nat (fun _ _ => False) (fun _ _ => Type 1) "
                  "(fun _ _ _ => ItemSpec \"ep2::thm\") 0")
        thm_src = (
            "prelude\nimport Init\nimport OlEp2SpecClean\n"
            "open Trusted.VerificationResult\n"
            "theorem thmAcc : Acc (fun (_ _ : Nat) => False) 0 := Acc.intro 0 (fun _ h => False.elim h)\n"
            "instance thmStrong : ItemSpec \"ep2::thm\" where pre := epPre; post := epPost\n"
            f"theorem thmTyEq : {thm_ty} thmAcc = ItemSpec \"ep2::thm\" :=\n"
            "  @congrArg _ _ thmAcc (Acc.intro 0 (fun _ h => False.elim h))\n"
            f"    (fun h => {thm_ty} h) rfl\n"
            f"def thmWeak : {thm_ty} thmAcc :=\n"
            "  cast thmTyEq.symm { pre := fun _ => False, post := fun _ _ => True }\n"
            "instance thmOther : ItemSpec \"ep2::thm_other\" where pre := epPre; post := epPost\n")
        olean_module(ol2, "OlEp2ThmMajor", thm_src, ["Init", "OlEp2SpecClean"])
        thm_mods = base_spec_mods + ["OlEp2SpecClean", "OlEp2ThmMajor"]
        olean_reject(ol2, thm_mods, "[specInstanceAmbiguous] epMultiCert", "#[thmStrong, thmWeak]",
                     specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::thm", "cert": "epMultiCert"}])
        # Control: `thmWeak` is no candidate for another `defId` (it is classified, not failed closed).
        thm_ok = olean_accept(ol2, thm_mods, specStrengthChecks=[
            {"kind": "itemSynth", "defId": "ep2::thm_other", "cert": "epMultiCert",
             "requiredCategories": ["wrongReturn"]}])
        assert thm_ok["specStrengthChecksPassed"] == 1, thm_ok

        # B1-4 / A4-5 (kernel-native evaluators). `Lean.reduceBool c` and `Lean.reduceNat c` are
        # reduced by the kernel and by `Meta.whnf` by *running the compiled code of `c`*, which the
        # IR interpreter finds in the loaded artifacts. `nativeFlag` writes a marker file when it is
        # evaluated; compiling `OlEp2NativeUse` runs it once (the elaborator normalizes the type), and
        # that proves the canary is live. The auditor must then (a) never run it, in the instance
        # scan, in the statement-origin pass, in tag validation or in replay, and (b) reject.
        native_marker = ol2.stage / "native-evaluator-ran"
        assert '"' not in str(native_marker) and "\\" not in str(native_marker)
        olean_module(ol2, "OlEp2NativeImpl", (
            "prelude\nimport Init\n"
            "unsafe def nativeImpl (_ : Unit) : Bool :=\n"
            f"  match unsafeIO (do IO.FS.writeFile \"{native_marker}\" \"ran\"; pure true) with\n"
            "  | .ok b => b\n  | .error _ => true\n"
            "@[implemented_by nativeImpl] def nativeHelper (_ : Unit) : Bool := true\n"
            "def nativeFlag : Bool := nativeHelper ()\n"
            "def nativeNat : Nat := 0\n"), ["Init"])
        olean_module(ol2, "OlEp2NativeUse", (
            "prelude\nimport Init\nimport OlEp2SpecClean\nimport OlEp2NativeImpl\n"
            "open Trusted.VerificationResult\n"
            "set_option linter.deprecated false\n"
            "instance evStrong : ItemSpec \"ep2::ev\" where pre := epPre; post := epPost\n"
            "def evWeak : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec \"ep2::ev\")\n"
            "    (Lean.reduceBool nativeFlag) := { pre := fun _ => False, post := fun _ _ => True }\n"
            "def evSort : Bool.rec (motive := fun _ => Type 2) (Type 1) (Type 1) (Lean.reduceBool nativeFlag) := Type\n"
            "def evInhab : evSort := Nat\n"
            "def evNat : Nat := Lean.reduceNat nativeNat\n"),
            ["Init", "OlEp2SpecClean", "OlEp2NativeImpl"])
        assert native_marker.exists(), "native-evaluator canary is not live (the compiler did not run it)"
        native_marker.unlink()
        native_mods = base_spec_mods + ["OlEp2SpecClean", "OlEp2NativeImpl", "OlEp2NativeUse"]
        native_err = olean_reject(
            ol2, native_mods, "[nativeDecideReached] Lean.reduceBool",
            "kernel-native evaluator", "[nativeDecideReached] Lean.trustCompiler",
            specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::ev", "cert": "epMultiCert"}],
            claimModules=["OlEp2NativeUse"])
        assert not native_marker.exists(), "audited code ran inside OleanEnvAuditor (specStrengthChecks + claimModules)"
        assert "specInstanceAmbiguous" not in native_err and "kernelReplayFailed" not in native_err, native_err
        # `Lean.reduceNat` alone (no `Lean.reduceBool` anywhere) is the same class.
        olean_module(ol2, "OlEp2NativeNat", "prelude\nimport Init\nset_option linter.deprecated false\n"
                     "def rnVal : Nat := 0\ndef rnUse : Nat := Lean.reduceNat rnVal\n", ["Init"])
        olean_reject(ol2, ["OlEp2NativeNat"], "[nativeDecideReached] Lean.reduceBool", "kernel-native evaluator")

        # A2-5: `Lean.reduceBool` hidden ONLY inside a forged `Meta.instanceExtension` entry's
        # `ent.val` (no declaration in `data.constants` mentions `Lean.reduceBool`).
        olean_module(ol2, "OlEp2NativeInst", (
            "prelude\nimport Init\nimport Lean.Elab.Command\nimport OlEp2SpecClean\n"
            "open Lean Meta Trusted.VerificationResult\n"
            "def a25Flag : Bool := true\n"
            "run_cmd Elab.Command.liftTermElabM do\n"
            "  let keys ← DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit \"ep2::a25\"))\n"
            "  let ent : InstanceEntry := { keys := keys, val := mkApp (mkConst ``Lean.reduceBool) (mkConst ``a25Flag), "
            "priority := 5000, globalName? := none, synthOrder := #[], attrKind := AttributeKind.global }\n"
            "  instanceExtension.add ent AttributeKind.global\n"),
            ["Init", "Lean.Elab.Command", "OlEp2SpecClean"])
        olean_reject(ol2, base_spec_mods + ["OlEp2SpecClean", "OlEp2NativeInst"],
                     "[nativeDecideReached] Lean.reduceBool", "kernel-native evaluator",
                     toolchainRoots=["Init", "Std", "Lean"])

        # A1-1 (duplicate reserved theorem copy native-evaluator RCE bypass of B1-4): when M1's
        # clean `a1f.eq_1` shadows M2's evil `a1f.eq_1` in `env.find?`, `reachesNativeEvaluator`
        # must still inspect M2's stored `declEdges` before `reservedTheoremCopyOk` runs the kernel.
        olean_module(ol2, "OlEp2DupM0", "prelude\nimport Init\ndef a1f : Nat → Nat | 0 => 0 | n + 1 => n\n", ["Init"])
        olean_module(ol2, "OlEp2DupM1", "prelude\nimport Init\nimport OlEp2DupM0\n"
                     "theorem useDupM1 : a1f 0 = 0 := a1f.eq_1\n", ["Init", "OlEp2DupM0"])
        olean_module(ol2, "OlEp2DupM2", (
            "prelude\nimport Init\nimport Lean.Elab.Command\nimport OlEp2DupM0\nimport OlEp2NativeImpl\nopen Lean\n"
            "run_cmd Elab.Command.liftCoreM do\n"
            "  let ty := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (mkApp (mkConst ``a1f) (mkNatLit 0)) (mkNatLit 0)\n"
            "  let trig := mkApp (mkConst ``Lean.reduceBool) (mkConst ``nativeFlag)\n"
            "  let eqTrue := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) trig (mkConst ``Bool.true)\n"
            "  let pfTrue := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)\n"
            "  let val := Expr.letE `h eqTrue pfTrue (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit 0)) false\n"
            "  addDecl (.thmDecl { name := `a1f.eq_1, levelParams := [], type := ty, value := val })\n"),
            ["Init", "Lean.Elab.Command", "OlEp2DupM0", "OlEp2NativeImpl"])
        assert native_marker.exists(), "A1-1 duplicate-reserved canary is not live (compiler did not run it)"
        native_marker.unlink()
        # Load M2 before M1 so M1's clean `a1f.eq_1` wins in `env.find?`.
        olean_reject(ol2, ["OlEp2NativeImpl", "OlEp2DupM0", "OlEp2DupM2", "OlEp2DupM1"],
                     "[nativeDecideReached] Lean.reduceBool", "kernel-native evaluator",
                     toolchainRoots=["Init", "Std", "Lean"])
        assert not native_marker.exists(), "A1-1 duplicate reserved theorem executed audited code inside OleanEnvAuditor!"

        # A2-4 (duplicate reserved theorem copy with `Classical.choice` in `constructiveModules`):
        # when M1's clean `a1f.eq_1` shadows `OlEp2DupChoice`'s classical `a1f.eq_1` in `env.find?`,
        # auditing `OlEp2DupChoice` under `constructiveModules` with `allowClassicalChoice=True`
        # must still reject `Classical.choice`.
        olean_module(ol2, "OlEp2DupChoice", (
            "prelude\nimport Init\nimport Lean.Elab.Command\nimport OlEp2DupM0\nopen Lean\n"
            "run_cmd Elab.Command.liftCoreM do\n"
            "  let ty := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) (mkApp (mkConst ``a1f) (mkNatLit 0)) (mkNatLit 0)\n"
            "  let choiceVal := mkApp2 (mkConst ``Classical.choice [Level.one]) (mkConst ``Nat) "
            "(mkApp2 (mkConst ``Nonempty.intro [Level.one]) (mkConst ``Nat) (mkNatLit 0))\n"
            "  let val := Expr.letE `c (mkConst ``Nat) choiceVal (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkNatLit 0)) false\n"
            "  addDecl (.thmDecl { name := `a1f.eq_1, levelParams := [], type := ty, value := val })\n"),
            ["Init", "Lean.Elab.Command", "OlEp2DupM0"])
        olean_reject(ol2, ["OlEp2DupM0", "OlEp2DupChoice", "OlEp2DupM1"],
                     "[unapprovedAxiom]", "Classical.choice",
                     toolchainRoots=["Init", "Std", "Lean"],
                     allowClassicalChoice=True, constructiveModules=["OlEp2DupChoice"])

        # B1-5 & A1-5a/d (specification-library provenance & constructive `allowClassicalChoice=False`
        # with checker-compiled `Trusted`).
        spec_lib_parts = ol2.artifacts[runner.SPEC_LIB_MODULE]
        for spec_spoof in (
            {"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk", runner.SPEC_LIB_MODULE],
             "artifacts": []},
            {"roots": [runner.SPEC_LIB_MODULE], "modules": ["OlEp2ConstructiveOk"], "artifacts": []},
            {"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"],
             "artifacts": [[runner.SPEC_LIB_MODULE, spec_lib_parts]]},
            {"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
             "constructiveModules": [runner.SPEC_LIB_MODULE]},
            {"roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
             "graph": {runner.SPEC_LIB_MODULE: []}},
            {"roots": [runner.SPEC_LIB_MODULE + ".Fake"], "modules": [runner.SPEC_LIB_MODULE + ".Fake"],
             "artifacts": []},
        ):
            expect_failure(lambda req=spec_spoof: ol2.audit_olean_request(req), 1, "olean-audit",
                           "moduleProvenanceSpoofed", runner.SPEC_LIB_MODULE)
        assert ol2.spec_lib_owned is False
        expect_failure(lambda: ol2.audit_olean_request({
            "roots": ["OlEp2SpecClean"], "modules": ["OlEp2SpecClean"], "artifacts": [],
            "specStrengthChecks": [{"kind": "claim", "claim": "epClaim_ok", "cert": "epMultiCert"}],
        }), 1, "olean-audit", "moduleProvenanceSpoofed", "checker's own compiled")
        # With a checker-owned library the request needs no mention of it: it joins the audit by
        # itself, under the constructive policy, and the checks run against it. Also verify `A1-5a`:
        # when checker-compiled `Trusted` uses `Classical.choice`, `allowClassicalChoice=False`
        # accepts a constructive caller and rejects a classical caller.
        olean_module(ol2, "Trusted.Ep2ChoiceBase", prelude_init + (
            "noncomputable def trustedChoiceBase : Nat := Classical.choice ⟨0⟩\n"), ["Init"])
        olean_module(ol2, "OlEp2UsesTrustedChoice", "prelude\nimport Trusted.Ep2ChoiceBase\n"
                     "noncomputable def badTransChoice : Nat := trustedChoiceBase\n", ["Trusted.Ep2ChoiceBase"])
        saved_modules = ol2.modules
        ol2.modules = {**saved_modules, "Trusted.Rustc.V2026_06_01.MirSemantics": "MirSemantics.lean",
                       "Trusted.VerificationResult": "VerificationResult.lean",
                       "Trusted.Ep2ChoiceBase": "Ep2ChoiceBase.lean"}
        ol2.spec_lib_owned = True
        try:
            owned = ol2.audit_olean_request({
                "roots": ["OlEp2SpecClean"], "modules": ["OlEp2SpecClean"], "artifacts": [],
                "specStrengthChecks": clean_checks, "scope": "ep2-owned-spec-lib",
            })
            assert owned["specStrengthChecksPassed"] == len(clean_checks), owned
            assert owned["constructiveModulesChecked"] == 1 and runner.SPEC_LIB_MODULE in owned["modules"], owned
            # A1-5a positive: constructive caller passes even though `Trusted.Ep2ChoiceBase` uses `Classical.choice`.
            owned_c_ok = ol2.audit_olean_request({
                "roots": ["OlEp2ConstructiveOk"], "modules": ["OlEp2ConstructiveOk"], "artifacts": [],
                "allowClassicalChoice": False, "scope": "ep2-a15a-ok",
            })
            assert owned_c_ok["constructiveModulesChecked"] == 2, owned_c_ok
            # A1-5a negative: caller transitively reaching `Trusted.Ep2ChoiceBase`'s `Classical.choice` is rejected.
            expect_failure(lambda: ol2.audit_olean_request({
                "roots": ["OlEp2UsesTrustedChoice"], "modules": ["OlEp2UsesTrustedChoice"], "artifacts": [],
                "allowClassicalChoice": False, "scope": "ep2-a15a-bad",
            }), 1, "olean-audit", "Classical.choice")
            # Ownership does not relax the rule: the caller still cannot name the library.
            expect_failure(lambda: ol2.audit_olean_request({
                "roots": ["OlEp2SpecClean"], "modules": ["OlEp2SpecClean", runner.SPEC_LIB_MODULE],
                "artifacts": [], "specStrengthChecks": clean_checks,
            }), 1, "olean-audit", "moduleProvenanceSpoofed", runner.SPEC_LIB_MODULE)
        finally:
            ol2.modules = saved_modules
            ol2.spec_lib_owned = False

        # B2-1 + A2-1a/b + A2-2a/b + A2-6 (forged registered-instance & default-instance entries).
        # `instanceExtension.add` bypasses `addInstance`'s "return type is a class" check, so forged
        # entries concluding in a variable (`T`, B2-1), stuck projection (`c.ty`, A2-1a), or stuck
        # eliminator (`Bool.rec _ s.a s.b s.tag`, A2-1b) keyed like `ItemSpec d` make `inferInstance`
        # resolve to weak specs (`rfl`-proved in `OlEp2ForgedUse`), and forged `defaultInstanceExtension`
        # entries (A2-6) can inject weak defaults; all must be caught as candidates.
        olean_module(ol2, "OlEp2ForgedInst", (
            "prelude\nimport Init\nimport Lean.Elab.Command\nimport OlEp2SpecClean\n"
            "open Lean Meta Trusted.VerificationResult\n"
            "instance fiStrong : ItemSpec \"ep2::fi\" where pre := epPre; post := epPost\n"
            "class FiHolder (T : Type 1) where val : T\n"
            "instance fiHolderInst : FiHolder (ItemSpec \"ep2::fi\") :=\n"
            "  ⟨{ pre := fun _ => False, post := fun _ _ => True }⟩\n"
            "def fiUniversal {T : Type 1} [h : FiHolder T] : T := h.val\n"
            "instance a2ProjStrong : ItemSpec \"ep2::a2proj\" where pre := epPre; post := epPost\n"
            "class A2Carrier : Type 2 where\n  ty : Type 1\n  inst : ty\n"
            "instance a2CarrierInst : A2Carrier where\n"
            "  ty := ItemSpec \"ep2::a2proj\"\n  inst := { pre := fun _ => False, post := fun _ _ => True }\n"
            "def a2ProjUniv [c : A2Carrier] : c.ty := c.inst\n"
            "instance a2RecStrong : ItemSpec \"ep2::a2rec\" where pre := epPre; post := epPost\n"
            "class A2Sum : Type 2 where\n"
            "  tag : Bool\n  a : Type 1\n  b : Type 1\n  inst : Bool.rec (motive := fun _ => Type 1) a b tag\n"
            "instance a2SumInst : A2Sum where\n"
            "  tag := false\n  a := ItemSpec \"ep2::a2rec\"\n  b := PUnit\n"
            "  inst := { pre := fun _ => False, post := fun _ _ => True }\n"
            "def a2RecUniv [s : A2Sum] : Bool.rec (motive := fun _ => Type 1) s.a s.b s.tag := s.inst\n"
            "def a2DefUniv [c : A2Carrier] : c.ty := c.inst\n"
            "run_cmd Elab.Command.liftTermElabM do\n"
            "  let k1 ← DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit \"ep2::fi\"))\n"
            "  instanceExtension.add { keys := k1, val := mkConst ``fiUniversal, priority := 5000, "
            "globalName? := some ``fiUniversal, synthOrder := #[1], attrKind := AttributeKind.global } AttributeKind.global\n"
            "  let k2 ← DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit \"ep2::a2proj\"))\n"
            "  instanceExtension.add { keys := k2, val := mkConst ``a2ProjUniv, priority := 5000, "
            "globalName? := some ``a2ProjUniv, synthOrder := #[0], attrKind := AttributeKind.global } AttributeKind.global\n"
            "  let k3 ← DiscrTree.mkPath (mkApp (mkConst ``ItemSpec) (mkStrLit \"ep2::a2rec\"))\n"
            "  instanceExtension.add { keys := k3, val := mkConst ``a2RecUniv, priority := 5000, "
            "globalName? := some ``a2RecUniv, synthOrder := #[0], attrKind := AttributeKind.global } AttributeKind.global\n"
            "  modifyEnv fun env => defaultInstanceExtension.addEntry env { className := ``ItemSpec, instanceName := ``a2DefUniv, priority := 1000 }\n"
            "instance fiOtherStrong : ItemSpec \"ep2::fi_other\" where pre := epPre; post := epPost\n"
            "def c_fi := epMultiCert\ndef c_fi_other := epMultiCert\n"
            "def c_a2proj := epMultiCert\ndef c_a2rec := epMultiCert\n"),
            ["Init", "Lean.Elab.Command", "OlEp2SpecClean"])
        olean_module(ol2, "OlEp2ForgedUse", (
            "prelude\nimport Init\nimport OlEp2ForgedInst\n"
            "open Trusted.VerificationResult\n"
            "theorem fiResolvesWeak : (inferInstance : ItemSpec \"ep2::fi\").pre [0] = False := rfl\n"
            "theorem a2ProjResolvesWeak : (inferInstance : ItemSpec \"ep2::a2proj\").pre [0] = False := rfl\n"
            "theorem a2RecResolvesWeak : (inferInstance : ItemSpec \"ep2::a2rec\").pre [0] = False := rfl\n"),
            ["Init", "OlEp2ForgedInst"])
        forged_mods = base_spec_mods + ["OlEp2SpecClean", "OlEp2ForgedInst", "OlEp2ForgedUse"]
        fi_err = olean_reject(
            ol2, forged_mods,
            "[specInstanceAmbiguous] c_fi", "fiUniversal",
            "[specInstanceAmbiguous] c_a2proj", "a2ProjUniv", "a2DefUniv",
            "[specInstanceAmbiguous] c_a2rec", "a2RecUniv",
            "[specInstanceAmbiguous] c_fi_other", "fiOtherStrong",
            toolchainRoots=["Init", "Std", "Lean"],
            specStrengthChecks=[
                {"kind": "itemSynth", "defId": "ep2::fi", "cert": "c_fi"},
                {"kind": "itemSynth", "defId": "ep2::a2proj", "cert": "c_a2proj"},
                {"kind": "itemSynth", "defId": "ep2::a2rec", "cert": "c_a2rec"},
                {"kind": "itemSynth", "defId": "ep2::fi_other", "cert": "c_fi_other"},
            ])
        assert "#[a2DefUniv, a2ProjUniv, a2RecUniv, fiOtherStrong, fiUniversal]" in fi_err, fi_err

        # A2-2a & A2-2b (forged `isGlobalInstanceRegistered` entries): a plain non-instance `def`
        # backed by a `.global` entry with either a spoofed `globalName?` on an unrelated `val`
        # (A2-2a) or wrong discrimination-tree keys (A2-2b) must still fail with `specStrengthCertMissing`.
        olean_module(ol2, "OlEp2ForgedKeys", (
            "prelude\nimport Init\nimport Lean.Elab.Command\nimport OlEp2SpecClean\n"
            "open Lean Meta Trusted.VerificationResult\n"
            "def a2Plain : ItemSpec \"ep2::a2plain\" := { pre := epPre, post := epPost }\n"
            "def a2Dummy : Nat := 0\n"
            "def a2WrongKeys : ItemSpec \"ep2::a2wkeys\" := { pre := epPre, post := epPost }\n"
            "run_cmd Elab.Command.liftTermElabM do\n"
            "  let natKeys ← DiscrTree.mkPath (mkConst ``Nat)\n"
            "  instanceExtension.add { keys := natKeys, val := mkConst ``a2Dummy, priority := 1000, "
            "globalName? := some ``a2Plain, synthOrder := #[], attrKind := AttributeKind.global } AttributeKind.global\n"
            "  instanceExtension.add { keys := natKeys, val := mkConst ``a2WrongKeys, priority := 1000, "
            "globalName? := some ``a2WrongKeys, synthOrder := #[], attrKind := AttributeKind.global } AttributeKind.global\n"),
            ["Init", "Lean.Elab.Command", "OlEp2SpecClean"])
        olean_reject(
            ol2, base_spec_mods + ["OlEp2SpecClean", "OlEp2ForgedKeys"],
            "[specStrengthCertMissing] a2Plain",
            "[specStrengthCertMissing] a2WrongKeys",
            toolchainRoots=["Init", "Std", "Lean"],
            specStrengthChecks=[
                {"kind": "itemSynth", "defId": "ep2::a2plain", "cert": "epMultiCert"},
                {"kind": "itemSynth", "defId": "ep2::a2wkeys", "cert": "epMultiCert"},
            ])

        # A3-1 (`module`-file unexported private instance vs exported `public instance`):
        # In a `module` file, a non-`public` instance is withheld from `.olean` (`exportEntry?`
        # exports `none` for `isPrivateName`), so `module` importers cannot synthesize it; standalone
        # `itemSynth` must reject it with `specStrengthCertMissing` while accepting `public instance`.
        olean_module(ol2, "OlEp2ModVis", (
            "module\nprelude\npublic import Init\npublic import Anneal.OleanSpecStrengthAuditor\n"
            "open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.VerificationResult Anneal.OleanSpecStrengthAuditor\n"
            "public section\n"
            "@[expose] def mvPre (xs : List Value) : Prop := xs = [0]\n"
            "@[expose] def mvPost (_ : List Value) (r : Value) : Prop := r = 10\n"
            "@[expose] def mvCert : SpecStrengthCert mvPre mvPost := {\n"
            "  witnessInput := [0], witnessValid := rfl, referenceOutput := 10, referenceAccepted := rfl,\n"
            "  mutantOutput := 0, mutantRejected := (by dsimp [mvPost]; decide) }\n"
            "public instance mvPubInst : ItemSpec \"ep2::mv_pub\" where pre := mvPre; post := mvPost\n"
            "end\n"
            "instance mvPrivInst : ItemSpec \"ep2::mv_priv\" where pre := mvPre; post := mvPost\n"),
            ["Init", "Anneal.OleanSpecStrengthAuditor"], module_file=True)
        mv_ok = olean_accept(ol2, base_spec_mods + ["OlEp2ModVis"],
                             specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::mv_pub", "cert": "mvCert"}])
        assert mv_ok["specStrengthChecksPassed"] == 1, mv_ok
        olean_reject(ol2, base_spec_mods + ["OlEp2ModVis"], "[specStrengthCertMissing]", "mvPrivInst",
                     specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::mv_priv", "cert": "mvCert"}])

        # A4-7 (26-deep binary branching) in a compiled `.olean`.
        exp_lines = ["prelude", "import Init", "import OlEp2SpecClean", "open Trusted.VerificationResult",
                     "instance expStrong : ItemSpec \"ep2::exp\" where pre := epPre; post := epPost",
                     "noncomputable section", "def eb0 : Bool := true"]
        for k in range(1, 27):
            exp_lines.append(f"def eb{k} : Bool := Bool.rec eb{k - 1} eb{k - 1} eb{k - 1}")
        exp_lines.append("def expWeak : Bool.rec (motive := fun _ => Type 1) PUnit (ItemSpec \"ep2::exp\") eb26 :=")
        exp_lines.append("  { pre := fun _ => False, post := fun _ _ => True }")
        exp_lines.append("end\n")
        olean_module(ol2, "OlEp2A4Exp", "\n".join(exp_lines), ["Init", "OlEp2SpecClean"])
        t_exp0 = time.monotonic()
        olean_reject(ol2, base_spec_mods + ["OlEp2SpecClean", "OlEp2A4Exp"], "[specInstanceAmbiguous]",
                     specStrengthChecks=[{"kind": "itemSynth", "defId": "ep2::exp", "cert": "epMultiCert"}])
        assert time.monotonic() - t_exp0 < 20.0, "A4-7 linear-budget gate exceeded time budget"

        runner.make_tree_writable(ol2.stage)
        shutil.rmtree(ol2.stage)
        runner.make_tree_writable(ol2.checkout)
        shutil.rmtree(ol2.checkout)
        done("Episode 2 compiled spec-strength gates (V8/V9, 4 claim & 4 synth kinds, A1-4, A3-3 _sunfold, A1-2/S3 shadows, "
             "B1-1 theorem-major, B1-4/A1-1/A2-5 native-evaluator canaries, B1-5/A1-5/A2-4 provenance & constructive, "
             "A1-3/A1-6, B2-1/A2-1/A2-2/A2-6/A3-1 forged & private-module instances, A4-7)")
    except BaseException as error:
        (suite / "failure.traceback").write_text(traceback.format_exc())
        print(f"SELF-TEST FAILED: {error}\nPreserved fixture sources/raw logs: {suite}", file=sys.stderr)
        return 2
    finally:
        # This module loads its own copy of the checker; its per-process auditor binaries are not
        # the ones `check_trusted.main()` removes.
        runner.remove_process_binaries()
    print(f"PASS: {len(passed)} fixture groups in {time.monotonic() - started:.1f}s; sequential, no research builds")
    shutil.rmtree(suite)
    return 0
