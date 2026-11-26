#!/usr/bin/env python3
"""Check the declared-import, kernel-dependency, statement-origin, and Cargo boundaries of Anneal.

No downloads, Lake, cache, project hooks, or shell commands. See trusted/README.md
and trusted/audit/README.md.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import tomllib

sys.dont_write_bytecode = True  # Public self-test imports must not write checkout caches.


TOOLCHAIN = "leanprover/lean4:v4.34.1"
PARTS = ("olean", "olean.server", "olean.private", "ir.sig", "ir")
MAX_BYTES = 512 * 1024 * 1024
CHILD_TIMEOUT_SECS = 180
# The compiled-environment auditor re-checks every non-toolchain declaration in the kernel (the
# downstream environment holds ~50k declarations), so it gets a longer, still bounded, envelope.
OLEAN_CHILD_TIMEOUT_SECS = 900
# Natively compiled auditor binaries built by this process without `--fast` (never shared between
# processes; `main()` removes them on exit): `{binary key: path}`.
_PROCESS_OLEAN_BINARIES: dict[str, Path] = {}


def remove_process_binaries() -> None:
    """Remove the per-process auditor binaries built without `--fast`."""
    for path in _PROCESS_OLEAN_BINARIES.values():
        shutil.rmtree(path.parent, ignore_errors=True)
    _PROCESS_OLEAN_BINARIES.clear()


OLEAN_AUDITOR = "trusted/audit/OleanEnvAuditor.lean"
OLEAN_AUDIT_MODES = ("olean-audit", "olean-downstream-audit")
ROOT_MANIFEST = "trusted/root-manifest.sha256"
ROOT_MANIFEST_PHASE = "root-manifest"
# The trusted checker and the compiled environment auditor must always be covered by the root
# manifest, next to the root build inputs it already pins.
ROOT_MANIFEST_REQUIRED = ("trusted/audit/check_trusted.py", OLEAN_AUDITOR)
ROOT_MANIFEST_REPO_REQUIRED = (
    "Cargo.toml",
    "Cargo.lock",
    "flake.nix",
    "flake.lock",
    "trusted/audit/check_trusted.py",
    OLEAN_AUDITOR,
)
OLEAN_RESULT_KEYS = frozenset({
    "auditor", "schema", "scope", "modules", "loadedModules", "artifactPartsChecked",
    "auditedDeclarations", "reachableDeclarations", "codegenCompanions", "irDeclarationsChecked",
    "intrinsicTagsChecked", "kernelTagConfirmations", "constructiveModulesChecked",
    "specStrengthChecksPassed", "axioms", "localTestAxioms",
    "kernelConfirmedNativeAxioms", "provisionalNativeAxioms", "replayedDeclarations", "replay",
    "importMicros", "elapsedMicros"})
OLEAN_COUNT_KEYS = ("loadedModules", "artifactPartsChecked", "auditedDeclarations", "reachableDeclarations",
                    "codegenCompanions", "irDeclarationsChecked", "intrinsicTagsChecked",
                    "kernelTagConfirmations", "constructiveModulesChecked", "specStrengthChecksPassed",
                    "localTestAxioms", "replayedDeclarations", "importMicros", "elapsedMicros")
SPEC_CHECK_ALLOWED_KEYS = frozenset({
    "kind", "claim", "defId", "cert", "requiredCategories",
    "requireDeterministic", "requireInputSensitive"})
SPEC_CHECK_SYNTH_KINDS = frozenset({
    "itemSynth", "statefulItemSynth", "totalItemSynth", "modularItemSynth"})
# The specification-strength gate trusts the certificate types and `coversCategory` of this module
# (OleanEnvAuditor matches them by declaring module). Like `Trusted`, it is therefore always compiled
# from the checkout by this checker and can never be supplied or named by an `--audit-olean` caller.
SPEC_LIB_MODULE = "Anneal.OleanSpecStrengthAuditor"

# Each entry is (module_name, relative_path, direct_imports, role)
# where role is "theory", "examples", "claim", or "test".
DOWNSTREAM_TARGETS = [
    ("Anneal.Refinement", "theory/Anneal/Refinement.lean", ["Trusted"], "theory"),
    ("Anneal.Effect", "theory/Anneal/Effect.lean", ["Trusted"], "theory"),
    ("Anneal.ITree", "theory/Anneal/ITree.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect"], "theory"),
    ("Anneal.Pass", "theory/Anneal/Pass.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree"], "theory"),
    ("Anneal.EffectWP", "theory/Anneal/EffectWP.lean", ["Trusted", "Anneal.Effect"], "theory"),
    ("Anneal.ITreeWP", "theory/Anneal/ITreeWP.lean", ["Std.Do", "Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.EffectWP"], "theory"),
    ("Anneal.Scalars", "theory/Anneal/Scalars.lean", ["Trusted"], "theory"),
    ("Anneal.Memory", "theory/Anneal/Memory.lean", ["Trusted"], "theory"),
    ("Anneal.BitValidity", "theory/Anneal/BitValidity.lean", ["Trusted", "Anneal.Scalars"], "theory"),
    ("Anneal.UnsafeObligations", "theory/Anneal/UnsafeObligations.lean", ["Trusted", "Anneal.Memory"], "theory"),
    ("Anneal.SepLogic", "theory/Anneal/SepLogic.lean", ["Trusted", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Memory", "Anneal.UnsafeObligations"], "theory"),
    ("Anneal.Rustc.V2026_06_01.Lower", "theory/Anneal/Rustc/V2026_06_01/Lower.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.SepLogic"], "theory"),
    ("Anneal.Rustc.V2026_06_01.SymbolicEval", "theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Scalars", "Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower"], "theory"),
    ("Anneal.Rustc.V2026_06_01.SymReflect", "theory/Anneal/Rustc/V2026_06_01/SymReflect.lean", ["Trusted", "Anneal.ITreeWP", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval"], "theory"),
    ("Anneal.Rustc.V2026_06_01.TraceCheck", "theory/Anneal/Rustc/V2026_06_01/TraceCheck.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Rustc.V2026_06_01.Lower"], "theory"),
    ("Anneal.FunctionalTranslation", "theory/Anneal/FunctionalTranslation.lean", ["Trusted", "Anneal.Refinement", "Anneal.ITree", "Anneal.ITreeWP", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower"], "theory"),
    ("Anneal.MirFuelFree", "theory/Anneal/MirFuelFree.lean", ["Trusted", "Anneal.ITreeWP", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.FunctionalTranslation"], "theory"),
    ("Anneal.MirLoops", "theory/Anneal/MirLoops.lean", ["Anneal.MirFuelFree", "Anneal.FunctionalTranslation"], "theory"),
    ("Anneal.PureMirExec", "theory/Anneal/PureMirExec.lean", ["Trusted", "Anneal.MirFuelFree"], "theory"),
    ("Anneal.MirLiftCore", "theory/Anneal/MirLiftCore.lean", ["Trusted", "Anneal.MirFuelFree", "Anneal.PureMirExec", "Anneal.MirLoops"], "theory"),
    ("Anneal.MirLiftBench", "theory/Anneal/MirLiftBench.lean", ["Trusted", "Anneal.MirFuelFree", "Anneal.PureMirExec", "Anneal.MirLiftCore"], "theory"),
    ("Anneal.SepLogicLenses", "theory/Anneal/SepLogicLenses.lean", ["Anneal.SepLogic", "Anneal.FunctionalTranslation", "Anneal.MirLiftCore", "Anneal.MirFuelFree"], "theory"),
    ("Anneal.PureLift.Lens", "theory/Anneal/PureLift/Lens.lean", [], "theory"),
    ("Anneal.PureLift.PermTree", "theory/Anneal/PureLift/PermTree.lean", ["Anneal.PureLift.Lens"], "theory"),
    ("Anneal.PureLift.LoanGraph", "theory/Anneal/PureLift/LoanGraph.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree"], "theory"),
    ("Anneal.PureLift.SpatialPin", "theory/Anneal/PureLift/SpatialPin.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph"], "theory"),
    ("Anneal.PureLift.Plan", "theory/Anneal/PureLift/Plan.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin"], "theory"),
    ("Anneal.PureLift.BlockCfg", "theory/Anneal/PureLift/BlockCfg.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan"], "theory"),
    ("Anneal.PureLift.Adapter", "theory/Anneal/PureLift/Adapter.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg"], "theory"),
    ("Anneal.PureLift.Canaries.Fixtures", "theory/Anneal/PureLift/Canaries/Fixtures.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter"], "theory"),
    ("Anneal.PureLift.Canaries.CoreAndHardening", "theory/Anneal/PureLift/Canaries/CoreAndHardening.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries.Fixtures"], "theory"),
    ("Anneal.PureLift.Canaries.PlanAndCfg", "theory/Anneal/PureLift/Canaries/PlanAndCfg.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries.Fixtures"], "theory"),
    ("Anneal.PureLift.Canaries.RegionReuse", "theory/Anneal/PureLift/Canaries/RegionReuse.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries.Fixtures"], "theory"),
    ("Anneal.PureLift.Canaries.Writebacks", "theory/Anneal/PureLift/Canaries/Writebacks.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries.Fixtures"], "theory"),
    ("Anneal.PureLift.Canaries", "theory/Anneal/PureLift/Canaries.lean", ["Anneal.PureLift.Canaries.Fixtures", "Anneal.PureLift.Canaries.CoreAndHardening", "Anneal.PureLift.Canaries.PlanAndCfg", "Anneal.PureLift.Canaries.RegionReuse", "Anneal.PureLift.Canaries.Writebacks"], "theory"),
    ("Anneal.PureLift.MirLiftCoreInterop", "theory/Anneal/PureLift/MirLiftCoreInterop.lean", ["Anneal.BitValidity", "Anneal.MirLiftCore", "Anneal.SepLogicLenses", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Canaries"], "theory"),
    ("Anneal.PureLift.V2026_06_01Bridge", "theory/Anneal/PureLift/V2026_06_01Bridge.lean", ["Anneal.PureLift.MirLiftCoreInterop"], "theory"),
    ("Anneal.PureLift", "theory/Anneal/PureLift.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries", "Anneal.PureLift.MirLiftCoreInterop", "Anneal.PureLift.V2026_06_01Bridge"], "theory"),
    ("Anneal.OleanSpecStrengthAuditor", "theory/Anneal/OleanSpecStrengthAuditor.lean", ["Trusted"], "theory"),
    ("Anneal", "theory/Anneal.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.MirLoops", "Anneal.Scalars", "Anneal.Memory", "Anneal.BitValidity", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.Rustc.V2026_06_01.SymReflect", "Anneal.Rustc.V2026_06_01.TraceCheck", "Anneal.FunctionalTranslation", "Anneal.MirFuelFree", "Anneal.PureMirExec", "Anneal.MirLiftCore", "Anneal.MirLiftBench", "Anneal.SepLogicLenses", "Anneal.PureLift", "Anneal.OleanSpecStrengthAuditor"], "theory"),
    ("Smoke", "examples/Smoke.lean", ["Anneal"], "examples"),
    ("ToyYDiagram", "examples/refinement/ToyYDiagram.lean", ["Anneal.Refinement"], "examples"),
    ("ToyMachine", "examples/step-result/ToyMachine.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass"], "examples"),
    ("ToyCFG", "examples/pass/ToyCFG.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass"], "examples"),
    ("MirVerification", "examples/mir/MirVerification.lean", ["Trusted", "Anneal"], "examples"),
    ("SmokeTest", "tests/Smoke.lean", ["Anneal"], "claim"),
    ("AxiomaticYDiagram", "tests/refinement/AxiomaticYDiagram.lean", ["Anneal.Refinement"], "test"),
    ("ConcreteYDiagram", "tests/refinement/ConcreteYDiagram.lean", ["Anneal.Refinement", "ToyYDiagram"], "test"),
    ("AxiomaticSimulation", "tests/step-result/AxiomaticSimulation.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass"], "test"),
    ("Canaries", "tests/step-result/Canaries.lean", ["Std.Do", "Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "ToyMachine"], "test"),
    ("AxiomaticForwarder", "tests/pass/AxiomaticForwarder.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass"], "test"),
    ("ConcreteForwarder", "tests/pass/ConcreteForwarder.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "ToyCFG"], "test"),
    ("SymbolicEvalTests", "tests/mir/SymbolicEvalTests.lean", ["Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.Rustc.V2026_06_01.SymReflect"], "test"),
    ("FunctionalTranslationTests", "tests/mir/FunctionalTranslationTests.lean", ["Anneal.FunctionalTranslation"], "test"),
    ("FunctionalTranslationEquivTests", "tests/mir/FunctionalTranslationEquivTests.lean", ["Anneal.FunctionalTranslation"], "test"),
    ("PureLiftV2026BridgeTests", "tests/mir/PureLiftV2026BridgeTests.lean", ["Anneal.PureLift.V2026_06_01Bridge"], "test"),
]


class Failure(Exception):
    def __init__(self, code: int, phase: str, message: str):
        super().__init__(message)
        self.code, self.phase = code, phase


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fingerprint(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def regular(path: Path, phase: str) -> None:
    try:
        mode = path.lstat().st_mode
    except OSError as error:
        raise Failure(2, phase, f"cannot inspect {path}: {error}") from error
    if not stat.S_ISREG(mode):
        raise Failure(1, phase, f"expected a regular file: {path}")


def require(condition, phase, message):
    if not condition:
        raise Failure(2, phase, message)


def valid_imports(value):
    return isinstance(value, list) and all(
        isinstance(edge, dict) and set(edge) == {"module", "importAll", "isExported", "isMeta"}
        and isinstance(edge["module"], str) and bool(edge["module"])
        and all(type(edge[k]) is bool for k in ("importAll", "isExported", "isMeta")) for edge in value)


def valid_graph(value):
    return isinstance(value, dict) and all(isinstance(k, str) and k and valid_imports(v) for k, v in value.items())


def is_stdlib_module(name: str, prefix: Path) -> bool:
    if not (name in ("Init", "Std") or name.startswith(("Init.", "Std."))):
        return False
    if not re.fullmatch(r"(?:Init|Std)(?:\.[A-Za-z][A-Za-z0-9_]*)*", name):
        return False
    return (prefix / "lib/lean" / (name.replace(".", "/") + ".olean")).is_file()


def check_cargo_boundary(checkout: Path) -> dict[str, str]:
    """Verify that trusted/rustc-capture has zero dependencies on untrusted workspace crates."""
    phase = "cargo-boundary"
    root_toml_path = checkout / "Cargo.toml"
    trusted_toml_path = checkout / "trusted/rustc-capture/Cargo.toml"
    for path in (root_toml_path, trusted_toml_path):
        regular(path, phase)
    try:
        root_toml = tomllib.loads(root_toml_path.read_text())
        trusted_toml = tomllib.loads(trusted_toml_path.read_text())
    except (tomllib.TOMLDecodeError, OSError) as error:
        raise Failure(1, phase, f"malformed Cargo manifest: {error}") from error
    workspace = root_toml.get("workspace")
    if not isinstance(workspace, dict) or not isinstance(workspace.get("members"), list):
        raise Failure(1, phase, "missing workspace.members in root Cargo.toml")
    members = workspace["members"]
    if "trusted/rustc-capture" not in members:
        raise Failure(1, phase, "trusted/rustc-capture missing from workspace.members")
    untrusted_crate_names = set()
    for member in members:
        if not isinstance(member, str):
            raise Failure(1, phase, "non-string workspace member")
        member_toml_path = checkout / member / "Cargo.toml"
        regular(member_toml_path, phase)
        try:
            member_toml = tomllib.loads(member_toml_path.read_text())
        except (tomllib.TOMLDecodeError, OSError) as error:
            raise Failure(1, phase, f"malformed member Cargo.toml in {member}: {error}") from error
        pkg_name = member_toml.get("package", {}).get("name")
        if not isinstance(pkg_name, str) or not pkg_name:
            raise Failure(1, phase, f"missing package.name in {member}")
        if not member.startswith("trusted/"):
            untrusted_crate_names.add(pkg_name)

    def check_dep_table(table: object, section: str) -> None:
        if table is None:
            return
        if not isinstance(table, dict):
            raise Failure(1, phase, f"invalid {section} in trusted/rustc-capture/Cargo.toml")
        for dep_name, spec in table.items():
            if dep_name in untrusted_crate_names:
                raise Failure(1, phase, f"trusted/rustc-capture depends on untrusted workspace crate {dep_name}")
            if isinstance(spec, dict):
                pkg = spec.get("package")
                if isinstance(pkg, str) and pkg in untrusted_crate_names:
                    raise Failure(1, phase, f"trusted/rustc-capture depends on untrusted workspace crate {pkg}")
                dep_path = spec.get("path")
                if isinstance(dep_path, str):
                    resolved = (trusted_toml_path.parent / dep_path).resolve()
                    try:
                        rel = resolved.relative_to(checkout.resolve()).as_posix()
                    except ValueError:
                        raise Failure(1, phase, f"trusted/rustc-capture path dependency escapes checkout: {dep_path}")
                    if not rel.startswith("trusted/"):
                        raise Failure(1, phase, f"trusted/rustc-capture path dependency points outside trusted/: {rel}")

    for section in ("dependencies", "dev-dependencies", "build-dependencies"):
        check_dep_table(trusted_toml.get(section), section)
    targets = trusted_toml.get("target")
    if isinstance(targets, dict):
        for cfg_name, cfg_table in targets.items():
            if isinstance(cfg_table, dict):
                for section in ("dependencies", "dev-dependencies", "build-dependencies"):
                    check_dep_table(cfg_table.get(section), f"target.{cfg_name}.{section}")
    return {
        "Cargo.toml": digest(root_toml_path),
        "trusted/rustc-capture/Cargo.toml": digest(trusted_toml_path),
    }


def verify_capture_manifest(manifest_path: Path, root: Path) -> dict:
    """Verify a CaptureManifest.json handshake against .rs and Mir/<Item>.lean files on disk."""
    phase = "manifest"
    regular(manifest_path, phase)
    try:
        manifest = json.loads(manifest_path.read_text())
    except (ValueError, OSError) as error:
        raise Failure(1, phase, f"malformed CaptureManifest.json: {error}") from error
    if not isinstance(manifest, dict) or set(manifest) != {"schema", "compilation_succeeded", "rust_sources", "targets"}:
        raise Failure(1, phase, "unexpected CaptureManifest.json schema keys")
    if manifest["schema"] != 1:
        raise Failure(1, phase, f"unsupported CaptureManifest.json schema {manifest['schema']}")
    if manifest["compilation_succeeded"] is not True:
        raise Failure(1, phase, "compilation_succeeded is not true in CaptureManifest.json")
    if not isinstance(manifest["rust_sources"], list) or not manifest["rust_sources"]:
        raise Failure(1, phase, "CaptureManifest.json must record at least one Rust source file")

    def climbs_above_root(rel: str) -> bool:
        norm = os.path.normpath(rel)
        return norm == os.pardir or norm.startswith(os.pardir + os.sep)

    root_resolved = root.resolve()
    rust_audit_sources: list[tuple[str, Path]] = []
    for entry in manifest["rust_sources"]:
        if (not isinstance(entry, list) or len(entry) != 2
                or not all(isinstance(x, str) and x for x in entry)
                or not re.fullmatch(r"[0-9a-f]{64}", entry[1])):
            raise Failure(1, phase, "invalid rust_sources entry in CaptureManifest.json")
        # rustc-capture records sources relative to its working directory and keeps the
        # absolute path of a primary-package source outside it (`#[path]` modules, generated
        # `include!` files), so absolute entries are digest-checked as recorded; a relative
        # entry, however, must not climb above the manifest root (`../escape.rs`).
        if not os.path.isabs(entry[0]) and climbs_above_root(entry[0]):
            raise Failure(1, phase, f"CaptureManifest.json rust_sources path escapes checkout: {entry[0]}")
        raw_src = root / entry[0]
        regular(raw_src, phase)
        src_path = raw_src.resolve()
        regular(src_path, phase)
        if digest(src_path) != entry[1]:
            raise Failure(1, phase, f"Rust source digest mismatch for {entry[0]}")
        rust_audit_sources.append((entry[0], src_path))
    if not isinstance(manifest["targets"], list) or not manifest["targets"]:
        raise Failure(1, phase, "CaptureManifest.json must record at least one verification target")
    seen_defs = set()
    lean_audit_targets: list[tuple[str, Path]] = []
    for target in manifest["targets"]:
        if (not isinstance(target, dict)
                or set(target) != {"def_id", "mir_module_path", "mir_module_sha256"}
                or not all(isinstance(target[k], str) and target[k] for k in target)
                or not re.fullmatch(r"[0-9a-f]{64}", target["mir_module_sha256"])):
            raise Failure(1, phase, "invalid target entry in CaptureManifest.json")
        if target["def_id"] in seen_defs:
            raise Failure(1, phase, f"duplicate target def_id {target['def_id']}")
        seen_defs.add(target["def_id"])
        # Generated `Mir/<Item>.lean` modules live under the manifest root (cargo-anneal derives
        # their module names from the relative path): absolute, root-escaping, symlinked, or
        # non-`.lean` paths fail.
        mir_rel = target["mir_module_path"]
        if os.path.isabs(mir_rel) or climbs_above_root(mir_rel):
            raise Failure(
                1, phase, f"CaptureManifest.json mir_module_path escapes checkout: {mir_rel}"
            )
        if not mir_rel.endswith(".lean"):
            raise Failure(
                1, phase, f"CaptureManifest.json mir_module_path must be a .lean file: {mir_rel}"
            )
        raw_mir = root / mir_rel
        regular(raw_mir, phase)
        mir_path = raw_mir.resolve()
        try:
            mir_path.relative_to(root_resolved)
        except ValueError:
            raise Failure(
                1, phase, f"CaptureManifest.json mir_module_path escapes checkout: {mir_rel}"
            )
        regular(mir_path, phase)
        if digest(mir_path) != target["mir_module_sha256"]:
            raise Failure(1, phase, f"Mir module digest mismatch for {mir_rel}")
        lean_audit_targets.append((mir_rel, mir_path))
    # Waiver pins on the captured Rust sources (`lang="rust"` so included non-`.rs` files
    # cannot evade `audit_rust_text`); waiver pins plus annotated-claim non-vacuity on the
    # `Mir/<Item>.lean` targets (`lang="lean"`, after their digests matched).
    audit_waivers_and_vacuity(rust_audit_sources, vacuity=False, lang="rust")
    audit_waivers_and_vacuity(lean_audit_targets, vacuity=True, lang="lean")
    return manifest


def snapshot(root: Path) -> tuple[dict, dict[str, str]]:
    """Complete root inventory, including files added after initial discovery."""
    if root.is_symlink() or not root.is_dir():
        raise Failure(1, "snapshot", f"expected regular source directory: {root}")
    inventory, modules, folded = {}, {}, set()
    def walk_error(error):
        raise Failure(2, "snapshot", f"incomplete source-directory observation: {error}")

    for directory, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        for name in sorted(dirs + files):
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            if relative.casefold() in folded:
                raise Failure(1, "snapshot", f"case-colliding entry: {relative}")
            folded.add(relative.casefold())
            mode = path.lstat().st_mode
            if stat.S_ISDIR(mode):
                inventory[relative] = {"kind": "directory"}
                continue
            regular(path, "snapshot")
            if any(relative.endswith("." + part) for part in PARTS) or relative.endswith(".ilean"):
                raise Failure(1, "snapshot", f"compiled artifact in source root: {relative}")
            inventory[relative] = {"kind": "file", "sha256": digest(path), "bytes": path.stat().st_size}
            if path.suffix == ".lean":
                components = relative[:-5].split("/")
                if components[0] != "Trusted" or not all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", c) for c in components):
                    raise Failure(1, "snapshot", f"unmappable Lean source: {relative}")
                module = ".".join(components)
                if module in modules:
                    raise Failure(1, "snapshot", f"duplicate module: {module}")
                modules[module] = relative
            elif relative.startswith("locks/"):
                if not re.fullmatch(r"locks/foundation-lock-[A-Za-z0-9._-]+\.json", relative):
                    raise Failure(1, "snapshot", f"unexpected file in locks/: {relative}")
    if "Trusted" not in modules:
        raise Failure(1, "snapshot", "missing Trusted.lean umbrella")
    if sum(e.get("bytes", 0) for e in inventory.values()) > MAX_BYTES // 8:
        raise Failure(2, "snapshot", "Trusted input exceeds the small-check resource envelope")
    return inventory, dict(sorted(modules.items()))


def _trusted_cache_file(path: Path) -> bool:
    """A cache entry is used only if it is a regular file owned by this user and writable by no
    one else; anything else is a cache miss (the gate recomputes, it never trusts the entry)."""
    try:
        st = path.lstat()
    except OSError:
        return False
    return (stat.S_ISREG(st.st_mode) and st.st_uid == os.getuid()
            and not st.st_mode & (stat.S_IWGRP | stat.S_IWOTH))


def _trusted_cache_dir(path: Path) -> bool:
    """A cache directory is trusted only if it is a regular directory owned by this user and
    writable by no one else."""
    try:
        st = path.lstat()
    except OSError:
        return False
    return (stat.S_ISDIR(st.st_mode) and st.st_uid == os.getuid()
            and not st.st_mode & (stat.S_IWGRP | stat.S_IWOTH))


def _trusted_cache_tree(cache_root: Path, target: Path, *, is_dir: bool = False) -> bool:
    """Verify `cache_root`, every intermediate directory down to `target`, and `target` itself
    contain no symlinks and are owned by this user with no group/world write permission."""
    try:
        rel = target.relative_to(cache_root)
    except ValueError:
        return False
    cur = cache_root
    if not _trusted_cache_dir(cur):
        return False
    parts = rel.parts
    for part in parts[:-1]:
        cur = cur / part
        if not _trusted_cache_dir(cur):
            return False
    if not parts:
        return is_dir
    return _trusted_cache_dir(target) if is_dir else _trusted_cache_file(target)


def _ensure_trusted_cache_dir(cache_root: Path, target_dir: Path) -> bool:
    """Create `cache_root`..`target_dir` with private permissions if absent, and confirm every
    directory in the chain satisfies `_trusted_cache_dir` (refusing symlinks or shared dirs)."""
    try:
        rel = target_dir.relative_to(cache_root)
    except ValueError:
        return False
    try:
        if not cache_root.exists() and not cache_root.is_symlink():
            cache_root.mkdir(parents=True, exist_ok=True)
            cache_root.chmod(0o700)
        if not _trusted_cache_dir(cache_root):
            return False
        cur = cache_root
        for part in rel.parts:
            cur = cur / part
            if not cur.exists() and not cur.is_symlink():
                cur.mkdir(mode=0o700)
            if not _trusted_cache_dir(cur):
                return False
        return True
    except OSError:
        return False


def _canonical_regular(path: Path) -> bool:
    """True iff `path` is an absolute, canonical, non-symlinked regular file whose containing
    directory also resolves to itself."""
    if not path.is_absolute():
        return False
    try:
        st = path.lstat()
        if not stat.S_ISREG(st.st_mode):
            return False
        return path.resolve() == path and path.parent.resolve() == path.parent
    except OSError:
        return False


class Checker:
    def __init__(
        self,
        checkout: Path,
        lean: Path | None = None,
        *,
        temp_parent: Path | None = None,
        fast: bool = False,
        cache_dir: Path | None = None,
        base_snapshot: Path | None = None,
        expected_tcb_drift: tuple[str, ...] = (),
    ):
        self.checkout = checkout.resolve()
        self.source = self.checkout / "trusted/lean"
        self.lean = (lean or Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean").absolute()
        self.fast = bool(fast)
        self.base_snapshot = base_snapshot.resolve() if base_snapshot is not None else None
        self.expected_tcb_drift = tuple(expected_tcb_drift)
        self.cache_dir: Path | None = None
        self.expected_lean_sha: str | None = None
        self._compiled_inspector: Path | None = None
        self._compiled_olean_auditor: Path | None = None
        self.root_manifest: dict[str, str] | None = None
        if self.fast:
            env_cache = os.environ.get("ANNEAL_TRUSTED_CACHE_DIR")
            raw_cache = (
                cache_dir
                if cache_dir is not None
                else (
                    Path(env_cache)
                    if env_cache
                    else Path(tempfile.gettempdir()) / f"anneal-trusted-cache-{os.getuid()}"
                )
            )
            self.cache_dir = raw_cache.resolve()
            if self.cache_dir == self.checkout or self.checkout in self.cache_dir.parents:
                raise Failure(2, "admission", f"cache directory must reside outside checkout: {self.cache_dir}")
        self.stage = Path(tempfile.mkdtemp(prefix="anneal-trusted-", dir=temp_parent)).resolve()
        self.phase, self.execution_began, self.counter = "admission", False, 0
        self.environment = {k: v for k, v in os.environ.items()
                            if not k.startswith(("LEAN", "LAKE", "ELAN", "DYLD_"))}
        self.environment["PATH"] = os.defpath
        self.artifacts: dict[str, list[list[str]]] = {}
        self.graph: dict = {}
        self.expected_artifacts: dict[str, str] = {}
        # Set once this checker has compiled `SPEC_LIB_MODULE` from the checkout and audited it
        # (constructive policy + live model certificates).
        self.spec_lib_owned = False
        self.last_status = None

    def budget(self) -> None:
        size = sum(p.stat().st_size for p in self.stage.rglob("*") if p.is_file())
        if size > MAX_BYTES:
            raise Failure(2, self.phase, "512 MiB retained-build envelope exceeded")

    def process(self, label: str, arguments: list[str], *, executable: Path | None = None,
                timeout: int = CHILD_TIMEOUT_SECS) -> str:
        self.phase = label
        self.counter += 1
        stem = self.stage / f"{self.counter:03d}-{label}"
        stdout, stderr = Path(str(stem) + ".stdout"), Path(str(stem) + ".stderr")
        command = [str(executable or self.lean), *arguments]
        start, code, timed_out = time.monotonic(), None, False
        try:
            with stdout.open("xb") as out, stderr.open("xb") as err:
                try:
                    completed = subprocess.run(command, cwd=self.stage, env=self.environment,
                                               stdout=out, stderr=err, timeout=timeout, check=False)
                    code = completed.returncode
                except subprocess.TimeoutExpired:
                    timed_out = True
        except OSError as error:
            raise Failure(2, label, f"could not execute Lean: {error}") from error
        observation = {"argv": command, "returncode": code, "timeout": timed_out,
                       "seconds": round(time.monotonic() - start, 3),
                       "stdoutBytes": stdout.stat().st_size, "stderrBytes": stderr.stat().st_size}
        Path(str(stem) + ".status.json").write_text(json.dumps(observation, indent=2))
        self.last_status = observation
        self.budget()
        if timed_out:
            raise Failure(2, label, f"direct Lean child exceeded {timeout} seconds; no retry")
        if code != 0:
            raise Failure(2, label, f"Lean exited {code}; see {stem}.stdout/.stderr")
        return stdout.read_text(encoding="utf-8", errors="strict")

    def _get_compiled_inspector(self) -> Path | None:
        if not self.fast or self.cache_dir is None or self.expected_lean_sha is None:
            return None
        if self._compiled_inspector is not None and _trusted_cache_tree(self.cache_dir, self._compiled_inspector):
            return self._compiled_inspector
        leanc = self.lean.parent / "leanc"
        if not leanc.is_file():
            return None
        bin_key = fingerprint({
            "schema": 1,
            "toolchain": TOOLCHAIN,
            "leanSha256": self.expected_lean_sha,
            "leancSha256": digest(leanc),
            "inspectorSha256": getattr(self, "inspector_hash", None),
        })
        bin_dir = self.cache_dir / "inspector-bin"
        bin_path = bin_dir / f"TrustedBoundary-{bin_key}"
        if _trusted_cache_tree(self.cache_dir, bin_path) and os.access(bin_path, os.X_OK):
            self._compiled_inspector = bin_path
            return bin_path
        if not _ensure_trusted_cache_dir(self.cache_dir, bin_dir):
            return None
        try:
            tmp_dir = Path(tempfile.mkdtemp(prefix=f"tmp-insp-{bin_key[:12]}-", dir=bin_dir))
        except OSError:
            return None
        try:
            c_path = tmp_dir / "TrustedBoundary.c"
            tmp_bin = tmp_dir / "TrustedBoundary"
            res_c = subprocess.run(
                [str(self.lean), "-c", str(c_path), str(self.inspector)],
                cwd=self.stage,
                env=self.environment,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=CHILD_TIMEOUT_SECS,
                check=False,
            )
            if res_c.returncode != 0 or not c_path.is_file():
                return None
            res_bin = subprocess.run(
                [str(leanc), "-O3", "-rdynamic", "-o", str(tmp_bin), str(c_path)],
                cwd=self.stage,
                env=self.environment,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=CHILD_TIMEOUT_SECS,
                check=False,
            )
            if res_bin.returncode != 0 or not tmp_bin.is_file():
                return None
            tmp_bin.chmod(0o755)
            os.replace(tmp_bin, bin_path)
            self._compiled_inspector = bin_path
            return bin_path
        except (OSError, subprocess.SubprocessError):
            return None
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def _get_compiled_olean_auditor(self) -> Path | None:
        """Native `OleanEnvAuditor-<key>` binary, content-addressed by the staged auditor source,
        `lean`, and `leanc`: cached under `--fast`, otherwise built once per process in a private
        temporary directory. `None` falls back to running the staged auditor source with
        `lean --run`, so the gate itself never depends on a cache."""
        if self.expected_lean_sha is None or not hasattr(self, "olean_auditor_hash"):
            return None
        if self._compiled_olean_auditor is not None:
            root_for_bin = self.cache_dir if (self.fast and self.cache_dir is not None) else self._compiled_olean_auditor.parent
            if _trusted_cache_tree(root_for_bin, self._compiled_olean_auditor):
                return self._compiled_olean_auditor
        leanc = self.lean.parent / "leanc"
        if not leanc.is_file():
            return None
        bin_key = fingerprint({
            "schema": 1,
            "tool": "OleanEnvAuditor",
            "toolchain": TOOLCHAIN,
            "leanSha256": self.expected_lean_sha,
            "leancSha256": digest(leanc),
            "auditorSha256": self.olean_auditor_hash,
        })
        created_bin_dir = False
        if self.fast and self.cache_dir is not None:
            cache_root = self.cache_dir
            bin_dir = self.cache_dir / "inspector-bin"
        else:
            # Without `--fast` nothing is shared across runs: the binary is built from the staged,
            # hashed source once per process in a private temporary directory.
            known = _PROCESS_OLEAN_BINARIES.get(bin_key)
            if known is not None and _trusted_cache_tree(known.parent, known) and os.access(known, os.X_OK):
                self._compiled_olean_auditor = known
                return known
            try:
                bin_dir = Path(tempfile.mkdtemp(prefix="anneal-trusted-olean-bin-"))
                created_bin_dir = True
            except OSError:
                return None
            cache_root = bin_dir
        bin_path = bin_dir / f"OleanEnvAuditor-{bin_key}"
        if _trusted_cache_tree(cache_root, bin_path) and os.access(bin_path, os.X_OK):
            self._compiled_olean_auditor = bin_path
            return bin_path
        if not _ensure_trusted_cache_dir(cache_root, bin_dir):
            if created_bin_dir:
                shutil.rmtree(bin_dir, ignore_errors=True)
            return None
        try:
            tmp_dir = Path(tempfile.mkdtemp(prefix=f"tmp-olean-{bin_key[:12]}-", dir=bin_dir))
        except OSError:
            if created_bin_dir:
                shutil.rmtree(bin_dir, ignore_errors=True)
            return None
        stored = False
        try:
            c_path = tmp_dir / "OleanEnvAuditor.c"
            tmp_bin = tmp_dir / "OleanEnvAuditor"
            # No status files: the warm-cache contract counts only checked Lean children.
            res_c = subprocess.run(
                [str(self.lean), "-c", str(c_path), str(self.olean_auditor)],
                cwd=self.stage, env=self.environment, stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL, timeout=CHILD_TIMEOUT_SECS, check=False)
            if res_c.returncode != 0 or not c_path.is_file():
                return None
            if digest(self.olean_auditor) != self.olean_auditor_hash:
                raise Failure(2, "freshness", "staged OleanEnvAuditor changed while compiling")
            res_bin = subprocess.run(
                [str(leanc), "-O3", "-rdynamic", "-o", str(tmp_bin), str(c_path)],
                cwd=self.stage, env=self.environment, stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL, timeout=CHILD_TIMEOUT_SECS, check=False)
            if res_bin.returncode != 0 or not tmp_bin.is_file():
                return None
            tmp_bin.chmod(0o755)
            os.replace(tmp_bin, bin_path)
            self._compiled_olean_auditor = bin_path
            if not self.fast:
                _PROCESS_OLEAN_BINARIES[bin_key] = bin_path
            stored = True
            return bin_path
        except (OSError, subprocess.SubprocessError):
            return None
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)
            if created_bin_dir and not stored:
                shutil.rmtree(bin_dir, ignore_errors=True)

    def _inspect_cache_key(self, mode: str, fields: dict) -> str | None:
        if not self.fast or self.cache_dir is None or self.expected_lean_sha is None:
            return None
        inspector_sha = getattr(self, "inspector_hash", None)
        if mode == "foundation":
            return fingerprint({
                "schema": 1,
                "mode": "foundation",
                "toolchain": TOOLCHAIN,
                "leanSha256": self.expected_lean_sha,
                "inspectorSha256": inspector_sha,
                "lock": self.lock,
            })
        if mode == "preflight":
            sources = fields.get("sources", [])
            source_digests = [(mod_name, digest(Path(src_path))) for mod_name, src_path in sources]
            return fingerprint({
                "schema": 1,
                "mode": "preflight",
                "toolchain": TOOLCHAIN,
                "leanSha256": self.expected_lean_sha,
                "inspectorSha256": inspector_sha,
                "lock": self.lock,
                "graph": fields.get("graph", self.graph),
                "allowedAxiomModules": fields.get("allowedAxiomModules", []),
                "sources": source_digests,
            })
        if mode in ("audit", "downstream-audit", *OLEAN_AUDIT_MODES):
            if mode in OLEAN_AUDIT_MODES:
                # Never satisfy an OleanEnvAuditor audit from cache if any artifact or source path
                # is non-canonical, splits base directories, mismatches its module path, swaps
                # olean/IR groups, or omits an on-disk companion: let the auditor run and reject it.
                for mod, groups in self.artifacts.items():
                    if not isinstance(groups, list) or len(groups) != 2:
                        return None
                    olean_parts, ir_parts = groups
                    if len(olean_parts) not in (1, 3) or len(ir_parts) not in (0, 2):
                        return None
                    rel_suffix = "/" + mod.replace(".", "/") + ".olean"
                    if not isinstance(olean_parts[0], str) or not olean_parts[0].endswith(rel_suffix):
                        return None
                    base = olean_parts[0][:-6]
                    expected_olean = PARTS[:3] if len(olean_parts) == 3 else PARTS[:1]
                    for p, ext in zip(olean_parts, expected_olean):
                        if p != f"{base}.{ext}" or not _canonical_regular(Path(p)):
                            return None
                    for p, ext in zip(ir_parts, PARTS[3:]):
                        if p != f"{base}.{ext}" or not _canonical_regular(Path(p)):
                            return None
                    listed = set(olean_parts) | set(ir_parts)
                    for ext in PARTS:
                        cand = Path(f"{base}.{ext}")
                        if str(cand) not in listed and (cand.exists() or cand.is_symlink()):
                            return None
                for _, p in fields.get("sources", []):
                    if not _canonical_regular(Path(p)):
                        return None
                # Staged source paths differ per run; key them by module and content instead.
                fields = {**fields, "sources": [(m, digest(Path(p))) for m, p in fields.get("sources", [])]}
                inspector_sha = {"trustedBoundary": inspector_sha,
                                 "oleanEnvAuditor": getattr(self, "olean_auditor_hash", None)}
                artifact_hashes = [
                    (
                        mod,
                        [
                            [(Path(p).name, digest(Path(p))) for p in group]
                            for group in self.artifacts[mod]
                        ],
                    )
                    for mod in sorted(self.artifacts)
                ]
            else:
                artifact_hashes = [
                    (
                        mod,
                        [
                            (Path(p).name, self.expected_artifacts.get(p) or digest(Path(p)))
                            for group in self.artifacts[mod]
                            for p in group
                        ],
                    )
                    for mod in sorted(self.artifacts)
                ]
            return fingerprint({
                "schema": 1,
                "mode": mode,
                "toolchain": TOOLCHAIN,
                "leanSha256": self.expected_lean_sha,
                "inspectorSha256": inspector_sha,
                "lock": self.lock,
                "graph": fields["graph"] if "graph" in fields else self.graph,
                "artifactHashes": artifact_hashes,
                "fields": fields,
            })
        return None

    def make_setup(self, module: str, imports: list[dict]) -> dict:
        if not self.fast:
            return self.inspect("setup", module=module, imports=imports)
        setup = {
            "name": module,
            "isModule": False,
            "imports": imports,
            "importArts": dict(self.artifacts),
            "dynlibs": [],
            "plugins": [],
            "options": {},
        }
        self.validate_result("setup", setup, {"module": module, "imports": imports})
        return setup

    def _module_cache_key(
        self,
        module: str,
        source_sha256: str,
        compile_flags: list[str],
        direct_edges: list[dict],
    ) -> str:
        reachable: set[str] = set()
        pending = [edge["module"] for edge in direct_edges]
        while pending:
            curr = pending.pop()
            if curr not in reachable:
                reachable.add(curr)
                for edge in self.graph.get(curr, []):
                    pending.append(edge["module"])
        imp_records = []
        for imp_mod in sorted(reachable):
            part_hashes = [
                (Path(p).name, self.expected_artifacts[p])
                for group in self.artifacts.get(imp_mod, [[], []])
                for p in group
            ]
            imp_records.append((imp_mod, part_hashes))
        return fingerprint({
            "schema": 1,
            "toolchain": TOOLCHAIN,
            "leanSha256": self.expected_lean_sha,
            "module": module,
            "sourceSha256": source_sha256,
            "compileFlags": compile_flags,
            "directImports": direct_edges,
            "transitiveImports": imp_records,
        })

    def _restore_cached_module(self, module: str, cache_key: str, output: Path) -> bool:
        if not self.fast or self.cache_dir is None:
            return False
        entry_dir = self.cache_dir / "olean" / cache_key
        meta_path = entry_dir / "meta.json"
        if not _trusted_cache_tree(self.cache_dir, meta_path):
            return False
        try:
            meta = json.loads(meta_path.read_text())
        except (ValueError, OSError):
            return False
        if not isinstance(meta, dict) or "olean" not in meta or not set(meta).issubset(set(PARTS)):
            return False
        for part, expected_sha in meta.items():
            cached_part = entry_dir / f"artifact.{part}"
            if not _trusted_cache_tree(self.cache_dir, cached_part) or digest(cached_part) != expected_sha:
                return False
        output.parent.mkdir(parents=True, exist_ok=True)
        available = {}
        for part, expected_sha in meta.items():
            dest = output.with_name(output.name[:-5] + part)
            shutil.copyfile(entry_dir / f"artifact.{part}", dest)
            if digest(dest) != expected_sha:
                return False
            available[part] = str(dest)
            self.expected_artifacts[str(dest)] = expected_sha
        self.artifacts[module] = [
            [available[p] for p in PARTS[:3] if p in available],
            [available[p] for p in PARTS[3:] if p in available],
        ]
        return True

    def _store_cached_module(self, cache_key: str, available: dict[str, str]) -> None:
        if not self.fast or self.cache_dir is None:
            return
        olean_root = self.cache_dir / "olean"
        if not _ensure_trusted_cache_dir(self.cache_dir, olean_root):
            return
        entry_dir = olean_root / cache_key
        if entry_dir.exists() or entry_dir.is_symlink():
            return
        try:
            tmp_dir = Path(tempfile.mkdtemp(prefix=f"tmp-{cache_key[:12]}-", dir=olean_root))
        except OSError:
            return
        try:
            meta = {}
            for part, path_str in available.items():
                shutil.copyfile(path_str, tmp_dir / f"artifact.{part}")
                meta[part] = self.expected_artifacts[path_str]
            (tmp_dir / "meta.json").write_text(json.dumps(meta, sort_keys=True))
            if entry_dir.exists() or entry_dir.is_symlink():
                shutil.rmtree(tmp_dir, ignore_errors=True)
            else:
                os.replace(tmp_dir, entry_dir)
        except OSError:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def inspect(self, mode: str, **fields) -> dict:
        self.phase = mode
        cache_key = self._inspect_cache_key(mode, fields)
        if cache_key is not None and self.cache_dir is not None:
            cache_file = self.cache_dir / "inspect" / f"{mode}-{cache_key}.json"
            if _trusted_cache_tree(self.cache_dir, cache_file):
                try:
                    cached_result = json.loads(cache_file.read_text())
                    if isinstance(cached_result, dict):
                        self.validate_result(mode, cached_result, fields)
                        return cached_result
                except (ValueError, OSError, Failure):
                    pass
        request = {"mode": mode, "sysroot": str(self.prefix),
                   "artifacts": sorted(self.artifacts.items()),
                   "foundation": self.foundation, "graph": self.graph,
                   "axioms": self.lock["axioms"], **fields}
        if mode in OLEAN_AUDIT_MODES and "graph" in fields and fields["graph"] is None:
            del request["graph"]
        stem = self.stage / f"request-{self.counter + 1:03d}-{mode}"
        request_path, result_path = Path(str(stem) + ".json"), Path(str(stem) + ".result.json")
        request_path.write_text(json.dumps(request, sort_keys=True))
        self.last_status = None
        olean_mode = mode in OLEAN_AUDIT_MODES
        compiled_inspector = self._get_compiled_olean_auditor() if olean_mode else self._get_compiled_inspector()
        try:
            if compiled_inspector is not None:
                self.process(mode, [str(request_path), str(result_path)], executable=compiled_inspector,
                             timeout=OLEAN_CHILD_TIMEOUT_SECS if olean_mode else CHILD_TIMEOUT_SECS)
            elif olean_mode:
                self.process(mode, ["-j1", "--run", str(self.olean_auditor), str(request_path), str(result_path)],
                             timeout=OLEAN_CHILD_TIMEOUT_SECS)
            else:
                self.process(mode, ["-j1", "-M2048", "--run", str(self.inspector), str(request_path), str(result_path)])
        except Failure as failure:
            self.budget()
            if self.last_status and self.last_status["returncode"] == 1 and not self.last_status["timeout"] and result_path.is_file():
                try:
                    response = json.loads(result_path.read_text())
                except (ValueError, OSError):
                    raise failure
                if (isinstance(response, dict) and set(response) == {"ok", "category", "message"}
                        and response["ok"] is False and response["category"] == "policy"
                        and isinstance(response["message"], str) and response["message"]):
                    raise Failure(1, mode, response["message"]) from failure
            raise
        try:
            response = json.loads(result_path.read_text())
        except (ValueError, OSError) as error:
            raise Failure(2, mode, f"missing/malformed inspector result: {error}") from error
        if not isinstance(response, dict) or set(response) != {"ok", "result"} or response["ok"] is not True or not isinstance(response["result"], dict):
            raise Failure(2, mode, "unexpected inspector protocol response")
        result = response["result"]
        self.validate_result(mode, result, fields)
        if cache_key is not None and self.cache_dir is not None:
            inspect_dir = self.cache_dir / "inspect"
            if _ensure_trusted_cache_dir(self.cache_dir, inspect_dir):
                try:
                    tmp_fd, tmp_name = tempfile.mkstemp(prefix=f"tmp-{mode}-", dir=inspect_dir)
                    with os.fdopen(tmp_fd, "w", encoding="utf-8") as handle:
                        json.dump(result, handle, sort_keys=True)
                    os.replace(tmp_name, inspect_dir / f"{mode}-{cache_key}.json")
                except OSError:
                    pass
        return result

    def validate_result(self, mode, result, fields):
        """Exact schemas for the six inspector consumers."""
        if mode == "setup":
            require(set(result) == {"name", "isModule", "imports", "importArts", "dynlibs", "plugins", "options"}
                    and result["name"] == fields["module"] and result["isModule"] is False
                    and result["imports"] == fields["imports"] and valid_imports(result["imports"])
                    and result["importArts"] == self.artifacts and result["dynlibs"] == []
                    and result["plugins"] == [] and result["options"] == {}, mode, "invalid setup observation")
        elif mode == "foundation":
            require(set(result) == {"graph"} and valid_graph(result["graph"]), mode, "invalid foundation observation")
        elif mode == "preflight":
            require(set(result) == {"graph", "headers"} and valid_graph(result["graph"])
                    and isinstance(result["headers"], list), mode, "invalid preflight observation")
            for h in result["headers"]:
                require(isinstance(h, dict) and set(h) == {"module", "imports"}
                        and isinstance(h["module"], str) and h["module"] and valid_imports(h["imports"]),
                        mode, "invalid header observation")
        elif mode == "graph-tests":
            require(result == {"graphTests": True}, mode, "invalid graph-test observation")
        elif mode == "audit":
            require(set(result) == {"graph", "declarations", "kernelDeclarations", "compilerOnlyNames",
                                   "reachableDeclarations", "axioms", "replay"}
                    and valid_graph(result["graph"]) and result["replay"] is True
                    and isinstance(result["declarations"], list)
                    and all(type(result[k]) is int and result[k] >= 0
                            for k in ("kernelDeclarations", "compilerOnlyNames", "reachableDeclarations")),
                    mode, "invalid audit observation")
            names = []
            for declaration in result["declarations"]:
                require(isinstance(declaration, dict) and set(declaration) == {"name", "module", "kind", "dependencies"}
                        and isinstance(declaration["name"], str) and declaration["name"]
                        and declaration["module"] in fields["trusted"]
                        and isinstance(declaration["kind"], str)
                        and declaration["kind"] in {"definition", "theorem", "opaque", "quotient", "inductive", "constructor", "recursor"}
                        and isinstance(declaration["dependencies"], list)
                        and all(isinstance(n, str) and n for n in declaration["dependencies"])
                        and len(set(declaration["dependencies"])) == len(declaration["dependencies"]),
                        mode, "invalid declaration observation")
                names.append(declaration["name"])
            require(len(names) == len(set(names)) == result["kernelDeclarations"]
                    and result["reachableDeclarations"] >= len(names)
                    and isinstance(result["axioms"], list)
                    and all(isinstance(n, str) and n in {a[0] for a in self.lock["axioms"]} for n in result["axioms"])
                    and len(result["axioms"]) == len(set(result["axioms"])), mode, "inconsistent audit counts/axioms")
        elif mode == "downstream-audit":
            expected_downstream = (fields["theory"] + fields["examples"]
                                   + fields["claimModules"] + fields["testModules"])
            require(set(result) == {"downstreamModules", "replayedDeclarations", "claimTheoremsChecked",
                                    "localTestAxioms", "replay"}
                    and result["replay"] is True
                    and result["downstreamModules"] == expected_downstream
                    and all(type(result[k]) is int and result[k] >= 0
                            for k in ("replayedDeclarations", "claimTheoremsChecked", "localTestAxioms")),
                    mode, "invalid downstream-audit observation")
        elif mode in OLEAN_AUDIT_MODES:
            require(set(result) == OLEAN_RESULT_KEYS
                    and result["auditor"] == "OleanEnvAuditor" and result["schema"] == 1
                    and result["scope"] == fields["scope"]
                    and result["replay"] is True
                    and result["modules"] == sorted(fields["modules"])
                    and all(type(result[k]) is int and result[k] >= 0 for k in OLEAN_COUNT_KEYS)
                    and result["auditedDeclarations"] >= result["replayedDeclarations"]
                    and result["constructiveModulesChecked"] == len(fields.get("constructiveModules", []))
                    and result["specStrengthChecksPassed"] == len(fields.get("specStrengthChecks", []))
                    and result["provisionalNativeAxioms"] == []
                    and result["kernelConfirmedNativeAxioms"] == []
                    and isinstance(result["axioms"], list)
                    and all(isinstance(n, str) and n in {a[0] for a in self.lock["axioms"]} for n in result["axioms"])
                    and (fields.get("allowClassicalChoice", True) or "Classical.choice" not in result["axioms"])
                    and len(result["axioms"]) == len(set(result["axioms"]))
                    and (result["localTestAxioms"] == 0 or bool(fields.get("localAxiomModules"))),
                    mode, "invalid compiled-environment audit observation")
        else:
            raise Failure(2, mode, "unknown inspector result mode")

    def olean_audit(self, mode: str, **fields) -> dict:
        """Run the compiled-environment auditor (`OleanEnvAuditor`) fail-closed: any violation,
        provisional native axiom, missing artifact, or malformed verdict is a `Failure`."""
        if mode not in OLEAN_AUDIT_MODES:
            raise Failure(2, mode, "unknown compiled-environment audit mode")
        regular(self.olean_auditor, "tool-snapshot")
        result = self.inspect(mode, **fields)
        if result.get("replay") is not True or result.get("provisionalNativeAxioms") != []:
            raise Failure(2, mode, "incomplete compiled-environment audit evidence")
        return result

    def audit_olean_request(self, request: dict) -> dict:
        """`--audit-olean`: audit caller-supplied compiled modules with the trust-gating policy.

        Call after `tool_admission()` (and after `run()` when the audited modules import
        `Trusted`: the checker's own audited `Trusted` artifacts are then added to the roots and
        modules; callers can neither supply nor name `Trusted` modules). `request` names `roots`
        and the exact other non-toolchain `modules`, their `artifacts`
        (`[[module, [[olean parts], [ir parts]]], ...]`) and
        optionally `graph`, `localAxiomModules`, `claimModules`, `statementForbidden`,
        `statementUnfold`, `sources` and `scope`. Provisional native evaluation and extra
        toolchain roots cannot be requested here."""
        allowed = {"roots", "modules", "artifacts", "graph", "localAxiomModules", "claimModules",
                   "statementForbidden", "statementUnfold", "sources", "scope",
                   "allowClassicalChoice", "constructiveModules", "specStrengthChecks"}
        phase = "olean-audit"
        require(isinstance(request, dict) and set(request) <= allowed
                and {"roots", "modules", "artifacts"} <= set(request), phase, "malformed --audit-olean request")
        for key in ("roots", "modules", "localAxiomModules", "claimModules", "statementForbidden",
                    "statementUnfold", "constructiveModules"):
            value = request.get(key, [])
            require(isinstance(value, list) and all(isinstance(m, str) and m for m in value), phase,
                    f"malformed --audit-olean field {key}")
        allow_classical = request.get("allowClassicalChoice", True)
        require(type(allow_classical) is bool, phase, "malformed --audit-olean field allowClassicalChoice")
        constructive_mods = request.get("constructiveModules", [])
        require(len(constructive_mods) == len(set(constructive_mods)), phase,
                "malformed --audit-olean field constructiveModules")
        spec_checks = request.get("specStrengthChecks", [])
        require(isinstance(spec_checks, list), phase, "malformed --audit-olean field specStrengthChecks")
        for entry in spec_checks:
            require(isinstance(entry, dict) and set(entry) <= SPEC_CHECK_ALLOWED_KEYS
                    and {"kind", "cert"} <= set(entry)
                    and isinstance(entry["kind"], str) and isinstance(entry["cert"], str) and bool(entry["cert"]),
                    phase, "malformed --audit-olean specStrengthChecks entry")
            if entry["kind"] == "claim":
                require("claim" in entry and "defId" not in entry
                        and isinstance(entry["claim"], str) and bool(entry["claim"]),
                        phase, "malformed --audit-olean claim specStrengthChecks entry")
            elif entry["kind"] in SPEC_CHECK_SYNTH_KINDS:
                require("defId" in entry and "claim" not in entry
                        and isinstance(entry["defId"], str) and bool(entry["defId"]),
                        phase, "malformed --audit-olean synth specStrengthChecks entry")
            else:
                raise Failure(2, phase, f"unsupported --audit-olean specStrengthChecks kind: {entry['kind']}")
            if "requiredCategories" in entry:
                cats = entry["requiredCategories"]
                require(isinstance(cats, list) and all(isinstance(c, str) and bool(c) for c in cats),
                        phase, "malformed --audit-olean requiredCategories")
            for bkey in ("requireDeterministic", "requireInputSensitive"):
                if bkey in entry:
                    require(type(entry[bkey]) is bool, phase, f"malformed --audit-olean {bkey}")
        require(bool(request["roots"]) and len(request["roots"]) == len(set(request["roots"])), phase,
                "malformed --audit-olean field roots")
        require(bool(request["modules"]) and len(request["modules"]) == len(set(request["modules"])), phase,
                "malformed --audit-olean field modules")
        artifacts = request["artifacts"]
        require(isinstance(artifacts, list), phase, "malformed --audit-olean artifacts")
        # `Trusted` modules are compiled from the checkout by this checker (`run()`), never taken
        # from the caller: a caller-supplied `Trusted` could redefine `VerificationResult`.
        trusted_names = set(getattr(self, "modules", {}))

        def is_trusted_name(name: str) -> bool:
            return name in trusted_names or name == "Trusted" or name.startswith("Trusted.")

        named = [*request["roots"], *request["modules"],
                 *request.get("localAxiomModules", []), *request.get("claimModules", []),
                 *constructive_mods,
                 *(e[0] for e in artifacts if isinstance(e, list) and e and isinstance(e[0], str)),
                 *(s[0] for s in (request.get("sources") if isinstance(request.get("sources"), list) else [])
                   if isinstance(s, list) and s and isinstance(s[0], str)),
                 *(request.get("graph", {}) if isinstance(request.get("graph"), dict) else {})]
        spoofed = sorted({n for n in named if is_trusted_name(n)})
        if spoofed:
            raise Failure(1, phase, f"[moduleProvenanceSpoofed] --audit-olean cannot supply or name Trusted modules "
                                    f"({', '.join(spoofed)}); they come from the checker's own compilation")
        # The certificate types the spec-strength gate recognizes live in `SPEC_LIB_MODULE`, and the
        # auditor identifies them by that module name: a caller-supplied module of that name (or a
        # submodule under it) could declare `SpecStrengthCert` as a one-field structure and
        # "certify" a vacuous claim.
        spec_spoofed = sorted({n for n in named if n == SPEC_LIB_MODULE or n.startswith(SPEC_LIB_MODULE + ".")})
        if spec_spoofed:
            raise Failure(1, phase, f"[moduleProvenanceSpoofed] --audit-olean cannot supply or name {SPEC_LIB_MODULE} "
                                    f"({', '.join(spec_spoofed)}); it comes from the checker's own compilation")
        spec_lib_owned = bool(self.spec_lib_owned and SPEC_LIB_MODULE in self.artifacts)
        if spec_checks and not spec_lib_owned:
            raise Failure(1, phase, f"[moduleProvenanceSpoofed] specStrengthChecks need the checker's own compiled "
                                    f"{SPEC_LIB_MODULE} (compile_spec_library()); none is available")
        sources = request.get("sources", [])
        require(isinstance(sources, list) and all(
            isinstance(s, list) and len(s) == 2 and all(isinstance(x, str) and x for x in s) for s in sources)
            and len({s[0] for s in sources}) == len(sources),
            phase, "malformed --audit-olean sources")
        source_hashes: dict[str, str] = {}
        for _, path in sources:
            regular(Path(path), phase)
            if not _canonical_regular(Path(path)):
                raise Failure(1, phase, f"[moduleProvenanceSpoofed] non-canonical source path: {path}")
            source_hashes[path] = digest(Path(path))
        scope = request.get("scope", "request")
        require(isinstance(scope, str) and bool(scope), phase, "malformed --audit-olean scope")
        if "graph" in request:
            graph = request["graph"]
            require(valid_graph(graph), phase, "malformed --audit-olean graph")
            for mod, edges in graph.items():
                if mod in self.foundation and edges != self.lock["graph"].get(mod):
                    raise Failure(1, phase, f"[graphMismatch] --audit-olean cannot override locked foundation DAG for {mod}")
            merged_graph: dict | None = {**self.graph, **graph}
        else:
            merged_graph = None
        compiled_trusted = [m for m in getattr(self, "modules", {}) if m in self.artifacts]
        # The checker's own spec library joins every request once compiled (callers may import it),
        # always under the constructive policy.
        compiled_own = [*compiled_trusted, *([SPEC_LIB_MODULE] if spec_lib_owned else [])]
        owned_constructive = [SPEC_LIB_MODULE] if spec_lib_owned else []
        # When `Trusted` was compiled by this checker (`run()`), `Trusted` itself legitimately uses
        # `Classical.choice`. Setting `allowClassicalChoice=False` on a caller request therefore
        # enforces the constructive policy on all caller `modules` (including their full transitive
        # dependency closure into `Trusted`), rather than rejecting unused `Classical.choice`
        # declarations inside `Trusted` (`A1-5a`).
        if not allow_classical and compiled_trusted:
            effective_allow_classical = True
            effective_constructive = list(dict.fromkeys([*request["modules"], *constructive_mods, *owned_constructive]))
        else:
            effective_allow_classical = allow_classical
            effective_constructive = list(dict.fromkeys([*constructive_mods, *owned_constructive]))
        saved_artifacts = dict(self.artifacts)
        saved_expected = dict(self.expected_artifacts)
        saved_graph = dict(self.graph)
        caller_hashes: dict[str, str] = {}
        try:
            for entry in artifacts:
                require(isinstance(entry, list) and len(entry) == 2 and isinstance(entry[0], str) and bool(entry[0])
                        and entry[0] not in self.artifacts and isinstance(entry[1], list) and len(entry[1]) == 2
                        and all(isinstance(g, list) and all(isinstance(p, str) and os.path.isabs(p) for p in g)
                                for g in entry[1]), phase, "malformed --audit-olean artifact entry")
                for group in entry[1]:
                    for path in group:
                        regular(Path(path), phase)
                        if not _canonical_regular(Path(path)):
                            raise Failure(1, phase, f"[moduleProvenanceSpoofed] non-canonical artifact path: {path}")
                        h = digest(Path(path))
                        self.expected_artifacts[path] = h
                        caller_hashes[path] = h
                self.artifacts[entry[0]] = [list(entry[1][0]), list(entry[1][1])]
            if merged_graph is not None:
                self.graph = merged_graph
            verdict = self.olean_audit(
                "olean-audit", scope=scope, roots=[*request["roots"], *compiled_own],
                modules=[*request["modules"], *compiled_own],
                graph=merged_graph,
                allowClassicalChoice=effective_allow_classical,
                constructiveModules=effective_constructive,
                specStrengthChecks=spec_checks,
                localAxiomModules=request.get("localAxiomModules", []),
                claimModules=request.get("claimModules", []),
                statementForbidden=request.get("statementForbidden", []),
                statementUnfold=request.get("statementUnfold", []),
                sources=[tuple(s) for s in sources])
            for path, expected in (*caller_hashes.items(), *source_hashes.items()):
                regular(Path(path), "freshness")
                if digest(Path(path)) != expected:
                    raise Failure(2, "freshness", f"caller input changed during check: {path}")
            return verdict
        finally:
            self.artifacts = saved_artifacts
            self.expected_artifacts = saved_expected
            self.graph = saved_graph

    def tool_admission(self) -> None:
        # The root manifest is verified before any Lean child runs.
        self.root_manifest = verify_root_manifest(self.checkout)
        self.initial, self.modules = snapshot(self.source)
        self.tool_paths = [
            self.checkout / "trusted/audit/check_trusted.py",
            self.checkout / "trusted/audit/TrustedBoundary.lean",
            self.checkout / OLEAN_AUDITOR,
        ]
        for path in self.tool_paths:
            regular(path, "tool-snapshot")
        self.tool_hashes = {str(p.relative_to(self.checkout)): digest(p) for p in self.tool_paths}
        self.inspector = self.stage / "TrustedBoundary.lean"
        shutil.copyfile(self.tool_paths[1], self.inspector)
        # Staged inputs are read-only from here on (GUIDE.md): no later step or child
        # process can mutate them in place; freshness() still re-hashes them.
        make_read_only(self.inspector)
        self.inspector_hash = digest(self.inspector)
        # The compiled-environment auditor is required unconditionally: there is no code path
        # that skips it when the source is absent (`regular` above already failed closed).
        self.olean_auditor = self.stage / "OleanEnvAuditor.lean"
        shutil.copyfile(self.tool_paths[2], self.olean_auditor)
        make_read_only(self.olean_auditor)
        self.olean_auditor_hash = digest(self.olean_auditor)
        if self.olean_auditor_hash != self.tool_hashes[OLEAN_AUDITOR]:
            raise Failure(2, "tool-snapshot", "OleanEnvAuditor changed while staging")
        source_copy = self.stage / "source"
        source_copy.mkdir()
        for relative, entry in self.initial.items():
            destination = source_copy / relative
            if entry["kind"] == "directory":
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(self.source / relative, destination)
                make_read_only(destination)
                if digest(destination) != entry["sha256"]:
                    raise Failure(2, "snapshot", f"source changed while copying {relative}")
        self.source_copy = source_copy
        try:
            toolchain_text = (source_copy / "lean-toolchain").read_text().strip()
        except OSError as error:
            raise Failure(2, "lock", f"cannot read lean-toolchain: {error}") from error
        toolchain_tag = toolchain_text.split(":", 1)[-1] if ":" in toolchain_text else toolchain_text
        versioned_lock = source_copy / "locks" / f"foundation-lock-{toolchain_tag}.json"
        lock_file = versioned_lock if versioned_lock.is_file() else (source_copy / "foundation-lock.json")
        self.lock_path = lock_file
        try:
            self.lock = json.loads(lock_file.read_text())
        except (ValueError, OSError) as error:
            raise Failure(2, "lock", f"cannot read foundation lock: {error}") from error
        if not isinstance(self.lock, dict) or type(self.lock.get("schema")) is not int or self.lock.get("schema") != 1 or self.lock.get("toolchain") != TOOLCHAIN:
            raise Failure(2, "lock", "unsupported lock/toolchain schema")
        require(set(self.lock) == {"schema", "toolchain", "distributions", "modules", "graph", "axioms"}
                and isinstance(self.lock["distributions"], dict) and bool(self.lock["distributions"])
                and all(isinstance(v, str) and v and isinstance(h, str) and bool(re.fullmatch(r"[0-9a-f]{64}", h))
                        for v, h in self.lock["distributions"].items())
                and isinstance(self.lock["modules"], dict) and valid_graph(self.lock["graph"])
                and isinstance(self.lock["axioms"], list)
                and all(isinstance(a, list) and len(a) == 2 and all(isinstance(n, str) and n for n in a)
                        for a in self.lock["axioms"]), "lock", "malformed foundation lock")
        if toolchain_text != TOOLCHAIN:
            raise Failure(1, "lock", "lean-toolchain differs from lock")
        regular(self.lean, "toolchain")
        self.lean = self.lean.resolve()
        actual_version = self.process("version", ["--version"]).strip()
        expected_lean_sha = self.lock["distributions"].get(actual_version)
        if expected_lean_sha is None:
            raise Failure(2, "toolchain", f"Lean version/commit differs from lock: {actual_version}")
        if digest(self.lean) != expected_lean_sha:
            raise Failure(2, "toolchain", "unsupported toolchain distribution/launcher bytes")
        self.expected_lean_sha = expected_lean_sha
        self.version = actual_version
        self.prefix = Path(self.process("prefix", ["--print-prefix"]).strip()).resolve()
        if self.prefix != self.lean.parent.parent:
            raise Failure(2, "toolchain", "compiler prefix differs from selected executable")
        self.foundation = list(self.lock["modules"])
        if set(self.foundation) != set(self.lock["graph"]):
            raise Failure(2, "lock", "foundation module/DAG keys differ")
        require(valid_graph(self.lock["graph"]), "lock", "invalid foundation DAG policy")
        for module, record in self.lock["modules"].items():
            if not re.fullmatch(r"Init(?:\.[A-Za-z][A-Za-z0-9_]*)+", module):
                raise Failure(2, "lock", f"invalid foundation module {module}")
            require(isinstance(record, dict) and set(record) == {"sourceSha256", "parts"}
                    and isinstance(record["sourceSha256"], str)
                    and bool(re.fullmatch(r"[0-9a-f]{64}", record["sourceSha256"]))
                    and isinstance(record["parts"], dict) and set(record["parts"]) == set(PARTS)
                    and all(h is None or isinstance(h, str) and bool(re.fullmatch(r"[0-9a-f]{64}", h))
                            for h in record["parts"].values()), "lock", f"incomplete artifact-part policy for {module}")
            source_path = self.prefix / "src/lean" / (module.replace(".", "/") + ".lean")
            regular(source_path, "foundation")
            if digest(source_path) != record["sourceSha256"]:
                raise Failure(2, "foundation", f"foundation source digest mismatch: {module}")
            available = {}
            for part, expected in record["parts"].items():
                relative = module.replace(".", "/") + "." + part
                installed = self.prefix / "lib/lean" / relative
                if expected is None:
                    if installed.exists() or installed.is_symlink():
                        raise Failure(2, "foundation", f"unexpected companion part: {relative}")
                    continue
                regular(installed, "foundation")
                if digest(installed) != expected:
                    raise Failure(2, "foundation", f"artifact digest mismatch: {relative}")
                copied = self.stage / "foundation" / relative
                copied.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(installed, copied)
                if digest(copied) != expected:
                    raise Failure(2, "foundation", f"artifact changed while copying: {relative}")
                available[part] = str(copied)
                self.expected_artifacts[str(copied)] = expected
            self.artifacts[module] = [[available[p] for p in PARTS[:3] if p in available],
                                      [available[p] for p in PARTS[3:] if p in available]]
            if not self.artifacts[module][0]:
                raise Failure(2, "foundation", f"missing olean for {module}")
        self.graph = dict(self.lock["graph"])
        if self.inspect("foundation").get("graph") != self.graph:
            raise Failure(1, "foundation", "locked compiled foundation DAG differs")

    def freshness(self) -> None:
        self.phase = "freshness"
        try:
            self._freshness()
        except (Failure, OSError) as error:
            raise Failure(2, "freshness", f"input revalidation failed: {error}") from error

    def _freshness(self) -> None:
        current, modules = snapshot(self.source)
        if current != self.initial or modules != self.modules:
            raise Failure(2, "freshness", "Trusted root inventory/bytes changed during check")
        staged, staged_modules = snapshot(self.source_copy)
        if staged != self.initial or staged_modules != self.modules:
            raise Failure(2, "freshness", "staged Trusted root inventory/bytes changed during check")
        if any(digest(self.checkout / p) != h for p, h in self.tool_hashes.items()):
            raise Failure(2, "freshness", "checker/policy inputs changed during check")
        if digest(self.inspector) != self.inspector_hash:
            raise Failure(2, "freshness", "staged inspector changed")
        if digest(self.olean_auditor) != self.olean_auditor_hash:
            raise Failure(2, "freshness", "staged OleanEnvAuditor changed")
        if verify_root_manifest(self.checkout) != self.root_manifest:
            raise Failure(2, "freshness", "root manifest coverage changed during check")
        for path, expected in self.expected_artifacts.items():
            regular(Path(path), "freshness")
            if digest(Path(path)) != expected:
                raise Failure(2, "freshness", f"staged artifact changed: {path}")

    def compile_and_audit_downstream(self, targets=None) -> dict:
        """Compile theory/, examples/, and tests/ against audited Trusted artifacts and run downstream-audit."""
        if targets is None:
            targets = DOWNSTREAM_TARGETS
        examples_toolchain = self.checkout / "examples/lean-toolchain"
        examples_lakefile = self.checkout / "examples/lakefile.toml"
        inputs = [self.checkout / path for _, path, _, _ in targets]
        if any(path.startswith("examples/") for _, path, _, _ in targets):
            for path in (examples_toolchain, examples_lakefile):
                regular(path, "downstream-input")
            if examples_toolchain.read_text().strip() != TOOLCHAIN:
                raise Failure(1, "downstream-input", "examples/lean-toolchain differs from pinned toolchain")
            lakefile_text = examples_lakefile.read_text()
            for module, path, _, _ in targets:
                if path.startswith("examples/") and f'"{module}"' not in lakefile_text:
                    raise Failure(1, "downstream-input", f"examples/lakefile.toml missing target {module}")
        hashes = {}
        copies = {}
        for module, path, _, _ in targets:
            full = self.checkout / path
            regular(full, "downstream-input")
            hashes[full] = digest(full)
            dest = self.stage / "downstream-source" / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(full, dest)
            make_read_only(dest)
            if digest(dest) != hashes[full]:
                raise Failure(2, "downstream-input", f"source changed while copying {path}")
            copies[module] = dest
        # Waiver pins and annotated-claim non-vacuity on the staged (read-only) copies,
        # before any downstream compilation.
        waiver_audit = audit_waivers_and_vacuity([(path, copies[module]) for module, path, _, _ in targets])
        allowed_axiom_mods = [
            module
            for module, _, _, role in targets
            if role == "test" and "-- anneal-audit: policy=file-local-axioms" in copies[module].read_text()
        ]
        headers = self.inspect(
            "preflight",
            graph=self.lock["graph"],
            allowedAxiomModules=allowed_axiom_mods,
            sources=[(module, str(copies[module])) for module, _, _, _ in targets],
        ).get("headers")
        if not isinstance(headers, list) or {h["module"] for h in headers} != {m for m, _, _, _ in targets}:
            raise Failure(2, "preflight", "incomplete downstream header observation")
        header_imports = {h["module"]: h["imports"] for h in headers}
        known_downstream = {m for m, _, _, _ in targets}
        for module, _, declared_imports, _ in targets:
            edges = header_imports[module]
            for edge in edges:
                em = edge["module"]
                if (em not in self.artifacts
                        and em not in known_downstream
                        and not is_stdlib_module(em, self.prefix)):
                    raise Failure(1, "preflight", f"foreign/missing import {em} in {module}")
            actual_proj = [e["module"] for e in edges if not is_stdlib_module(e["module"], self.prefix)]
            expected_proj = [n for n in declared_imports if not is_stdlib_module(n, self.prefix)]
            if actual_proj != expected_proj:
                raise Failure(
                    1,
                    "preflight",
                    f"project imports of {module} ({actual_proj}) differ from DOWNSTREAM_TARGETS ({expected_proj})",
                )
        # `--fast` elaborates up to four declarations at once (`-j4`, `Elab.async`), so its peak heap
        # is several sequential peaks: `-M2048` makes the kernel abort with "excessive memory
        # consumption" on large theory modules that the sequential `-j1 -M2048` path accepts.
        downstream_flags = (
            ["-j4", "-M4096", "-t0", "-DElab.async=true", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
            if self.fast
            else ["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
        )
        for module, path, _, _ in targets:
            if not self.fast:
                self.freshness()
            edge_list = header_imports[module]
            output = self.stage / "downstream-lib" / (module.replace(".", "/") + ".olean")
            source_sha = hashes[self.checkout / path]
            cache_key = (
                self._module_cache_key(module, source_sha, downstream_flags, edge_list)
                if self.fast
                else ""
            )
            if self.fast and self._restore_cached_module(module, cache_key, output):
                self.graph[module] = edge_list
                continue
            setup = self.make_setup(module, edge_list)
            setup_path = self.stage / f"{module}.setup.json"
            setup_path.write_text(json.dumps(setup))
            output.parent.mkdir(parents=True, exist_ok=True)
            self.process("compile-" + module, [
                *downstream_flags, "--setup", str(setup_path), "-o", str(output),
                str(copies[module]),
            ])
            available = {}
            for part in PARTS:
                artifact = output.with_name(output.name[:-5] + part)
                if artifact.exists() or artifact.is_symlink():
                    regular(artifact, "compile")
                    available[part] = str(artifact)
                    self.expected_artifacts[str(artifact)] = digest(artifact)
            if "olean" not in available:
                raise Failure(2, "compile", f"compiler omitted output for {module}")
            self.artifacts[module] = [[available[p] for p in PARTS[:3] if p in available],
                                      [available[p] for p in PARTS[3:] if p in available]]
            self.graph[module] = edge_list
            self._store_cached_module(cache_key, available)
        if not self.fast:
            self.freshness()
        for full, expected in hashes.items():
            if digest(full) != expected:
                raise Failure(2, "freshness", f"downstream source changed during check: {full}")
        result = dict(self.inspect(
            "downstream-audit",
            trusted=list(self.modules),
            theory=[m for m, _, _, r in targets if r == "theory"],
            examples=[m for m, _, _, r in targets if r == "examples"],
            claimModules=[m for m, _, _, r in targets if r == "claim"],
            testModules=[m for m, _, _, r in targets if r == "test"],
        ))
        downstream_modules = [m for m, _, _, _ in targets]
        has_spec_lib = SPEC_LIB_MODULE in downstream_modules
        constructive_mods = [SPEC_LIB_MODULE] if has_spec_lib else []
        downstream_spec_checks = (
            [
                {
                    "kind": "itemSynth",
                    "defId": "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fxfsModelItemMultiCert",
                    "requiredCategories": [
                        "wrongReturn", "wrapOverflow", "truncatedLength",
                        "swappedByteOrder", "offByOneScalar",
                    ],
                },
                {
                    "kind": "itemSynth",
                    "defId": "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fxfsModelItemDetCert",
                    "requireDeterministic": True,
                },
                {
                    "kind": "itemSynth",
                    "defId": "anneal_model::fxfs_storage_boundary::vmo_subslice_bounds_valid",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fxfsModelItemInputSensitiveCert",
                    "requireInputSensitive": True,
                },
                {
                    "kind": "modularItemSynth",
                    "defId": "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fuchsiaModelModularItemMultiCert",
                    "requiredCategories": [
                        "wrongBranchTag", "truncatedLength",
                        "offByOneScalar", "unpreservedFrame",
                    ],
                },
                {
                    "kind": "modularItemSynth",
                    "defId": "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fuchsiaModelModularItemDetCert",
                    "requireDeterministic": True,
                },
                {
                    "kind": "modularItemSynth",
                    "defId": "anneal_model::fuchsia_usercopy::usercopy_copyin_bracketed",
                    "cert": "Anneal.OleanSpecStrengthAuditor.fuchsiaModelModularItemInputSensitiveCert",
                    "requireInputSensitive": True,
                },
            ]
            if has_spec_lib
            else []
        )
        result["oleanAudit"] = self.olean_audit(
            "olean-downstream-audit", scope="downstream",
            roots=[*self.modules, *downstream_modules], modules=[*self.modules, *downstream_modules],
            constructiveModules=constructive_mods,
            specStrengthChecks=downstream_spec_checks,
            localAxiomModules=allowed_axiom_mods,
            claimModules=[m for m, _, _, r in targets if r == "claim"],
            statementForbidden=[m for m, _, _, r in targets if r == "theory"],
            statementUnfold=[m for m, _, _, r in targets if r in ("claim", "examples", "test")],
            sources=[*((n, str(self.source_copy / p)) for n, p in self.modules.items()),
                     *((m, str(copies[m])) for m in downstream_modules)])
        result["waiverVacuityAudit"] = waiver_audit
        if has_spec_lib:
            self.spec_lib_owned = True
        return result

    def compile_spec_library(self) -> dict:
        """Compile `SPEC_LIB_MODULE` from the checkout against the audited `Trusted` artifacts and
        audit it (TrustedBoundary downstream audit, constructive OleanEnvAuditor policy, and the live
        model certificates). Call after `run()`; `--audit-olean` requests with `specStrengthChecks`
        are then judged against this copy, never a caller-supplied one."""
        target = [t for t in DOWNSTREAM_TARGETS if t[0] == SPEC_LIB_MODULE]
        if len(target) != 1 or any(n != "Trusted" and not n.startswith("Trusted.") for n in target[0][2]):
            raise Failure(2, "downstream-input", f"{SPEC_LIB_MODULE} must be a DOWNSTREAM_TARGETS entry importing only Trusted")
        return self.compile_and_audit_downstream(target)

    def run(self, *, check_downstream: bool = False) -> dict:
        base_hashes = (
            verify_base_snapshot(self.checkout, self.base_snapshot, self.expected_tcb_drift)
            if self.base_snapshot is not None
            else None
        )
        cargo_hashes = check_cargo_boundary(self.checkout) if (self.checkout / "Cargo.toml").exists() else {}
        rust_waiver_audit = audit_waivers_and_vacuity(rustc_capture_sources(self.checkout), vacuity=False)
        self.tool_admission()
        trusted_waiver_audit = audit_waivers_and_vacuity(
            [(f"trusted/lean/{rel}", self.source_copy / rel) for rel in self.modules.values()]
        )
        headers = self.inspect("preflight", sources=[(n, str(self.source_copy / p)) for n, p in self.modules.items()]).get("headers")
        if not isinstance(headers, list) or {h["module"] for h in headers} != set(self.modules) or len(headers) != len(self.modules):
            raise Failure(2, "preflight", "incomplete source-header inventory")
        imports = {h["module"]: h["imports"] for h in headers}
        for module, edges in imports.items():
            for edge in edges:
                if set(edge) != {"module", "importAll", "isExported", "isMeta"}:
                    raise Failure(2, "preflight", "malformed import observation")
                if (edge["module"] not in self.artifacts
                        and edge["module"] not in self.modules
                        and not is_stdlib_module(edge["module"], self.prefix)):
                    raise Failure(1, "preflight", f"foreign/missing import {edge['module']} in {module}")
        pending, order = set(self.modules), []
        while pending:
            ready = sorted(n for n in pending if all(e["module"] not in pending for e in imports[n]))
            if not ready:
                raise Failure(1, "preflight", "Trusted import cycle")
            order.extend(ready)
            pending.difference_update(ready)
        self.graph = {**self.graph, **imports}
        if self.fast:
            self.freshness()
        trusted_flags = (
            ["-j4", "-M2048", "-t0", "-DElab.async=true", "-Ddebug.skipKernelTC=false"]
            if self.fast
            else ["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
        )
        for module in order:
            output = self.stage / "lib" / (module.replace(".", "/") + ".olean")
            source_rel = self.modules[module]
            source_sha = self.initial[source_rel]["sha256"]
            cache_key = (
                self._module_cache_key(module, source_sha, trusted_flags, imports[module])
                if self.fast
                else ""
            )
            if self.fast and self._restore_cached_module(module, cache_key, output):
                self.execution_began = True
                continue
            setup = self.make_setup(module, imports[module])
            setup_path = self.stage / f"{module}.setup.json"
            setup_path.write_text(json.dumps(setup))
            output.parent.mkdir(parents=True, exist_ok=True)
            if not self.fast:
                self.freshness()
            self.execution_began = True
            self.process("compile-" + module, [
                *trusted_flags, "--setup", str(setup_path), "-o", str(output),
                str(self.source_copy / source_rel),
            ])
            available = {}
            for part in PARTS:
                path = output.with_name(output.name[:-5] + part)
                if path.exists() or path.is_symlink():
                    regular(path, "compile")
                    available[part] = str(path)
                    self.expected_artifacts[str(path)] = digest(path)
            if "olean" not in available:
                raise Failure(2, "compile", f"compiler omitted output for {module}")
            self.artifacts[module] = [[available[p] for p in PARTS[:3] if p in available],
                                      [available[p] for p in PARTS[3:] if p in available]]
            self._store_cached_module(cache_key, available)
        if not self.fast:
            self.freshness()
        report = self.inspect("audit", trusted=list(self.modules))
        if report.get("graph") != self.graph or report.get("replay") is not True:
            raise Failure(2, "audit", "incomplete final audit evidence")
        report["oleanAudit"] = self.olean_audit(
            "olean-audit", scope="trusted", roots=list(self.modules), modules=list(self.modules),
            sources=[(n, str(self.source_copy / p)) for n, p in self.modules.items()])
        if check_downstream:
            downstream = self.compile_and_audit_downstream()
            report["downstream"] = downstream
        self.freshness()
        report.update(sourceSha256=fingerprint(self.initial),
                      toolsSha256=fingerprint({**self.tool_hashes, **cargo_hashes}),
                      toolchain=self.version,
                      guarantee="kernel dependency closure, statement-origin separation, and Cargo DAG boundary")
        report["waiverVacuityAudit"] = {"trusted": trusted_waiver_audit, "rustcCapture": rust_waiver_audit}
        if base_hashes is not None:
            report["baseSnapshotSha256"] = fingerprint(base_hashes)
        (self.stage / "report.json").write_text(json.dumps(report, indent=2))
        self.budget()
        return report


# ===========================================================================
# BEGIN SHARED WAIVER-PIN & 3-AXIS AUDITOR
# Byte-identical in `tools/anneal-lsp/server/proof_health.py` and
# `trusted/audit/check_trusted.py` (the TCB checker must stay a single stdlib-only
# file, so it cannot import `proof_health`); `test_proof_health.py` enforces equality.
# Promoted from the validated `waiver_pin_audit_proto.py` prototype (`2dd38e6d`).
# ===========================================================================

from bisect import bisect_right as _wa_bisect_right  # noqa: E402
from pathlib import Path  # noqa: E402,F811
import re  # noqa: E402,F811
from typing import Any, Iterable  # noqa: E402,F811

# ---------------------------------------------------------------------------
# Rule Identifiers
# ---------------------------------------------------------------------------

RULE_UNPINNED_WAIVER = "unpinned_waiver"
RULE_MALFORMED_WAIVER_PIN = "malformed_waiver_pin"
RULE_DRIFTED_WAIVER_PIN = "drifted_waiver_pin"
RULE_DANGLING_WAIVER = "dangling_waiver"
RULE_INVALID_WAIVER_SYNTAX = "invalid_waiver_syntax"

RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS = "syntactic_contradiction_hypothesis"
RULE_TRIVIAL_CONCLUSION = "trivial_conclusion"
RULE_UNUSED_SUBJECT_IN_CONCLUSION = "unused_subject_in_conclusion"
RULE_TAUTOLOGICAL_IMPLICATION = "tautological_implication"
RULE_TIER_ASSUMPTION_MISMATCH = "tier_assumption_mismatch"

ALL_WAIVER_RULES: tuple[str, ...] = (
    RULE_UNPINNED_WAIVER,
    RULE_MALFORMED_WAIVER_PIN,
    RULE_DRIFTED_WAIVER_PIN,
    RULE_DANGLING_WAIVER,
    RULE_INVALID_WAIVER_SYNTAX,
)

ALL_VACUITY_RULES: tuple[str, ...] = (
    RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
    RULE_TRIVIAL_CONCLUSION,
    RULE_UNUSED_SUBJECT_IN_CONCLUSION,
    RULE_TAUTOLOGICAL_IMPLICATION,
    RULE_TIER_ASSUMPTION_MISMATCH,
)

ALL_WAIVER_AUDIT_RULES: tuple[str, ...] = ALL_WAIVER_RULES + ALL_VACUITY_RULES

WAIVER_DIRECTIVE_TIERS: dict[str, str] = {
    "trusted": "TCB",
    "allow_compile_time_guard": "S1",
    "documented_intent": "S2",
    "pinned_compiler_coupled": "S3",
}

VALID_3AXIS_KINDS: frozenset[str] = frozenset(
    ("safety", "refinement", "divergence", "codec", "helper")
)
VALID_3AXIS_WITNESSES: frozenset[str] = frozenset(
    ("universal", "exists-sat", "negative")
)
VALID_3AXIS_ASSUMES: dict[str, str] = {
    "S0": "S0",
    "S0_rustcLowering": "S0",
    "S0_fnVerified": "S0",
    "S1": "S1",
    "S1_compileTimeGuard": "S1",
    "S2": "S2",
    "S2_documentedIntent": "S2",
    "S3": "S3",
    "S3_pinnedCompilerCoupled": "S3",
    "TCB": "TCB",
}


# ---------------------------------------------------------------------------
# Immutable Finding & Metadata Record Classes (`__slots__`, no `dataclasses`)
# ---------------------------------------------------------------------------


class WaiverPinFinding:
    """One waiver-pin or 3-axis non-vacuity finding. Immutable; compares and hashes by value."""

    __slots__ = (
        "rule",
        "line",
        "message",
        "suggestion",
        "symbol",
        "expected_pin",
        "actual_pin",
        "tier",
    )

    def __init__(
        self,
        rule: str,
        line: int,
        message: str,
        suggestion: str,
        symbol: str = "",
        expected_pin: str = "",
        actual_pin: str = "",
        tier: str = "",
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "rule", rule)
        set_attr(self, "line", line)
        set_attr(self, "message", message)
        set_attr(self, "suggestion", suggestion)
        set_attr(self, "symbol", symbol)
        set_attr(self, "expected_pin", expected_pin)
        set_attr(self, "actual_pin", actual_pin)
        set_attr(self, "tier", tier)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("WaiverPinFinding is immutable")

    def _key(self) -> tuple[str, int, str, str, str, str, str, str]:
        return (
            self.rule,
            self.line,
            self.message,
            self.suggestion,
            self.symbol,
            self.expected_pin,
            self.actual_pin,
            self.tier,
        )

    def __eq__(self, other: object) -> bool:
        if other.__class__ is not WaiverPinFinding:
            return NotImplemented
        return self._key() == other._key()  # type: ignore[attr-defined]

    def __hash__(self) -> int:
        return hash(self._key())

    def __repr__(self) -> str:
        return (
            "WaiverPinFinding(rule=%r, line=%r, symbol=%r, tier=%r, expected_pin=%r, actual_pin=%r)"
            % (
                self.rule,
                self.line,
                self.symbol,
                self.tier,
                self.expected_pin,
                self.actual_pin,
            )
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "rule": self.rule,
            "line": self.line,
            "message": self.message,
            "suggestion": self.suggestion,
            "symbol": self.symbol,
            "expected_pin": self.expected_pin,
            "actual_pin": self.actual_pin,
            "tier": self.tier,
        }


class WaiverAnnotation:
    """Parsed `anneal:` directive extracted from a doc comment or `#[doc = "..."]` attribute.

    `canonical` is the directive text with inline `pin:` tokens removed and whitespace collapsed
    outside string literals; every directive of a doc block is folded into that block's pin hash,
    so swapping a waiver's tier (e.g. `documented_intent` -> `pinned_compiler_coupled`), adding a
    waiver, or editing a rationale invalidates the pin just like an edit to the target item.
    """

    __slots__ = (
        "directive",
        "tier",
        "reason",
        "pin_tokens",
        "line",
        "raw_line",
        "syntax_error",
        "canonical",
    )

    def __init__(
        self,
        directive: str,
        tier: str,
        reason: str,
        pin_tokens: tuple[str, ...],
        line: int,
        raw_line: str,
        syntax_error: str = "",
        canonical: str = "",
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "directive", directive)
        set_attr(self, "tier", tier)
        set_attr(self, "reason", reason)
        set_attr(self, "pin_tokens", pin_tokens)
        set_attr(self, "line", line)
        set_attr(self, "raw_line", raw_line)
        set_attr(self, "syntax_error", syntax_error)
        set_attr(self, "canonical", canonical)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("WaiverAnnotation is immutable")


class TheoremMetadataRecord:
    """Parsed 3-axis theorem metadata and signature analysis for a Lean `theorem`/`lemma`."""

    __slots__ = (
        "name",
        "line",
        "kind",
        "witness",
        "assumes",
        "subject",
        "hypotheses",
        "conclusion",
    )

    def __init__(
        self,
        name: str,
        line: int,
        kind: str,
        witness: str,
        assumes: str,
        subject: str,
        hypotheses: tuple[str, ...],
        conclusion: str,
    ) -> None:
        set_attr = object.__setattr__
        set_attr(self, "name", name)
        set_attr(self, "line", line)
        set_attr(self, "kind", kind)
        set_attr(self, "witness", witness)
        set_attr(self, "assumes", assumes)
        set_attr(self, "subject", subject)
        set_attr(self, "hypotheses", hypotheses)
        set_attr(self, "conclusion", conclusion)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("TheoremMetadataRecord is immutable")


# ---------------------------------------------------------------------------
# Fast Offset-to-Line & Normalization Helpers
# ---------------------------------------------------------------------------

_WA_BLANK_BYTES_TABLE = bytes(10 if i == 10 else 32 for i in range(256))
_PIN_EXACT_RE = re.compile(r"^pin:sha256:([0-9a-f]{12})$")
_PIN_TOKEN_RE = re.compile(r"(?<!\S)(pin:\S*)")


def _wa_blank(seg: str) -> str:
    if "\n" not in seg:
        return " " * len(seg)
    if seg.isascii():
        return seg.encode("ascii").translate(_WA_BLANK_BYTES_TABLE).decode("ascii")
    return "\n".join([" " * len(part) for part in seg.split("\n")])


class _WaLineCounter:
    __slots__ = ("text", "off", "line")

    def __init__(self, text: str) -> None:
        self.text = text
        self.off = 0
        self.line = 1

    def __call__(self, offset: int) -> int:
        if offset >= self.off:
            self.line += self.text.count("\n", self.off, offset)
        elif offset * 2 < self.off:
            self.line = self.text.count("\n", 0, offset) + 1
        else:
            self.line -= self.text.count("\n", offset, self.off)
        self.off = offset
        return self.line


def _is_lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?"


def _is_rust_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def compute_sha256_pin12(normalized_target: str) -> str:
    """Return the 12-hex-character SHA-256 prefix of `normalized_target`."""
    import hashlib  # Lazy: fresh hook processes that never pin skip the OpenSSL import.

    return hashlib.sha256(normalized_target.encode("utf-8")).hexdigest()[:12]


def format_pin_tag(hex12: str) -> str:
    return f"pin:sha256:{hex12}"


_RUST_PUNCT = frozenset("()[]{}:;,.")


def _skip_quoted(text: str, q_start: int, n: int) -> int:
    """Return the offset just past the closing `"` of a backslash-escaped string body starting
    at `q_start` (the first character after the opening quote), or `n` if unterminated."""
    cur = q_start
    while cur < n:
        q = text.find('"', cur)
        if q == -1:
            return n
        bs = 0
        k = q - 1
        while k >= q_start and text[k] == "\\":
            bs += 1
            k -= 1
        cur = q + 1
        if bs % 2 == 0:
            return cur
    return n


def _match_rust_string_literal(text: str, pos: int, n: int) -> int | None:
    """End offset of a Rust raw / byte / C / normal string or char/byte literal at `pos`."""
    end = _match_rust_raw_string(text, pos, n)
    if end is not None:
        return end
    end = _match_rust_char_literal(text, pos, n)
    if end is not None:
        return end
    ch = text[pos]
    if ch == '"':
        return _skip_quoted(text, pos + 1, n)
    if (
        ch in "bc"
        and pos + 1 < n
        and text[pos + 1] == '"'
        and (pos == 0 or not _is_rust_ident_char(text[pos - 1]))
    ):
        return _skip_quoted(text, pos + 2, n)
    return None


def _normalize_rust_item(stripped: str) -> str:
    """Canonicalize a comment-stripped Rust item span for SHA-256 pinning.

    Whitespace runs outside string / raw-string / byte-string / char literals collapse to a
    single space, and whitespace adjacent to `()[]{}:;,.` is dropped (Rust's token stream is
    insensitive to it). Literals are copied verbatim and are recognized with the same lexer as
    the comment stripper, so `'"'` / `b'"'` char literals no longer open a phantom string.
    """
    n = len(stripped)
    out: list[str] = []
    app = out.append
    last = ""
    pending_ws = False
    i = 0
    while i < n:
        ch = stripped[i]
        if ch in " \t\r\n\f\v":
            pending_ws = True
            i += 1
            continue
        end = _match_rust_string_literal(stripped, i, n) if ch in "\"'rbc" else None
        tok = stripped[i:end] if end is not None else ch
        if pending_ws and out and last not in _RUST_PUNCT and tok[0] not in _RUST_PUNCT:
            app(" ")
        app(tok)
        last = tok[-1]
        pending_ws = False
        i = end if end is not None else i + 1
    return "".join(out)


def _match_lean_literal(text: str, pos: int, n: int) -> int | None:
    """End offset of a Lean string / raw string / char literal / `«guillemet»` identifier at
    `pos`, or `None` (a `'` after an identifier character is a prime, not a char literal)."""
    ch = text[pos]
    if ch == '"':
        return _skip_quoted(text, pos + 1, n)
    if ch == "«":
        g = text.find("»", pos + 1)
        return n if g == -1 else g + 1
    if ch == "r" and (pos == 0 or not (_is_lean_ident_char(text[pos - 1]) or text[pos - 1] == ".")):
        p = pos + 1
        while p < n and text[p] == "#":
            p += 1
        if p < n and text[p] == '"':
            closer = '"' + "#" * (p - pos - 1)
            c = text.find(closer, p + 1)
            return n if c == -1 else c + len(closer)
        return None
    if ch == "'" and (pos == 0 or not _is_lean_ident_char(text[pos - 1])):
        if pos + 2 < n and text[pos + 1] == "\\":
            q = pos + 3 if text[pos + 2] != "u" else text.find("}", pos + 2) + 1
            if text[pos + 2] == "x":
                q = pos + 5
            if 0 < q < n and text[q] == "'":
                return q + 1
            return None
        if pos + 2 < n and text[pos + 1] not in "'\\\n" and text[pos + 2] == "'":
            return pos + 3
    return None


_LEAN_CHAR_LIT_RE = re.compile(r"(?<![\w'!?])'(?:\\[^']{1,10}|[^'\\\n])'")


def _normalize_lean_decl(no_comments: str) -> str:
    """Canonicalize a comment-blanked Lean declaration span for SHA-256 pinning.

    Lean is whitespace-sensitive (`xs[i]` indexes but `xs [i]` applies `xs` to a list literal;
    `f x.y` projects but `f x .y` passes a leading-dot constructor; tactic blocks and `where` /
    `|` alternatives are column-sensitive), so unlike Rust this never deletes a separator:
    per line it keeps the exact leading indentation, collapses interior whitespace runs outside
    string / char literals to one space, strips trailing whitespace, and drops blank
    (comment-only) lines.
    """
    if '"' not in no_comments and "«" not in no_comments and _LEAN_CHAR_LIT_RE.search(no_comments) is None:
        fast: list[str] = []
        for raw in no_comments.split("\n"):
            body = raw.split()
            if body:
                fast.append(" " * (len(raw) - len(raw.lstrip(" \t\r\f\v"))) + " ".join(body))
        return "\n".join(fast)
    n = len(no_comments)
    lines: list[str] = []
    cur: list[str] = []
    indent = 0
    at_line_start = True
    pending_ws = False
    i = 0
    while i < n:
        ch = no_comments[i]
        if ch == "\n":
            if cur:
                lines.append(" " * indent + "".join(cur))
            cur = []
            indent = 0
            at_line_start = True
            pending_ws = False
            i += 1
            continue
        if ch in " \t\r\f\v":
            if at_line_start:
                indent += 1
            else:
                pending_ws = True
            i += 1
            continue
        end = _match_lean_literal(no_comments, i, n) if ch in "\"'r«" else None
        tok = no_comments[i:end] if end is not None else ch
        if pending_ws and cur:
            cur.append(" ")
        cur.append(tok)
        at_line_start = False
        pending_ws = False
        i = end if end is not None else i + 1
    if cur:
        lines.append(" " * indent + "".join(cur))
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Directive & Pin Line Parser (`b1f15f743c:trusted/rustc-capture/src/spec.rs`)
# ---------------------------------------------------------------------------


_U128_MAX = (1 << 128) - 1


def _is_ascii_alpha(c: str) -> bool:
    return ("a" <= c <= "z") or ("A" <= c <= "Z")


def _is_ascii_digit(c: str) -> bool:
    return "0" <= c <= "9"


def _lex_spec_tokens(s: str) -> tuple[list[tuple[str, Any]], str]:
    """Lex an `anneal:` directive body exactly like `b1f15f743c:trusted/rustc-capture/src/spec.rs`
    (`lex`): ASCII identifiers/integers only (`u128` range), `"..."` strings admitting only the
    `\\"` and `\\\\` escapes, and `(`, `)`, `=`, `==`, `!=` punctuation."""
    out: list[tuple[str, Any]] = []
    n = len(s)
    i = 0
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c == "(":
            out.append(("LParen", "("))
            i += 1
            continue
        if c == ")":
            out.append(("RParen", ")"))
            i += 1
            continue
        if c == "=":
            if i + 1 < n and s[i + 1] == "=":
                out.append(("EqEq", "=="))
                i += 2
            else:
                out.append(("Eq", "="))
                i += 1
            continue
        if c == "!":
            if i + 1 < n and s[i + 1] == "=":
                out.append(("Ne", "!="))
                i += 2
            else:
                return [], f"expected `!=` at offset {i}"
            continue
        if c == '"':
            start = i
            i += 1
            val: list[str] = []
            closed = False
            while i < n:
                d = s[i]
                i += 1
                if d == '"':
                    closed = True
                    break
                if d == "\\":
                    if i < n and s[i] in ('"', "\\"):
                        val.append(s[i])
                        i += 1
                    else:
                        return [], f"unsupported escape sequence in string literal at offset {start}"
                else:
                    val.append(d)
            if not closed:
                return [], f"unterminated string literal at offset {start}"
            out.append(("Str", "".join(val)))
            continue
        if _is_ascii_alpha(c) or c == "_":
            start = i
            i += 1
            while i < n and (_is_ascii_alpha(s[i]) or _is_ascii_digit(s[i]) or s[i] == "_"):
                i += 1
            out.append(("Ident", s[start:i]))
            continue
        if _is_ascii_digit(c):
            start = i
            i += 1
            while i < n and _is_ascii_digit(s[i]):
                i += 1
            # `[adv B3]` `int()` raises `ValueError` past `sys.get_int_max_str_digits()` (4300)
            # digits, so one long numeral crashed the scan instead of being rejected: `u128::MAX`
            # has 39 significant digits (leading zeros do not count, as in `u128::from_str`).
            sig_digits = s[start:i].lstrip("0")
            if len(sig_digits) > 39:
                return [], f"integer `{s[start:i]}` too large"
            val_int = int(sig_digits) if sig_digits else 0
            if val_int > _U128_MAX:
                return [], f"integer `{s[start:i]}` too large"
            out.append(("Int", val_int))
            continue
        return [], f"unexpected character `{c}` at offset {i}"
    return out, ""


_INLINE_CODE_SPAN_RE = re.compile(r"`[^`]*`")
_WAIVER_TIERS: frozenset[str] = frozenset(("TCB", "S1", "S2", "S3"))
_DIRECTIVE_HEAD_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_]*)")
_PIN_LINE_ADVICE = "put the pin on its own doc line (`pin:sha256:<12hex>`)"


def _split_pin_tokens(rest: str) -> tuple[str, list[str]]:
    """Split whitespace-delimited `pin:` tokens (outside `"..."` strings) out of `rest`."""
    pins: list[str] = []
    parts: list[str] = []
    n = len(rest)
    i = 0
    while i < n:
        ch = rest[i]
        if ch == '"':
            j = i + 1
            while j < n:
                if rest[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if rest[j] == '"':
                    j += 1
                    break
                j += 1
            parts.append(rest[i:j])
            i = j
            continue
        if rest.startswith("pin:", i) and (i == 0 or rest[i - 1].isspace()):
            j = i
            while j < n and not rest[j].isspace():
                j += 1
            pins.append(rest[i:j])
            i = j
            continue
        parts.append(ch)
        i += 1
    return "".join(parts), pins


def _canonical_directive_text(body: str) -> str:
    """Collapse whitespace outside `"..."` strings (string contents are kept verbatim)."""
    out: list[str] = []
    n = len(body)
    pending = False
    i = 0
    while i < n:
        ch = body[i]
        if ch.isspace():
            pending = True
            i += 1
            continue
        if ch == '"':
            j = i + 1
            while j < n:
                if body[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if body[j] == '"':
                    j += 1
                    break
                j += 1
        else:
            j = i + 1
        if pending and out:
            out.append(" ")
        out.append(body[i:j])
        pending = False
        i = j
    return "".join(out)


def _structured_directive(toks: list[tuple[str, Any]]) -> tuple[str, str] | None:
    """Match a lexed directive against spec.rs's structured forms; return `(kind, reason)`."""
    kinds = [t[0] for t in toks]
    vals = [t[1] for t in toks]
    if (
        kinds == ["Ident", "Ident", "LParen", "Ident", "EqEq", "Ident", "RParen"]
        and vals[0] == "spec"
        and vals[1] == "ensures"
        and vals[3] == "ret"
    ):
        return ("spec", "")
    if kinds == ["Ident", "Ident"] and vals[0] == "spec" and vals[1] == "well_formed":
        return ("spec", "")
    if kinds == ["Ident", "Ident", "Ne", "Int"] and vals[0] in ("requires", "invariant"):
        return (str(vals[0]), "")
    if kinds == ["Ident", "Ident", "Eq", "Str"] and vals[0] == "trusted" and vals[1] == "reason":
        return ("trusted", str(vals[3]))
    return None


def parse_pin_line(raw_line: str) -> str | None:
    """Return the trimmed text of a standalone pin doc line (`pin:sha256:<12hex>`), else `None`.

    Pin lines contain no `anneal:` substring, so spec.rs's `parse_doc` treats them as ordinary
    documentation: this is the only pin placement compatible with every waiver directive
    (`allow_compile_time_guard` and `trusted reason = "..."` admit no trailing tokens).
    """
    t = raw_line.strip()
    if t.startswith("pin:") and "anneal:" not in t:
        return t
    return None


def parse_anneal_directive_line(raw_line: str, line_no: int) -> WaiverAnnotation | None:
    """Parse one trimmed doc line containing `anneal:` with spec.rs (`parse_doc`) semantics.

    Returns `None` for lines without `anneal:` (ordinary documentation). Valid non-waiver
    directives (`spec`, `requires`, `invariant`) are returned with tier `S0` so that they are
    folded into the block's pin hash. Inline `pin:` tokens are accepted only on the free-form
    `documented_intent` / `pinned_compiler_coupled` rationales, which spec.rs keeps verbatim.
    """
    line = raw_line.strip()
    if "anneal:" not in line:
        return None
    if not line.startswith("anneal:"):
        # Prose that only mentions `anneal:...` inside markdown code spans is documentation.
        if "anneal:" not in _INLINE_CODE_SPAN_RE.sub("", line):
            return None
        return WaiverAnnotation(
            directive="unknown",
            tier="",
            reason="",
            pin_tokens=(),
            line=line_no,
            raw_line=line,
            syntax_error=f"`anneal:` must start the doc-comment line: `{line}`",
        )

    rest = line[len("anneal:") :]
    rest_wo_pins, pins = _split_pin_tokens(rest)
    canonical = "anneal:" + _canonical_directive_text(rest_wo_pins)
    head_m = _DIRECTIVE_HEAD_RE.match(rest)
    head = head_m.group(1) if head_m else "unknown"
    head_tier = WAIVER_DIRECTIVE_TIERS.get(
        head, "S0" if head in ("spec", "requires", "invariant") else ""
    )

    def mk(directive: str, tier: str, reason: str = "", err: str = "") -> WaiverAnnotation:
        return WaiverAnnotation(
            directive=directive,
            tier=tier,
            reason=reason,
            pin_tokens=tuple(pins),
            line=line_no,
            raw_line=line,
            syntax_error=err,
            canonical=canonical,
        )

    # (1) spec.rs: `rest.trim() == "allow_compile_time_guard"` -- nothing else on the line.
    if rest.strip() == "allow_compile_time_guard":
        return mk("allow_compile_time_guard", "S1", "allow_compile_time_guard")
    if head == "allow_compile_time_guard":
        if pins and rest_wo_pins.strip() == "allow_compile_time_guard":
            return mk(
                head,
                "S1",
                err=(
                    "spec.rs requires `anneal:allow_compile_time_guard` to be the entire doc line, "
                    f"so an inline pin makes `cargo anneal` reject it; {_PIN_LINE_ADVICE}"
                ),
            )
        return mk(
            head,
            "S1",
            err=(
                "spec.rs accepts only the bare `anneal:allow_compile_time_guard` directive "
                f"(no rationale, `reason = ...`, or trailing tokens): `{line}`"
            ),
        )

    # (2) spec.rs: `rest.strip_prefix(kw)` on the *untrimmed* remainder, then a non-empty
    # trimmed rationale (free-form, so an inline pin token is tolerated but is not a rationale).
    for kw in ("documented_intent", "pinned_compiler_coupled"):
        if rest.startswith(kw) and (len(rest) == len(kw) or rest[len(kw)].isspace()):
            rationale = _split_pin_tokens(rest[len(kw) :])[0].strip()
            if not rationale:
                return mk(
                    kw,
                    WAIVER_DIRECTIVE_TIERS[kw],
                    err=(
                        f"`anneal:{kw}` requires a non-empty rationale "
                        f"(a `pin:` token is not a rationale): `{line}`"
                    ),
                )
            return mk(kw, WAIVER_DIRECTIVE_TIERS[kw], rationale)

    # (3) Structured directives: spec.rs lexes the whole remainder (pin tokens included).
    toks, err = _lex_spec_tokens(rest)
    if err:
        if pins:
            toks2, err2 = _lex_spec_tokens(rest_wo_pins)
            if not err2 and _structured_directive(toks2) is not None:
                return mk(
                    head,
                    head_tier,
                    err=(
                        f"inline `pin:` token breaks the spec.rs grammar of `anneal:{head}` "
                        f"(`cargo anneal` would reject the line); {_PIN_LINE_ADVICE}"
                    ),
                )
        return mk(head, head_tier, err=f"in `{line}`: {err}")
    kind = _structured_directive(toks)
    if kind is None:
        if head == "trusted":
            return mk("trusted", "TCB", err=f"`anneal:trusted` requires exactly `reason = \"...\"`: `{line}`")
        if head in ("requires", "invariant"):
            return mk(
                head, "S0", err=f"invalid `anneal:{head}` syntax (expected `<ident> != <int>`): `{line}`"
            )
        if head == "spec":
            return mk("spec", "S0", err=f"unsupported `anneal:spec` syntax `{line}`")
        return mk(head, head_tier, err=f"unsupported Anneal directive `{line}`")
    directive, reason = kind
    if directive == "trusted":
        if not reason.strip():
            return mk("trusted", "TCB", err=f"`anneal:trusted` requires a non-empty reason: `{line}`")
        return mk("trusted", "TCB", reason)
    return mk(directive, "S0", directive)


def waiver_hash_input(anns: Iterable[WaiverAnnotation], normalized_item: str) -> str:
    """SHA-256 pin pre-image of a doc block: its canonical directives (source order) + item."""
    directive_lines = [a.canonical for a in anns if a.canonical]
    if not directive_lines:
        return normalized_item
    return "\n".join(directive_lines) + "\n" + normalized_item


def _validate_waiver_block(
    anns: list[WaiverAnnotation],
    block_pins: list[tuple[str, int]],
    target_symbol: str,
    hash_input: str,
) -> list[WaiverPinFinding]:
    """Validate directive syntax and the `pin:sha256:<12hex>` of one doc block.

    `block_pins` are the standalone pin lines of the block; inline pins on free-form waiver
    rationales are also honoured. Every pin of the block must agree and must equal
    `sha256(hash_input)[:12]`, where `hash_input` binds both the block's directives and the
    normalized target item.
    """
    findings: list[WaiverPinFinding] = []
    expected_pin = format_pin_tag(compute_sha256_pin12(hash_input))

    bad = [a for a in anns if a.syntax_error]
    for ann in bad:
        findings.append(
            WaiverPinFinding(
                rule=RULE_INVALID_WAIVER_SYNTAX,
                line=ann.line,
                symbol=target_symbol or ann.directive,
                tier=ann.tier,
                expected_pin=expected_pin,
                actual_pin=ann.pin_tokens[0] if ann.pin_tokens else "",
                message=f"Invalid Anneal directive syntax: {ann.syntax_error}",
                suggestion=(
                    "Use the exact spec.rs forms (`anneal:trusted reason = \"...\"`, "
                    "`anneal:allow_compile_time_guard`, `anneal:documented_intent <rationale>`, "
                    "`anneal:pinned_compiler_coupled <reason>`) and record the pin on its own doc "
                    f"line: `{expected_pin}`."
                ),
            )
        )
    if bad:
        return findings

    waivers = [a for a in anns if a.tier in _WAIVER_TIERS]
    if not waivers:
        return findings
    pins = [p for p, _ in block_pins] + [p for a in waivers for p in a.pin_tokens]

    for ann in waivers:
        if not pins:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_UNPINNED_WAIVER,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin="",
                    message=(
                        f"Unpinned `{ann.tier}` waiver `anneal:{ann.directive}` on `{target_symbol}` "
                        f"(missing `{expected_pin}`)."
                    ),
                    suggestion=f"Add the doc line `{expected_pin}` to this waiver's doc block.",
                )
            )
        elif len(set(pins)) > 1:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_MALFORMED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=",".join(pins),
                    message=(
                        f"Multiple conflicting `pin:` tokens in the doc block of `{target_symbol}`: "
                        f"{pins!r}."
                    ),
                    suggestion=f"Keep a single `{expected_pin}` pin line.",
                )
            )
        elif _PIN_EXACT_RE.match(pins[0]) is None:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_MALFORMED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=pins[0],
                    message=(
                        f"Malformed waiver pin `{pins[0]}` on `anneal:{ann.directive}` for "
                        f"`{target_symbol}` (expected `pin:sha256:<12 lowercase hex digits>`)."
                    ),
                    suggestion=f"Replace `{pins[0]}` with `{expected_pin}`.",
                )
            )
        elif pins[0] != expected_pin:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_DRIFTED_WAIVER_PIN,
                    line=ann.line,
                    symbol=target_symbol or ann.directive,
                    tier=ann.tier,
                    expected_pin=expected_pin,
                    actual_pin=pins[0],
                    message=(
                        f"Waiver pin drift on `{target_symbol}` (`anneal:{ann.directive}`, tier "
                        f"`{ann.tier}`): recorded `{pins[0]}`, but the directives + target "
                        f"declaration hash to `{expected_pin}`."
                    ),
                    suggestion=(
                        f"Re-audit `{target_symbol}` under tier `{ann.tier}` and update the pin to "
                        f"`{expected_pin}`."
                    ),
                )
            )
    return findings


def _collect_block_directives(
    doc_lines: Iterable[tuple[int, str]],
) -> tuple[list[WaiverAnnotation], list[tuple[str, int]]]:
    """Parse `(line_no, text)` doc lines into directives and standalone pin lines."""
    anns: list[WaiverAnnotation] = []
    pins: list[tuple[str, int]] = []
    for line_no, raw in doc_lines:
        if "anneal:" in raw:
            ann = parse_anneal_directive_line(raw, line_no)
            if ann is not None:
                anns.append(ann)
            continue
        if "pin:" in raw:
            p = parse_pin_line(raw)
            if p is not None:
                pins.append((p, line_no))
    return anns, pins


# ---------------------------------------------------------------------------
# Rust (`.rs`) Lexer, Doc-Attribute Extractor & Target Item Span Scanner
# ---------------------------------------------------------------------------


def _match_rust_raw_string(text: str, pos: int, n: int) -> int | None:
    """If `text[pos:]` starts a Rust raw string (`r"..."`, `r#"..."#`, `br#"..."#`, `cr#"..."#`),
    return the end offset past the closing delimiter; otherwise `None`."""
    ch = text[pos]
    if ch not in "rbc":
        return None
    if pos > 0 and _is_rust_ident_char(text[pos - 1]):
        return None
    p = pos
    if ch in "bc":
        if p + 1 < n and text[p + 1] == "r":
            p += 2
        else:
            return None
    else:
        p += 1
    hashes = 0
    while p < n and text[p] == "#":
        hashes += 1
        p += 1
    if p >= n or text[p] != '"':
        return None
    closer = '"' + "#" * hashes
    c = text.find(closer, p + 1)
    return n if c == -1 else c + len(closer)


def _match_rust_char_literal(text: str, pos: int, n: int) -> int | None:
    """If `text[pos:]` starts a Rust character or byte literal (`'x'`, `'\\n'`, `'\\''`,
    `'\\u{1F600}'`, `b'x'`) rather than a lifetime (`'a`, `'static`), return the end offset past
    the closing `'`; otherwise `None`."""
    p = pos
    if text[p] == "b":
        if pos > 0 and _is_rust_ident_char(text[pos - 1]):
            return None
        if p + 1 < n and text[p + 1] == "'":
            p += 1
        else:
            return None
    elif text[p] == "'":
        if pos > 0 and _is_rust_ident_char(text[pos - 1]):
            return None
    else:
        return None

    if p + 2 >= n:
        return None
    if text[p + 1] == "\\":
        # Skip the escaped character first so that `'\''` and `'\\'` close correctly.
        q = p + 3
        if text[p + 2] == "u" and q < n and text[q] == "{":
            close = text.find("}", q, q + 10)
            if close == -1:
                return None
            q = close + 1
        elif text[p + 2] == "x":
            q = p + 5
        return q + 1 if q < n and text[q] == "'" else None
    if text[p + 1] != "'" and text[p + 1] != "\n" and text[p + 2] == "'":
        return p + 3
    return None


def _unescape_rust_doc_string(raw: str) -> str:
    """Decode a Rust (non-raw) string literal body the way `rustc` does for `#[doc = "..."]`:
    `\\n \\r \\t \\\\ \\0 \\' \\"`, `\\xNN`, `\\u{...}`, and `\\`-newline continuations (which
    also skip the following whitespace). Escapes such as `anneal\\x3atrusted` therefore cannot
    hide a waiver directive from the auditor."""
    out: list[str] = []
    i = 0
    n = len(raw)
    simple = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", "0": "\0", "'": "'", '"': '"'}
    while i < n:
        ch = raw[i]
        if ch != "\\" or i + 1 >= n:
            out.append(ch)
            i += 1
            continue
        nxt = raw[i + 1]
        if nxt in simple:
            out.append(simple[nxt])
            i += 2
            continue
        if nxt == "x" and i + 3 < n and all(c in "0123456789abcdefABCDEF" for c in raw[i + 2 : i + 4]):
            out.append(chr(int(raw[i + 2 : i + 4], 16)))
            i += 4
            continue
        if nxt == "u" and i + 2 < n and raw[i + 2] == "{":
            close = raw.find("}", i + 3)
            if close != -1:
                digits = raw[i + 3 : close].replace("_", "")
                try:
                    out.append(chr(int(digits, 16)))
                    i = close + 1
                    continue
                except ValueError:
                    pass
        if nxt == "\n" or (nxt == "\r" and i + 2 < n and raw[i + 2] == "\n"):
            i += 2 if nxt == "\n" else 3
            while i < n and raw[i] in " \t\r\n":
                i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def _find_rust_attr_end(text: str, open_bracket: int, n: int) -> int:
    """Offset just past the `]` matching the `[` at `open_bracket` (string-literal aware)."""
    depth = 0
    p = open_bracket
    while p < n:
        ch = text[p]
        if ch in "\"'rbc":
            end = _match_rust_string_literal(text, p, n)
            if end is not None:
                p = end
                continue
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return p + 1
        p += 1
    return n


_RUST_ATTR_DOC_ASSIGN_RE = re.compile(r"\bdoc\s*=")


def _scan_rust_tokens_and_docs(
    text: str,
) -> tuple[str, list[tuple[int, int, int, str, bool]], list[tuple[int, int, str]]]:
    """Return `(comment_stripped_text, doc_segments, opaque_doc_attrs)` for Rust source `text`.

    - `comment_stripped_text` has the exact length and newlines of `text`, with all comments
      (`//`, `///`, `//!`, `/* ... */`) and literal `#[doc = ...]` / `#![doc = ...]` attributes
      blanked, while string / char literals, lifetimes, and semantic attributes (`#[repr(C)]`)
      are kept.
    - `doc_segments` holds `(start, end, start_line, doc_text, is_inner)` for every doc comment
      and literal doc attribute; inner docs (`//!`, `/*! */`, `#![doc]`) document the enclosing
      module, never the next item.
    - `opaque_doc_attrs` holds `(start, start_line, kind)` for outer attributes whose doc text
      `rustc` computes (`#[doc = concat!(..)]`, `#[doc = include_str!(..)]`,
      `#[cfg_attr(.., doc = ..)]`): a waiver hidden there is invisible to source scanning.
    """
    n = len(text)
    out: list[str] = []
    app = out.append
    docs: list[tuple[int, int, int, str, bool]] = []
    opaque: list[tuple[int, int, str]] = []
    line_of = _WaLineCounter(text)
    i = 0
    while i < n:
        ch = text[i]
        if ch == "/" and i + 1 < n and text[i + 1] in "/*":
            if text[i + 1] == "/":
                nl = text.find("\n", i + 2)
                end = n if nl == -1 else nl
                raw_comment = text[i:end]
                if raw_comment.startswith("///") and not raw_comment.startswith("////"):
                    docs.append((i, end, line_of(i), raw_comment[3:], False))
                elif raw_comment.startswith("//!"):
                    docs.append((i, end, line_of(i), raw_comment[3:], True))
                app(" " * (end - i))
                i = end
                continue
            depth = 1
            cur = i + 2
            while depth > 0 and cur < n:
                c = text.find("*/", cur)
                if c == -1:
                    cur = n
                    break
                o = text.find("/*", cur, c)
                if o != -1:
                    depth += 1
                    cur = o + 2
                else:
                    depth -= 1
                    cur = c + 2
            raw_blk = text[i:cur]
            body = raw_blk[3 : -2 if raw_blk.endswith("*/") else len(raw_blk)]
            if raw_blk.startswith("/**") and not raw_blk.startswith("/***") and raw_blk != "/**/":
                docs.append((i, cur, line_of(i), body, False))
            elif raw_blk.startswith("/*!"):
                docs.append((i, cur, line_of(i), body, True))
            app(_wa_blank(raw_blk))
            i = cur
            continue

        if ch == "#" and i + 1 < n:
            attr_start = i
            p_bang = i + 1
            while p_bang < n and text[p_bang] in " \t\r\n":
                p_bang += 1
            is_inner = p_bang < n and text[p_bang] == "!"
            p_open = p_bang + 1 if is_inner else p_bang
            while p_open < n and text[p_open] in " \t\r\n":
                p_open += 1
            if p_open < n and text[p_open] == "[":
                p = p_open + 1
                while p < n and text[p].isspace():
                    p += 1
                if text.startswith("doc", p) and (p + 3 < n and not _is_rust_ident_char(text[p + 3])):
                    q = p + 3
                    while q < n and text[q].isspace():
                        q += 1
                    if q < n and text[q] == "=":
                        q += 1
                        while q < n and text[q].isspace():
                            q += 1
                        raw_end = _match_rust_raw_string(text, q, n)
                        doc_val: str | None = None
                        val_end = q
                        if raw_end is not None:
                            q_quote = text.find('"', q)
                            hashes = q_quote - (q + (2 if text[q] in "bc" else 1))
                            doc_val = text[q_quote + 1 : raw_end - 1 - hashes]
                            val_end = raw_end
                        elif q < n and text[q] == '"':
                            val_end = _skip_quoted(text, q + 1, n)
                            doc_val = _unescape_rust_doc_string(text[q + 1 : val_end - 1])
                        if doc_val is not None:
                            while val_end < n and text[val_end].isspace():
                                val_end += 1
                            if val_end < n and text[val_end] == "]":
                                attr_end = val_end + 1
                                docs.append((attr_start, attr_end, line_of(attr_start), doc_val, is_inner))
                                app(_wa_blank(text[attr_start:attr_end]))
                                i = attr_end
                                continue
                        # `#[doc = #var]` is a `quote!` template inside a proc-macro body, not an
                        # attribute of this file; anything else computed by `rustc` is opaque.
                        if not is_inner and doc_val is None and q < n and text[q] != "#":
                            opaque.append((attr_start, line_of(attr_start), "doc = <computed>"))
                elif not is_inner:
                    attr_end = _find_rust_attr_end(text, p_open, n)
                    if _RUST_ATTR_DOC_ASSIGN_RE.search(text, p, attr_end):
                        attr_head = "cfg_attr(.., doc = ..)" if text.startswith("cfg_attr", p) else ".., doc = .."
                        opaque.append((attr_start, line_of(attr_start), attr_head))

        lit_end = _match_rust_string_literal(text, i, n) if ch in "\"'rbc" else None
        if lit_end is not None:
            app(text[i:lit_end])
            i = lit_end
            continue

        app(ch)
        i += 1

    return "".join(out), docs, opaque


def _find_preceding_rust_attributes_start(stripped: str, doc_start: int) -> int:
    """Walk backwards across any outer attributes `#[...]` immediately preceding `doc_start`
    on the same Rust item (e.g., `#[repr(C)]` written above `/// anneal:...`), using
    string-literal-aware forward bracket matching so brackets inside attribute string literals
    (`#[deprecated(note = "use foo[0]")]`) never desync attribute discovery."""
    cur = doc_start
    while cur > 0:
        p = cur
        while p > 0 and stripped[p - 1] in " \t\r\n":
            p -= 1
        if p <= 0 or stripped[p - 1] != "]":
            break
        matched_hash = -1
        search_h = p - 2
        while search_h >= 0:
            h_idx = stripped.rfind("#", 0, search_h + 1)
            if h_idx == -1:
                break
            q_br = h_idx + 1
            while q_br < p and stripped[q_br] in " \t\r\n":
                q_br += 1
            if q_br < p and stripped[q_br] == "[":
                if _find_rust_attr_end(stripped, q_br, p) == p:
                    matched_hash = h_idx
                    break
            search_h = h_idx - 1
        if matched_hash != -1:
            cur = matched_hash
        else:
            break
    return cur


_RUST_ITEM_NAME_RE = re.compile(
    r"\b(?:fn|struct|enum|union|type|const|static|trait|mod|macro_rules!)\s+((?:r#)?[A-Za-z_][A-Za-z0-9_]*)"
)
_RUST_WORD_RE = re.compile(r"(?:r#)?[A-Za-z_][A-Za-z0-9_]*!?")
_RUST_SEMI_ITEMS = frozenset(("const", "static", "type", "use", "extern", "let"))


def _rust_item_kind(stripped: str, i: int, n: int) -> tuple[str, int]:
    """Skip outer attributes, visibility, and qualifiers starting at `i`; return the item
    keyword (`fn`, `struct`, `const`, `impl`, ...) and its offset (`("", i)` if none)."""
    p = i
    while p < n:
        while p < n and stripped[p].isspace():
            p += 1
        if p >= n:
            return "", i
        if stripped[p] == "#":
            q = p + 1
            while q < n and stripped[q].isspace():
                q += 1
            if q < n and stripped[q] == "[":
                p = _find_rust_attr_end(stripped, q, n)
                continue
            return "", i
        m = _RUST_WORD_RE.match(stripped, p)
        if m is None:
            return "", i
        word = m.group(0)
        word_start = p
        p = m.end()
        if word == "pub":
            while p < n and stripped[p].isspace():
                p += 1
            if p < n and stripped[p] == "(":
                depth = 0
                while p < n:
                    if stripped[p] == "(":
                        depth += 1
                    elif stripped[p] == ")":
                        depth -= 1
                        if depth == 0:
                            p += 1
                            break
                    p += 1
            continue
        if word in ("unsafe", "async", "default", "safe"):
            continue
        if word == "extern":
            while p < n and stripped[p].isspace():
                p += 1
            if stripped.startswith("crate", p):
                return "extern", word_start
            if p < n and stripped[p] == '"':
                p = _skip_quoted(stripped, p + 1, n)
            continue
        if word == "const":
            q = p
            while q < n and stripped[q].isspace():
                q += 1
            m2 = _RUST_WORD_RE.match(stripped, q)
            if m2 is not None and m2.group(0) in ("fn", "unsafe", "async", "extern"):
                continue
            return "const", word_start
        return word, word_start
    return "", i


def _extract_rust_target_span(
    stripped: str, search_from: int, pre_attr_start: int
) -> tuple[int, int, str] | None:
    """Scan forward from `search_from` in comment-stripped Rust text to the end of the annotated
    item. Returns `(start_offset, end_offset, item_name)` or `None` if the waiver is dangling.

    `const` / `static` / `type` / `use` / `extern crate` items end at their top-level `;` (so a
    struct-literal initializer `Foo { .. }.with(2)` stays inside the pinned span); other items
    end at the `}` closing their body or at a top-level `;`, where generic-argument depth `<..>`
    is tracked at brace level 0 so a const-generic block in a signature
    (`-> Wrapper<{ N }>`) is never mistaken for the item body.
    """
    n = len(stripped)
    i = search_from
    while i < n and stripped[i] in " \t\r\n":
        i += 1
    if i >= n or stripped[i] == "}":
        return None

    start_off = min(pre_attr_start, i)
    kind, kw_off = _rust_item_kind(stripped, i, n)
    semi_item = kind in _RUST_SEMI_ITEMS
    p = i
    paren = bracket = brace = angle = 0
    saw_item_token = False

    def finish(end: int) -> tuple[int, int, str]:
        if kind == "impl":
            return start_off, end, "impl"
        m = _RUST_ITEM_NAME_RE.search(stripped, kw_off if kind else start_off, end)
        return start_off, end, (m.group(1) if m else "item")

    while p < n:
        ch = stripped[p]
        if ch in " \t\r\n":
            p += 1
            continue
        if ch in "\"'rbc":
            lit_end = _match_rust_string_literal(stripped, p, n)
            if lit_end is not None:
                saw_item_token = True
                p = lit_end
                continue
        top = paren == 0 and bracket == 0 and brace == 0
        if ch == "(":
            paren += 1
        elif ch == ")":
            if paren > 0:
                paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            if bracket > 0:
                bracket -= 1
        elif (
            ch == "<"
            and top
            and not semi_item
            and (p + 1 >= n or stripped[p + 1] not in "<=")
            and (p == 0 or stripped[p - 1] != "<")
        ):
            angle += 1
        elif ch == ">" and top and not semi_item and angle > 0 and stripped[p - 1] not in "-=":
            angle -= 1
        elif ch == "{":
            brace += 1
        elif ch == "}":
            if brace == 0:
                return None
            brace -= 1
            p += 1
            if not semi_item and brace == 0 and paren == 0 and bracket == 0 and angle == 0:
                return finish(p)
            continue
        elif ch == ";" and top and (semi_item or angle == 0):
            if not saw_item_token:
                return None
            return finish(p + 1)
        saw_item_token = True
        p += 1
    return None


def _rust_outer_doc_groups(
    stripped: str, doc_segments: list[tuple[int, int, int, str, bool]]
) -> list[tuple[int, int, list[tuple[int, str]]]]:
    """Group consecutive *outer* doc segments of one item (separated only by whitespace,
    comments, or outer attributes `#[...]`)."""
    groups: list[tuple[int, int, list[tuple[int, str]]]] = []
    for seg_start, seg_end, seg_line, doc_body, is_inner in doc_segments:
        if is_inner:
            continue
        if groups:
            prev_start, prev_end, prev_lines = groups[-1]
            if not stripped[
                prev_end : _find_preceding_rust_attributes_start(stripped, seg_start)
            ].strip():
                groups[-1] = (prev_start, seg_end, prev_lines + [(seg_line, doc_body)])
                continue
        groups.append((seg_start, seg_end, [(seg_line, doc_body)]))
    return groups


def audit_rust_text(text: str, *, file_path: str | Path | None = None) -> list[WaiverPinFinding]:
    """Scan Rust source `text` for `S0`-`S3` waiver pin and directive syntax findings."""
    _ = file_path
    if "anneal" not in text and "doc" not in text:
        return []

    stripped, doc_segments, opaque = _scan_rust_tokens_and_docs(text)
    findings: list[WaiverPinFinding] = []

    for _, op_line, op_kind in opaque:
        findings.append(
            WaiverPinFinding(
                rule=RULE_INVALID_WAIVER_SYNTAX,
                line=op_line,
                symbol=op_kind,
                message=(
                    f"Unauditable computed doc attribute `#[{op_kind}]`: `rustc` expands it before the "
                    "Anneal capture reads doc attributes, so a waiver directive hidden there would evade "
                    "SHA-256 pinning."
                ),
                suggestion="Write Anneal directives only as literal `///` lines or `#[doc = \"...\"]` attributes.",
            )
        )

    for seg_start, seg_end, seg_line, doc_body, is_inner in doc_segments:
        if is_inner:
            for off_l, raw_l in enumerate(doc_body.split("\n")):
                ann = parse_anneal_directive_line(raw_l, seg_line + off_l)
                if ann is not None:
                    findings.append(
                        WaiverPinFinding(
                            rule=RULE_DANGLING_WAIVER,
                            line=ann.line,
                            symbol=ann.directive,
                            tier=ann.tier,
                            message=(
                                f"`anneal:{ann.directive}` sits in an inner doc comment (`//!`, `/*! */`, "
                                "`#![doc]`), which documents the enclosing module rather than the next item."
                            ),
                            suggestion="Move the directive into an outer `///` doc comment on the target item.",
                        )
                    )

    for grp_start, grp_end, line_docs in _rust_outer_doc_groups(stripped, doc_segments):
        doc_lines = [
            (base_line + off_l, raw_l)
            for base_line, doc_body in line_docs
            for off_l, raw_l in enumerate(doc_body.split("\n"))
        ]
        anns, block_pins = _collect_block_directives(doc_lines)
        if not anns:
            continue
        pre_attr_start = _find_preceding_rust_attributes_start(stripped, grp_start)
        target_info = _extract_rust_target_span(stripped, grp_end, pre_attr_start)
        if target_info is None:
            for ann in anns:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_DANGLING_WAIVER,
                        line=ann.line,
                        symbol=ann.directive,
                        tier=ann.tier,
                        message=(
                            f"Dangling `anneal:{ann.directive}` waiver annotation with no following Rust item declaration."
                        ),
                        suggestion="Attach the waiver doc-comment directly to a `fn`, `struct`, `enum`, `union`, `type`, or `const` item.",
                    )
                )
            continue
        t_start, t_end, item_name = target_info
        hash_input = waiver_hash_input(anns, _normalize_rust_item(stripped[t_start:t_end]))
        findings.extend(_validate_waiver_block(anns, block_pins, item_name, hash_input))

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    return findings


# ---------------------------------------------------------------------------
# Lean 4 (`.lean`) Lexer, Waiver Pin Scanner & 3-Axis Non-Vacuity Auditor
# ---------------------------------------------------------------------------


def _scan_lean_comments_and_strings(
    text: str,
) -> tuple[str, list[tuple[int, int, int, str, str]]]:
    """Single-pass Lean 4 scanner returning:
    - `code_only`: comments AND string literals blanked (preserving offsets and `\\n`),
    - `comment_blocks`: list of `(start_off, end_off, start_line, comment_body, kind)` for `--`
      (`"l"`), `/- ... -/` (`"b"`), `/-- ... -/` docstrings (`"d"`), and `/-! ... -/` module
      docstrings (`"m"`).
    """
    n = len(text)
    if n == 0:
        return "", []
    out_code: list[str] = []
    comments: list[tuple[int, int, int, str, str]] = []
    app_c = out_code.append
    find = text.find
    line_of = _WaLineCounter(text)
    pos = 0
    i_blk = find("/-", 0)
    i_lin = find("--", 0)
    i_str = find('"', 0)
    i_gui = find("«", 0)

    while pos < n:
        if i_blk != -1 and i_blk < pos:
            i_blk = find("/-", pos)
        if i_lin != -1 and i_lin < pos:
            i_lin = find("--", pos)
        if i_str != -1 and i_str < pos:
            i_str = find('"', pos)
        if i_gui != -1 and i_gui < pos:
            i_gui = find("«", pos)

        nxt = n
        kind = 0
        if 0 <= i_blk < nxt:
            nxt = i_blk
            kind = 1
        if 0 <= i_lin < nxt:
            nxt = i_lin
            kind = 2
        if 0 <= i_str < nxt:
            nxt = i_str
            kind = 3
        if 0 <= i_gui < nxt:
            nxt = i_gui
            kind = 4

        if kind == 0:
            tail = text[pos:]
            app_c(tail)
            break
        if nxt > pos:
            seg = text[pos:nxt]
            app_c(seg)

        if kind == 4:
            if (
                nxt > 0
                and nxt + 1 < n
                and text[nxt - 1] == "'"
                and text[nxt + 1] == "'"
                and (nxt < 2 or (not _is_lean_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\"))
            ):
                app_c(" ")
                pos = nxt + 1
                continue
            g_end = find("»", nxt + 1)
            if g_end != -1 and find("\n", nxt + 1, g_end) == -1:
                seg = text[nxt : g_end + 1]
                app_c(seg)
                pos = g_end + 1
            else:
                app_c("«")
                pos = nxt + 1
            continue

        if kind == 2:
            nl = find("\n", nxt + 2)
            end = n if nl == -1 else nl
            comments.append((nxt, end, 0, text[nxt + 2 : end], "l"))
            blank = " " * (end - nxt)
            app_c(blank)
            pos = end
            continue

        if kind == 1:
            depth = 1
            cur = nxt + 2
            while depth > 0 and cur < n:
                c = find("-/", cur)
                if c == -1:
                    cur = n
                    break
                o = find("/-", cur, c)
                if o != -1:
                    depth += 1
                    cur = o + 2
                else:
                    depth -= 1
                    cur = c + 2
            raw_blk = text[nxt:cur]
            inner = raw_blk[3 if raw_blk.startswith("/--") or raw_blk.startswith("/-!") else 2 : -2 if raw_blk.endswith("-/") else len(raw_blk)]
            c_kind = "d" if raw_blk.startswith("/--") else ("m" if raw_blk.startswith("/-!") else "b")
            c_line = line_of(nxt) if (c_kind in ("d", "m") and ("anneal:" in inner or "pin:" in inner)) else 0
            comments.append((nxt, cur, c_line, inner, c_kind))
            app_c(" " * (cur - nxt) if "\n" not in raw_blk else _wa_blank(raw_blk))
            pos = cur
            continue

        # String literal or quote char literal `'\"'` / `'"'`
        if nxt > 0 and text[nxt - 1] in "#r'\\":
            h = nxt
            while h > 0 and text[h - 1] == "#":
                h -= 1
            if (
                h > 0
                and text[h - 1] == "r"
                and (h < 2 or not (_is_lean_ident_char(text[h - 2]) or text[h - 2] == "."))
            ):
                closer = '"' + "#" * (nxt - h)
                c = find(closer, nxt + 1)
                cur = n if c == -1 else c + len(closer)
                seg = text[nxt:cur]
                app_c(_wa_blank(seg))
                pos = cur
                continue
            if (
                nxt + 1 < n
                and text[nxt + 1] == "'"
                and (
                    (
                        text[nxt - 1] == "'"
                        and (
                            nxt < 2
                            or (not _is_lean_ident_char(text[nxt - 2]) and text[nxt - 2] != "\\")
                        )
                    )
                    or (
                        nxt >= 2
                        and text[nxt - 2 : nxt] == "'\\"
                        and (nxt < 3 or not _is_lean_ident_char(text[nxt - 3]))
                    )
                )
            ):
                app_c(" ")
                pos = nxt + 1
                i_str = find('"', pos)
                continue

        cur = nxt + 1
        while cur < n:
            q = find('"', cur)
            if q == -1:
                cur = n
                break
            bs = 0
            k = q - 1
            while k >= nxt + 1 and text[k] == "\\":
                bs += 1
                k -= 1
            cur = q + 1
            if bs % 2 == 0:
                break
        seg = text[nxt:cur]
        app_c(_wa_blank(seg))
        pos = cur

    return "".join(out_code), comments


def _no_comments_slice(
    text: str, comment_blocks: list[tuple[int, int, int, str, str]], starts: list[int], a: int, b: int
) -> str:
    """`text[a:b]` with every comment blanked (string literals preserved), rebuilt on demand
    from the comment offsets (only pinned declarations need it, so the full-file
    comment-blanked copy is never materialized)."""
    k = _wa_bisect_right(starts, a) - 1
    if k < 0:
        k = 0
    parts: list[str] = []
    pos = a
    nb = len(comment_blocks)
    while k < nb:
        cs, ce = comment_blocks[k][0], comment_blocks[k][1]
        if cs >= b:
            break
        if ce > pos:
            lo = cs if cs > pos else pos
            if lo > pos:
                parts.append(text[pos:lo])
            hi = ce if ce < b else b
            parts.append(_wa_blank(text[lo:hi]))
            pos = hi
        k += 1
    if pos < b:
        parts.append(text[pos:b])
    return "".join(parts)


_LEAN_COL0_BOUNDARY_RE = re.compile(r"\n(?=\S)")
_LEAN_NONEMPTY_LINE_RE = re.compile(r"\n([ \t]*)(?=\S)")
_LEAN_CONTINUATION_RE = re.compile(
    r"[ \t]*(?:\||where\b|termination_by\b|decreasing_by\b|deriving\b(?![ \t]+instance\b))"
)
# A line at or left of the declaration's column ends it only if it starts a *command* (optionally
# preceded by `@[...]` attributes or declaration modifiers skipped by `_skip_lean_attrs_and_modifiers`).
# Lean term bodies (`def layoutSize : Nat :=\n8`) and column-0 `structure`/`where` members
# (`protected b : Nat`, `@[simp] aux : 1 = 1 := rfl`) are not followed by a command keyword after
# skipping `@[...]` and modifiers, so they remain inside the pinned span.
_LEAN_BARE_COMMAND_START_RE = re.compile(
    r"#[A-Za-z_]\w*(?!\[)|"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example|"
    r"end|namespace|section|mutual|variable|universe|open|export|set_option|attribute|"
    r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|"
    r"declare_syntax_cat|initialize|builtin_initialize|deriving|import|"
    r"omit|include|add_decl_doc|register_option|run_cmd|run_elab|run_meta|alias)\b"
)


def _is_lean_command_start(code_only: str, cand: int) -> bool:
    """Return `True` iff `code_only[cand:]` starts a top-level Lean command (after any `@[...]`
    attributes and declaration modifiers)."""
    kw = _skip_lean_attrs_and_modifiers(code_only, cand)
    return _LEAN_BARE_COMMAND_START_RE.match(code_only, kw) is not None


def _lean_indent_of(code_only: str, offset: int, text: str | None = None) -> int:
    """Return the column offset (`0`-based) of `offset`'s line indentation (ignoring any
    leading `/- ... -/` block comment on the same line when `text` is given).

    With `text`, this is the indentation used for a declaration's *own* start line, and it is
    deliberately the smallest plausible column: the first non-blank `text` column of the line,
    or, when the line opens with the tail of a block comment begun on an earlier line, the
    smaller of that and the comment opener's line indentation. A smaller declaration indent
    only keeps more following lines inside the span (conservative: never a pin bypass)."""
    nl = code_only.rfind("\n", 0, offset)
    line_start = 0 if nl == -1 else nl + 1
    if text is None:
        return offset - line_start
    p = line_start
    while p < offset and text[p] in " \t":
        p += 1
    indent = p - line_start
    if p < offset and not text.startswith("/-", p):
        open_pos = text.rfind("/-", 0, offset)
        if open_pos != -1:
            nl0 = text.rfind("\n", 0, open_pos)
            ls0 = 0 if nl0 == -1 else nl0 + 1
            q = ls0
            while q < open_pos and text[q] in " \t":
                q += 1
            if q == open_pos and q - ls0 < indent:
                indent = q - ls0
    return indent


def _find_lean_decl_end(
    code_only: str, after_hdr_pos: int, decl_indent: int = 0, text: str | None = None
) -> int:
    """Find the end offset of a Lean declaration starting at indentation `decl_indent` before `after_hdr_pos`.

    - Any line indented strictly deeper than `decl_indent` (`line_indent > decl_indent`) belongs to
      the declaration's body (`structure`/`class` fields, `where` auxiliary `def`s, tactics) and
      never ends the span.
    - Otherwise a line at `line_indent <= decl_indent` ends the span only if it starts a command
      (`_is_lean_command_start`: a command keyword optionally preceded by `@[...]` attributes and
      modifiers); non-command lines such as a column-0 term body (`def x : Nat :=\\n8`), column-0
      `protected b : Nat` / `@[simp] aux := rfl` members, and pattern-match / `where` /
      `termination_by` continuations stay inside.
    """
    n = len(code_only)
    pos = after_hdr_pos
    # Without any `-/` after the header no line can start with a closed same-line block comment
    # (`/- c -/ def next`), so column-0 `code_only` boundaries are exact. `find` (not `in` on a
    # slice) keeps this O(distance) instead of copying the rest of the file per declaration.
    if decl_indent <= 0 and (text is None or text.find("-/", after_hdr_pos) == -1):
        while pos < n:
            m = _LEAN_COL0_BOUNDARY_RE.search(code_only, pos)
            if m is None:
                return n
            cand = m.start() + 1
            if _LEAN_CONTINUATION_RE.match(code_only, cand) or not _is_lean_command_start(
                code_only, cand
            ):
                pos = cand + 1
                continue
            return m.start()
        return n

    while pos < n:
        m = _LEAN_NONEMPTY_LINE_RE.search(code_only, pos)
        if m is None:
            return n
        ws = m.group(1)
        cand = m.end()
        line_indent = len(ws)
        if text is not None and line_indent > decl_indent:
            # A block comment opened on this very line (`/- c -/ def next`) is blanked to spaces
            # in `code_only`; its opening column is the line's indentation only when at most one
            # space separates `-/` from the command token and the preceding non-empty line in
            # `code_only` is not `where` (so `where\n/- c -/  def helper` keeps `def helper`
            # inside the declaration's `where` block).
            line_start = m.start() + 1
            q = line_start
            while q < cand and text[q] in " \t":
                q += 1
            if q < cand and text.startswith("/-", q) and (
                text.endswith("-/", line_start, cand) or text.endswith("-/ ", line_start, cand)
            ):
                prev_end = m.start()
                while prev_end > after_hdr_pos and code_only[prev_end - 1] in " \t\r\n":
                    prev_end -= 1
                prev_nl = code_only.rfind("\n", after_hdr_pos, prev_end)
                prev_line = code_only[prev_nl + 1 if prev_nl != -1 else after_hdr_pos : prev_end].strip()
                if prev_line != "where" and not prev_line.endswith(" where"):
                    line_indent = q - line_start
        if line_indent > decl_indent:
            pos = cand + 1
            continue
        if _LEAN_CONTINUATION_RE.match(code_only, cand):
            pos = cand + 1
            continue
        if _is_lean_command_start(code_only, cand):
            return m.start()
        pos = cand + 1
    return n


def _extract_lean_decl_span(
    code_only: str, search_from: int, text: str | None = None
) -> tuple[int, int, str, str] | None:
    """Find the Lean declaration immediately following `search_from`.
    Returns `(start_off, end_off, decl_kind, decl_name)` or `None` if dangling."""
    n = len(code_only)
    i = search_from
    while i < n and code_only[i] in " \t\r\n":
        i += 1
    if i >= n:
        return None
    # If the next token is `end`, `namespace`, or `section`, the waiver is dangling!
    for bad_kw in ("end", "namespace", "section"):
        if code_only.startswith(bad_kw, i) and (
            i + len(bad_kw) >= n or not _is_lean_ident_char(code_only[i + len(bad_kw)])
        ):
            return None

    hit = _match_lean_decl_at(code_only, i, skip_in_prefixes=True)
    if hit is None:
        return None
    hdr_end, decl_kind, decl_name = hit
    end_off = _find_lean_decl_end(code_only, hdr_end, _lean_indent_of(code_only, i, text), text)
    return i, end_off, decl_kind, decl_name


_LEAN_DECL_KW_RE = re.compile(
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example)\b"
    r"(?:[ \t\r\n]+([^\s({\[\:]+))?"
)


def _match_lean_decl_at(
    code_only: str, i: int, *, skip_in_prefixes: bool = False
) -> tuple[int, str, str] | None:
    """If a declaration starts at `i` (after optional `@[...]` attributes, whose arguments may
    nest brackets as in `@[aesop safe [constructors]]`, declaration modifiers, and optionally
    `<command> in` prefixes), return `(header_end, decl_kind, decl_name)`."""
    kw = (
        _skip_lean_prefixes_attrs_and_modifiers(code_only, i)
        if skip_in_prefixes
        else _skip_lean_attrs_and_modifiers(code_only, i)
    )
    m = _LEAN_DECL_KW_RE.match(code_only, kw)
    if m is None:
        return None
    return m.end(), m.group(1), m.group(2) or m.group(1)


# ---------------------------------------------------------------------------
# 3-Axis Theorem Metadata & `TRIVIAL_PROOF` / Vacuity Analysis
# ---------------------------------------------------------------------------

_3AXIS_LINE_RE = re.compile(
    r"^\s*(Kind|Witness|Assumes|Subject)\s*:\s*(.+?)\s*$", re.IGNORECASE
)

_LEAN_THM_NAME_RE = re.compile(r"[ \t\r\n]+([^ \t\r\n({\[:⦃]+)")


def _iter_lean_theorem_headers(code_only: str) -> list[tuple[int, int, str]]:
    """Fast C-level `str.find` scanner returning `(kw_start, name_end, thm_name)`
    for every `theorem` or `lemma` declaration in `code_only`."""
    find = code_only.find
    name_match = _LEAN_THM_NAME_RE.match
    out: list[tuple[int, int, str]] = []
    for kw, kw_len in (("theorem", 7), ("lemma", 5)):
        idx = find(kw, 0)
        while idx != -1:
            nxt = find(kw, idx + kw_len)
            if idx > 0:
                prev_ch = code_only[idx - 1]
                if prev_ch.isalnum() or prev_ch in "_'!?":
                    idx = nxt
                    continue
            m = name_match(code_only, idx + kw_len)
            if m is not None:
                out.append((idx, m.end(), m.group(1)))
            idx = nxt
    out.sort()
    return out


_LEAN_MODIFIERS = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "scoped",
    "local",
)


def _skip_lean_attrs_and_modifiers(code_only: str, pos: int) -> int:
    """Advance `pos` past any whitespace, `@[...]` attributes, and declaration modifiers
    (`private`, `protected`, `noncomputable`, etc.) to the declaration keyword (`theorem`,
    `lemma`, `def`, ...)."""
    n = len(code_only)
    p = pos
    while p < n:
        while p < n and code_only[p] in " \t\r\n":
            p += 1
        if p >= n:
            break
        if code_only[p] == "@":
            q = p + 1
            while q < n and code_only[q] in " \t":
                q += 1
            if q < n and code_only[q] == "[":
                depth = 1
                q += 1
                while q < n and depth > 0:
                    c = code_only[q]
                    if c == "[":
                        depth += 1
                    elif c == "]":
                        depth -= 1
                    q += 1
                p = q
                continue
        matched_mod = False
        for mod in _LEAN_MODIFIERS:
            if code_only.startswith(mod, p):
                end_m = p + len(mod)
                if end_m < n and code_only[end_m] in " \t\r\n":
                    p = end_m + 1
                    matched_mod = True
                    break
        if not matched_mod:
            break
    return p


_LEAN_IN_PREFIX_CMD_RE = re.compile(
    r"(?:set_option|open|variable|universe|attribute|include|omit|export|"
    r"notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules)\b"
)
_LEAN_IN_TOKEN_RE = re.compile(r"[(){}\[\]\n]|:=|(?<![\w'!?.\u00bb])in(?![\w'!?.\u00bb])")


def _skip_lean_prefixes_attrs_and_modifiers(
    code_only: str, pos: int, limit: int | None = None
) -> int:
    """Advance `pos` past any whitespace, `@[...]` attributes, declaration modifiers, and
    `<command> in` prefixes (`set_option ... in`, `open ... in`, `variable ... in`,
    `attribute ... in`, ...) to the declaration keyword (`theorem`, `lemma`, `def`, ...)."""
    end_lim = len(code_only) if limit is None else min(len(code_only), limit)
    p = pos
    while p < end_lim:
        q = _skip_lean_attrs_and_modifiers(code_only, p)
        if q >= end_lim:
            return end_lim
        m = _LEAN_IN_PREFIX_CMD_RE.match(code_only, q)
        if m is None or m.end() > end_lim:
            return q
        depth = 0
        in_end = -1
        for tm in _LEAN_IN_TOKEN_RE.finditer(code_only, m.end(), end_lim):
            tok = tm.group()
            if tok in "({[":
                depth += 1
            elif tok in ")}]":
                if depth > 0:
                    depth -= 1
            elif tok == "in" and depth == 0:
                in_end = tm.end()
                break
            elif tok == ":=" and depth == 0:
                break
            elif tok == "\n" and depth == 0:
                cand = tm.end()
                while cand < end_lim and code_only[cand] in " \t\r\n":
                    cand += 1
                if cand < end_lim and _is_lean_command_start(code_only, cand):
                    break
        if in_end == -1:
            return q
        p = in_end
    return p


def _parse_3axis_metadata(comment_text: str) -> dict[str, str]:
    meta, _ = _parse_3axis_metadata_and_conflicts(comment_text)
    return meta


_PAREN_ONLY_RE = re.compile(r"[()]")
_WS_RUN_RE = re.compile(r"[ \t\r\n]+")
_STMT_END_SCAN_RE = re.compile(r"[(){}\[\]\n;]|:=|(?<![\w'!?.])let\b")
# `[adv B3]` The opening `'` leads the pattern and the "no identifier char / `'` / `.` / `!` / `?`
# before it" lookbehind follows it (`(?<![\w'.!?]')`, the same assertion one char later), so
# `re` scans for the literal `'` at C speed instead of running a lookbehind at every offset:
# identifier primes (`h'`, `x''`) used to cost a full regex pass over each statement.
_SCAN_CHAR_LIT_ALT = r"'(?<![\w'.!?]')(?:\\[^\n]{1,8}?|[^\\'\n])'"
_CHAR_LITERAL_RE = re.compile(_SCAN_CHAR_LIT_ALT)
# `[adv B3]` Depth-0 scanners are built from literal-first alternatives (`\(|\)|...` rather than
# `[(){}...]`, and the char literal in its `'`-first form), so `re` can skip straight to the next
# candidate character; the binder-keyword alternative needs a lookbehind at every offset and
# defeats that. Each scanner therefore has a `_NOKW` twin without the keyword alternative, used
# whenever `_has_binder_keyword` shows no standalone keyword occurs anywhere in the scanned text:
# the keyword alternative could not match there, so both regexes yield the same token stream.
_SCAN_BRACKET_ALTS = r"\(|\)|\{|\}|\[|\]|⟨|⟩|⦃|⦄"
_BINDER_KEYWORD_ALT = r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
# One literal-prefixed regex per keyword (`by(?<![\w'.!?]by)(?![\w'!?])` is the keyword alternative
# restricted to `by`, with the lookbehind moved behind the literal), tried only when the keyword
# occurs as a substring at all.
(
    _KW_BY_SEARCH,
    _KW_IF_SEARCH,
    _KW_FUN_SEARCH,
    _KW_LET_SEARCH,
    _KW_MATCH_SEARCH,
    _KW_HAVE_SEARCH,
    _KW_SHOW_SEARCH,
    _KW_FORALL_SEARCH,
    _KW_EXISTS_SEARCH,
) = (
    re.compile(kw + r"(?<![\w'.!?]" + kw + r")(?![\w'!?])").search
    for kw in ("by", "if", "fun", "let", "match", "have", "show", "forall", "exists")
)


def _has_binder_keyword(expr: str) -> bool:
    """`True` iff a standalone prefix-binder keyword (`forall`, `exists`, `fun`, `if`, `match`,
    `let`, `have`, `show`, `by`) occurs in `expr`: exactly `re.search(_BINDER_KEYWORD_ALT, expr)`,
    at C-level substring speed for the usual text that has none."""
    return (
        ("by" in expr and _KW_BY_SEARCH(expr) is not None)
        or ("if" in expr and _KW_IF_SEARCH(expr) is not None)
        or ("fun" in expr and _KW_FUN_SEARCH(expr) is not None)
        or ("let" in expr and _KW_LET_SEARCH(expr) is not None)
        or ("match" in expr and _KW_MATCH_SEARCH(expr) is not None)
        or ("have" in expr and _KW_HAVE_SEARCH(expr) is not None)
        or ("show" in expr and _KW_SHOW_SEARCH(expr) is not None)
        or ("forall" in expr and _KW_FORALL_SEARCH(expr) is not None)
        or ("exists" in expr and _KW_EXISTS_SEARCH(expr) is not None)
    )


def _has_prefix_binder_hint(expr: str) -> bool:
    """`True` iff `expr` contains `∀`, `∃`, `λ` or a standalone binder keyword anywhere."""
    return "∀" in expr or "∃" in expr or "λ" in expr or _has_binder_keyword(expr)


_ARROW_SCAN_NOKW_RE = re.compile(
    r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|↔|<->|<\|>|<\||\$|→|->|∀|∃|λ"
)
_ARROW_SCAN_RE = re.compile(_ARROW_SCAN_NOKW_RE.pattern + "|" + _BINDER_KEYWORD_ALT)
_PIPE_ARM_RE = re.compile(r"\n[ \t]*\|")
_WHERE_SCAN_RE = re.compile(
    r"«[^»]*»|"
    + _SCAN_CHAR_LIT_ALT
    + "|"
    + _SCAN_BRACKET_ALTS
    + r"|where(?<![\w'.!?]where)(?![\w'!?])"
)
_BRACE_SEP_SCAN_RE = re.compile(
    r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|//|(?<![|<])\|(?![|>])|,"
)
# `[adv A3]` Depth-0 `let` assign tracker for `_split_lean_theorem_header` and header binder
# default-value (`optParam` / `autoParam`) stripper. Literal-first lookbehinds keep `re`'s C-level
# character-bitmap fast skip intact.
_LET_ASSIGN_SCAN_RE = re.compile(
    r"«[^»]*»|"
    + _SCAN_CHAR_LIT_ALT
    + "|"
    + _SCAN_BRACKET_ALTS
    + r"|:=|;|←|<-|let(?<![\w'.!?]let)(?=[ \t\r\n])"
)
_BINDER_DEFAULT_SCAN_RE = re.compile(
    r"«[^»]*»|"
    + _SCAN_CHAR_LIT_ALT
    + "|"
    + _SCAN_BRACKET_ALTS
    + r"|:=|let(?<![\w'.!?]let)(?![\w'!?])|have(?<![\w'.!?]have)(?![\w'!?])"
)


def _is_open_depth0_let_before_assign(prefix_slice: str) -> bool:
    """`True` iff `prefix_slice` (everything between a theorem's `:` and a balanced `:=`) has an
    unclosed depth-0 `let` keyword whose own `:=` is the candidate `:=` at the end of
    `prefix_slice` (so `let x := 1 in x = x := rfl`, `(let x := 1 in x) = ... := rfl`,
    `do let x ← f; ... := rfl`, `droplet = droplet := rfl`, and `s.let = t := rfl` all return
    `False`, while `let x := 5`, `let\\tx := 5`, `let\\n  x := 5`, and `let f (x := 1) := 2`
    return `True` at the `let`'s own `:=`)."""
    depth = 0
    open_let = False
    for m in _LET_ASSIGN_SCAN_RE.finditer(prefix_slice):
        t = m.group(0)
        c0 = t[0]
        if c0 == "«" or c0 == "'":
            continue
        if c0 in "({[⟨⦃":
            depth += 1
        elif c0 in ")}]⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            open_let = t == "let"
    return open_let


def _strip_binder_default(b_type: str) -> str:
    """Strip a trailing depth-0 `:= default` (`optParam` / `autoParam`) from a binder type
    `(x : T := v)` -> `T`, leaving depth-0 `let`/`have` bindings and nested `{ a := 1 }` intact."""
    if ":=" not in b_type:
        return b_type
    depth = 0
    for m in _BINDER_DEFAULT_SCAN_RE.finditer(b_type):
        t = m.group(0)
        c0 = t[0]
        if c0 == "«" or c0 == "'":
            continue
        if c0 in "({[⟨⦃":
            depth += 1
        elif c0 in ")}]⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t == ":=":
                stripped = b_type[: m.start()].strip()
                return stripped if stripped else b_type
            return b_type
    return b_type


def _neutralize_char_literals(expr: str) -> str:
    """Rewrite every character literal (`'→'`, `'('`, `'\\''`) as `'u<hex>'`, which keeps distinct
    literals distinct but contains no operator or bracket, so the depth-0 scans below never read
    a connective out of one. The lookbehind keeps identifier primes (`x'`, `h''`) from opening a
    literal; string literals are already blanked by the lexer."""
    return _CHAR_LITERAL_RE.sub(
        lambda m: "'u" + "_".join(format(ord(c), "x") for c in m.group(0)[1:-1]) + "'", expr
    )


def _skip_char_literal_before(seg: str, start: int, target: int, end_lim: int) -> int:
    """If a Lean char literal opens in `seg[start:target]` (e.g. `'('` or `')'` enclosing `target`),
    return the offset immediately after that char literal; otherwise return `-1`."""
    q = seg.find("'", start, target)
    while q != -1:
        m = _CHAR_LITERAL_RE.match(seg, q, end_lim)
        if m is not None:
            return m.end()
        q = seg.find("'", q + 1, target)
    return -1


_BINDER_SCAN_RE = re.compile(r"[(){}\[\]]|:=|:")


def _scan_binder_group(seg: str, p: int, limit: int | None = None) -> tuple[int, int]:
    """For a bracket group opening at `seg[p]` (`(`, `{`, `[`, or `⦃`), return `(offset past its
    matching close, offset of its first depth-1 ':' that is not ':=', or -1)` using C-level
    `str.find`. Returns `(end_lim + 1, -1)` if the group is unclosed before `limit`."""
    end_lim = len(seg) if limit is None else limit
    ch = seg[p]
    close_ch = ")" if ch == "(" else ("}" if ch == "{" else ("]" if ch == "[" else "⦄"))
    find = seg.find
    cur = p + 1
    depth = 1
    while depth > 0 and cur < end_lim:
        c_close = find(close_ch, cur, end_lim)
        if c_close == -1:
            return end_lim + 1, -1
        c_open = find(ch, cur, c_close)
        target = c_open if c_open != -1 else c_close
        if find("'", cur, target) != -1:
            lit_end = _skip_char_literal_before(seg, cur, target, end_lim)
            if lit_end != -1:
                cur = lit_end
                continue
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            cur = c_close + 1
    if depth > 0:
        return end_lim + 1, -1
    # Find the binder's `:` before any nested bracket (and outside char literals)
    scan_end = cur - 1 if cur > p + 1 else cur
    col_scan = p + 1
    while col_scan < scan_end:
        col_idx = find(":", col_scan, scan_end)
        if col_idx == -1:
            break
        lit_end = _skip_char_literal_before(seg, col_scan, col_idx, end_lim)
        if lit_end != -1:
            col_scan = lit_end
            continue
        if col_idx + 1 >= cur or seg[col_idx + 1] != "=":
            prefix = seg[p + 1 : col_idx]
            if "'" in prefix:
                prefix = _neutralize_char_literals(prefix)
            if (
                prefix.count("(") == prefix.count(")")
                and prefix.count("{") == prefix.count("}")
                and prefix.count("[") == prefix.count("]")
                and prefix.count("⦃") == prefix.count("⦄")
            ):
                return cur, col_idx
        break
    return cur, -1


def _is_outer_paren_wrapped(t: str) -> bool:
    """Return `True` iff `t` starts with `(` and that opening `(` closes at `len(t) - 1`."""
    n = len(t)
    if n < 2 or t[0] != "(" or t[-1] != ")":
        return False
    has_quote = "'" in t
    find = t.find
    cur = 1
    depth = 1
    while depth > 0 and cur < n:
        c_close = find(")", cur, n)
        if c_close == -1:
            return False
        c_open = find("(", cur, c_close)
        if has_quote:
            target = c_open if c_open != -1 else c_close
            lit_end = _skip_char_literal_before(t, cur, target, n)
            if lit_end != -1:
                cur = lit_end
                continue
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            if depth == 0:
                return c_close == n - 1
            cur = c_close + 1
    return False


def _has_depth0_brace_sep(expr: str) -> bool:
    """`True` iff `expr` has `//`, `|`, or `,` at depth 0 outside brackets, `«...»`, and char
    literals: distinguishes subtypes `{x : T // p}` and set-builders `{x : T | p}` from implicit
    dependent-arrow binders `{x : T}`."""
    if "//" not in expr and "|" not in expr and "," not in expr:
        return False
    depth = 0
    for m in _BRACE_SEP_SCAN_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "({[⟨⦃":
            depth += 1
        elif t in ")}]⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return True
    return False


def _find_depth0_where(seg: str, start: int, end: int) -> int:
    """Return the offset of the first standalone depth-0 `where` keyword in `seg[start:end]`
    (outside `()[]{}⟨⟩⦃⦄`, `«...»`, and char literals), or `-1`."""
    if seg.find("where", start, end) == -1:
        return -1
    depth = 0
    for m in _WHERE_SCAN_RE.finditer(seg, start, end):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "({[⟨⦃":
            depth += 1
        elif t in ")}]⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return m.start()
    return -1


def _arrow_premise_binder(prem: str) -> tuple[str, str]:
    """The hypothesis a `→` premise contributes. A premise that is exactly one `(names : T)`,
    `{names : T}` (not a subtype `{x : T // p}` or set-builder `{x : T | p}`), `⦃names : T⦄`, or
    `[names : T]` binder group is a dependent-arrow binder (`(h : False) → P`, `{h : False} → P`,
    `⦃n : Nat⦄ → n < 0 → P`): it binds `names` like a header binder, so it is returned as
    `(names, T)`. Anything else is the anonymous premise `("", prem)`."""
    if len(prem) >= 5 and ":" in prem:
        c0 = prem[0]
        c_end = prem[-1]
        if (
            (c0 == "(" and c_end == ")")
            or (c0 == "{" and c_end == "}")
            or (c0 == "⦃" and c_end == "⦄")
            or (c0 == "[" and c_end == "]")
        ):
            q, col = _scan_binder_group(prem, 0, len(prem))
            if q == len(prem) and col != -1:
                names = prem[1:col].strip()
                b_type = prem[col + 1 : q - 1].strip()
                if (
                    b_type
                    and _BARE_BINDER_NAMES_RE.fullmatch(names) is not None
                    and (c0 != "{" or not _has_depth0_brace_sep(b_type))
                ):
                    return names, b_type
    return "", prem


# `[adv B3]` One C-level match for the overwhelmingly common header binder `(names : T)` /
# `{names : T}` / `[names : T]`: no bracket, `:` or `'` in `names`, the `:` is not `:=`, and `T`
# holds no bracket of the group's own kind and no `'` -- so the first same-kind close bracket
# closes the group, the first `:` is the binder colon, and the delimiter-parity check on `names`
# holds trivially. Trailing ` \t\r\n` is consumed too. Anything else (nested or mixed brackets,
# char literals, `:=` defaults, untyped groups) does not match and takes the general path.
_SIMPLE_BINDER_MATCH = {
    "(": re.compile(r"\(([^(){}\[\]⦃⦄:']*):(?!=)([^()']*)\)[ \t\r\n]*").match,
    "{": re.compile(r"\{([^(){}\[\]⦃⦄:']*):(?!=)([^{}']*)\}[ \t\r\n]*").match,
    "[": re.compile(r"\[([^(){}\[\]⦃⦄:']*):(?!=)([^\[\]']*)\][ \t\r\n]*").match,
}


def _split_lean_theorem_header(
    code_segment: str, after_name_pos: int, limit_end: int | None = None
) -> tuple[list[tuple[str, str]], str, list[str]] | None:
    """Given `code_segment`, parse starting at `after_name_pos` (up to `limit_end`):
    - explicit/implicit binders `(x : T)`, `{x : T}`, `[inst : C]` before `:`,
    - top-level `∀ ...,` and `→` (`->`) premises inside the theorem statement,
    - the final conclusion before top-level `:=`, `where`, or `|`, and
    - `extra_binders`, everything the first two cannot represent: untyped `(x)` / `{x}` groups
      (`untyped:x`), bare names (`bare`), unnamed `[C]` instances (`[C]`), and `stmt-cut` when
      the statement was cut at a line-leading `|`.
    Returns `(hypotheses_as_(binder_names, type_str), conclusion_str, extra_binders)`, a pure
    function of `code_segment[after_name_pos:limit_end]` (the `_THM_AUDIT_CACHE` key).
    """
    n = len(code_segment) if limit_end is None else min(len(code_segment), limit_end)
    i = after_name_pos
    if i < n and code_segment[i] == "." and code_segment.startswith(".{", i):
        close_u = code_segment.find("}", i + 2, n)
        if close_u != -1:
            i = close_u + 1

    binders: list[tuple[str, str]] = []
    extra_binders: list[str] = []
    colon_pos = -1
    p = i
    find = code_segment.find
    m_paren = _SIMPLE_BINDER_MATCH["("]
    m_brace = _SIMPLE_BINDER_MATCH["{"]
    m_brack = _SIMPLE_BINDER_MATCH["["]
    binders_append = binders.append
    while p < n and code_segment[p] in " \t\r\n":
        p += 1
    while p < n:
        ch = code_segment[p]
        if ch == "(":
            m_b = m_paren(code_segment, p, n)
            if m_b is not None:
                b_names, b_type = m_b.group(1, 2)
                b_type = b_type.strip()
                if ":=" in b_type:
                    b_type = _strip_binder_default(b_type)
                binders_append((b_names.strip(), b_type))
                p = m_b.end()
                continue
        if ch in "({[":
            if ch != "(":
                m_b = (m_brace if ch == "{" else m_brack)(code_segment, p, n)
                if m_b is not None:
                    # `{names : T}` / `[names : T]` with no bracket or `'` before `:` and no
                    # same-kind bracket or `'` in `T`.
                    b_names, b_type = m_b.group(1, 2)
                    b_type = b_type.strip()
                    if ":=" in b_type:
                        b_type = _strip_binder_default(b_type)
                    binders_append((b_names.strip(), b_type))
                    p = m_b.end()
                    continue
            close_ch = ")" if ch == "(" else ("}" if ch == "{" else "]")
            fast_close = find(close_ch, p + 1, n)
            if (
                fast_close != -1
                and find(ch, p + 1, fast_close) == -1
                and find("'", p + 1, fast_close) == -1
            ):
                col_idx = find(":", p + 1, fast_close)
                if col_idx != -1 and (
                    col_idx + 1 >= fast_close or code_segment[col_idx + 1] != "="
                ):
                    prefix_b = code_segment[p + 1 : col_idx]
                    if (
                        prefix_b.count("(") == prefix_b.count(")")
                        and prefix_b.count("{") == prefix_b.count("}")
                        and prefix_b.count("[") == prefix_b.count("]")
                        and prefix_b.count("⦃") == prefix_b.count("⦄")
                    ):
                        b_t = code_segment[col_idx + 1 : fast_close].strip()
                        if ":=" in b_t:
                            b_t = _strip_binder_default(b_t)
                        binders_append((prefix_b.strip(), b_t))
                    else:
                        inner = code_segment[p + 1 : fast_close].strip()
                        if inner:
                            extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
                else:
                    inner = code_segment[p + 1 : fast_close].strip()
                    if inner:
                        extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
                p = fast_close + 1
                continue
            q, colon_in_binder = _scan_binder_group(code_segment, p, n)
            if q > n:
                return None
            if colon_in_binder != -1:
                b_t = code_segment[colon_in_binder + 1 : q - 1].strip()
                if ":=" in b_t:
                    b_t = _strip_binder_default(b_t)
                binders_append((code_segment[p + 1 : colon_in_binder].strip(), b_t))
            else:
                inner = code_segment[p + 1 : q - 1].strip() if q > p + 1 else ""
                if inner:
                    extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
            p = q
            continue
        if ch == ":":
            if p + 1 < n and code_segment[p + 1] == "=":
                return None
            colon_pos = p
            break
        if ch in " \t\r\n":
            p += 1
            while p < n and code_segment[p] in " \t\r\n":
                p += 1
            continue
        if ch == "⦃":
            # Strict-implicit binder `⦃x : T⦄`, using balanced scanning so nested `⦃...⦄`
            # (e.g. `⦃h : ∀ ⦃y : Nat⦄, False⦄`) and `'⦄'` char literals stay intact.
            q, col_s = _scan_binder_group(code_segment, p, n)
            if q > n:
                return None
            if col_s != -1:
                b_n = code_segment[p + 1 : col_s].strip()
                b_t = _strip_binder_default(code_segment[col_s + 1 : q - 1].strip())
                if b_n and b_t:
                    binders_append((b_n, b_t))
                else:
                    inner = code_segment[p + 1 : q - 1].strip()
                    if inner:
                        extra_binders.append(f"untyped:{inner}")
            else:
                inner = code_segment[p + 1 : q - 1].strip() if q > p + 1 else ""
                if inner:
                    extra_binders.append(f"untyped:{inner}")
            p = q
            continue
        if (
            ch == "w"
            and code_segment.startswith("where", p)
            and (p + 5 >= n or not _is_lean_ident_char(code_segment[p + 5]))
        ):
            return None
        extra_binders.append("bare")
        p += 1

    if colon_pos == -1:
        return None

    # Fast path to find top-level `:=` separating theorem statement from proof body
    stmt_start = colon_pos + 1
    stmt_end = -1
    prefix_slice = ""
    search_eq = stmt_start
    # `[adv A3]` On pattern-matching theorems (`theorem t : P\n  | 0 => ...`) whose proof body
    # later contains `have h := ...`, checking whether `=>` and a line-leading `|` occur before the
    # very first `:=` avoids slicing, char-neutralizing, and bracket-counting the proof body only
    # to discard it at `\n  |` below.
    first_eq = find(":=", stmt_start, n)
    early_pipe_m = (
        _PIPE_ARM_RE.search(code_segment, stmt_start, first_eq)
        if first_eq != -1 and first_eq - stmt_start > 256 and find("=>", stmt_start, first_eq) != -1
        else None
    )
    if early_pipe_m is not None:
        pipe_start = early_pipe_m.start()
        w_pos = (
            _find_depth0_where(code_segment, stmt_start, pipe_start)
            if find("where", stmt_start, pipe_start) != -1
            else -1
        )
        if w_pos != -1:
            stmt = code_segment[stmt_start:w_pos].strip()
        else:
            extra_binders.append("stmt-cut")
            stmt = code_segment[stmt_start:pipe_start].strip()
    else:
        while search_eq < n:
            eq_pos = first_eq if search_eq == stmt_start else find(":=", search_eq, n)
            if eq_pos == -1:
                break
            prefix_slice = code_segment[stmt_start:eq_pos]
            bal_slice = _neutralize_char_literals(prefix_slice) if "'" in prefix_slice else prefix_slice
            if (
                bal_slice.count("(") == bal_slice.count(")")
                and bal_slice.count("{") == bal_slice.count("}")
                and bal_slice.count("[") == bal_slice.count("]")
                and (
                    bal_slice.isascii()  # O(1): no `⟨⟩⦃⦄«»` to count in pure-ASCII text
                    or (
                        bal_slice.count("⟨") == bal_slice.count("⟩")
                        and bal_slice.count("⦃") == bal_slice.count("⦄")
                        and bal_slice.count("«") == bal_slice.count("»")
                    )
                )
            ):
                if "let" in prefix_slice and _is_open_depth0_let_before_assign(prefix_slice):
                    # `[adv A3]` Only an unclosed depth-0 `let` (`let x := v`, `let\tx := v`,
                    # `let\n  x := v`, `let f (x := 1) := 2`) claims this `:=`; closed `let ... in ...`
                    # bindings, parenthesised `(let x := 1 in x)`, `do` `let x ← f`, and suffixes
                    # (`droplet`, `s.let`) leave the proof's `:=` intact.
                    search_eq = eq_pos + 2
                    continue
                stmt_end = eq_pos
                break
            search_eq = eq_pos + 2

        # Check if a pattern-matching arm `\n  | ... =>` or `where` ended the statement before `stmt_end`
        if stmt_end == -1 or "=>" in prefix_slice:
            # Clamp to `n`: the statement can never run into the next theorem, and the parse must stay a
            # pure function of `code_segment[after_name_pos:n]` (the `_THM_AUDIT_CACHE` key).
            search_bound = stmt_end if stmt_end != -1 else n
            pipe_m = _PIPE_ARM_RE.search(code_segment, stmt_start, search_bound)
            if pipe_m is not None:
                pipe_start = pipe_m.start()
                # `[adv A3]` Check depth-0 `where` before `\n  |`: in `theorem t : A ∧ B where\n  left\n  | 0 => ...`,
                # the pattern-matching arm belongs to a `where` field, so the statement ended at `where`
                # (cutting at `|` instead left `A ∧ B where\n  left` and added a bogus `stmt-cut`).
                w_pos = (
                    _find_depth0_where(code_segment, stmt_start, pipe_start)
                    if find("where", stmt_start, pipe_start) != -1
                    else -1
                )
                if w_pos != -1:
                    decl_end_bound = w_pos
                else:
                    decl_end_bound = pipe_start
                    # A line-leading `|` normally opens an equation arm, but `||` / `|>` / `|x|` open one
                    # just as well for this scan: the statement may continue past the cut.
                    extra_binders.append("stmt-cut")
            else:
                decl_end_bound = (
                    stmt_end if stmt_end != -1 else min(_find_lean_decl_end(code_segment, stmt_start), n)
                )
                if find("where", stmt_start, decl_end_bound) != -1:
                    w_pos = _find_depth0_where(code_segment, stmt_start, decl_end_bound)
                    if w_pos != -1:
                        decl_end_bound = w_pos
            stmt = code_segment[stmt_start:decl_end_bound].strip()
        else:
            if "where" in prefix_slice:
                # `[adv B3]` `theorem t : A ∧ B where left := ..; right := ..`: the first `:=` belongs to
                # a structure-instance field, and the statement ends at the depth-0 `where` before it
                # (it used to read `A ∧ B where left`, never a trivial or tautological conclusion).
                w_pos = _find_depth0_where(code_segment, stmt_start, stmt_end)
                if w_pos != -1:
                    prefix_slice = code_segment[stmt_start:w_pos]
            stmt = prefix_slice.strip()
    if not stmt:
        return None

    hyps = binders
    cur_stmt = stmt
    if cur_stmt[0] not in "(∀f" and "→" not in cur_stmt and "->" not in cur_stmt:
        return hyps, cur_stmt, extra_binders
    while cur_stmt:
        while cur_stmt[0] == "(" and cur_stmt[-1] == ")" and _is_outer_paren_wrapped(cur_stmt):
            cur_stmt = cur_stmt[1:-1].strip()
            if not cur_stmt:
                break

        if not cur_stmt:
            break

        c0 = cur_stmt[0]
        if c0 == "∀" or (
            c0 == "f"
            and cur_stmt.startswith("forall")
            and len(cur_stmt) > 6
            and not _is_lean_ident_char(cur_stmt[6])
        ):
            q_len = 1 if c0 == "∀" else 6
            idx_q = q_len
            comma_idx = -1
            n_cur = len(cur_stmt)
            find_cur = cur_stmt.find
            saw_q_group = False
            saw_q_bare_before_colon = False
            saw_q_bare_colon = False
            while idx_q < n_cur:
                c2 = cur_stmt[idx_q]
                if c2 in " \t\r\n":
                    idx_q += 1
                    continue
                if c2 == "⦃":
                    r_s, col_s = _scan_binder_group(cur_stmt, idx_q, n_cur)
                    if r_s <= n_cur:
                        if not saw_q_bare_colon:
                            saw_q_group = True
                            if col_s != -1:
                                b_n = cur_stmt[idx_q + 1 : col_s].strip()
                                b_t = cur_stmt[col_s + 1 : r_s - 1].strip()
                                if ":=" in b_t:
                                    b_t = _strip_binder_default(b_t)
                                if b_n and b_t:
                                    hyps.append((b_n, b_t))
                                else:
                                    inner = cur_stmt[idx_q + 1 : r_s - 1].strip()
                                    if inner:
                                        extra_binders.append(f"untyped:{inner}")
                            else:
                                inner = cur_stmt[idx_q + 1 : r_s - 1].strip() if r_s > idx_q + 1 else ""
                                if inner:
                                    extra_binders.append(f"untyped:{inner}")
                        idx_q = r_s
                        continue
                if c2 in "({[":
                    if not saw_q_bare_colon:
                        saw_q_group = True
                    close_ch = ")" if c2 == "(" else ("}" if c2 == "{" else "]")
                    fast_close = find_cur(close_ch, idx_q + 1, n_cur)
                    if (
                        fast_close != -1
                        and find_cur(c2, idx_q + 1, fast_close) == -1
                        and find_cur("'", idx_q + 1, fast_close) == -1
                    ):
                        if not saw_q_bare_colon:
                            col_in = find_cur(":", idx_q + 1, fast_close)
                            if col_in != -1 and (
                                col_in + 1 >= fast_close or cur_stmt[col_in + 1] != "="
                            ):
                                prefix_qb = cur_stmt[idx_q + 1 : col_in]
                                if (
                                    prefix_qb.count("(") == prefix_qb.count(")")
                                    and prefix_qb.count("{") == prefix_qb.count("}")
                                    and prefix_qb.count("[") == prefix_qb.count("]")
                                    and prefix_qb.count("⦃") == prefix_qb.count("⦄")
                                ):
                                    b_t_q = cur_stmt[col_in + 1 : fast_close].strip()
                                    if ":=" in b_t_q:
                                        b_t_q = _strip_binder_default(b_t_q)
                                    hyps.append((prefix_qb.strip(), b_t_q))
                                else:
                                    inner = cur_stmt[idx_q + 1 : fast_close].strip()
                                    if inner:
                                        extra_binders.append(
                                            f"[{inner}]" if c2 == "[" else f"untyped:{inner}"
                                        )
                            else:
                                inner = cur_stmt[idx_q + 1 : fast_close].strip()
                                if inner:
                                    extra_binders.append(
                                        f"[{inner}]" if c2 == "[" else f"untyped:{inner}"
                                    )
                        idx_q = fast_close + 1
                        continue
                    r, col_in = _scan_binder_group(cur_stmt, idx_q, n_cur)
                    if r > n_cur:
                        break
                    if not saw_q_bare_colon:
                        if col_in != -1:
                            b_t_q = cur_stmt[col_in + 1 : r - 1].strip()
                            if ":=" in b_t_q:
                                b_t_q = _strip_binder_default(b_t_q)
                            hyps.append((cur_stmt[idx_q + 1 : col_in].strip(), b_t_q))
                        else:
                            inner = cur_stmt[idx_q + 1 : r - 1].strip() if r > idx_q + 1 else ""
                            if inner:
                                extra_binders.append(
                                    f"[{inner}]" if c2 == "[" else f"untyped:{inner}"
                                )
                    idx_q = r
                    continue
                if c2 == ",":
                    comma_idx = idx_q
                    break
                if (
                    c2 == ":"
                    and not saw_q_group
                    and (idx_q + 1 >= n_cur or cur_stmt[idx_q + 1] != "=")
                ):
                    saw_q_bare_colon = True
                elif not saw_q_bare_colon:
                    saw_q_bare_before_colon = True
                idx_q += 1
            if comma_idx != -1:
                raw_q_binders = cur_stmt[q_len:comma_idx].strip()
                if saw_q_bare_colon and not saw_q_group:
                    b_n, _, b_t = raw_q_binders.partition(":")
                    hyps.append((b_n.strip(), b_t.strip()))
                elif saw_q_bare_before_colon:
                    extra_binders.append("bare")
                cur_stmt = cur_stmt[comma_idx + 1 :].strip()
                continue

        if "→" not in cur_stmt and "->" not in cur_stmt:
            break

        if (
            "->" not in cur_stmt
            and "↔" not in cur_stmt
            and "<->" not in cur_stmt
            and "<|" not in cur_stmt
            and "$" not in cur_stmt
            and "'" not in cur_stmt
            and "«" not in cur_stmt
            and "⟨" not in cur_stmt
            and "⦃" not in cur_stmt
            and not _has_prefix_binder_hint(cur_stmt)
        ):
            arrow_parts = cur_stmt.split("→")
            if all(
                p_seg.count("(") == p_seg.count(")")
                and p_seg.count("{") == p_seg.count("}")
                and p_seg.count("[") == p_seg.count("]")
                for p_seg in arrow_parts[:-1]
            ):
                for p_seg in arrow_parts[:-1]:
                    hyps.append(_arrow_premise_binder(p_seg.strip()))
                cur_stmt = arrow_parts[-1].strip()
                if cur_stmt.startswith("("):
                    continue
                break

        # Single-pass scan for all top-level `→` / `->` premises up to any top-level binder.
        # If a looser infix connective (`↔`, `<->`, `<|>`, `<|`, `$`) appears at depth 0 before
        # any depth-0 prefix binder, it governs the whole statement, so `→` is not top-level.
        depth_a = 0
        arrow_spans: list[tuple[int, int]] = []
        looser_hit = False
        re_loop = False
        arrow_scan_re = _ARROW_SCAN_RE if _has_binder_keyword(cur_stmt) else _ARROW_SCAN_NOKW_RE
        for m_a in arrow_scan_re.finditer(cur_stmt):
            t_a = m_a.group(0)
            if t_a[0] == "«" or t_a[0] == "'":
                continue
            if t_a in "({[⟨⦃":
                depth_a += 1
            elif t_a in ")}]⟩⦄":
                if depth_a > 0:
                    depth_a -= 1
            elif depth_a == 0:
                if t_a in ("↔", "<->", "<|>", "<|", "$"):
                    looser_hit = True
                    break
                if t_a in ("→", "->"):
                    arrow_spans.append((m_a.start(), m_a.end()))
                    continue
                if t_a in ("∀", "forall") and arrow_spans:
                    re_loop = True
                break

        if not looser_hit and arrow_spans:
            seg_start = 0
            n_cs = len(cur_stmt)
            for a_start, a_end in arrow_spans:
                hyps.append(_arrow_premise_binder(cur_stmt[seg_start:a_start].strip()))
                seg_start = a_end
                while seg_start < n_cs and cur_stmt[seg_start] in " \t\r\n":
                    seg_start += 1
                if seg_start < n_cs and (
                    cur_stmt[seg_start] in "(∀"
                    or (
                        cur_stmt[seg_start] == "f"
                        and cur_stmt.startswith("forall", seg_start)
                        and (seg_start + 6 >= n_cs or not _is_lean_ident_char(cur_stmt[seg_start + 6]))
                    )
                ):
                    re_loop = True
                    break
            cur_stmt = cur_stmt[seg_start:].strip()
            if re_loop:
                continue
        break

    return hyps, cur_stmt, extra_binders


_NORM_CACHE: dict[str, str] = {}


def _norm_expr(s: str) -> str:
    """Normalize whitespace and strip redundant outer parentheses of a Lean expression.

    An expression already in normal form (one line, single-spaced, no surrounding whitespace, not
    starting with `(`) is returned as is. Every other result is memoized in `_NORM_CACHE`, which
    `audit_lean_text` clears at the start of every scan (deduplication within one file only; no
    state survives across scans)."""
    hit = _NORM_CACHE.get(s)
    if hit is not None:
        return hit
    if not s:
        return ""
    # `[adv A3]` These substring tests are C-level scans, cheaper than hashing `s` into the memo.
    if (
        s[0] not in " \t\r\n("
        and s[-1] not in " \t\r\n"
        and "  " not in s
        and "\n" not in s
        and "\t" not in s
        and "\r" not in s
    ):
        return s
    t = _norm_expr_uncached(s)
    _NORM_CACHE[s] = t
    return t


def _norm_expr_uncached(s: str) -> str:
    """The normal form itself. `[adv B4]` This is its only definition: `_norm_expr` adds the
    already-normal fast path and the memo on top, and must agree with it on every input."""
    if "  " not in s and "\n" not in s and "\t" not in s and "\r" not in s:
        t = s.strip()
    else:
        t = " ".join(s.split())
    while len(t) >= 2 and t[0] == "(" and t[-1] == ")" and _is_outer_paren_wrapped(t):
        t = t[1:-1].strip()
    return t


_NUM_LIT_RE = re.compile(r"^\d+$")
_DIGIT_SEARCH = re.compile(r"\d").search
_REL_OP_SEARCH = re.compile(r"[=≠<≤>≥∧∨↔¬]").search
_S0_PIN_TRIGGER_SEARCH = re.compile(
    r"paddingFree|adtPad|hasPinnedCoupledWaiver|pad0|totalPad|rustOrderCanonical|evalConst|compileTimeError"
).search
_RUST_ORDER_CANON_RE = re.compile(r"rustOrderCanonical\s*:?=\s*true")
_IDENT_EXTRACT_RE = re.compile(r"[^\W\d][\w'!?]*")
_DATA_TYPE_WORDS = frozenset(
    (
        "Nat",
        "Int",
        "Bool",
        "String",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Unit",
        "Type",
        "Prop",
        "Sort",
        "List",
        "Array",
        "Option",
        "Vector",
    )
)


_CONJ_TRIV_SPLIT_RE = re.compile(r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|∧")
_DISJ_TRIV_SPLIT_RE = re.compile(r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|∨")
_TOP_SPLIT_RE_CACHE: dict[str, re.Pattern[str]] = {
    sep: re.compile(r"«[^»]*»|" + _SCAN_BRACKET_ALTS + "|" + re.escape(sep))
    for sep in ("≠", "≤", "≥", "×", "::")
}


def _split_top_level(expr: str, sep: str) -> list[str]:
    """Split `expr` on `sep` occurrences outside `()`, `[]`, `{}`, `⟨⟩`, `⦃⦄`, and `«...»` (C-level `finditer`)."""
    if sep not in expr:
        return [_norm_expr(expr)]
    pat = _TOP_SPLIT_RE_CACHE.get(sep)
    if pat is None:
        pat = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|" + re.escape(sep))
        _TOP_SPLIT_RE_CACHE[sep] = pat
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


_TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE = re.compile(
    r"«[^»]*»|" + _SCAN_BRACKET_ALTS + r"|↔|<->|<\|>|<\||\$|→|->|∨|\\/|∧|/\\|∀|∃|λ"
)
_TOP_LEVEL_LOOSER_THAN_NOT_RE = re.compile(
    _TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE.pattern + "|" + _BINDER_KEYWORD_ALT
)
_CONJ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|∧|/\\")
_CONJ_TOP_BOUND_NOKW_RE = re.compile(
    r"«[^»]*»|" + _SCAN_BRACKET_ALTS + r"|↔|<->|→|->|<\|>|<\||\|>|\$|∨|\\/|∀|∃|λ"
)
_CONJ_TOP_BOUND_RE = re.compile(_CONJ_TOP_BOUND_NOKW_RE.pattern + "|" + _BINDER_KEYWORD_ALT)


def _arrow_false_antecedent(expr: str) -> str | None:
    """If normalized `expr` is exactly `X → False` / `X -> False` (including `X → (False)` and
    dependent-arrow `(h : X) → False`) -- one top-level implication whose whole consequent is
    `False`, the term `¬ X` unfolds to -- return normalized `X`, else `None`. `A → B → False`
    (`A → ¬ B`), `A ↔ B → False` (`↔` governs), `f <| P → False` (`<|` governs) and
    `∀ x, P x → False` (the arrow belongs to the binder body) are not negations of one proposition."""
    if "False" not in expr or ("→" not in expr and "->" not in expr):
        return None
    depth = 0
    scan_re = (
        _TOP_LEVEL_LOOSER_THAN_NOT_RE
        if _has_binder_keyword(expr)
        else _TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE
    )
    for m in scan_re.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t == "→" or t == "->":
                if _norm_expr(expr[m.end() :]) != "False":
                    return None
                raw_ant = expr[: m.start()].strip()
                b_names, b_type = _arrow_premise_binder(raw_ant)
                if b_names:
                    return _norm_expr(b_type) or None
                return _norm_expr(raw_ant) or None
            if t not in ("∧", "/\\", "∨", "\\/"):
                return None
    return None


def _negated_operand(part: str) -> str | None:
    """The proposition `X` that normalized `part` denies -- `X → False`, or `¬ X` when `¬`
    governs the whole expression (`¬ P → α` is the implication `(¬ P) → α` and denies nothing)
    -- else `None`."""
    if "False" in part and ("→" in part or "->" in part):
        x = _arrow_false_antecedent(part)
        if x is not None:
            return x
    if part.startswith("¬") and not _has_top_level_looser_than_not(part):
        return _norm_expr(part[1:]) or None
    return None


def _has_top_level_looser_than_not(expr: str) -> bool:
    """`True` iff `expr` contains a top-level (depth-0 outside `()[]{}⟨⟩⦃⦄` and `«...»`)
    connective with lower Lean 4 precedence than prefix `¬` (prec 40) — namely `∧`/`/\\` (35),
    `∨`/`\\/` (30), `→`/`->` (25), `↔`/`<->` (20), `<|`/`$` (10), or `<|>` (2) — before any
    depth-0 prefix binder.

    In Lean 4, `¬ P → α` parses as `(¬ P) → α` (NOT `¬ (P → α)`), and `¬ P ∨ Q` parses as
    `(¬ P) ∨ Q` (NOT `¬ (P ∨ Q)`), whereas `¬ (P → α)` has `→` at depth 1 and returns `False`.
    """
    if (
        "→" not in expr
        and "->" not in expr
        and "↔" not in expr
        and "<->" not in expr
        and "∨" not in expr
        and "\\/" not in expr
        and "∧" not in expr
        and "/\\" not in expr
        and "<|" not in expr
        and "$" not in expr
    ):
        return False
    depth = 0
    scan_re = (
        _TOP_LEVEL_LOOSER_THAN_NOT_RE
        if _has_binder_keyword(expr)
        else _TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE
    )
    for m in scan_re.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return t in ("↔", "<->", "<|>", "<|", "$", "→", "->", "∨", "\\/", "∧", "/\\")
    return False


def _has_top_level_prefix_binder(expr: str) -> bool:
    """`True` iff `expr` has a depth-0 (outside `()[]{}⟨⟩⦃⦄` and `«...»`) prefix binder or keyword
    (`∀`, `∃`, `λ`, `forall`, `exists`, `fun`, `if`, `match`, `let`, `have`, `show`, `by`), whose
    body runs to the end of `expr`. Such an expression is not one relation between two terms:
    in `∀ x ∈ s, x :: xs = []` or `if c then True else n < 0` the `=` / `<` belongs to the body,
    which holds vacuously over an empty domain or in the other branch."""
    if not _has_prefix_binder_hint(expr):
        return False
    depth = 0
    scan_re = (
        _TOP_LEVEL_LOOSER_THAN_NOT_RE
        if _has_binder_keyword(expr)
        else _TOP_LEVEL_LOOSER_THAN_NOT_NOKW_RE
    )
    for m in scan_re.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0 and t not in (
            "↔", "<->", "<|>", "<|", "$", "→", "->", "∨", "\\/", "∧", "/\\"
        ):
            return True
    return False


def _split_top_level_conjuncts(expr: str) -> list[str]:
    """Split `expr` on top-level `∧` / `/\\` conjuncts outside `()[]{}⟨⟩⦃⦄` and `«...»`,
    only when no looser connective (`↔`, `<->`, `→`, `->`, `∨`, `\\/`, `<|>`, `<|`, `|>`, `$`)
    governs `expr` at depth 0, recursively flattening parenthesized conjunctions."""
    if "∧" not in expr and "/\\" not in expr:
        return [expr]
    bound = len(expr)
    depth = 0
    for m in (
        _CONJ_TOP_BOUND_RE if _has_binder_keyword(expr) else _CONJ_TOP_BOUND_NOKW_RE
    ).finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("↔", "<->", "→", "->", "<|>", "<|", "|>", "$", "∨", "\\/"):
                return [expr]
            bound = m.start()
            break
    if bound <= 0:
        return [expr]
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _CONJ_SPLIT_RE.finditer(expr, 0, bound):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    if not parts:
        return [expr]
    parts.append(expr[start:])
    out: list[str] = []
    for raw_p in parts:
        np = _norm_expr(raw_p)
        if not np:
            continue
        if ("∧" in np or "/\\" in np) and len(np) < len(expr):
            out.extend(_split_top_level_conjuncts(np))
        else:
            out.append(np)
    return out if out else [expr]


_QUANT_COMMA_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|,")
# Strictly linear (no overlapping `\s*` inside `+` — avoids $O(2^n)$ backtracking on long
# non-matching binder prefixes such as `∀ very_long_variable_name < n, ...`).
_BARE_BINDER_NAMES_RE = re.compile(r"[^\W\d][\w'!?]*(?:\s+[^\W\d][\w'!?]*)*")
_NO_BOUND_NAMES: frozenset[str] = frozenset()


def _split_quantifier_prefix(expr: str) -> tuple[str, str, str] | None:
    """For normalized `∃ binders, body` / `∀ binders, body` (or ASCII `exists` / `forall`), return
    `(quantifier, binders, body)` split at the first depth-0 `,`; `None` for anything else."""
    c0 = expr[0]
    if c0 == "∃" or c0 == "∀":
        q_len = 1
    elif (
        (c0 == "e" and expr.startswith("exists"))
        or (c0 == "f" and expr.startswith("forall"))
    ) and len(expr) > 6 and not _is_lean_ident_char(expr[6]):
        q_len = 6
        c0 = "∃" if c0 == "e" else "∀"
    else:
        return None
    depth = 0
    for m in _QUANT_COMMA_RE.finditer(expr, q_len):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return c0, expr[q_len : m.start()], expr[m.end() :]
    return None


def _parse_quantifier_binder_groups(binders: str) -> list[tuple[list[str], str | None]] | None:
    """Parse a quantifier's binder section into `[(names, type_or_None), ...]` in telescope order,
    returning `None` if it contains a binder predicate (`i < n`, `x ∈ s`), instance bracket
    (`[inst : C]`), pattern (`⟨a, b⟩`), or unrecognised syntax. Handles unparenthesised types with
    parenthesised arguments (`x : List (Fin 0)`, `b : BitVec (n + 1)`), as well as `(x : T)`,
    `{x : T}`, and strict-implicit `⦃x : T⦄` groups."""
    b = binders.strip()
    if not b:
        return None
    fullmatch = _BARE_BINDER_NAMES_RE.fullmatch
    if fullmatch(b) is not None:
        return [(b.split(), None)]
    if b[0] not in "({[⦃" and ":" in b:
        col = b.find(":")
        if (
            col != -1
            and (col + 1 >= len(b) or b[col + 1] != "=")
            and "(" not in b[:col]
            and "{" not in b[:col]
            and "[" not in b[:col]
            and "⦃" not in b[:col]
        ):
            names_raw = b[:col].strip()
            b_type = b[col + 1 :].strip()
            if fullmatch(names_raw) is not None and b_type:
                return [(names_raw.split(), b_type)]
    groups: list[tuple[list[str], str | None]] = []
    p = 0
    n = len(b)
    while p < n:
        ch = b[p]
        if ch in " \t\r\n":
            p += 1
            continue
        if ch in "({⦃":
            close_ch = ")" if ch == "(" else ("}" if ch == "{" else "⦄")
            q, col = _scan_binder_group(b, p, n)
            if q > n or b[q - 1] != close_ch:
                return None
            if col == -1:
                inner = b[p + 1 : q - 1].strip()
                if fullmatch(inner) is None:
                    return None
                groups.append((inner.split(), None))
            else:
                names_raw = b[p + 1 : col].strip()
                b_type = b[col + 1 : q - 1].strip()
                if fullmatch(names_raw) is None or not b_type:
                    return None
                groups.append((names_raw.split(), b_type))
            p = q
            continue
        m = _BARE_BINDER_NAMES_RE.match(b, p)
        if m is None:
            return None
        groups.append((m.group(0).split(), None))
        p = m.end()
    return groups if groups else None


def _plain_quantifier_binders(
    binders: str,
    type_vars: frozenset[str] = frozenset(),
    *,
    shadowed: frozenset[str] = frozenset(),
    allow_untyped: bool = True,
    allow_new_type_vars: bool = False,
    groups: list[tuple[list[str], str | None]] | None | bool = False,
) -> bool:
    """`True` iff a quantifier's binder section only introduces variables that range over data in
    telescope order: optionally bare/untyped names (`x y`, when `allow_untyped=True`), `names : T`,
    or `(names : T)` / `{names : T}` groups with `T` accepted by `_is_non_prop_binder_type`
    (respecting shadowing of both `type_vars` and reserved base/container names). A binder
    predicate (`x > 0`, `x ∈ s`), an instance bracket, a proof binder (`h : P`) or an
    unrecognised domain (`Fin n`) restricts the quantifier and is not plain. `groups` may carry
    the caller's `_parse_quantifier_binder_groups(binders)` result (`False`: not parsed yet)."""
    if groups is False:
        groups = _parse_quantifier_binder_groups(binders)
    if groups is None or groups is True:
        return False
    tv = set(type_vars)
    sh = set(shadowed)
    for names, b_type in groups:
        if b_type is None:
            if not allow_untyped:
                return False
            tv.difference_update(names)
            sh.update(names)
            continue
        bt = _norm_expr(b_type)
        if not _is_non_prop_binder_type(bt, frozenset(tv), shadowed=frozenset(sh)):
            return False
        if allow_new_type_vars and _is_type_universe(bt):
            for nm in names:
                if nm in _FALSE_ELIM_RESERVED_NAMES:
                    sh.add(nm)
                else:
                    tv.add(nm)
                    sh.discard(nm)
        else:
            tv.difference_update(names)
            sh.update(names)
    return True


_BOUND_NAME_SCAN_RE = re.compile(r"[(\[{⟨⦃]|[)\]}⟩⦄]|:|[^\W\d][\w'!?]*")


def _quantifier_bound_names(binders: str) -> frozenset[str]:
    """The variables a quantifier's binder section binds: every identifier outside a type
    annotation (`x y : T`, `(x : T) {y : U} ⦃z : V⦄`, `⟨a, b⟩`). A binder predicate's operand
    (`x ∈ s`) is included too: over-approximating only makes the caller more conservative."""
    names: list[str] = []
    depth = 0
    skip_depth = -1
    for m in _BOUND_NAME_SCAN_RE.finditer(binders):
        t = m.group(0)
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
            if depth < skip_depth:
                skip_depth = -1
        elif t == ":":
            if skip_depth == -1:
                skip_depth = depth
        elif skip_depth == -1:
            names.append(t)
    return frozenset(names)


_LEAN_EXPR_KW_STOP = frozenset(
    ("fun", "forall", "exists", "if", "then", "else", "match", "with", "let", "in", "have", "show", "by", "where")
)
_DEP_ARROW_BINDER_PREFIX_RE = re.compile(r"[({⦃]([^{}()⦃⦄:=]*):")


def _body_may_rebind_name(body: str, name: str) -> bool:
    """`True` iff `body` contains an inner binder (`∀`, `∃`, `λ`, `forall`, `exists`, `fun`,
    `let`, `have`, `match` arm, or dependent-arrow `(name : T)`) that may rebind `name`."""
    if name not in body:
        return False
    esc = re.escape(name)
    if (
        (
            "∀" in body
            or "∃" in body
            or "λ" in body
            or "forall" in body
            or "exists" in body
            or "fun" in body
            or "let" in body
            or "have" in body
            or "match" in body
        )
        and re.search(
            rf"(?:∀|∃|λ|\||(?<![\w'.!?])(?:forall|exists|fun|let|have)(?![\w'!?]))[^,=>;]*(?<![\w'.!?]){esc}(?![\w'!?])",
            body,
        )
    ):
        return True
    if ":" in body and ("→" in body or "->" in body):
        for m in _DEP_ARROW_BINDER_PREFIX_RE.finditer(body):
            if name in m.group(1).split():
                return True
    return False


def _top_level_arrow_domains(expr: str) -> list[str]:
    """Return the leading domain types `[D1, D2, ...]` of a top-level `D1 → D2 → ... → R` type."""
    ne = _norm_expr(expr)
    if not ne or ("→" not in ne and "->" not in ne):
        return []
    domains: list[str] = []
    depth = 0
    seg_start = 0
    for m in (_ARROW_SCAN_RE if _has_binder_keyword(ne) else _ARROW_SCAN_NOKW_RE).finditer(ne):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "({[⟨⦃":
            depth += 1
        elif t in ")}]⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("→", "->"):
                domains.append(_norm_expr(ne[seg_start : m.start()]))
                seg_start = m.end()
            else:
                break
    return domains


def _first_standalone_use(body: str, name: str) -> int:
    """Offset of the first occurrence of identifier `name` in `body` that is a whole identifier,
    not a field name (`x.name`), and not inside a `«...»` guillemet identifier, or `-1`."""
    pos = 0
    n_body = len(body)
    has_guil = "«" in body
    while True:
        idx = body.find(name, pos)
        if idx == -1:
            return -1
        pos = idx + len(name)
        if idx > 0 and (_is_lean_ident_char(body[idx - 1]) or body[idx - 1] == "."):
            continue
        if pos < n_body and _is_lean_ident_char(body[pos]):
            continue
        if has_guil:
            g_open = body.rfind("«", 0, idx)
            if g_open != -1:
                g_close = body.find("»", g_open + 1)
                if g_close != -1 and idx < g_close:
                    pos = g_close + 1
                    continue
        return idx


# `[adv B4]` / `[adv A4]` One whole Lean numeric literal: `0xFF` / `0b11` / `0o17`, or decimal
# digits with optional `_` digit separators, fraction, and exponent (`12`, `1_000`, `1.5`, `1e5`,
# `1.5e-3`).
_NUM_ARG_RE = re.compile(
    r"0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*|0[bB][01](?:_?[01])*|0[oO][0-7](?:_?[0-7])*"
    r"|\d(?:_?\d)*(?:\.\d(?:_?\d)*)?(?:[eE][-+]?\d(?:_?\d)*)?"
)
_CHAR_ARG_RE = re.compile(r"'u[0-9a-f_]+'|'(?:\\[^\n]{1,8}?|[^\\'\n])'")


def _skip_string_literal_arg(body: str, pos: int, n_body: int) -> int:
    """Advance past a single `\"...\"` literal starting at `body[pos]`, or return `-1` if unclosed."""
    q = pos + 1
    while q < n_body:
        q2 = body.find('"', q)
        if q2 == -1:
            return -1
        bs = 0
        bk = q2 - 1
        while bk > pos and body[bk] == "\\":
            bs += 1
            bk -= 1
        q = q2 + 1
        if bs % 2 == 0:
            return q
    return -1


def _skip_atomic_proj_chain(body: str, pos: int, n_body: int) -> int:
    """Advance past trailing `.field` projections and `[...]` subscripts on an atomic argument."""
    while pos < n_body:
        c = body[pos]
        if c == ".":
            pos += 1
            if pos >= n_body:
                break
            if body[pos] == "«":
                g_end = body.find("»", pos + 1)
                pos = n_body if g_end == -1 else g_end + 1
            else:
                m_seg = _PROJ_SEG_RE.match(body, pos)
                if m_seg is None:
                    break
                pos = m_seg.end()
        elif c == "[":
            d = 1
            pos += 1
            while pos < n_body and d > 0:
                if body[pos] == "[":
                    d += 1
                elif body[pos] == "]":
                    d -= 1
                pos += 1
        else:
            break
    return pos


def _untyped_binders_inhabited_by_calls(
    untyped_names: set[str],
    body: str,
    fn_domains: dict[str, tuple[bool, ...]],
    shadowed_fns: frozenset[str],
) -> bool:
    """`True` iff every untyped `∀` binder name in `untyped_names` is passed directly as an
    argument (not projected `s.val` or indexed `s[0]`, and not rebound by an inner binder) to some
    unshadowed outer function binder `f` in `fn_domains` at a parameter position whose domain is
    unconditionally inhabited (e.g. `(R : Nat → Prop) (h : ∀ s, R s ∧ False)`)."""
    if not untyped_names or not fn_domains:
        return False
    remaining = set(untyped_names)
    rebound_cache: dict[str, bool] = {}
    n_body = len(body)
    # `[adv B3]` Lean fixes an untyped binder's type at its first use, so only that occurrence
    # counts: in `∀ s, E s ∧ R s ∧ False` with `E : Fin 0 → Prop` (or `Fin.elim0 s`, or
    # `(s : Fin 0) = s`) `s` ranges over an empty type -- `R s` merely coerces it -- and the
    # hypothesis holds vacuously instead of being contradictory.
    first_use = {nm: _first_standalone_use(body, nm) for nm in untyped_names}
    for f_name, dom_flags in fn_domains.items():
        if f_name in shadowed_fns or not any(dom_flags) or f_name not in body:
            continue
        # Do not rely on `f_name` if an inner binder inside `body` rebinds it.
        if _body_may_rebind_name(body, f_name):
            continue
        pos = 0
        f_len = len(f_name)
        while pos < n_body and remaining:
            idx = body.find(f_name, pos)
            if idx == -1:
                break
            pos = idx + f_len
            if idx > 0 and (_is_lean_ident_char(body[idx - 1]) or body[idx - 1] in ".@"):
                continue
            if pos < n_body and _is_lean_ident_char(body[pos]):
                continue
            # Ensure `f_name` is in function-head position (not itself an argument to an outer call
            # like `Apply R s` where `s` is an argument to `Apply`, not `R`).
            prev_i = idx - 1
            while prev_i >= 0 and body[prev_i] in " \t\r\n":
                prev_i -= 1
            if prev_i >= 0 and (
                _is_lean_ident_char(body[prev_i]) or body[prev_i] in ")]}⟩⦄»\""
            ):
                continue
            # Parse up to `len(dom_flags)` atomic arguments right after `f_name`.
            arg_pos = pos
            for arg_idx, is_inhab in enumerate(dom_flags):
                while arg_pos < n_body and body[arg_pos] in " \t\r\n":
                    arg_pos += 1
                if arg_pos >= n_body:
                    break
                ch = body[arg_pos]
                if ch in "([{⟨⦃":
                    close_map = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
                    close_c = close_map[ch]
                    d = 1
                    q = arg_pos + 1
                    while q < n_body and d > 0:
                        if body[q] == ch:
                            d += 1
                        elif body[q] == close_c:
                            d -= 1
                        q += 1
                    # `[adv A3]` A named argument `(x := v)` shifts all following positional slots.
                    if ch == "(" and ":=" in body[arg_pos + 1 : q - 1]:
                        break
                    arg_pos = _skip_atomic_proj_chain(body, q, n_body)
                    continue
                if ch == '"':
                    # `[adv A4]` Neutralized or raw string literal argument (`R "hi" s`): one slot.
                    q = _skip_string_literal_arg(body, arg_pos, n_body)
                    if q == -1:
                        break
                    arg_pos = _skip_atomic_proj_chain(body, q, n_body)
                    continue
                if ch == "'":
                    # `[adv A4]` Char literal argument (`R 'a' s`, raw or neutralized `'u61'`): one slot.
                    m_ch = _CHAR_ARG_RE.match(body, arg_pos)
                    if m_ch is None:
                        break
                    arg_pos = _skip_atomic_proj_chain(body, m_ch.end(), n_body)
                    continue
                if ch.isdecimal():
                    # `[adv A3]` Numeral argument (`R 0 s`): consume this slot and advance.
                    # `[adv B4]` The whole literal is one slot. Reading only the leading digits
                    # split `0xFF` / `0b11` / `1e5` into a numeral and an identifier (`xFF`), which
                    # moved every later argument one slot to the right: with
                    # `R : Nat → Fin 0 → Nat → Prop`, the `s` of `∀ s, R 0xFF s ∧ False` was read
                    # at the inhabited third slot instead of the empty `Fin 0`, and a hypothesis
                    # that holds vacuously was reported as a contradiction.
                    m_num = _NUM_ARG_RE.match(body, arg_pos)
                    if m_num is None:
                        break
                    q = m_num.end()
                    if q < n_body and _is_lean_ident_char(body[q]):
                        # Not a literal this scan can delimit: stop rather than misalign.
                        break
                    arg_pos = _skip_atomic_proj_chain(body, q, n_body)
                    continue
                m_id = _IDENT_EXTRACT_RE.match(body, arg_pos)
                if m_id is None:
                    break
                tok = m_id.group(0)
                if tok in _LEAN_EXPR_KW_STOP:
                    break
                end_tok = m_id.end()
                if end_tok < n_body and body[end_tok] == '"':
                    # `[adv A4]` Interpolated string (`s!"..."` / `m!"..."`): stop conservatively
                    # so it neither splits across two slots nor hides inner uses of an untyped var.
                    break
                if end_tok < n_body and body[end_tok] in ".[":
                    # `s.val` / `s[0]` passes a projection/element of `s`, NOT `s` itself:
                    # e.g. `s : Fin 0` has `s.val : Nat` even though `Fin 0` is empty.
                    # `[adv A3]` Still consume the whole projection chain as one atomic arg so
                    # later arguments (`R xs.length s`) are still aligned and checked.
                    arg_pos = _skip_atomic_proj_chain(body, end_tok, n_body)
                    continue
                if is_inhab and tok in remaining and first_use[tok] == arg_pos:
                    rebound = rebound_cache.get(tok)
                    if rebound is None:
                        rebound = _body_may_rebind_name(body, tok)
                        rebound_cache[tok] = rebound
                    if not rebound:
                        remaining.discard(tok)
                arg_pos = end_tok
        if not remaining:
            return True
    return not remaining


def _split_dep_arrow_prefix(expr: str) -> tuple[str, str, str] | None:
    """For normalized `(names : T) → body` / `{names : T} → body` / `⦃names : T⦄ → body` (excluding
    subtypes `{x : T // p}`, set-builders `{x : T | p}`, and expressions governed by a looser
    depth-0 connective such as `↔`), return `(names, T, body)`, else `None`."""
    n = len(expr)
    if n < 7 or expr[0] not in "({⦃":
        return None
    q, col = _scan_binder_group(expr, 0, n)
    if q > n or col == -1:
        return None
    names = expr[1:col].strip()
    b_type = expr[col + 1 : q - 1].strip()
    if (
        not b_type
        or _BARE_BINDER_NAMES_RE.fullmatch(names) is None
        or (expr[0] == "{" and _has_depth0_brace_sep(b_type))
    ):
        return None
    p = q
    while p < n and expr[p] in " \t\r\n":
        p += 1
    if p < n and expr[p] == "→":
        body = expr[p + 1 :]
    elif p + 1 < n and expr[p] == "-" and expr[p + 1] == ">":
        body = expr[p + 2 :]
    else:
        return None
    if "↔" in body or "<->" in body or "<|" in body or "$" in body:
        depth = 0
        scan_re = _ARROW_SCAN_RE if _has_binder_keyword(body) else _ARROW_SCAN_NOKW_RE
        for m in scan_re.finditer(body):
            t = m.group(0)
            if t[0] == "«" or t[0] == "'":
                continue
            if t in "({[⟨⦃":
                depth += 1
            elif t in ")}]⟩⦄":
                if depth > 0:
                    depth -= 1
            elif depth == 0:
                if t in ("↔", "<->", "<|>", "<|", "$"):
                    return None
                if t not in ("→", "->"):
                    break
    return names, b_type, body


def _hyp_atoms(
    expr: str,
    bound: frozenset[str],
    q_chain: tuple[str, ...],
    q_nat_vars: frozenset[str],
    scope_path: tuple[int, ...],
    out: list[tuple[str, frozenset[str], tuple[str, ...], frozenset[str], tuple[int, ...]]],
    *,
    shadowed: frozenset[str] = frozenset(),
    fn_domains: dict[str, tuple[bool, ...]] | None = None,
    fn_domains_loader: Any = None,
    scope_counter: list[int] | None = None,
    scope_binds: dict[tuple[int, ...], frozenset[str]] | None = None,
    q_float_vars_out: dict[tuple[int, ...], frozenset[str]] | None = None,
    q_float_vars: frozenset[str] = frozenset(),
) -> None:
    """Append to `out` the atoms that must ALL hold for normalized hypothesis `expr` to hold, as
    `(atom, quantifier-bound names in scope, enclosing quantifier binder sections, quantifier-typed
    Nat-like vars in scope, unique quantifier scope path)`: its top-level conjuncts
    (`_split_top_level_conjuncts`), descending through every `∃ binders,` prefix (an existential is
    unsatisfiable whenever its body is), through `∀ binders,` prefixes whose domains are provably
    inhabited (explicit unshadowed inhabited types, or untyped names applied to an unshadowed outer
    binder with an inhabited domain; `∀ h : P, False`, `∀ i < n, False`, `∀ a : α, False`, and
    `∀ a, R a ∧ False` over `R : α → Prop` stay one opaque atom), and through dependent arrows
    `(x : T) → body` with an unconditionally inhabited domain `T`."""
    if scope_counter is None:
        scope_counter = [0]
    for part in _split_top_level_conjuncts(expr):
        if part and part[0] in "∃∀ef":
            split = _split_quantifier_prefix(part)
            if split is not None:
                quantifier, binders, body = split
                body_n = _norm_expr(body)
                if body_n:
                    groups = _parse_quantifier_binder_groups(binders)
                    can_descend = quantifier == "∃"
                    if not can_descend:
                        if _plain_quantifier_binders(
                            binders, shadowed=shadowed, allow_untyped=False, groups=groups
                        ):
                            can_descend = True
                        elif (
                            groups is not None
                            and (fn_domains or fn_domains_loader is not None)
                            and _plain_quantifier_binders(
                                binders, shadowed=shadowed, allow_untyped=True, groups=groups
                            )
                        ):
                            if fn_domains is None and fn_domains_loader is not None:
                                fn_domains = fn_domains_loader()
                                fn_domains_loader = None
                            if fn_domains:
                                untyped_names = {
                                    nm for g_names, g_type in groups if g_type is None for nm in g_names
                                }
                                q_all = bound | _quantifier_bound_names(binders)
                                can_descend = _untyped_binders_inhabited_by_calls(
                                    untyped_names, body_n, fn_domains, q_all
                                )
                    if can_descend:
                        q_bound = _quantifier_bound_names(binders)
                        next_nat = set(q_nat_vars) - q_bound
                        next_float = set(q_float_vars) - q_bound
                        next_sh = set(shadowed)
                        if groups is not None:
                            for g_names, g_type in groups:
                                if g_type is not None:
                                    bt = _norm_expr(g_type)
                                    if (bt in _NAT_LIKE_TYPES and bt not in next_sh) or (
                                        bt.startswith("Fin ") and "Fin" not in next_sh
                                    ):
                                        next_nat.update(g_names)
                                    else:
                                        next_nat.difference_update(g_names)
                                    if bt in _FLOAT_TYPE_NAMES and bt not in next_sh:
                                        next_float.update(g_names)
                                    else:
                                        next_float.difference_update(g_names)
                                else:
                                    next_nat.difference_update(g_names)
                                    next_float.difference_update(g_names)
                                next_sh.update(g_names)
                        else:
                            next_sh.update(q_bound)
                        child_id = scope_counter[0]
                        scope_counter[0] = child_id + 1
                        child_path = scope_path + (child_id,)
                        if scope_binds is not None:
                            scope_binds[child_path] = q_bound
                        if q_float_vars_out is not None and next_float:
                            q_float_vars_out[child_path] = frozenset(next_float)
                        _hyp_atoms(
                            body_n,
                            bound | q_bound,
                            q_chain + (binders,),
                            frozenset(next_nat),
                            child_path,
                            out,
                            shadowed=frozenset(next_sh),
                            fn_domains=fn_domains,
                            fn_domains_loader=fn_domains_loader,
                            scope_counter=scope_counter,
                            scope_binds=scope_binds,
                            q_float_vars_out=q_float_vars_out,
                            q_float_vars=frozenset(next_float),
                        )
                        continue
        elif part and part[0] in "({⦃" and ":" in part and ("→" in part or "->" in part):
            dep_split = _split_dep_arrow_prefix(part)
            if dep_split is not None:
                b_names_s, b_type_s, body_s = dep_split
                bt = _norm_expr(b_type_s)
                body_n = _norm_expr(body_s)
                if body_n and _is_non_prop_binder_type(bt, _NO_BOUND_NAMES, shadowed=shadowed):
                    g_names = b_names_s.split()
                    q_bound = frozenset(g_names)
                    next_nat = set(q_nat_vars) - q_bound
                    next_float = set(q_float_vars) - q_bound
                    next_sh = set(shadowed)
                    if (bt in _NAT_LIKE_TYPES and bt not in next_sh) or (
                        bt.startswith("Fin ") and "Fin" not in next_sh
                    ):
                        next_nat.update(g_names)
                    if bt in _FLOAT_TYPE_NAMES and bt not in next_sh:
                        next_float.update(g_names)
                    next_sh.update(g_names)
                    child_id = scope_counter[0]
                    scope_counter[0] = child_id + 1
                    child_path = scope_path + (child_id,)
                    if scope_binds is not None:
                        scope_binds[child_path] = q_bound
                    if q_float_vars_out is not None and next_float:
                        q_float_vars_out[child_path] = frozenset(next_float)
                    _hyp_atoms(
                        body_n,
                        bound | q_bound,
                        q_chain + (f"{b_names_s} : {b_type_s}",),
                        frozenset(next_nat),
                        child_path,
                        out,
                        shadowed=frozenset(next_sh),
                        fn_domains=fn_domains,
                        fn_domains_loader=fn_domains_loader,
                        scope_counter=scope_counter,
                        scope_binds=scope_binds,
                        q_float_vars_out=q_float_vars_out,
                        q_float_vars=frozenset(next_float),
                    )
                    continue
        out.append((part, bound, q_chain, q_nat_vars, scope_path))


_SIMPLE_TERM_TOKEN_RE = re.compile(
    r'\s+|«[^»]*»|(?<![\w\'.!?])\'[^\'\n]*\'|"0\d+"|\.?[^\W\d][\w\'!?]*(?:\.[^\W\d][\w\'!?]*)*'
    r"|\.?\d+(?:\.\d+)*|::|\+\+|[-+*/%^@#↑]|!(?!=)|([(\[⟨])|([)\]⟩])"
)
_SIMPLE_RELATION_RE = re.compile(
    r"«[^»]*»|(?<![\w'.!?])'[^'\n]*'|[()\[\]{}⟨⟩⦃⦄]|≠|≤|≥|<|>|="
)


def _is_simple_term(e: str) -> bool:
    """`True` iff `e` is an application / arithmetic / list-cons of names, numerals, literals and
    balanced `()` `[]` `⟨⟩` groups (whose contents are opaque): no other operator at depth 0, so
    it cannot carry a second proposition (`some s && bad s`, `some s ×' Bad s`, `x |> Bad`)."""
    n = len(e)
    if n == 0:
        return False
    depth = 0
    pos = 0
    match = _SIMPLE_TERM_TOKEN_RE.match
    while pos < n:
        m = match(e, pos)
        if m is None:
            if depth == 0:
                return False
            pos += 1
            continue
        if m.group(1):
            depth += 1
        elif m.group(2):
            if depth == 0:
                return False
            depth -= 1
        pos = m.end()
    return depth == 0


def _is_simple_refutation_premise(part: str) -> bool:
    """`True` iff normalized `part` is one atomic proposition: `False`, or -- optionally under a
    single negation (`¬ X` / `X → False`) -- `True` or exactly one depth-0 relation (`=`, `≠`,
    `<`, `>`, `≤`, `≥`) between simple terms (`_is_simple_term`). A deliberately strict
    whitelist: it gates the `False`-elimination exemption, where a looser reading would exempt
    a premise that carries a second proposition."""
    h = part
    if h == "False":
        return True
    denied = _arrow_false_antecedent(h) if ("False" in h and ("→" in h or "->" in h)) else None
    if denied is not None:
        h = denied
    elif h.startswith("¬"):
        h = _norm_expr(h[1:])
    if h == "True":
        return True
    depth = 0
    rel = None
    for m in _SIMPLE_RELATION_RE.finditer(h):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if rel is not None:
                return False
            rel = m
    if rel is None:
        return False
    return _is_simple_term(h[: rel.start()].strip()) and _is_simple_term(h[rel.end() :].strip())


_TOP_BOUND_NOKW_RE = re.compile(
    r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|"
    r"↔|→|->|<\|>|<\||\|>|\$|∨|∃|∀|λ"
)
_TOP_BOUND_RE = re.compile(_TOP_BOUND_NOKW_RE.pattern + "|" + _BINDER_KEYWORD_ALT)


def _find_top_level_bound(expr: str, *, allow_or: bool) -> int:
    """Return the character offset of the first depth-0 prefix binder/keyword (`∀`, `∃`, `fun`,
    `λ`, `if`, `match`, `let`, `have`, `show`, `by`) whose body extends to the end of `expr`,
    `len(expr)` if none exists, or `-1` if a depth-0 infix connective looser than the target
    (`↔`, `→`, `->`, `<|>`, `<|`, `|>`, `$`, plus `∨` when `allow_or=False`) appears before any
    prefix binder.

    Notice why distinguishing prefix binders from looser infix connectives is essential:
    - In `p ↔ q ∨ True`, `↔` (precedence 20) binds looser than `∨` (30) across the whole
      expression (`p ↔ (q ∨ True)`), so `∨` is NOT the top-level connective (`return -1`).
    - In `f = fun x => x ∨ True` or `∃ y : Nat, y = y ∨ p`, the prefix binder starts at offset
      `4` / `0` *before* `∨`, so there is no `∨` in `expr[:bound]` and `∨` is inside the binder.
    - In `True ∨ ∀ x : Nat, P x` or `x = x ∨ ∃ y : Nat, y > x` or `True ∨ if c then p else q`,
      `∨` appears in `expr[:bound]` *before* the prefix binder, so `∨` IS the top-level connective
      and `expr[op_end:]` (containing the prefix binder) is the right-hand disjunct!
    """
    depth = 0
    for m in (_TOP_BOUND_RE if _has_binder_keyword(expr) else _TOP_BOUND_NOKW_RE).finditer(expr):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("↔", "→", "->", "<|>", "<|", "|>", "$"):
                return -1
            if t == "∨":
                if not allow_or:
                    return -1
                continue
            return m.start()
    return len(expr)


def _all_conjuncts_trivial(expr: str, float_vars: frozenset[str] = _NO_BOUND_NAMES) -> bool:
    """`True` iff `expr` has >= 2 top-level `∧` conjuncts and all are trivially true; stops at
    the first non-trivial conjunct (so long genuine conclusions cost one conjunct check)."""
    idx = expr.find("∧")
    if idx == -1:
        return False
    first = expr[:idx]
    if (
        "«" not in first
        and "'" not in first
        and "↔" not in first
        and "→" not in first
        and "->" not in first
        and first.count("(") == first.count(")")
        and first.count("[") == first.count("]")
        and first.count("{") == first.count("}")
        and first.count("⟨") == first.count("⟩")
        and first.count("⦃") == first.count("⦄")
        and not _is_trivially_true(first, float_vars)
    ):
        return False
    bound = _find_top_level_bound(expr, allow_or=False)
    if bound <= 0:
        return False
    pat = _CONJ_TRIV_SPLIT_RE
    depth = 0
    start = 0
    count = 0
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if not _is_trivially_true(expr[start : m.start()], float_vars):
                return False
            count += 1
            start = m.end()
    return count >= 1 and _is_trivially_true(expr[start:], float_vars)


def _any_disjunct_trivial(expr: str, float_vars: frozenset[str] = _NO_BOUND_NAMES) -> bool:
    """`True` iff `expr` has >= 2 top-level `∨` disjuncts and at least one is trivially true
    (e.g. `P ∨ True`, `x = x ∨ P`, or `True ∨ ∀ x, P x`, which can be discharged by
    `Or.inr trivial` / `Or.inl rfl` without proving `P`)."""
    bound = _find_top_level_bound(expr, allow_or=True)
    if bound <= 0:
        return False
    pat = _DISJ_TRIV_SPLIT_RE
    depth = 0
    start = 0
    count = 0
    found_trivial = False
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            count += 1
            if _is_trivially_true(expr[start : m.start()], float_vars):
                found_trivial = True
            start = m.end()
    if count == 0:
        return False
    return found_trivial or _is_trivially_true(expr[start:], float_vars)


_STANDALONE_EQ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|(?<![=!<>:])=(?![=>])")
# `[adv B3]` A prefix that is only non-bracket text and balanced bracket groups nested at most two
# deep, with no `«`: the depth-0 scanners (which count every bracket kind alike and skip `«...»`)
# are at depth 0 right after it. Unrolled (`run (group run)*`, each group opening on a character
# the runs cannot match), so a failing match backtracks linearly.
_DEPTH0_PREFIX_FULLMATCH = re.compile(
    r"[^()\[\]{}⟨⟩⦃⦄«]*(?:[(\[{⟨⦃][^()\[\]{}⟨⟩⦃⦄«]*"
    r"(?:[(\[{⟨⦃][^()\[\]{}⟨⟩⦃⦄«]*[)\]}⟩⦄][^()\[\]{}⟨⟩⦃⦄«]*)*"
    r"[)\]}⟩⦄][^()\[\]{}⟨⟩⦃⦄«]*)*"
).fullmatch


def _split_single_depth0_op(
    expr: str, op: str, not_before: str, not_after: str
) -> list[str] | None:
    """C-level shortcut for the depth-0 split scans on a one-character relation `op` that is not
    an operator when preceded by a `not_before` or followed by a `not_after` character. Returns
    exactly what the scan returns when that can be decided without it -- `[expr]` when `op` does
    not occur or its only occurrence is excluded by a neighbour, `[lhs, rhs]` when its only
    occurrence follows a provably depth-0 prefix (`_DEPTH0_PREFIX_FULLMATCH`) -- and `None`
    (run the scan) otherwise: several occurrences, deeper nesting, `«...»`, stray brackets."""
    i = expr.find(op)
    if i == -1:
        return [_norm_expr(expr)]
    if expr.find(op, i + 1) != -1:
        return None
    if (i > 0 and expr[i - 1] in not_before) or (i + 1 < len(expr) and expr[i + 1] in not_after):
        return [_norm_expr(expr)]
    if _DEPTH0_PREFIX_FULLMATCH(expr, 0, i) is None:
        return None
    return [_norm_expr(expr[:i]), _norm_expr(expr[i + 1 :])]


def _split_top_level_eq(expr: str) -> list[str]:
    """Split `expr` on top-level standalone `=` (excluding `==`, `=>`, `:=`, `!=`, `<=`, `>=`) outside `()[]{}⟨⟩⦃⦄` and `«...»`."""
    fast = _split_single_depth0_op(expr, "=", "=!<>:", "=>")
    if fast is not None:
        return fast
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _STANDALONE_EQ_SPLIT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


def _is_trivially_true(
    conj: str,
    float_vars: frozenset[str] = _NO_BOUND_NAMES,
    *,
    already_norm: bool = False,
) -> bool:
    """`True`, `¬ False`, a reflexive `a = a` / `a ↔ a` / `a ≤ a` (excluding `Float`/`Float32`,
    where `NaN ≤ NaN` is false) conjunct, a parenthesized trivial conjunction/disjunction, or a
    universally quantified `∀ ..., <trivial>` whose body is itself trivially true."""
    raw = conj if already_norm else conj.strip()
    if raw in ("True", "¬ False", "¬False"):
        return True
    if "=" not in raw and "↔" not in raw and "≤" not in raw and "True" not in raw and "False" not in raw:
        return False
    c = raw if already_norm else _norm_expr(raw)
    if not already_norm:
        if c in ("True", "¬ False", "¬False"):
            return True
        if len(c) < len(raw):
            if "∧" in c and _all_conjuncts_trivial(c, float_vars):
                return True
            if "∨" in c and _any_disjunct_trivial(c, float_vars):
                return True
    if c.startswith("∀") or (
        c.startswith("forall") and len(c) > 6 and not _is_lean_ident_char(c[6])
    ):
        q_split = _split_quantifier_prefix(c)
        if q_split is not None:
            _, q_bind_str, q_body = q_split
            next_fv = float_vars
            if float_vars or "Float" in q_bind_str:
                groups = _parse_quantifier_binder_groups(q_bind_str)
                fv_set = set(float_vars)
                if groups is not None:
                    for g_names, g_type in groups:
                        if g_type is not None:
                            g_bt = _norm_expr(_strip_binder_default(g_type))
                        else:
                            g_bt = ""
                        if g_bt in _FLOAT_TYPE_NAMES:
                            fv_set.update(g_names)
                        else:
                            fv_set.difference_update(g_names)
                else:
                    fv_set.difference_update(_quantifier_bound_names(q_bind_str))
                next_fv = frozenset(fv_set)
            body = _norm_expr(q_body)
            return (
                _is_trivially_true(body, next_fv, already_norm=True)
                or ("∧" in body and _all_conjuncts_trivial(body, next_fv))
                or ("∨" in body and _any_disjunct_trivial(body, next_fv))
            )
    n_c = len(c)
    for op in ("↔", "≤", "="):
        op_i = c.find(op)
        if op_i == -1:
            continue
        if op == "=":
            if c.find("=", op_i + 1) == -1 and ":=" not in c and "«" not in c and "'" not in c:
                # `[adv B3]` / `[adv A3]` `_norm_expr` only collapses whitespace and strips outer
                # `(...)`, so it preserves the first non-`(`, non-whitespace char of each side.
                lp = 0
                while lp < op_i and c[lp] in "( \t\r\n":
                    lp += 1
                rp = op_i + 1
                while rp < n_c and c[rp] in "( \t\r\n":
                    rp += 1
                if (c[lp] if lp < op_i else "") != (c[rp] if rp < n_c else ""):
                    continue
                lhs = c[:op_i]
                if (
                    lhs.count("(") == lhs.count(")")
                    and lhs.count("[") == lhs.count("]")
                    and lhs.count("{") == lhs.count("}")
                    and (
                        lhs.isascii()
                        or (lhs.count("⟨") == lhs.count("⟩") and lhs.count("⦃") == lhs.count("⦄"))
                    )
                ):
                    nl = _norm_expr(lhs)
                    if nl and nl == _norm_expr(c[op_i + 1 :]):
                        return True
                continue
            sides = _split_top_level_eq(c)
            if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
                return True
            continue
        if c.find(op, op_i + 1) == -1 and "«" not in c and "'" not in c:
            lp = 0
            while lp < op_i and c[lp] in "( \t\r\n":
                lp += 1
            rp = op_i + 1
            while rp < n_c and c[rp] in "( \t\r\n":
                rp += 1
            if (c[lp] if lp < op_i else "") != (c[rp] if rp < n_c else ""):
                continue
            lhs = c[:op_i]
            if (
                lhs.count("(") == lhs.count(")")
                and lhs.count("[") == lhs.count("]")
                and lhs.count("{") == lhs.count("}")
                and (
                    lhs.isascii()
                    or (lhs.count("⟨") == lhs.count("⟩") and lhs.count("⦃") == lhs.count("⦄"))
                )
            ):
                nl = _norm_expr(lhs)
                if nl and nl == _norm_expr(c[op_i + 1 :]):
                    if op == "≤" and _operand_may_be_float(nl, float_vars):
                        continue
                    return True
            continue
        sides = _split_top_level(c, op)
        if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
            if op == "≤" and _operand_may_be_float(sides[0], float_vars):
                continue
            return True
    return False


_NAT_LIKE_TYPES = frozenset(("Nat", "ℕ", "UInt8", "UInt16", "UInt32", "UInt64", "USize"))
# Generic projections that are always `Nat` (`.length`, `.size`, `.toNat`) plus this repository's
# `Nat`-typed layout fields. NOT `.fst` / `.val` / `.bytes` (A2): `(p : Int × Nat) (h : p.fst < 0)`
# and `(x : {z : Int // z < 5}) (h : x.val < 0)` are satisfiable, so flagging them is a false positive.
_NAT_VALUED_SUFFIXES = (
    ".length",
    ".size",
    ".toNat",
    ".pad0",
    ".padMid",
    ".padTail",
    ".totalPad",
    ".totalSize",
    ".align",
    ".repadWidth",
    ".sumFieldWidths",
    ".totalPadBytes",
    ".tagByteWidth",
    ".toTag",
    ".rawWidth",
)
_NAT_VALUED_PREFIXES = (
    "sumSizes ",
    "maxAlign ",
    "cEnd ",
    "memKey ",
    "nzBit ",
    "Nat.",
    "MirValueCodec.uintByteSize ",
    "Mir.PlaceAndRvalue.alignUp ",
    "PlaceAndRvalue.alignUp ",
)
_NAT_ARITH_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|[-+*/%^]")
_PROJ_SEG_RE = re.compile(r"[^\W\d][\w'!?]*|\d+")
# Binary infix operators with Lean 4 precedence strictly tighter than `=` / `<` (50) and looser
# than function application (1024): if one appears at depth 0, it governs the operand instead of
# a leading constructor or `Nat`-valued function (`some x >>= f`, `Except.ok x *> y`,
# `sumSizes xs |>.toInt`). Operators looser than `=` (`&&`, `×'`, bare `|>`) are intentionally
# excluded so two-premise hypotheses such as `none = some s ×' Bad s` keep their existing reading.
_HIGH_PREC_INFIX_RE = re.compile(
    r"«[^»]*»|"
    + _SCAN_CHAR_LIT_ALT
    + "|"
    + _SCAN_BRACKET_ALTS
    + r"|\|>\.|>>=|>>|<\*>|<\*|\*>|<\$>|<<<|>>>|&&&|\|\|\||\^\^\^|\+\+|[-+*/%^∘]"
)
_LOOSER_THAN_CONS_RE = re.compile(
    r"«[^»]*»|"
    + _SCAN_CHAR_LIT_ALT
    + "|"
    + _SCAN_BRACKET_ALTS
    + r"|\|>\.|>>=|>>|<\*>|<\*|\*>|&&&|\|\|\||\^\^\^"
)


def _has_depth0_pattern(expr: str, pat: re.Pattern[str]) -> bool:
    depth = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return True
    return False


def _has_depth0_high_prec_infix(e: str) -> bool:
    """`True` iff `e` contains a depth-0 binary operator tighter than `=`/`<` (e.g. `>>=`, `|>.`,
    `*>`, `<*`, `<*>`, `&&&`, `>>>`, `+`), so `e` is NOT headed by a leading constructor/function."""
    return _has_depth0_pattern(e, _HIGH_PREC_INFIX_RE)


def _has_depth0_looser_than_cons(e: str) -> bool:
    """`True` iff `e` contains a depth-0 operator tighter than `=` (50) and looser than `::` (67)
    that can turn a non-empty list into `[]` (e.g. `x :: xs >>= f`, `x :: xs |>.tail`, `x :: xs *> []`)."""
    return _has_depth0_pattern(e, _LOOSER_THAN_CONS_RE)


def _is_single_projection_chain(e: str) -> bool:
    """`True` iff normalized `e` is one projection/subscript chain (`xs.length`,
    `(xs.map f).length`, `arr[i].size`), not an application (`f xs.length`, `(f)(xs).length`)
    or infix expression (`x>>>xs.length`)."""
    n = len(e)
    if n == 0:
        return False
    p = 0
    ch = e[0]
    if ch in "([{⟨":
        close_map = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
        close_c = close_map[ch]
        depth = 1
        p = 1
        while p < n and depth > 0:
            c = e[p]
            if c == ch:
                depth += 1
            elif c == close_c:
                depth -= 1
            p += 1
        if depth != 0:
            return False
    elif ch == "«":
        end_g = e.find("»", 1)
        if end_g == -1:
            return False
        p = end_g + 1
    else:
        m = _IDENT_EXTRACT_RE.match(e, 0)
        if m is None:
            return False
        p = m.end()
    while p < n:
        c = e[p]
        if c == ".":
            p += 1
            if p >= n:
                return False
            if e[p] == "«":
                end_g = e.find("»", p + 1)
                if end_g == -1:
                    return False
                p = end_g + 1
            else:
                m = _PROJ_SEG_RE.match(e, p)
                if m is None:
                    return False
                p = m.end()
        elif c == "[":
            depth = 1
            p += 1
            while p < n and depth > 0:
                if e[p] == "[":
                    depth += 1
                elif e[p] == "]":
                    depth -= 1
                p += 1
            if depth != 0:
                return False
        else:
            return False
    return True


def _nat_operand_kind(e: str, nat_vars: frozenset[str]) -> int:
    """Classify normalized `e` for `< 0` / `0 > ...` vacuity checks:
    - `2`: pure unsigned/`Nat`-valued (non-negative even under `-`, which saturates/wraps >= 0),
    - `1`: coerced non-negative (`↑...` or `Nat.cast ...`, non-negative under `+`/`*`/`/`/`%`/`^`,
           but NOT under `-`, since `↑a.length - ↑b.length < 0` and `↑a.length - 1 < 0` hold in `Int`),
    - `0`: unknown (may be negative)."""
    e = _norm_expr(e)
    if not e:
        return 0
    parts: list[str] | None = None
    has_sub = False
    depth = 0
    start = 0
    for m in _NAT_ARITH_SPLIT_RE.finditer(e):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if parts is None:
                parts = []
            if t == "-":
                has_sub = True
            parts.append(e[start : m.start()])
            start = m.end()
    if parts is not None:
        parts.append(e[start:])
        min_kind = 2
        for p in parts:
            k = _nat_operand_kind(p, nat_vars)
            if k == 0:
                return 0
            if k < min_kind:
                min_kind = k
        if has_sub and min_kind < 2:
            return 0
        return min_kind
    if e.startswith("↑"):
        inner = e[1:].strip()
        return 1 if _nat_operand_kind(inner, nat_vars) >= 1 else 0
    if e.startswith("Nat.cast ") or e == "Nat.cast":
        return 1 if not _has_depth0_high_prec_infix(e) else 0
    if e in nat_vars or _NUM_LIT_RE.match(e) is not None:
        return 2
    if e.startswith(_NAT_VALUED_PREFIXES):
        return 2 if not _has_depth0_high_prec_infix(e) else 0
    if e.endswith(_NAT_VALUED_SUFFIXES) and _is_single_projection_chain(e):
        return 2
    return 0


def _is_nat_like_operand(e: str, nat_vars: frozenset[str]) -> bool:
    """`True` iff `e` is syntactically non-negative: a numeral, a binder declared `Nat`-like, a
    known `Nat`-valued projection/function (`.length`, `.size`, `.toNat`, `sumSizes ...`, etc.),
    a coercion `↑...` / `Nat.cast ...` of one, or a depth-0 `+`/`*`/`/`/`%`/`^` (and, on purely
    unsigned/`Nat` operands only, `-`) combination of such operands."""
    return _nat_operand_kind(e, nat_vars) >= 1


_PURE_DATA_BASE_TYPES = frozenset(
    (
        "Nat",
        "ℕ",
        "Int",
        "ℤ",
        "Bool",
        "String",
        "Char",
        "Unit",
        "PUnit",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Int8",
        "Int16",
        "Int32",
        "Int64",
        "ISize",
        "Float",
        "Float32",
        "ByteArray",
    )
)
_ALWAYS_INHABITED_CONTAINERS = frozenset(("List", "Array", "Option", "BitVec"))
_PARAM_DATA_CONTAINERS = frozenset(("Sum", "Except", "Prod"))
_SAFE_TYPECLASS_HEADS = frozenset(
    (
        "Decidable",
        "DecidableEq",
        "DecidablePred",
        "DecidableRel",
        "BEq",
        "Ord",
        "Repr",
        "ToString",
        "Hashable",
        "SizeOf",
    )
)
_TYPE_UNIVERSE_RE = re.compile(r"^Type(?:\*|\s+(?:[\w.+*]+|\([\w\s.+*]+\)))?$")
_TYPE_ARG_NAME_RE = re.compile(r"[^\W\d][\w'.]*|\d+")
# Global names the `False`-elimination exemption reads by spelling. A binder that rebinds one
# (`(Nat : Prop) (hn : Nat)`, `(False : Prop)`) changes what the spelling means, so it voids the
# exemption (`Type` / `Prop` / `Sort` are keywords and cannot be rebound).
_FALSE_ELIM_RESERVED_NAMES = (
    _PURE_DATA_BASE_TYPES
    | _ALWAYS_INHABITED_CONTAINERS
    | _PARAM_DATA_CONTAINERS
    | _SAFE_TYPECLASS_HEADS
    | frozenset(("False", "True"))
)


def _is_type_universe(bt: str) -> bool:
    """`True` iff normalized `bt` is `Type`, `Type*`, or `Type <level>` (strictly above `Prop`;
    excludes `Sort u` which can instantiate to `Prop`)."""
    return _TYPE_UNIVERSE_RE.match(bt) is not None


def _atomic_type_args(rest: str) -> list[str] | None:
    """Split the argument text of a type application into atomic arguments -- names, numerals
    and balanced `(...)` groups -- or return `None` when anything else sits at depth 0 (an infix
    relation such as `∈` / `≍` / `=`, a product, a subtype brace, a binder ...): `List Nat ∈ S`
    and `Decidable P ∈ S` are propositions, not applications of `List` / `Decidable`."""
    args: list[str] = []
    has_quote = "'" in rest
    p = 0
    n = len(rest)
    while p < n:
        ch = rest[p]
        if ch in " \t\r\n":
            p += 1
            continue
        if ch == "(":
            depth = 0
            q = p
            while q < n:
                c = rest[q]
                if has_quote and c == "'":
                    lit_end = _skip_char_literal_before(rest, q, q + 1, n)
                    if lit_end != -1:
                        q = lit_end
                        continue
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                    if depth == 0:
                        break
                q += 1
            if q >= n:
                return None
            args.append(rest[p : q + 1])
            p = q + 1
            continue
        m = _TYPE_ARG_NAME_RE.match(rest, p)
        if m is None:
            return None
        args.append(m.group(0))
        p = m.end()
    return args


def _is_safe_typeclass_expr(expr: str) -> bool:
    """`True` iff `expr` is exactly an application of a safe computational typeclass to atomic
    arguments (`Decidable P`, `Decidable (a = b)`, `DecidableEq α`, `BEq α`)."""
    head, sep, rest = _norm_expr(expr).partition(" ")
    return bool(sep) and head in _SAFE_TYPECLASS_HEADS and bool(_atomic_type_args(rest))


def _is_non_prop_binder_type(
    b_type: str,
    type_vars: frozenset[str],
    *,
    shadowed: frozenset[str] = frozenset(),
) -> bool:
    """`True` iff `b_type` is, by a strict whitelist grammar, a data / universe / safe-typeclass
    binder type that is inhabited whenever its type variables are -- never a `Prop` assumption,
    an uninhabited type (`Empty`, `Fin 0`), a subtype, a predicate application or a relation:

        T ::= Prop | Type [level] | base | type-var | F × F × ...        (F ::= base | type-var)
            | (List | Array | Option | BitVec) arg                        (always inhabited)
            | (Sum | Except | Prod) F F
            | safe-typeclass arg+                                         (classically inhabited)

    where `arg` is a name, a numeral or a balanced `(...)` group, and no base/container/typeclass
    name is in `shadowed`. Anything else is rejected."""
    bt = _norm_expr(b_type)
    if not bt:
        return False
    if (
        bt == "Prop"
        or (bt in _PURE_DATA_BASE_TYPES and bt not in shadowed)
        or bt in type_vars
        or _is_type_universe(bt)
    ):
        return True
    if "×" in bt:
        factors = _split_top_level(bt, "×")
        if len(factors) >= 2:
            return all(
                (f in _PURE_DATA_BASE_TYPES and f not in shadowed) or f in type_vars
                for f in factors
            )
    head, sep, rest = bt.partition(" ")
    if not sep or head in shadowed:
        return False
    args = _atomic_type_args(rest)
    if not args:
        return False
    if head in _SAFE_TYPECLASS_HEADS:
        return True
    if head in _ALWAYS_INHABITED_CONTAINERS:
        return len(args) == 1
    if head in _PARAM_DATA_CONTAINERS:
        return len(args) == 2 and all(
            ((na := _norm_expr(a)) in _PURE_DATA_BASE_TYPES and na not in shadowed)
            or na in type_vars
            for a in args
        )
    return False


def _is_single_premise_false_elim(
    all_hyps: list[tuple[str, str]],
    target_idx: int,
    extra_binders: list[str] | tuple[str, ...] = (),
    quantifier_binders: tuple[str, ...] = (),
) -> bool:
    """`True` iff `all_hyps[target_idx]` is the sole propositional premise of a `: False`
    refutation (`noConfusion`) theorem, which then states `¬ premise` and is not vacuous:
    `target_idx` binds at most one premise name (rejects `(h1 h2 : false = true)`); every other
    binder in `all_hyps` is a named data / type / safe-typeclass binder
    (`_is_non_prop_binder_type`, type variables tracked in telescope order); no binder (outer or
    inside `quantifier_binders`) rebinds a name the check reads by spelling
    (`_FALSE_ELIM_RESERVED_NAMES`); `extra_binders` holds nothing but safe anonymous instances
    (no untyped or bare binder, no `[Fact P]`, and no `stmt-cut` marker, i.e. the conclusion was
    not cut short at a `|` line); and every binder section in `quantifier_binders` -- all
    quantifiers enclosing the premise's one atom -- consists solely of explicitly typed data /
    type-variable binders checked in telescope order (`∃ x : α, x ≠ x` is one proposition;
    `∃ h : P, ...`, `∃ x ∈ s, ...`, untyped `∃ hp, ...`, and shadowed `∃ (α : Prop) (hp : α), ...`
    are rejected).

    The check sees one theorem header, like every other rule here: hypotheses a `variable` /
    `include` command adds are invisible to it."""
    t_names, _ = all_hyps[target_idx]
    if len(t_names.split()) > 1:
        return False
    for eb in extra_binders:
        if not (eb.startswith("[") and eb.endswith("]") and _is_safe_typeclass_expr(eb[1:-1])):
            return False
    type_vars: set[str] = set()
    for i, (b_names, b_type) in enumerate(all_hyps):
        names = b_names.split()
        for tok in names:
            if tok in _FALSE_ELIM_RESERVED_NAMES:
                return False
        if i == target_idx:
            if quantifier_binders:
                q_tv = set(type_vars)
                q_sh: set[str] = set()
                for q_binders in quantifier_binders:
                    groups = _parse_quantifier_binder_groups(q_binders)
                    if groups is None:
                        return False
                    for g_names, g_type in groups:
                        if g_type is None:
                            return False
                        for tok in g_names:
                            if tok in _FALSE_ELIM_RESERVED_NAMES:
                                return False
                        g_bt = _norm_expr(g_type)
                        if not _is_non_prop_binder_type(
                            g_bt, frozenset(q_tv), shadowed=frozenset(q_sh)
                        ):
                            return False
                        if _is_type_universe(g_bt):
                            q_tv.update(g_names)
                        else:
                            q_tv.difference_update(g_names)
                        q_sh.update(g_names)
            type_vars.difference_update(names)
            continue
        if not names:
            return False
        bt = _norm_expr(b_type)
        if not _is_non_prop_binder_type(bt, frozenset(type_vars)):
            return False
        if _is_type_universe(bt):
            type_vars.update(names)
        else:
            type_vars.difference_update(names)
    return True


_LT_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|(?<![<])<(?![<=|\-$*])")
_GT_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|(?<![->=|*$])>(?![>=])")
_LE_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩⦃⦄]|≤")


def _split_top_level_pat(expr: str, pat: re.Pattern[str]) -> list[str]:
    """Split `expr` at depth-0 matches of `pat` outside `()[]{}⟨⟩⦃⦄` and `«...»`."""
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨⦃":
            depth += 1
        elif t in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


def _is_nonempty_list_literal(s: str) -> bool:
    """`True` iff `s` is a single non-empty `[...]` list literal whose opening `[` closes at
    `len(s) - 1` (excludes `[]` and indexing expressions like `[[], xs][0]`)."""
    if "'" in s:
        s = _neutralize_char_literals(s)
    n = len(s)
    if n <= 2 or s[0] != "[" or s[-1] != "]":
        return False
    depth = 0
    for i, ch in enumerate(s):
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return i == n - 1
    return False


_BOOL_CONTRADICTORY_PAIRS = frozenset(
    (
        ("true", "false"),
        ("false", "true"),
        ("Bool.true", "Bool.false"),
        ("Bool.false", "Bool.true"),
    )
)


def _num_lit_key(lit: str) -> tuple[int, str]:
    """Order-preserving comparison key of a decimal numeral (`_NUM_LIT_RE`) of any length:
    `(significant digit count, significant digits)`. `[adv B3]` `int(lit)` raises `ValueError`
    past `sys.get_int_max_str_digits()` (4300) digits, so `(h : 99...9 = 1)` with a long enough
    literal crashed the scan of its whole file instead of being flagged."""
    if not lit.isascii():
        lit = "".join(str(int(ch)) for ch in lit)
    digits = lit.lstrip("0")
    return len(digits), digits


_FLOAT_TYPE_NAMES = frozenset(("Float", "Float32"))


def _operand_may_be_float(
    e: str,
    float_vars: frozenset[str],
    nat_vars: frozenset[str] = _NO_BOUND_NAMES,
) -> bool:
    """`True` iff normalized operand `e` may denote a `Float` / `Float32` (whose `≤` / `≥` are not
    reflexive: `NaN ≤ NaN` is false): it mentions a `Float`/`Float32` binder, the type / namespace
    `Float`/`Float32` itself (`Float.nan`, `(x : Float)`), or a `...Float` / `...Float32` name that
    is not a `nat_vars` binder and is used as a function:

    - projected: `n.toFloat`, `x.toFloat32`, `x |>.toFloat`;
    - applied in head position: `asFloat v`, `toFloat (x + 1)`, `toFloat ↑n`, `toFloat .zero`,
      `toFloat.{u} n`, `if c then toFloat n else 0`;
    - piped or composed: `toFloat <| n`, `toFloat $ n`, `toFloat <$> o`, `n |> toFloat`,
      `o <&> toFloat`, `toFloat ∘ f`, `f ∘ toFloat`;
    - any of these with the name in parentheses: `(toFloat) n`.

    A `...Float` name that is an infix operand or an argument (`lenFloat`, `lenFloat + 1`,
    `f lenFloat`, `if isFloat then a else b`) reads as a variable, and so does a name that merely
    contains `Float` (`numFloats`, `FloatCount`). The header cannot tell a variable argument from a
    function argument, so `o.map toFloat` reads as a variable too."""
    if not float_vars and "Float" not in e:
        return False
    n_e = len(e)
    for m in _IDENT_EXTRACT_RE.finditer(e):
        tok = m.group(0)
        if tok in float_vars or tok in _FLOAT_TYPE_NAMES:
            return True
        if tok in nat_vars or not (tok.endswith("Float") or tok.endswith("Float32")):
            continue
        lo = m.start()
        hi = m.end()
        if lo > 0 and e[lo - 1] == ".":
            return True
        if e.startswith(".{", hi):
            u_end = e.find("}", hi)
            if u_end != -1:
                hi = u_end + 1
        # `p` / `q`: the nearest non-blank characters around the name, outside any parentheses
        # that hold nothing but the name.
        while True:
            p = lo - 1
            while p >= 0 and e[p] in " \t\r\n":
                p -= 1
            q = hi
            while q < n_e and e[q] in " \t\r\n":
                q += 1
            if p < 0 or q >= n_e or e[p] != "(" or e[q] != ")":
                break
            lo = p
            hi = q + 1
        # `[adv B4]` / `[adv A4]` Recognize preceding right-pipe / composition (`∘`, `|>` excluding
        # `<|>`, and `<&>`) before checking for a following argument or combinator; check whether
        # `tok` is an argument to a preceding head (`f lenFloat <| n`, `«f» lenFloat y`,
        # `f "a" lenFloat y`) before accepting following combinators (`∘`, `$`, `<|` excl. `<|>`, `<$>`).
        if p >= 0 and (
            e[p] == "∘"
            or (e[p] == ">" and p > 0 and e[p - 1] == "|" and (p < 2 or e[p - 2] != "<"))
            or (p >= 2 and e[p - 2 : p + 1] == "<&>")
        ):
            return True
        if q >= n_e:
            continue
        if p >= 0 and (_is_lean_ident_char(e[p]) or e[p] in ")]}⟩⦄»\""):
            # After an identifier or a closing delimiter the name is an argument (`f lenFloat y`),
            # unless that identifier is a keyword (`then toFloat n`).
            w = p + 1
            while w > 0 and _is_lean_ident_char(e[w - 1]):
                w -= 1
            if e[w : p + 1] not in _LEAN_EXPR_KW_STOP:
                continue
        nc = e[q]
        if (
            nc in "∘$"
            or (e.startswith("<|", q) and not e.startswith("<|>", q))
            or e.startswith("<$>", q)
        ):
            return True
        if nc == "(":
            return True
        if q == hi:
            # No blank after the name: an operator or a subscript (`lenFloat+1`, `lenFloat[0]`).
            continue
        if nc in "[{⟨⦃«↑@#`\"" or (nc == "." and q + 1 < n_e and _is_lean_ident_char(e[q + 1])):
            return True
        m_arg = _IDENT_EXTRACT_RE.match(e, q)
        if m_arg is not None:
            if m_arg.group(0) not in _LEAN_EXPR_KW_STOP:
                return True
        elif _is_lean_ident_char(nc):
            # A numeral or a char literal (`toFloat 3`, `toFloat 'a'`).
            return True
    return False


def _check_hypothesis_contradiction(
    hyp_expr: str,
    nat_vars: frozenset[str] = frozenset(),
    float_vars: frozenset[str] = frozenset(),
    *,
    already_norm: bool = False,
) -> str | None:
    """Return a description if `hyp_expr` is a syntactic contradiction, else `None`.

    `nat_vars` are binders of a `Nat`-like type; the vacuous `x < 0` / `0 > x` rule fires only for
    `Nat`-valued operands (`_is_nat_like_operand`). `float_vars` are binders of type `Float` /
    `Float32` (where `NaN ≤ NaN` is false, so `¬ x ≤ x` / `¬ x ≥ x` are satisfiable)."""
    if not already_norm and (
        "=" not in hyp_expr
        and "≠" not in hyp_expr
        and "<" not in hyp_expr
        and "≤" not in hyp_expr
        and ">" not in hyp_expr
        and "≥" not in hyp_expr
        and "False" not in hyp_expr
        and "¬" not in hyp_expr
    ):
        return None
    h = hyp_expr if already_norm else _norm_expr(hyp_expr)
    if not h:
        return None
    # `X → False` (including `X → (False)`) is what `¬ X` unfolds to: read it as the negation it is.
    if "False" in h and h != "False" and ("→" in h or "->" in h):
        denied = _arrow_false_antecedent(h)
        if denied is not None:
            h = f"¬ ({denied})"
    # An expression whose top-level connective is looser than `¬` (`→`, `->`, `↔`, `<->`, `∨`,
    # `\/`, `∧`, `/\`, `<|>`, `<|`, `$`) is an implication/disjunction/iff/conjunction (e.g.
    # `¬ True → α`, `¬ (x = x) ∨ P`, `none = some x → α`), never an atomic single-premise contradiction.
    if _has_top_level_looser_than_not(h):
        return None
    if h == "False":
        return "`False` hypothesis"
    # `[adv B2]` An atom governed by a depth-0 prefix binder / keyword (`∀ x ∈ s, x :: xs = []`,
    # `∀ hp : P, xs.length < 0`, `if c then True else n < 0`) is opaque: `_hyp_atoms` already
    # descended through every quantifier whose domain it could prove inhabited, so what is left
    # may hold vacuously, and the relation splits below would read a relation out of its body.
    # `[adv B3]` The relation checks are pure, so they run first and the prefix-binder scan (a
    # keyword regex over all of `h`) runs only for the rare atom they would flag: same verdict
    # as testing the binder first, without scanning every ordinary hypothesis for keywords.
    reason = _relation_contradiction(h, nat_vars, float_vars)
    if reason is not None and _has_top_level_prefix_binder(h):
        return None
    return reason


def _relation_contradiction(
    h: str, nat_vars: frozenset[str], float_vars: frozenset[str]
) -> str | None:
    """The relation checks of `_check_hypothesis_contradiction` on normalized `h`, which that
    function has already shown has no depth-0 connective looser than `¬` and is not `False`. The
    caller discards the verdict when a depth-0 prefix binder governs `h`."""
    # Once `_has_top_level_looser_than_not(h)` is False, a leading `¬` governs the whole expression:
    # check negated `True` / reflexive `=` / `≤` / `≥` and return without falling through to
    # positive relation checks (which would misread `¬ x :: xs = []` or `¬ x ≠ x`).
    if h.startswith("¬"):
        inner = _norm_expr(h[1:])
        if inner == "True":
            return f"negated `True` hypothesis `{h}`"
        if not _has_top_level_looser_than_not(inner) and not _has_top_level_prefix_binder(inner):
            if "=" in inner:
                eq_sides = _split_top_level_eq(inner)
                if len(eq_sides) == 2 and eq_sides[0] and eq_sides[0] == eq_sides[1]:
                    return f"negated reflexive equality `{h}`"
            for le_op in ("≤", "≥"):
                if le_op in inner:
                    le_sides = _split_top_level(inner, le_op)
                    if (
                        len(le_sides) == 2
                        and le_sides[0]
                        and le_sides[0] == le_sides[1]
                        and not _operand_may_be_float(le_sides[0], float_vars, nat_vars)
                    ):
                        return f"negated reflexive `{le_op}` `{h}`"
        return None

    if h in (
        "true = false",
        "false = true",
        "Bool.true = Bool.false",
        "Bool.false = Bool.true",
    ):
        return f"contradictory boolean equality `{h}`"

    n_h = len(h)
    # Check `lhs ≠ rhs`
    if "≠" in h:
        neq_sides = _split_top_level(h, "≠")
        if len(neq_sides) == 2 and neq_sides[0] and neq_sides[0] == neq_sides[1]:
            return f"irreflexive inequality `{h}`"

    # Check `lhs < rhs` for `x < x`, `< 0`, or numeric `5 < 3`
    lt_i = h.find("<")
    if lt_i != -1:
        # `[adv A3]` When `<` occurs once and `h` cannot end in `0` or a numeral, only `nl == nr`
        # can fire, which requires matching first non-`(`, non-whitespace chars on both sides.
        skip_lt = False
        if h.find("<", lt_i + 1) == -1 and not h.rstrip(") \t\r\n")[-1:].isdecimal():
            lp = 0
            while lp < lt_i and h[lp] in "( \t\r\n":
                lp += 1
            rp = lt_i + 1
            while rp < n_h and h[rp] in "( \t\r\n":
                rp += 1
            if (h[lp] if lp < lt_i else "") != (h[rp] if rp < n_h else ""):
                skip_lt = True
        if not skip_lt:
            lt_sides = _split_single_depth0_op(h, "<", "<", "<=|-$*") or _split_top_level_pat(
                h, _LT_TOP_SPLIT_RE
            )
            if len(lt_sides) == 2:
                nl, nr = lt_sides
                if nl and nl == nr:
                    return f"irreflexive strict inequality `{h}`"
                if nr == "0" and _is_nat_like_operand(nl, nat_vars):
                    return f"vacuous `< 0` bound `{h}`"
                if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and _num_lit_key(nl) >= _num_lit_key(nr):
                    return f"contradictory numeric inequality `{nl} < {nr}`"

    # Check `lhs ≤ rhs` for numeric `5 ≤ 3` (`[adv A3]` only numerals can clash, so after stripping
    # outer parens/spaces both ends must be decimal digits).
    if (
        "≤" in h
        and (h[0].isdecimal() or (h[0] == "(" and h.lstrip("( \t\r\n")[:1].isdecimal()))
        and (h[-1].isdecimal() or (h[-1] == ")" and h.rstrip(") \t\r\n")[-1:].isdecimal()))
    ):
        le_sides = _split_single_depth0_op(h, "≤", "", "") or _split_top_level_pat(
            h, _LE_TOP_SPLIT_RE
        )
        if len(le_sides) == 2:
            nl, nr = le_sides
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and _num_lit_key(nl) > _num_lit_key(nr):
                return f"contradictory numeric inequality `{nl} ≤ {nr}`"

    # Check `lhs ≥ rhs` for numeric `3 ≥ 5` (`[adv B2]` / `[adv A3]` numeric endpoint guard)
    if (
        "≥" in h
        and (h[0].isdecimal() or (h[0] == "(" and h.lstrip("( \t\r\n")[:1].isdecimal()))
        and (h[-1].isdecimal() or (h[-1] == ")" and h.rstrip(") \t\r\n")[-1:].isdecimal()))
    ):
        ge_sides = _split_single_depth0_op(h, "≥", "", "") or _split_top_level(h, "≥")
        if len(ge_sides) == 2:
            nl, nr = ge_sides
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and _num_lit_key(nl) < _num_lit_key(nr):
                return f"contradictory numeric inequality `{nl} ≥ {nr}`"

    # Check `lhs > rhs` for `x > x`, `0 > n`, or numeric `3 > 5`
    gt_i = h.find(">")
    if gt_i != -1:
        skip_gt = False
        if h.find(">", gt_i + 1) == -1 and not h.lstrip("( \t\r\n")[:1].isdecimal():
            lp = 0
            while lp < gt_i and h[lp] in "( \t\r\n":
                lp += 1
            rp = gt_i + 1
            while rp < n_h and h[rp] in "( \t\r\n":
                rp += 1
            if (h[lp] if lp < gt_i else "") != (h[rp] if rp < n_h else ""):
                skip_gt = True
        if not skip_gt:
            gt_sides = _split_single_depth0_op(h, ">", "->=|*$", ">=") or _split_top_level_pat(
                h, _GT_TOP_SPLIT_RE
            )
            if len(gt_sides) == 2:
                nl, nr = gt_sides
                if nl and nl == nr:
                    return f"irreflexive strict inequality `{h}`"
                if nl == "0" and _is_nat_like_operand(nr, nat_vars):
                    return f"vacuous `0 > ...` bound `{h}`"
                if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and _num_lit_key(nl) <= _num_lit_key(nr):
                    return f"contradictory numeric inequality `{nl} > {nr}`"

    # Check `lhs = rhs`. `[adv B3]` / `[adv A3]` Every clash below needs BOTH complementary
    # constructor tokens (`none`+`some`, `[]`+`::`/second `[`, `.inl`+`.inr`, `.ok`+`.error`,
    # `true`+`false`) or numerals on both sides (first/last non-paren char is a decimal digit).
    if "=" in h and (
        ("none" in h and "some" in h)
        or ("[]" in h and ("::" in h or h.count("[") >= 2))
        or (".inl" in h and ".inr" in h)
        or (".ok" in h and ".error" in h)
        or ("true" in h and "false" in h)
        or (
            (h[0].isdecimal() or (h[0] == "(" and h.lstrip("( \t\r\n")[:1].isdecimal()))
            and (h[-1].isdecimal() or (h[-1] == ")" and h.rstrip(") \t\r\n")[-1:].isdecimal()))
        )
    ):
        eq_sides = _split_top_level_eq(h)
        if len(eq_sides) == 2:
            nl, nr = eq_sides
            if (nl, nr) in _BOOL_CONTRADICTORY_PAIRS:
                return f"contradictory boolean equality `{nl} = {nr}`"
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and _num_lit_key(nl) != _num_lit_key(nr):
                return f"distinct numeric literal equality `{nl} = {nr}`"
            if (
                nl in ("none", "Option.none")
                and (nr in ("some", "Option.some") or nr.startswith(("some ", "Option.some ")))
                and not _has_depth0_high_prec_infix(nr)
            ) or (
                nr in ("none", "Option.none")
                and (nl in ("some", "Option.some") or nl.startswith(("some ", "Option.some ")))
                and not _has_depth0_high_prec_infix(nl)
            ):
                return f"disjoint `Option` constructor equality `{h}`"
            if (
                nl == "[]"
                and (
                    (
                        "::" in nr
                        and len(_split_top_level(nr, "::")) >= 2
                        and not _has_depth0_looser_than_cons(nr)
                    )
                    or _is_nonempty_list_literal(nr)
                )
            ) or (
                nr == "[]"
                and (
                    (
                        "::" in nl
                        and len(_split_top_level(nl, "::")) >= 2
                        and not _has_depth0_looser_than_cons(nl)
                    )
                    or _is_nonempty_list_literal(nl)
                )
            ):
                return f"disjoint `List` constructor equality `{h}`"
            if (
                (nl in (".inl", "Sum.inl") or nl.startswith((".inl ", "Sum.inl ")))
                and (nr in (".inr", "Sum.inr") or nr.startswith((".inr ", "Sum.inr ")))
                and not _has_depth0_high_prec_infix(nl)
                and not _has_depth0_high_prec_infix(nr)
            ) or (
                (nr in (".inl", "Sum.inl") or nr.startswith((".inl ", "Sum.inl ")))
                and (nl in (".inr", "Sum.inr") or nl.startswith((".inr ", "Sum.inr ")))
                and not _has_depth0_high_prec_infix(nl)
                and not _has_depth0_high_prec_infix(nr)
            ):
                return f"disjoint `Sum` constructor equality `{h}`"
            if (
                (nl in (".ok", "Except.ok") or nl.startswith((".ok ", "Except.ok ")))
                and (nr in (".error", "Except.error") or nr.startswith((".error ", "Except.error ")))
                and not _has_depth0_high_prec_infix(nl)
                and not _has_depth0_high_prec_infix(nr)
            ) or (
                (nr in (".ok", "Except.ok") or nr.startswith((".ok ", "Except.ok ")))
                and (nl in (".error", "Except.error") or nl.startswith((".error ", "Except.error ")))
                and not _has_depth0_high_prec_infix(nl)
                and not _has_depth0_high_prec_infix(nr)
            ):
                return f"disjoint `Except` constructor equality `{h}`"

    return None


def _float_vars_before(all_hyps: list[tuple[str, str]], limit_idx: int) -> frozenset[str]:
    """Binders in `all_hyps[:limit_idx]` whose current unshadowed type in telescope order is
    `Float` or `Float32`."""
    cur_float: set[str] = set()
    shadowed: set[str] = set()
    for b_names, b_type in all_hyps[:limit_idx]:
        names = b_names.split()
        if not names:
            continue
        bt = _norm_expr(b_type)
        if bt in _FLOAT_TYPE_NAMES and bt not in shadowed:
            cur_float.update(names)
        else:
            cur_float.difference_update(names)
        shadowed.update(names)
    return frozenset(cur_float)


def _nat_vars_before(all_hyps: list[tuple[str, str]], limit_idx: int) -> frozenset[str]:
    """Binders in `all_hyps[:limit_idx]` whose current unshadowed type in telescope order is
    `Nat`-like (`_NAT_LIKE_TYPES` or `Fin ...`)."""
    cur_nat: set[str] = set()
    shadowed: set[str] = set()
    for b_names, b_type in all_hyps[:limit_idx]:
        names = b_names.split()
        if not names:
            continue
        bt = _norm_expr(b_type)
        if (bt in _NAT_LIKE_TYPES and bt not in shadowed) or (
            bt.startswith("Fin ") and "Fin" not in shadowed
        ):
            cur_nat.update(names)
        else:
            cur_nat.difference_update(names)
        shadowed.update(names)
    return frozenset(cur_nat)


_QUANT_RESERVED_NAMES = _FALSE_ELIM_RESERVED_NAMES | frozenset(("Fin",))
_DEP_DOM_COLON_RE = re.compile(
    r"«[^»]*»|" + _SCAN_CHAR_LIT_ALT + "|" + _SCAN_BRACKET_ALTS + r"|(?<!:):(?![=:])"
)


def _find_depth0_colon(expr: str) -> int:
    """Offset of the first depth-0 standalone `:` (not `:=` or `::`) in `expr`, or `-1`."""
    if ":" not in expr:
        return -1
    depth = 0
    for m in _DEP_DOM_COLON_RE.finditer(expr):
        t = m.group(0)
        c0 = t[0]
        if c0 == "«" or c0 == "'":
            continue
        if c0 in "([{⟨⦃":
            depth += 1
        elif c0 in ")]}⟩⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return m.start()
    return -1


def _quantifier_context_before(
    all_hyps: list[tuple[str, str]], limit_idx: int, need_fn_domains: bool = True
) -> tuple[frozenset[str], dict[str, tuple[bool, ...]]]:
    """Return `(shadowed_reserved, fn_domains)` in scope right before `all_hyps[limit_idx]`,
    tracked in telescope order: `shadowed_reserved` are reserved data/container/typeclass names
    (and `Fin`) rebound by earlier binders; `fn_domains` maps each earlier arrow-typed binder to a
    tuple of booleans recording whether each leading explicit domain type (stopping before any
    implicit/strict-implicit/instance domain `{...}`/`⦃...⦄`/`[...]` or default parameter
    `(x : T := v)`, which can be omitted at call sites) is unconditionally inhabited (left empty
    when `need_fn_domains` is false)."""
    if not need_fn_domains:
        shadowed_fast: set[str] = set()
        for b_names, _ in all_hyps[:limit_idx]:
            if not b_names:
                continue
            if " " not in b_names and "\t" not in b_names and "\n" not in b_names:
                if b_names in _QUANT_RESERVED_NAMES:
                    shadowed_fast.add(b_names)
            else:
                for tok in b_names.split():
                    if tok in _QUANT_RESERVED_NAMES:
                        shadowed_fast.add(tok)
        return (frozenset(shadowed_fast) if shadowed_fast else _NO_BOUND_NAMES), {}
    shadowed: set[str] = set()
    fn_domains: dict[str, tuple[bool, ...]] = {}
    for b_names, b_type in all_hyps[:limit_idx]:
        if not b_names:
            continue
        names = b_names.split() if (" " in b_names or "\t" in b_names or "\n" in b_names) else (b_names,)
        dom_flags: tuple[bool, ...] = ()
        if "→" in b_type or "->" in b_type:
            doms = _top_level_arrow_domains(b_type)
            flags: list[bool] = []
            cur_sh = set(shadowed)
            for d in doms:
                if not d or d[0] in "{⦃[":
                    break
                col = _find_depth0_colon(d)
                if col != -1:
                    # `[adv A4]` Dependent-arrow domain `(x y : T)` contributes one positional slot
                    # per bound name and brings those names into scope for all later domains of
                    # this arrow type (preventing both slot-shift on `(x y : Nat) → Fin 0 → Nat → Prop`
                    # and unshadowed type reads on `(Nat : Type) → Nat → Prop`).
                    names_raw = d[:col].strip()
                    t_raw = d[col + 1 :].strip()
                    if (
                        not t_raw
                        or _BARE_BINDER_NAMES_RE.fullmatch(names_raw) is None
                        or (":=" in t_raw and _strip_binder_default(t_raw) != t_raw)
                    ):
                        break
                    param_names = names_raw.split()
                    sh_snap = frozenset(cur_sh) if cur_sh else _NO_BOUND_NAMES
                    is_inhab = _is_non_prop_binder_type(t_raw, _NO_BOUND_NAMES, shadowed=sh_snap)
                    flags.extend([is_inhab] * len(param_names))
                    cur_sh.update(param_names)
                else:
                    sh_snap = frozenset(cur_sh) if cur_sh else _NO_BOUND_NAMES
                    flags.append(_is_non_prop_binder_type(d, _NO_BOUND_NAMES, shadowed=sh_snap))
            if flags:
                dom_flags = tuple(flags)
        for tok in names:
            if dom_flags:
                fn_domains[tok] = dom_flags
            else:
                fn_domains.pop(tok, None)
            if tok in _QUANT_RESERVED_NAMES:
                shadowed.add(tok)
    return (frozenset(shadowed) if shadowed else _NO_BOUND_NAMES), fn_domains


def _record_pos_neg_atom(part: str, pos_set: set[str], neg_set: set[str]) -> None:
    """Record normalized `part` and any proposition it denies (`¬ X`, `X → False`, `a ≠ b`,
    symmetric on `=`/`≠`) into `pos_set` / `neg_set`. Never split on `=`/`≠` inside an expression
    governed by a depth-0 prefix binder (`∀ x ∈ s, a = b`, `if c then True else a ≠ b`)."""
    denied = _negated_operand(part)
    if denied is not None:
        neg_set.add(denied)
        if (
            "=" in denied
            and not _has_top_level_looser_than_not(denied)
            and not _has_top_level_prefix_binder(denied)
        ):
            d_eq = _split_top_level_eq(denied)
            if len(d_eq) == 2 and d_eq[0] and d_eq[1]:
                neg_set.add(f"{d_eq[0]} = {d_eq[1]}")
                neg_set.add(f"{d_eq[1]} = {d_eq[0]}")
    elif (
        "≠" in part
        and not _has_top_level_looser_than_not(part)
        and not _has_top_level_prefix_binder(part)
    ):
        neq_sides = _split_top_level(part, "≠")
        if len(neq_sides) == 2 and neq_sides[0] and neq_sides[1]:
            neg_set.add(f"{neq_sides[0]} = {neq_sides[1]}")
            neg_set.add(f"{neq_sides[1]} = {neq_sides[0]}")
    elif (
        "=" in part
        and not _has_top_level_looser_than_not(part)
        and not _has_top_level_prefix_binder(part)
    ):
        eq_sides = _split_top_level_eq(part)
        if len(eq_sides) == 2 and eq_sides[0] and eq_sides[1]:
            pos_set.add(f"{eq_sides[0]} = {eq_sides[1]}")
    pos_set.add(part)


def _audit_lean_theorem(
    name: str,
    line: int,
    meta: dict[str, str],
    hyps: list[tuple[str, str]],
    conclusion: str,
    contradiction_only: bool = False,
    extra_binders: list[str] | tuple[str, ...] = (),
) -> list[WaiverPinFinding]:
    """Run all 5 `TRIVIAL_PROOF` and 3-axis metadata checks on a Lean `theorem`/`lemma`.

    With `contradiction_only`, only the hypothesis-contradiction check (step 2) runs, and only
    over named hypotheses (binders such as `(h : False)` / `(h : 0 = 1)` and named `∀`
    binders; anonymous `→` premises are left to the full audit): the scope applied to
    unannotated theorems by default, where a `True` / reflexive conclusion may be a
    deliberate smoke or sanity lemma but an explicitly assumed, syntactically unsatisfiable
    hypothesis is always a vacuity hazard.
    """
    all_hyps = hyps
    if contradiction_only:
        indexed_hyps = [(idx, h) for idx, h in enumerate(all_hyps) if h[0]]
        hyps = [h for _, h in indexed_hyps]
    else:
        indexed_hyps = enumerate(all_hyps)  # consumed once, by the contradiction loop below
    findings: list[WaiverPinFinding] = []
    norm_conc = "" if contradiction_only else _norm_expr(conclusion)
    is_false_conc = (
        norm_conc == "False"
        if not contradiction_only
        else ("False" in conclusion and _norm_expr(conclusion) == "False")
    )

    if meta:
        kind_raw = meta.get("kind", "")
        witness_raw = meta.get("witness", "")
        assumes_raw = meta.get("assumes", "")
        subject_raw = meta.get("subject", "")
        kind = kind_raw.lower() if kind_raw else ""
        witness = witness_raw.lower() if witness_raw else ""
        canon_tier = VALID_3AXIS_ASSUMES.get(assumes_raw, "")
    else:
        kind_raw = witness_raw = assumes_raw = subject_raw = kind = witness = canon_tier = ""

    # 1. Validate 3-axis metadata values and tier/witness consistency (`RULE_TIER_ASSUMPTION_MISMATCH`)
    if kind_raw and kind not in VALID_3AXIS_KINDS:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid 3-axis `Kind: {kind_raw}` "
                    f"(expected one of {sorted(VALID_3AXIS_KINDS)})."
                ),
                suggestion="Set `Kind:` to `safety`, `refinement`, `divergence`, `codec`, or `helper`.",
            )
        )

    if witness_raw and witness not in VALID_3AXIS_WITNESSES:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid or vacuous 3-axis `Witness: {witness_raw}` "
                    f"(expected one of {sorted(VALID_3AXIS_WITNESSES)})."
                ),
                suggestion="Use `Witness: universal`, `Witness: exists-sat`, or `Witness: negative`.",
            )
        )

    if assumes_raw and not canon_tier:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TIER_ASSUMPTION_MISMATCH,
                line=line,
                symbol=name,
                message=(
                    f"Theorem `{name}` declares invalid 3-axis `Assumes: {assumes_raw}` "
                    "(expected `S0`, `S1`, `S2`, `S3`, or `TCB`)."
                ),
                suggestion="Set `Assumes:` to `S0`, `S1`, `S2`, or `S3` matching the theorem's trust hypotheses.",
            )
        )

    # Hypotheses are joined once with " ; " (never part of an identifier), so a substring test on the
    # joined text equals `any(substring in t for t in hyps)` for every identifier-like trigger below.
    all_hyps_text = " ; ".join([t for _, t in hyps])
    if canon_tier == "S0" and (
        ".rust" in all_hyps_text
        or "AdtRepr.rust" in all_hyps_text
        or "reprRust" in name
        or "canonicalRust" in name
        or "evalConst" in all_hyps_text
        or "compileTimeError" in all_hyps_text
    ):
        # Check if an `S0` theorem secretly pins canonical zero-padding on `#[repr(Rust)]` without an evalConst guard
        mentions_rust_repr = (
            ".rust" in all_hyps_text
            or "AdtRepr.rust" in all_hyps_text
            or "reprRust" in name
            or "canonicalRust" in name
        )
        pins_zero_pad = mentions_rust_repr and (
            "paddingFree 0" in all_hyps_text
            or "adtPad = fun _ => 0" in all_hyps_text
            or "adtPad = (fun _ => 0)" in all_hyps_text
            or "hasPinnedCoupledWaiver" in all_hyps_text
            or "pad0 = 0" in all_hyps_text
            or "totalPad = 0" in all_hyps_text
            or ("rustOrderCanonical" in all_hyps_text
                and _RUST_ORDER_CANON_RE.search(all_hyps_text) is not None)
        )
        has_const_guard = (
            "evalConst" in all_hyps_text
            or "compileTimeError" in all_hyps_text
        )
        if pins_zero_pad and not has_const_guard:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier="S0",
                    message=(
                        f"Theorem `{name}` claims `Assumes: S0`, but its hypotheses pin canonical "
                        "zero-padding (`paddingFree` / `rustOrderCanonical` / `adtPad = 0`) on `#[repr(Rust)]`."
                    ),
                    suggestion="Change `Assumes: S0` to `Assumes: S3` (or universalize over all `ValidStructLayoutWorld`).",
                )
            )
        if has_const_guard and "≠ .compileTimeError" in all_hyps_text:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier="S0",
                    message=(
                        f"Theorem `{name}` claims `Assumes: S0`, but assumes a non-`.compileTimeError` "
                        "compile-time guard premise (`S1`)."
                    ),
                    suggestion="Change `Assumes: S0` to `Assumes: S1`.",
                )
            )

    if witness == "exists-sat":
        if "∃" not in norm_conc and "Exists" not in norm_conc and "NonEmpty" not in norm_conc:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Theorem `{name}` declares `Witness: exists-sat`, but its conclusion "
                        f"`{norm_conc}` is not an existential witness (`∃ ...`)."
                    ),
                    suggestion="State an existential conclusion `∃ ...` or change `Witness:` to `universal`.",
                )
            )
    elif witness == "negative":
        is_neg_conc = (
            norm_conc.startswith("¬")
            or "¬ " in norm_conc
            or "≠" in norm_conc
            or "= none" in norm_conc
            or "= false" in norm_conc
            or "= .ub" in norm_conc
            or "= .compileTimeError" in norm_conc
            or norm_conc == "False"
        )
        if not is_neg_conc:
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TIER_ASSUMPTION_MISMATCH,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Theorem `{name}` declares `Witness: negative`, but its conclusion "
                        f"`{norm_conc}` contains no negation or rejection predicate."
                    ),
                    suggestion="Ensure the conclusion states a rejection (`¬ ...`, `≠`, `= none`, `= false`) or change `Witness:`.",
                )
            )

    # 2. Check hypotheses for syntactic contradiction (`RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS`)
    conc_sp = norm_conc.find(" ")
    conc_head = (norm_conc if conc_sp == -1 else norm_conc[:conc_sp]).lstrip("(¬")
    # `X → False` denies `X` exactly as `¬ X` does, so an arrow into `False` counts as a negation.
    has_non_eq_neg = "¬" in all_hyps_text or (
        "False" in all_hyps_text and ("→" in all_hyps_text or "->" in all_hyps_text)
    )
    has_neq = "≠" in all_hyps_text
    any_neg = has_non_eq_neg or has_neq
    seen_pos_hyps: set[str] = set()
    seen_neg_hyps: set[str] = set()
    scoped_contradictions: set[str] = set()
    tautology_hit = False

    has_lt_all = "<" in all_hyps_text
    has_le_all = "≤" in all_hyps_text
    has_gt_all = ">" in all_hyps_text
    has_ge_all = "≥" in all_hyps_text
    has_false_all = "False" in all_hyps_text
    has_not_all = "¬" in all_hyps_text
    has_any_ineq_or_neg_in_all = (
        any_neg
        or has_lt_all
        or has_le_all
        or has_gt_all
        or has_ge_all
        or has_false_all
    )
    has_eq_in_all = "=" in all_hyps_text
    conc_head_in_all = bool(conc_head and conc_head in all_hyps_text)

    has_float_in_all = "Float" in all_hyps_text
    len_norm_conc = len(norm_conc)
    if has_any_ineq_or_neg_in_all or has_eq_in_all or conc_head_in_all:
        for orig_idx, (_, t) in indexed_hyps:
            has_ineq_or_neg = has_any_ineq_or_neg_in_all and (
                (has_lt_all and "<" in t)
                or (has_le_all and "≤" in t)
                or (has_neq and "≠" in t)
                or (has_not_all and "¬" in t)
                or (has_gt_all and ">" in t)
                or (has_ge_all and "≥" in t)
                or (has_false_all and "False" in t)
            )
            has_eq = has_eq_in_all and "=" in t
            may_taut = (
                not tautology_hit
                and conc_head_in_all
                and len(t) >= len_norm_conc
                and conc_head in t
            )
            if not has_ineq_or_neg and not has_eq and not has_non_eq_neg and not may_taut:
                continue
            # If the only trigger in `t` is `=`, and there are no `¬`/`≠` hypotheses in the theorem,
            # check whether `t` can possibly be a constructor/literal equality clash (`[adv A3]`:
            # require both complementary constructor tokens or numeral endpoints on atomic `=`,
            # skipping `_norm_expr` / `_check_hypothesis_contradiction` on equations like `x₀ = y`).
            eq_can_clash = has_eq and (
                any_neg
                or ("false" in t and "true" in t)
                or ("none" in t and "some" in t)
                or ("[]" in t and ("::" in t or t.count("[") >= 2))
                or (".inl" in t and ".inr" in t)
                or (".ok" in t and ".error" in t)
                or (
                    _DIGIT_SEARCH(t) is not None
                    and (
                        "∧" in t
                        or "/\\" in t
                        or "∃" in t
                        or "∀" in t
                        or "exists" in t
                        or "forall" in t
                        or (t[0] in "({⦃" and ":" in t and ("→" in t or "->" in t))
                        or (
                            t.lstrip("( \t\r\n")[:1].isdecimal()
                            and t.rstrip(") \t\r\n")[-1:].isdecimal()
                        )
                    )
                )
            )
            if not has_ineq_or_neg and not has_non_eq_neg and not eq_can_clash and not may_taut:
                continue
            nh = _norm_expr(t)
            if may_taut and nh and nh == norm_conc:
                tautology_hit = True
            if not nh or (not has_ineq_or_neg and not has_non_eq_neg and not eq_can_clash):
                continue
            if "'" in nh:
                nh = _neutralize_char_literals(nh)
            if any_neg:
                seen_pos_hyps.add(nh)
            atoms: list[
                tuple[str, frozenset[str], tuple[str, ...], frozenset[str], tuple[int, ...]]
            ] = []
            scope_binds: dict[tuple[int, ...], frozenset[str]] | None = None
            q_float_vars_out: dict[tuple[int, ...], frozenset[str]] | None = None
            has_conj = "∧" in nh or "/\\" in nh
            nh0 = nh[0]
            has_top_quant = (
                nh0 in "∃∀"
                or (nh0 == "f" and nh.startswith("forall"))
                or (nh0 == "e" and nh.startswith("exists"))
                or (nh0 in "({⦃" and ":" in nh and ("→" in nh or "->" in nh))
            )
            if has_conj or has_top_quant:
                has_forall = "∀" in nh or "forall" in nh
                # `[adv A4]` Conjunct-nested dependent arrows (`P ∧ ((x : Float) → ¬ x ≤ x)`,
                # `P ∧ ((x : Nat) → False)` with shadowed `Nat`) also descend inside `_hyp_atoms`
                # and need `shadowed`, `scope_binds`, and `q_float_vars_out`.
                has_quant = (
                    has_top_quant
                    or has_forall
                    or "∃" in nh
                    or "exists" in nh
                    or (":" in nh and ("→" in nh or "->" in nh))
                )
                if has_quant:
                    scope_binds = {}
                    if "Float" in nh:
                        q_float_vars_out = {}
                    q_shadowed, _ = _quantifier_context_before(all_hyps, orig_idx, False)
                    fn_loader = (
                        (lambda oi=orig_idx: _quantifier_context_before(all_hyps, oi, True)[1])
                        if has_forall
                        else None
                    )
                    _hyp_atoms(
                        nh,
                        _NO_BOUND_NAMES,
                        (),
                        _NO_BOUND_NAMES,
                        (),
                        atoms,
                        shadowed=q_shadowed,
                        fn_domains_loader=fn_loader,
                        scope_binds=scope_binds,
                        q_float_vars_out=q_float_vars_out,
                    )
                else:
                    _hyp_atoms(nh, _NO_BOUND_NAMES, (), _NO_BOUND_NAMES, (), atoms)
            else:
                atoms.append((nh, _NO_BOUND_NAMES, (), _NO_BOUND_NAMES, ()))
            hyp_nat_vars: frozenset[str] | None = None
            hyp_float_vars: frozenset[str] | None = None
            local_pos: dict[tuple[int, ...], set[str]] | None = None
            local_neg: dict[tuple[int, ...], set[str]] | None = None
            for part, bound, q_chain, q_nat_vars, scope_path in atoms:
                if (
                    "=" in part
                    or "≠" in part
                    or "<" in part
                    or "≤" in part
                    or ">" in part
                    or "≥" in part
                    or "False" in part
                    or "¬" in part
                ):
                    is_neg_le_ge = ("≤" in part or "≥" in part) and (
                        "¬" in part or ("False" in part and ("→" in part or "->" in part))
                    )
                    # `[adv B3]` / `[adv A3]` `Nat` binders matter to `... < 0`, `0 > ...`, and
                    # distinguishing a `Nat` binder named `*Float` from a `Float` conversion.
                    if hyp_nat_vars is None and (
                        ("<" in part and part[-1] in "0)")
                        or (">" in part and part[0] in "0(")
                        or (is_neg_le_ge and "Float" in part)
                    ):
                        hyp_nat_vars = _nat_vars_before(all_hyps, orig_idx)
                    part_nat_vars = hyp_nat_vars or _NO_BOUND_NAMES
                    if bound:
                        # A quantifier may rebind a `Nat` binder's name at another type, or bind
                        # its own `Nat`-typed variable (`∃ n : Nat, n < 0`).
                        part_nat_vars = (part_nat_vars - bound) | q_nat_vars
                    part_float_vars = _NO_BOUND_NAMES
                    if has_float_in_all and is_neg_le_ge:
                        if hyp_float_vars is None:
                            hyp_float_vars = _float_vars_before(all_hyps, orig_idx)
                        part_float_vars = hyp_float_vars
                        if bound:
                            q_fv = (
                                q_float_vars_out.get(scope_path, _NO_BOUND_NAMES)
                                if q_float_vars_out is not None
                                else _NO_BOUND_NAMES
                            )
                            part_float_vars = (part_float_vars - bound) | q_fv
                    reason = _check_hypothesis_contradiction(
                        part, part_nat_vars, part_float_vars, already_norm=True
                    )
                    # A `: False` theorem whose only premise is one atomic contradiction states
                    # the negation of that premise: it is a refutation, not a vacuous claim.
                    if (
                        reason is not None
                        and is_false_conc
                        and len(atoms) == 1
                        and _is_simple_refutation_premise(part)
                        and _is_single_premise_false_elim(
                            all_hyps, orig_idx, extra_binders, q_chain
                        )
                    ):
                        reason = None
                    if reason is not None:
                        findings.append(
                            WaiverPinFinding(
                                rule=RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                                line=line,
                                symbol=name,
                                tier=canon_tier,
                                message=(
                                    f"Vacuous theorem `{name}`: hypothesis contains {reason}, "
                                    "making the implication vacuously true."
                                ),
                                suggestion="Remove the contradictory hypothesis and prove the theorem over inhabited premises.",
                            )
                        )
                if not any_neg:
                    # `[adv B3]` No `¬`, `≠` or `→ False` in any hypothesis: nothing can ever be
                    # recorded as denied, so every pos/neg intersection below is empty.
                    continue
                if bound and not bound.isdisjoint(_IDENT_EXTRACT_RE.findall(part)):
                    # Mentions a quantified variable: not a fact about the theorem's own context,
                    # but contradictory conjuncts in the same quantifier scope (or an outer
                    # ancestor scope whose bound variables are not rebound along the path) share
                    # the same witness/value and still contradict each other.
                    if scope_path:
                        if local_pos is None:
                            local_pos = {}
                            local_neg = {}
                        lp = local_pos.setdefault(scope_path, set())
                        ln = local_neg.setdefault(scope_path, set())
                        _record_pos_neg_atom(part, lp, ln)
                    continue
                _record_pos_neg_atom(part, seen_pos_hyps, seen_neg_hyps)
            if local_pos is not None and local_neg is not None:
                for sp, lp in local_pos.items():
                    scoped_contradictions.update(lp & local_neg[sp])
                    if len(sp) > 1 and scope_binds:
                        rebound: set[str] = set()
                        for k in range(len(sp) - 1, 0, -1):
                            rebound.update(scope_binds.get(sp[: k + 1], _NO_BOUND_NAMES))
                            anc = sp[:k]
                            anc_pos = local_pos.get(anc)
                            if anc_pos:
                                for atom in anc_pos & local_neg[sp]:
                                    if rebound.isdisjoint(_IDENT_EXTRACT_RE.findall(atom)):
                                        scoped_contradictions.add(atom)
                            anc_neg = local_neg.get(anc)
                            if anc_neg:
                                for atom in anc_neg & lp:
                                    if rebound.isdisjoint(_IDENT_EXTRACT_RE.findall(atom)):
                                        scoped_contradictions.add(atom)

        contradictory_pairs = (seen_pos_hyps & seen_neg_hyps) | scoped_contradictions
        if contradictory_pairs:
            sample_p = sorted(contradictory_pairs)[0]
            findings.append(
                WaiverPinFinding(
                    rule=RULE_SYNTACTIC_CONTRADICTION_HYPOTHESIS,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Vacuous theorem `{name}`: hypotheses simultaneously assume `{sample_p}` and its negation."
                    ),
                    suggestion="Remove the mutually contradictory hypotheses.",
                )
            )

    if contradiction_only:
        return findings

    # 3. Check conclusion for `True`, reflexive `lhs = lhs` / `lhs ≤ lhs` / `lhs ↔ lhs`,
    #    conjunctions of trivial facts, or disjunctions with a trivial disjunct (`RULE_TRIVIAL_CONCLUSION`).
    #    `helper` lemmas and `negative` witnesses (whose point is a rejection) are exempt.
    if kind != "helper" and witness != "negative":
        has_quote_conc = "'" in norm_conc
        conc_check = _neutralize_char_literals(norm_conc) if has_quote_conc else norm_conc
        conc_float_vars = (
            _float_vars_before(all_hyps, len(all_hyps))
            if ("≤" in conc_check and has_float_in_all)
            else _NO_BOUND_NAMES
        )
        if "∧" in conc_check and _all_conjuncts_trivial(conc_check, conc_float_vars):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Trivial conclusion in theorem `{name}`: every conjunct of `{norm_conc}` is "
                        "trivially true (`True`, `¬ False`, or a reflexive `=` / `↔` / `≤`)."
                    ),
                    suggestion="State the actual semantic postcondition or codec/layout property in the conclusion.",
                )
            )
        elif "∨" in conc_check and _any_disjunct_trivial(conc_check, conc_float_vars):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=(
                        f"Trivial disjunctive conclusion in theorem `{name}`: `{norm_conc}` contains "
                        "a trivially true disjunct (`True`, `¬ False`, or reflexive `=` / `↔` / `≤`)."
                    ),
                    suggestion="Remove the trivial disjunct or replace `∨` with `∧`.",
                )
            )
        elif (
            "∧" not in conc_check
            and "∨" not in conc_check
            and _is_trivially_true(conc_check, conc_float_vars, already_norm=not has_quote_conc)
        ):
            findings.append(
                WaiverPinFinding(
                    rule=RULE_TRIVIAL_CONCLUSION,
                    line=line,
                    symbol=name,
                    tier=canon_tier,
                    message=f"Trivial conclusion in theorem `{name}`: `{norm_conc}` is trivially true.",
                    suggestion="Replace the trivial/reflexive conclusion with a non-trivial equivalence or invariant.",
                )
            )

    # 4. Check tautological implication (`RULE_TAUTOLOGICAL_IMPLICATION`)
    if tautology_hit:
        findings.append(
            WaiverPinFinding(
                rule=RULE_TAUTOLOGICAL_IMPLICATION,
                line=line,
                symbol=name,
                tier=canon_tier,
                message=(
                    f"Tautological implication in theorem `{name}`: conclusion `{norm_conc}` "
                    "is identical to an explicit hypothesis."
                ),
                suggestion="Strengthen the conclusion or remove the redundant hypothesis that assumes the goal.",
            )
        )

    # 5. Check unused subject in conclusion (`RULE_UNUSED_SUBJECT_IN_CONCLUSION`)
    if subject_raw:
        if subject_raw in conclusion or subject_raw in norm_conc:
            in_conc = True
        else:
            subj_short = subject_raw.split(".")[-1]
            in_conc = subj_short in conclusion or subj_short in norm_conc
        if not in_conc:
            subj_short = subject_raw.split(".")[-1]
            conc_idents = set(_IDENT_EXTRACT_RE.findall(norm_conc))
            connected_via_hyp = False
            for b_names, h_type in hyps:
                if subject_raw in h_type or subj_short in h_type:
                    hyp_vars = {
                        tok
                        for tok in _IDENT_EXTRACT_RE.findall(b_names + " " + h_type)
                        if tok != subj_short
                        and not tok.startswith("h")
                        and tok not in _DATA_TYPE_WORDS
                        and len(tok) >= 1
                        and tok[0].islower()
                    }
                    if hyp_vars & conc_idents:
                        connected_via_hyp = True
                        break
            if not connected_via_hyp:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_UNUSED_SUBJECT_IN_CONCLUSION,
                        line=line,
                        symbol=name,
                        tier=canon_tier,
                        message=(
                            f"Theorem `{name}` declares `Subject: {subject_raw}`, but its conclusion "
                            f"`{norm_conc}` never references `{subject_raw}` or its constrained state."
                        ),
                        suggestion=f"Constrain `{subject_raw}` in the theorem conclusion or update `Subject:`.",
                    )
                )
    elif kind in ("safety", "refinement", "divergence", "codec"):
        domain_binder_vars: list[str] = []
        all_value_vars: list[str] = []
        for b_names, b_type in hyps:
            if not b_names:
                continue
            if _REL_OP_SEARCH(b_type) is not None:
                continue
            is_primitive = b_type.strip().strip("()").strip() in _DATA_TYPE_WORDS
            for tok in b_names.split():
                tok_clean = tok.strip("()[]{}")
                if (
                    tok_clean
                    and not tok_clean.startswith("_")
                    and not tok_clean.startswith("h")
                    and tok_clean not in _DATA_TYPE_WORDS
                ):
                    all_value_vars.append(tok_clean)
                    if not is_primitive:
                        domain_binder_vars.append(tok_clean)
        target_vars = domain_binder_vars if domain_binder_vars else all_value_vars
        if target_vars:
            conc_idents = set(_IDENT_EXTRACT_RE.findall(norm_conc))
            if not any(v in conc_idents for v in target_vars):
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_UNUSED_SUBJECT_IN_CONCLUSION,
                        line=line,
                        symbol=name,
                        tier=canon_tier,
                        message=(
                            f"`{kind}` theorem `{name}` binds subject parameter(s) {target_vars}, "
                            f"but its conclusion `{norm_conc}` references none of them."
                        ),
                        suggestion="Ensure the conclusion states a property of the bound subject parameter(s).",
                    )
                )

    return findings


def _lean_comment_groups(
    code_only: str, comment_blocks: list[tuple[int, int, int, str, str]]
) -> list[tuple[int, int, list[tuple[int, str, str]]]]:
    """Group consecutive non-module-doc Lean comments of the same declaration (separated only by
    whitespace, `@[...]` attributes, declaration modifiers, or `<command> in` prefixes)."""
    groups: list[tuple[int, int, list[tuple[int, str, str]]]] = []
    for c_start, c_end, c_line, c_body, c_kind in comment_blocks:
        if groups and c_kind != "m":
            p_start, p_end, p_list = groups[-1]
            if p_list[-1][2] != "m":
                gap = code_only[p_end:c_start]
                if (
                    not gap
                    or gap.isspace()
                    or (
                        c_start - p_end <= 512
                        and ":=" not in gap
                        and _skip_lean_prefixes_attrs_and_modifiers(code_only, p_end, c_start) >= c_start
                    )
                ):
                    p_list.append((c_line, c_body, c_kind))
                    groups[-1] = (p_start, c_end, p_list)
                    continue
        groups.append((c_start, c_end, [(c_line, c_body, c_kind)]))
    return groups


def _lean_docstring_lines(c_list: list[tuple[int, str, str]], kind: str = "d") -> list[tuple[int, str]]:
    """`(line_no, text)` lines of the comments of the requested kind (`"d"` = `/-- -/`)."""
    out: list[tuple[int, str]] = []
    for base_line, c_body, c_kind in c_list:
        if c_kind == kind:
            out.extend((base_line + k, raw) for k, raw in enumerate(c_body.split("\n")))
    return out


_3AXIS_KEYS = frozenset(("kind", "witness", "assumes", "subject"))
_META_CACHE: dict[str, tuple[dict[str, str], list[str]]] = {}
_THM_AUDIT_CACHE: dict[tuple[str, str, str, bool], tuple[WaiverPinFinding, ...]] = {}
# In-process incremental splicing (`_find_incremental_lean_window`): only a long-lived process
# re-scanning edited files (the LSP daemon, a hook's before/after pair) benefits. A host that audits
# every file once -- the TCB checker -- turns it off, keeping the splice logic out of its decisions.
INCREMENTAL_SPLICING = True
_LAST_LEAN_AUDIT: dict[
    tuple[str, bool, str],
    tuple[str, str, list[int], list[int], list[int], tuple[WaiverPinFinding, ...]],
] = {}


def _find_incremental_lean_window(
    old_text: str,
    old_code: str,
    c_starts: list[int],
    c_ends: list[int],
    col0_thms: list[int],
    text: str,
) -> (
    tuple[
        int,
        int,
        int,
        int,
        int,
        int,
        int,
        int,
        str,
        list[tuple[int, int, int, str, str]],
    ]
    | None
):
    """If `text` is a localized edit of `old_text`, return two-ring window boundaries
    `(safe_lo, safe_hi_old, safe_hi_new, lo_line_offset, cut_lo_line, cut_hi_old_line,
    cut_hi_new_line, delta_lines, win_code, win_comments)` for `O(window)` incremental
    scanning, or `None` when a full scan is needed."""
    n_old = len(old_text)
    n_new = len(text)
    if n_old < 32768 or n_new < 32768 or len(col0_thms) < 8:
        return None
    step = 4096
    limit = n_old if n_old < n_new else n_new
    p = 0
    while p + step <= limit and old_text[p : p + step] == text[p : p + step]:
        p += step
    while p + 64 <= limit and old_text[p : p + 64] == text[p : p + 64]:
        p += 64
    delta_len = n_new - n_old
    s = n_old
    while s - step >= p and old_text[s - step : s] == text[s + delta_len - step : s + delta_len]:
        s -= step
    while s - 64 >= p and old_text[s - 64 : s] == text[s + delta_len - 64 : s + delta_len]:
        s -= 64
    if (p == 0 and s == n_old) or (p + (n_old - s) < (n_new * 3) // 4):
        return None

    def _backup_col0_decl(kw_pos: int) -> int | None:
        pos = kw_pos
        first_step = True
        while True:
            idx = _wa_bisect_right(c_ends, pos) - 1
            if (
                idx >= 0
                and (first_step or pos - c_ends[idx] <= 64)
                and old_code[c_ends[idx] : pos].strip() == ""
            ):
                c0 = c_starts[idx]
                nl = old_code.rfind("\n", 0, c0)
                pos = 0 if nl == -1 else nl + 1
                first_step = False
            else:
                break
        if pos > 0 and (old_text[pos - 1] != "\n" or old_code[pos - 1] != "\n"):
            return None
        if pos > 0:
            q = pos - 1
            while q > 0 and old_code[q - 1] in " \t\r\n":
                q -= 1
            prev_nl = old_code.rfind("\n", 0, q)
            prev_line = old_code[prev_nl + 1 : q].strip()
            if (
                prev_line.startswith("@")
                or prev_line.endswith("]")
                or prev_line == "where"
                or prev_line.startswith("where ")
                or prev_line.endswith(" where")
                or prev_line.endswith(" in")
                or prev_line == "in"
                or any(
                    prev_line == mod or prev_line.startswith(mod + " ") or prev_line.endswith(" " + mod)
                    for mod in _LEAN_MODIFIERS
                )
            ):
                return None
        return pos

    # `col0_thms[i_lo]` may be the theorem whose body/header contains `p`, so skip `i_lo`
    # and start searching for `cut_lo` at `i_lo - 1` (ensuring at least one full unmodified
    # theorem sits between `cut_lo` and `col0_thms[i_lo]`, keeping all of `col0_thms[i_lo]`'s
    # preceding docstrings, attributes, and modifiers strictly inside `[cut_lo, cut_hi_old)`).
    i_lo = _wa_bisect_right(col0_thms, p) - 2
    cut_lo: int | None = None
    safe_lo: int | None = None
    while i_lo >= 0:
        cand = _backup_col0_decl(col0_thms[i_lo])
        if cand is not None and cand <= p:
            if cut_lo is None:
                cut_lo = cand
            elif cand < cut_lo:
                safe_lo = cand
                break
        i_lo -= 1

    # Similarly, an edit ending at `s` may edit or insert a docstring/attribute that attaches
    # forward across whitespace/modifiers to `col0_thms[i_hi]`, so skip `i_hi` and start
    # searching for `cut_hi_old` at `i_hi + 1`.
    n_thms = len(col0_thms)
    i_hi = _wa_bisect_right(col0_thms, s - 1 if s > 0 else 0) + 1
    cut_hi_old: int | None = None
    safe_hi_old: int | None = None
    while i_hi < n_thms:
        cand = _backup_col0_decl(col0_thms[i_hi])
        if cand is not None and cand >= s:
            if cut_hi_old is None:
                cut_hi_old = cand
            elif cand > cut_hi_old:
                safe_hi_old = cand
                break
        i_hi += 1

    if (
        safe_lo is None
        or cut_lo is None
        or cut_hi_old is None
        or safe_hi_old is None
        or not (safe_lo < cut_lo <= p and s <= cut_hi_old < safe_hi_old)
    ):
        return None

    safe_hi_new = safe_hi_old + delta_len
    cut_hi_new = cut_hi_old + delta_len

    # Both `cut_hi_new` and `safe_hi_new` must be in the neutral lexer state: the outer ring
    # `text[cut_hi_new:safe_hi_new]` must lex identically to `old_code[cut_hi_old:safe_hi_old]`
    # with no comment crossing `cut_hi_new`, and the sentinel after `safe_hi_new` must survive
    # verbatim with no comment crossing `win_len` (catching both strings that stay open past
    # `safe_hi_new` and strings that swallow `cut_hi_new` before closing at a quote inside a
    # comment in `[cut_hi_new, safe_hi_new)`).
    win_len = safe_hi_new - safe_lo
    cut_hi_rel = cut_hi_new - safe_lo
    sentinel = "\nzzIncrementalLexSentinelzz"
    win_sent_code, win_sent_comments = _scan_lean_comments_and_strings(
        text[safe_lo:safe_hi_new] + sentinel
    )
    if len(win_sent_code) != win_len + len(sentinel) or not win_sent_code.endswith(sentinel):
        return None
    if win_sent_code[cut_hi_rel:win_len] != old_code[cut_hi_old:safe_hi_old]:
        return None
    if any((cs < cut_hi_rel < ce) or (ce > win_len) for cs, ce, _, _, _ in win_sent_comments):
        return None

    win_code = win_sent_code[:win_len]
    win_comments = list(win_sent_comments)
    lo_line_offset = old_text.count("\n", 0, safe_lo)
    cut_lo_line = lo_line_offset + old_text.count("\n", safe_lo, cut_lo) + 1
    cut_hi_old_line = cut_lo_line - 1 + old_text.count("\n", cut_lo, cut_hi_old) + 1
    cut_hi_new_line = lo_line_offset + text.count("\n", safe_lo, cut_hi_new) + 1
    delta_lines = cut_hi_new_line - cut_hi_old_line
    return (
        safe_lo,
        safe_hi_old,
        safe_hi_new,
        lo_line_offset,
        cut_lo_line,
        cut_hi_old_line,
        cut_hi_new_line,
        delta_lines,
        win_code,
        win_comments,
    )

# Which theorems the 3-axis / `TRIVIAL_PROOF` audit covers (`audit_lean_text(vacuity_scope=...)`):
# - `"all"`: every `theorem` / `lemma` gets every check (`--all-theorems`, the prototype default).
# - `"annotated"`: theorems with 3-axis metadata, an `anneal:` waiver docstring, or an Anneal
#   `Proof/` claim name (`verified` / `prove_*`) get every check; every other theorem gets only
#   the syntactic hypothesis-contradiction check (the always-on `proof_health.py` scope).
# - `"annotated-only"`: only the annotated / claim theorems are audited (the TCB checker scope).
VACUITY_SCOPES: frozenset[str] = frozenset(("all", "annotated", "annotated-only"))


def is_proof_claim_module(file_path: str | Path | None) -> bool:
    """`True` for files under an Anneal `Proof/` directory (any path component `Proof`)."""
    if file_path is None:
        return False
    return "Proof" in Path(file_path).parts[:-1]


def is_proof_claim_theorem_name(name: str) -> bool:
    """`True` for Anneal claim theorem names: `verified` or `prove_*` (last name component)."""
    short = name.rsplit(".", 1)[-1]
    return short == "verified" or short.startswith("prove_")


def _parse_3axis_metadata_and_conflicts(comment_text: str) -> tuple[dict[str, str], list[str]]:
    """Single-pass C-level line partition 3-axis metadata parser (last value wins) plus
    the keys declared more than once with different values."""
    hit = _META_CACHE.get(comment_text)
    if hit is not None:
        return hit
    meta: dict[str, str] = {}
    conflicts: list[str] = []
    for raw_line in comment_text.split("\n"):
        if ":" not in raw_line:
            continue
        k_part, _, v_part = raw_line.partition(":")
        if len(k_part) > 16:
            continue
        key = k_part.lstrip(" \t*-").rstrip(" \t").lower()
        if key in _3AXIS_KEYS:
            val = v_part.strip()
            if val:
                prev = meta.get(key)
                if prev is not None and prev != val and key not in conflicts:
                    conflicts.append(key)
                meta[key] = val
    res = (meta, conflicts)
    if len(_META_CACHE) < 4096:
        _META_CACHE[comment_text] = res
    return res


def _neutralize_lean_strings_in_slice(
    text: str,
    code_only: str,
    comment_blocks: list[tuple[int, int, int, str, str]],
    comment_starts: list[int],
    start: int,
    end: int,
) -> str | None:
    """Return `code_only[start:end]` with every real Lean string literal (`\"...\"` / `r#\"...\"#`)
    replaced by a deterministic opaque all-digit literal token `\"0<digits>\"` (matching neither
    `_IDENT_EXTRACT_RE` nor `_NUM_LIT_RE`, with no brackets/operators/spaces, preserving equality
    of identical strings and distinctness of different strings), or `None` when no real string
    literal occurs in `[start, end)` (quotes only inside comments, guillemets, or `'\"'`/`'\\\"'`
    char literals)."""
    n_text = len(text)
    n_comments = len(comment_blocks)
    find = text.find
    chunks: list[str] | None = None
    last_emit = start
    pos = start
    while pos < end:
        q = find('"', pos, end)
        if q == -1:
            break
        if code_only[q] != " ":
            pos = q + 1
            continue
        if n_comments:
            k = _wa_bisect_right(comment_starts, q) - 1
            if k >= 0 and comment_blocks[k][0] <= q < comment_blocks[k][1]:
                pos = comment_blocks[k][1]
                continue
        is_raw = False
        raw_start = q
        if q > 0 and text[q - 1] in "#r'\\":
            h = q
            while h > 0 and text[h - 1] == "#":
                h -= 1
            if (
                h > 0
                and text[h - 1] == "r"
                and (h < 2 or not (_is_lean_ident_char(text[h - 2]) or text[h - 2] == "."))
            ):
                is_raw = True
                raw_start = h - 1
            elif (
                q + 1 < n_text
                and text[q + 1] == "'"
                and (
                    (
                        text[q - 1] == "'"
                        and (
                            q < 2
                            or (not _is_lean_ident_char(text[q - 2]) and text[q - 2] != "\\")
                        )
                    )
                    or (
                        q >= 2
                        and text[q - 2 : q] == "'\\"
                        and (q < 3 or not _is_lean_ident_char(text[q - 3]))
                    )
                )
            ):
                pos = q + 1
                continue
        if is_raw:
            closer = '"' + "#" * (q - (raw_start + 1))
            c = find(closer, q + 1, end)
            cur = end if c == -1 else c + len(closer)
            str_start = raw_start if raw_start >= last_emit else q
        else:
            cur = q + 1
            while cur < end:
                q2 = find('"', cur, end)
                if q2 == -1:
                    cur = end
                    break
                bs = 0
                bk = q2 - 1
                while bk >= q + 1 and text[bk] == "\\":
                    bs += 1
                    bk -= 1
                cur = q2 + 1
                if bs % 2 == 0:
                    break
            str_start = q
        if chunks is None:
            chunks = []
        chunks.append(code_only[last_emit:str_start])
        chunks.append(f'"0{int(compute_sha256_pin12(text[str_start:cur]), 16)}"')
        last_emit = cur
        pos = cur
    if chunks is None:
        return None
    chunks.append(code_only[last_emit:end])
    return "".join(chunks)


def audit_lean_text(
    text: str,
    *,
    file_path: str | Path | None = None,
    check_3axis: bool = True,
    vacuity_scope: str = "all",
    _preparsed: tuple[str, list[tuple[int, int, int, str, str]]] | None = None,
) -> list[WaiverPinFinding]:
    """Scan Lean 4 source `text` for `S0`-`S3` waiver pin findings and 3-axis / `TRIVIAL_PROOF` hazards.

    Waiver directives and pin lines are read only from `/-- ... -/` docstrings (Lean's analogue
    of Rust's `///`); `--` and `/- ... -/` comments are ordinary comments, and directives in a
    `/-! ... -/` module docstring attach to no declaration (dangling). 3-axis metadata may live in
    any comment immediately preceding a declaration. `vacuity_scope` (see `VACUITY_SCOPES`)
    selects which theorems the 3-axis audit covers; `file_path` identifies `Proof/` claim modules.
    """
    if vacuity_scope not in VACUITY_SCOPES:
        raise ValueError(f"unknown vacuity_scope {vacuity_scope!r}")
    if not check_3axis and "anneal:" not in text and "pin:sha256:" not in text:
        return []
    state_key = (
        str(file_path) if file_path is not None else "",
        bool(check_3axis),
        vacuity_scope,
    )
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        prev = _LAST_LEAN_AUDIT.get(state_key)
        if prev is not None:
            old_text, old_code, c_starts, c_ends, col0_thms, old_findings = prev
            if text == old_text:
                return list(old_findings)
            win_info = _find_incremental_lean_window(
                old_text, old_code, c_starts, c_ends, col0_thms, text
            )
            if win_info is not None:
                (
                    safe_lo,
                    _safe_hi_old,
                    safe_hi_new,
                    lo_line_offset,
                    cut_lo_line,
                    cut_hi_old_line,
                    cut_hi_new_line,
                    delta_lines,
                    win_code,
                    win_comments,
                ) = win_info
                win_findings = audit_lean_text(
                    text[safe_lo:safe_hi_new],
                    file_path=file_path,
                    check_3axis=check_3axis,
                    vacuity_scope=vacuity_scope,
                    _preparsed=(win_code, win_comments),
                )
                spliced = [f for f in old_findings if f.line < cut_lo_line]
                for wf in win_findings:
                    adj_line = wf.line + lo_line_offset
                    if cut_lo_line <= adj_line < cut_hi_new_line:
                        spliced.append(
                            WaiverPinFinding(
                                rule=wf.rule,
                                line=adj_line,
                                message=wf.message,
                                suggestion=wf.suggestion,
                                symbol=wf.symbol,
                                expected_pin=wf.expected_pin,
                                actual_pin=wf.actual_pin,
                                tier=wf.tier,
                            )
                        )
                for f in old_findings:
                    if f.line >= cut_hi_old_line:
                        spliced.append(
                            f
                            if delta_lines == 0
                            else WaiverPinFinding(
                                rule=f.rule,
                                line=f.line + delta_lines,
                                message=f.message,
                                suggestion=f.suggestion,
                                symbol=f.symbol,
                                expected_pin=f.expected_pin,
                                actual_pin=f.actual_pin,
                                tier=f.tier,
                            )
                        )
                spliced.sort(key=lambda f: (f.line, f.rule, f.symbol))
                return spliced

    claim_module = is_proof_claim_module(file_path)
    if len(_NORM_CACHE) > 8192:
        _NORM_CACHE.clear()
    if _preparsed is not None:
        code_only, comment_blocks = _preparsed
    else:
        code_only, comment_blocks = _scan_lean_comments_and_strings(text)
    comment_starts: list[int] | None = None
    findings: list[WaiverPinFinding] = []
    line_of = _WaLineCounter(text)
    n_code = len(code_only)
    thms: list[tuple[int, int, str]] = []

    decl_comment_map: dict[int, str] = {}

    for grp_start, grp_end, c_list in _lean_comment_groups(code_only, comment_blocks):
        has_meta = False
        has_directive = False
        for _, c_body, c_kind in c_list:
            if ":" not in c_body:
                continue
            if "Kind:" in c_body or "Witness:" in c_body or "Assumes:" in c_body or "Subject:" in c_body:
                has_meta = True
            if c_kind != "l" and c_kind != "b" and ("anneal:" in c_body or "pin:" in c_body):
                has_directive = True
        if not has_meta and not has_directive:
            continue
        meta_text = c_list[0][1] if len(c_list) == 1 else "\n".join(c_body for _, c_body, _ in c_list)
        if has_directive:
            for line_no, raw in _lean_docstring_lines(c_list, "m"):
                if "anneal:" not in raw:
                    continue
                ann = parse_anneal_directive_line(raw, line_no)
                if ann is not None:
                    findings.append(
                        WaiverPinFinding(
                            rule=RULE_DANGLING_WAIVER,
                            line=ann.line,
                            symbol=ann.directive,
                            tier=ann.tier,
                            message=(
                                f"`anneal:{ann.directive}` sits in a `/-! ... -/` module docstring, which "
                                "attaches to no declaration."
                            ),
                            suggestion="Move the directive into the `/-- ... -/` docstring of the target declaration.",
                        )
                    )
            anns, block_pins = _collect_block_directives(_lean_docstring_lines(c_list, "d"))
        else:
            anns, block_pins = [], []
        if not anns and not has_meta:
            continue

        if not anns:
            d_start = grp_end
            while d_start < n_code and code_only[d_start] in " \t\r\n":
                d_start += 1
            if d_start < n_code:
                prev_m = decl_comment_map.get(d_start)
                decl_comment_map[d_start] = f"{prev_m}\n{meta_text}" if prev_m else meta_text
                if not code_only.startswith(("theorem ", "lemma ", "def ", "abbrev "), d_start):
                    kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
                    if kw_off < n_code and kw_off != d_start:
                        prev_kw = decl_comment_map.get(kw_off)
                        decl_comment_map[kw_off] = f"{prev_kw}\n{meta_text}" if prev_kw else meta_text
            continue

        decl_info = _extract_lean_decl_span(code_only, grp_end, text)
        if decl_info is None:
            for ann in anns:
                findings.append(
                    WaiverPinFinding(
                        rule=RULE_DANGLING_WAIVER,
                        line=ann.line,
                        symbol=ann.directive,
                        tier=ann.tier,
                        message=(
                            f"Dangling `anneal:{ann.directive}` waiver annotation in Lean file "
                            "with no following declaration."
                        ),
                        suggestion="Place the waiver docstring immediately before a `theorem`, `lemma`, or `def` declaration.",
                    )
                )
            continue
        d_start, d_end, _, d_name = decl_info
        prev_m = decl_comment_map.get(d_start)
        decl_comment_map[d_start] = f"{prev_m}\n{meta_text}" if prev_m else meta_text
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
        if kw_off < n_code and kw_off != d_start:
            prev_kw = decl_comment_map.get(kw_off)
            decl_comment_map[kw_off] = f"{prev_kw}\n{meta_text}" if prev_kw else meta_text
        if comment_starts is None:
            comment_starts = [c[0] for c in comment_blocks]
        # `<command> in` prefixes above or between comments in the group belong to the pinned command.
        p_start = _lean_in_prefix_start(code_only, grp_start)
        code_start = p_start
        while code_start < d_start and code_only[code_start] in " \t\r\n":
            code_start += 1
        hash_input = waiver_hash_input(
            anns,
            _normalize_lean_decl(
                _no_comments_slice(text, comment_blocks, comment_starts, code_start, d_end)
            ),
        )
        findings.extend(_validate_waiver_block(anns, block_pins, d_name, hash_input))

    if check_3axis:
        if len(_THM_AUDIT_CACHE) > 4096:
            _THM_AUDIT_CACHE.clear()
        # `[adv A3]` Full scans of large files (`>= 32 KiB`, `_preparsed is None`) already save
        # `_LAST_LEAN_AUDIT` for `O(window)` two-ring incremental splicing; skipping per-theorem
        # full-body slicing/hashing into `_THM_AUDIT_CACHE` on those cold full scans avoids hashing
        # every proof body while keeping `_THM_AUDIT_CACHE` active on smaller files and windows.
        use_thm_cache = INCREMENTAL_SPLICING and (len(text) < 32768 or _preparsed is not None)
        thm_cache = _THM_AUDIT_CACHE
        thm_cache_get = thm_cache.get
        cache_has_entries = use_thm_cache and bool(thm_cache)
        has_quote_in_text = '"' in text
        thms = _iter_lean_theorem_headers(code_only)
        n_thms = len(thms)
        for idx_t, (kw_start, name_end, thm_name) in enumerate(thms):
            comment_str = decl_comment_map.get(kw_start, "")
            contradiction_only = False
            if vacuity_scope != "all" and not comment_str and not (
                claim_module and is_proof_claim_theorem_name(thm_name)
            ):
                if vacuity_scope == "annotated-only":
                    continue
                contradiction_only = True
            next_thm_bound = thms[idx_t + 1][0] if idx_t + 1 < n_thms else n_code
            # `[adv A4]` `code_only` blanks string literals to spaces (so `TestStripLeanCommentsAndStrings`
            # and structural scanning stay untouched), which would collapse distinct strings in a
            # theorem header (`f "a" ≠ f "b"` -> `f ≠ f`, `R "hi" s` -> `R s`). Neutralize real
            # string literals only when a `"` appears in this theorem's slice.
            hdr_code = code_only
            hdr_start = name_end
            hdr_end = next_thm_bound
            if has_quote_in_text and text.find('"', name_end, next_thm_bound) != -1:
                if comment_starts is None:
                    comment_starts = [c[0] for c in comment_blocks]
                neut = _neutralize_lean_strings_in_slice(
                    text, code_only, comment_blocks, comment_starts, name_end, next_thm_bound
                )
                if neut is not None:
                    hdr_code = neut
                    hdr_start = 0
                    hdr_end = len(neut)
            # The audit is a pure function of (name, metadata comment, the exact bounded text
            # `_split_lean_theorem_header` reads, the check scope), so the cache key must be that
            # full slice: A1 truncated it at the first `:=`, which can sit inside a binder's
            # structure literal (`(h : ({ a := 1 } : S).P)`), letting a later edit to the conclusion
            # or to a later hypothesis hit a stale entry (false negatives across scans in one process).
            cache_key = (
                (
                    thm_name,
                    comment_str,
                    hdr_code if hdr_code is not code_only else code_only[name_end:next_thm_bound],
                    contradiction_only,
                )
                if use_thm_cache
                else None
            )
            cached_f = (
                thm_cache_get(cache_key)
                if cache_has_entries and cache_key is not None
                else None
            )
            if cached_f is not None:
                if cached_f:
                    thm_line = line_of(kw_start)
                    for tf in cached_f:
                        findings.append(
                            WaiverPinFinding(
                                rule=tf.rule,
                                line=thm_line,
                                message=tf.message,
                                suggestion=tf.suggestion,
                                symbol=tf.symbol,
                                expected_pin=tf.expected_pin,
                                actual_pin=tf.actual_pin,
                                tier=tf.tier,
                            )
                        )
                continue

            local_findings: list[WaiverPinFinding] = []
            meta, conflicts = _parse_3axis_metadata_and_conflicts(comment_str) if comment_str else ({}, [])
            if conflicts:
                for key in conflicts:
                    local_findings.append(
                        WaiverPinFinding(
                            rule=RULE_TIER_ASSUMPTION_MISMATCH,
                            line=0,
                            symbol=thm_name,
                            message=(
                                f"Theorem `{thm_name}` declares conflicting 3-axis `{key.capitalize()}:` "
                                "values; a later line would silently override an earlier one."
                            ),
                            suggestion=f"Keep exactly one `{key.capitalize()}:` line.",
                        )
                    )
            parsed = _split_lean_theorem_header(hdr_code, hdr_start, hdr_end)
            if parsed is not None:
                hyps, conc, extra_binders = parsed
                local_findings.extend(
                    _audit_lean_theorem(
                        thm_name, 0, meta, hyps, conc, contradiction_only, extra_binders
                    )
                )
            if cache_key is not None:
                thm_cache[cache_key] = tuple(local_findings)
            if local_findings:
                thm_line = line_of(kw_start)
                for tf in local_findings:
                    findings.append(
                        WaiverPinFinding(
                            rule=tf.rule,
                            line=thm_line,
                            message=tf.message,
                            suggestion=tf.suggestion,
                            symbol=tf.symbol,
                            expected_pin=tf.expected_pin,
                            actual_pin=tf.actual_pin,
                            tier=tf.tier,
                        )
                    )

    findings.sort(key=lambda f: (f.line, f.rule, f.symbol))
    if INCREMENTAL_SPLICING and _preparsed is None and len(text) >= 32768:
        if not thms:
            thms = _iter_lean_theorem_headers(code_only)
        col0_thms = [kw for kw, _, _ in thms if kw == 0 or code_only[kw - 1] == "\n"]
        if len(col0_thms) >= 8:
            if len(_LAST_LEAN_AUDIT) >= 16:
                _LAST_LEAN_AUDIT.clear()
            _LAST_LEAN_AUDIT[state_key] = (
                text,
                code_only,
                [c[0] for c in comment_blocks],
                [c[1] for c in comment_blocks],
                col0_thms,
                tuple(findings),
            )
    return findings


_LEAN_IN_SUFFIX_RE = re.compile(r"(?<![\w'!?.\u00bb])in[ \t\r]*$")


def _lean_in_prefix_start(code_only: str, pos: int) -> int:
    """Start of the chain of `<command> in` prefixes (`open Foo in`, `set_option opt v in`,
    `attribute [local simp] x in`, `variable (n : Nat) in`, ...) ending right before `pos` (a
    declaration's leading docstring or its first token), else `pos`.

    Lean parses `cmd in decl` as one command, so a waiver pin must bind these prefixes too:
    otherwise `set_option debug.skipKernelTC true in` (or `open Other in`, re-resolving every
    name of the statement) could be added before or edited above a pinned declaration's
    docstring without drifting its pin. A prefix may span several lines; its first line is the
    nearest prefix-command start above the `in` line (bounded walk).
    """
    start = pos
    while True:
        q = start
        while q > 0 and code_only[q - 1] in " \t\r\n":
            q -= 1
        if q == 0:
            return start
        line_start = code_only.rfind("\n", 0, q) + 1
        if _LEAN_IN_SUFFIX_RE.search(code_only, line_start, q) is None:
            return start
        cmd = line_start
        found_start = -1
        for _ in range(64):
            k = cmd
            while k < q and code_only[k] in " \t":
                k += 1
            kw = _skip_lean_attrs_and_modifiers(code_only, k)
            if _LEAN_IN_PREFIX_CMD_RE.match(code_only, kw) is not None:
                found_start = k
                break
            if _is_lean_command_start(code_only, k) or cmd == 0:
                break
            cmd = code_only.rfind("\n", 0, cmd - 1) + 1
        if found_start == -1 or found_start >= start:
            return start
        start = found_start


def compute_lean_decl_pins(text: str) -> dict[str, str]:
    """Map each top-level Lean declaration name in `text` to its `pin:sha256:<12hex>` tag
    (the hash binds the declaration's `/-- -/` directives and its normalized text)."""
    code_only, comment_blocks = _scan_lean_comments_and_strings(text)
    comment_starts = [c[0] for c in comment_blocks]
    n = len(code_only)
    anns_by_decl: dict[int, list[WaiverAnnotation]] = {}
    grp_start_by_decl: dict[int, int] = {}
    post_doc_start_by_decl: dict[int, int] = {}
    for grp_start, grp_end, c_list in _lean_comment_groups(code_only, comment_blocks):
        d = grp_end
        while d < n and code_only[d] in " \t\r\n":
            d += 1
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d)
        anns, _ = _collect_block_directives(_lean_docstring_lines(c_list, "d"))
        for key_off in (d,) if d == kw_off else (d, kw_off):
            if key_off in anns_by_decl:
                if anns:
                    anns_by_decl[key_off].extend(anns)
            else:
                anns_by_decl[key_off] = list(anns)
            if key_off not in grp_start_by_decl or grp_start < grp_start_by_decl[key_off]:
                grp_start_by_decl[key_off] = grp_start
            post_doc_start_by_decl[key_off] = d
    pins: dict[str, str] = {}
    pos = 0
    while pos < n:
        d_start = pos
        while d_start < n and code_only[d_start] in " \t\r\n":
            d_start += 1
        if d_start >= n:
            break
        hit = _match_lean_decl_at(code_only, d_start, skip_in_prefixes=True)
        if hit is None:
            nl = code_only.find("\n", d_start)
            if nl == -1:
                break
            pos = nl + 1
            continue
        hdr_end, _, d_name = hit
        kw_off = _skip_lean_prefixes_attrs_and_modifiers(code_only, d_start)
        doc_grp_start = grp_start_by_decl.get(kw_off, -1)
        if 0 <= doc_grp_start and d_start < doc_grp_start:
            pos = doc_grp_start
            continue
        post_doc_d = post_doc_start_by_decl.get(kw_off, d_start)
        d_end = _find_lean_decl_end(
            code_only, hdr_end, _lean_indent_of(code_only, post_doc_d, text), text
        )
        lead = grp_start_by_decl.get(kw_off, post_doc_d)
        p_start = _lean_in_prefix_start(code_only, lead)
        code_start = p_start
        while code_start < post_doc_d and code_only[code_start] in " \t\r\n":
            code_start += 1
        hash_input = waiver_hash_input(
            anns_by_decl.get(kw_off, []),
            _normalize_lean_decl(
                _no_comments_slice(text, comment_blocks, comment_starts, code_start, d_end)
            ),
        )
        pins[d_name] = format_pin_tag(compute_sha256_pin12(hash_input))
        pos = d_end
    return pins


def compute_rust_item_pins(text: str) -> dict[str, str]:
    """Map each doc-commented Rust item name in `text` to its `pin:sha256:<12hex>` tag
    (the hash binds the item's doc-block directives and its normalized text)."""
    stripped, doc_segments, _ = _scan_rust_tokens_and_docs(text)
    pins: dict[str, str] = {}
    for grp_start, grp_end, line_docs in _rust_outer_doc_groups(stripped, doc_segments):
        doc_lines = [
            (base_line + off_l, raw_l)
            for base_line, doc_body in line_docs
            for off_l, raw_l in enumerate(doc_body.split("\n"))
        ]
        anns, _ = _collect_block_directives(doc_lines)
        pre_attr = _find_preceding_rust_attributes_start(stripped, grp_start)
        info = _extract_rust_target_span(stripped, grp_end, pre_attr)
        if info is not None:
            t_start, t_end, name = info
            hash_input = waiver_hash_input(anns, _normalize_rust_item(stripped[t_start:t_end]))
            pins[name] = format_pin_tag(compute_sha256_pin12(hash_input))
    return pins


def audit_file(
    file_path: str | Path,
    *,
    check_3axis: bool = True,
    vacuity_scope: str = "all",
) -> list[WaiverPinFinding]:
    """Scan a `.rs` or `.lean` file on disk for waiver-pin and 3-axis non-vacuity findings."""
    path = Path(file_path)
    text = path.read_bytes().decode("utf-8", errors="replace")
    if path.suffix == ".rs":
        return audit_rust_text(text, file_path=path)
    return audit_lean_text(text, file_path=path, check_3axis=check_3axis, vacuity_scope=vacuity_scope)


def count_audit_findings_by_rule(findings: Iterable[WaiverPinFinding]) -> dict[str, int]:
    counts = {rule: 0 for rule in ALL_WAIVER_AUDIT_RULES}
    for f in findings:
        counts[f.rule] = counts.get(f.rule, 0) + 1
    return counts

# ===========================================================================
# END SHARED WAIVER-PIN & 3-AXIS AUDITOR
# ===========================================================================


# ---------------------------------------------------------------------------
# Waiver-pin / vacuity enforcement, read-only staging, and base-snapshot checks
# ---------------------------------------------------------------------------

WAIVER_PIN_PHASE = "waiver-pin"
VACUITY_PHASE = "vacuity-audit"
BASE_SNAPSHOT_PHASE = "base-snapshot"
_WAIVER_RULE_SET = frozenset(ALL_WAIVER_RULES)
_MAX_REPORTED_FINDINGS = 5
_WRITE_BITS = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
# The TCB checker audits every staged file exactly once per process, so findings are never
# spliced from an earlier scan: each audit is a cold, full pass over the exact staged bytes.
INCREMENTAL_SPLICING = False


def audit_waivers_and_vacuity(
    sources, *, vacuity: bool = True, lang: str | None = None
) -> dict[str, int]:
    """Enforce waiver pins and annotated-claim non-vacuity on `(label, path)` sources.

    `.rs` sources (or `lang="rust"`) get the waiver-pin audit; `.lean` sources (or
    `lang="lean"`) get the waiver-pin audit plus
    (with `vacuity`) every 3-axis / `TRIVIAL_PROOF` check on theorems carrying 3-axis
    metadata (`Kind:` / `Witness:` / `Assumes:` / `Subject:`) or an `anneal:` waiver
    docstring, and on `Proof/` claim theorems, plus the syntactic hypothesis-contradiction
    check on all named hypotheses (`vacuity_scope="annotated"`).
    Unannotated smoke lemmas without contradictory hypotheses (such as
    `theorem trivial_witness : True := trivial`) pass cleanly. Raises `Failure(1, "waiver-pin", ...)`
    when any source has a waiver finding, else `Failure(1, "vacuity-audit", ...)` on any
    vacuity finding, and returns `{"leanFiles": ..., "rustFiles": ...}` when clean. Pure
    Python: it spawns no subprocess, so `--fast` status-file counts are unaffected.
    """
    waiver_hits: list[tuple[str, WaiverPinFinding]] = []
    vacuity_hits: list[tuple[str, WaiverPinFinding]] = []
    n_lean = n_rust = 0
    for label, path in sources:
        regular(path, WAIVER_PIN_PHASE)
        try:
            text = path.read_bytes().decode("utf-8", errors="strict")
        except (OSError, UnicodeDecodeError) as error:
            raise Failure(1, WAIVER_PIN_PHASE, f"cannot read {label} as UTF-8: {error}") from error
        is_rust = (lang == "rust") if lang is not None else (path.suffix == ".rs")
        if is_rust:
            n_rust += 1
            findings = audit_rust_text(text, file_path=label)
        else:
            n_lean += 1
            findings = audit_lean_text(
                text, file_path=label, check_3axis=vacuity, vacuity_scope="annotated"
            )
        for finding in findings:
            (waiver_hits if finding.rule in _WAIVER_RULE_SET else vacuity_hits).append((label, finding))
    for phase, hits, what in ((WAIVER_PIN_PHASE, waiver_hits, "waiver-pin"),
                              (VACUITY_PHASE, vacuity_hits, "annotated-claim vacuity")):
        if hits:
            shown = "; ".join(f"{label}:{f.line}: [{f.rule}] {f.message}"
                              for label, f in hits[:_MAX_REPORTED_FINDINGS])
            more = f" (+{len(hits) - _MAX_REPORTED_FINDINGS} more)" if len(hits) > _MAX_REPORTED_FINDINGS else ""
            raise Failure(1, phase, f"{len(hits)} {what} finding(s): {shown}{more}")
    return {"leanFiles": n_lean, "rustFiles": n_rust}


def rustc_capture_sources(checkout: Path) -> list[tuple[str, Path]]:
    """`(relative label, path)` of every `trusted/rustc-capture/**/*.rs` source (sorted;
    build output `target/` and hidden directories skipped; symlinks rejected by the audit)."""
    base = checkout / "trusted/rustc-capture"
    if not base.is_dir():
        return []
    out: list[tuple[str, Path]] = []
    for directory, dirs, files in os.walk(base, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d != "target" and not d.startswith("."))
        for name in sorted(files):
            if name.endswith(".rs"):
                path = Path(directory) / name
                out.append((path.relative_to(checkout).as_posix(), path))
    return out


def make_read_only(path: Path) -> None:
    """Make a staged input copy read-only (`0444`) so no later step can mutate it in place."""
    os.chmod(path, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)


def make_tree_writable(root: Path) -> None:
    """Restore owner write permission under `root` (before `shutil.rmtree` cleanup)."""
    for directory, _dirs, files in os.walk(root, followlinks=False):
        for name in files:
            path = Path(directory) / name
            try:
                mode = path.lstat().st_mode
                if stat.S_ISREG(mode) and not mode & stat.S_IWUSR:
                    os.chmod(path, stat.S_IMODE(mode) | stat.S_IWUSR)
            except OSError:
                pass


def tcb_snapshot_files(root: Path) -> dict[str, Path]:
    """TCB files compared by `--base-snapshot`, keyed by checkout-relative POSIX path:
    `trusted/audit/{check_trusted.py,TrustedBoundary.lean,OleanEnvAuditor.lean}`,
    `trusted/root-manifest.sha256`, every non-doc file or symlink under `trusted/lean/`, and
    `trusted/rustc-capture/Cargo.toml`."""
    out: dict[str, Path] = {}
    for rel in ("trusted/audit/check_trusted.py", "trusted/audit/TrustedBoundary.lean", OLEAN_AUDITOR,
                ROOT_MANIFEST, "trusted/lean/lean-toolchain", "trusted/rustc-capture/Cargo.toml"):
        path = root / rel
        if path.exists() or path.is_symlink():
            out[rel] = path
    lean_root = root / "trusted/lean"
    if lean_root.is_symlink():
        out["trusted/lean"] = lean_root
    elif lean_root.is_dir():
        for directory, dirs, files in os.walk(lean_root, followlinks=False):
            dirs.sort()
            for dname in dirs:
                dpath = Path(directory) / dname
                if dpath.is_symlink():
                    out[dpath.relative_to(root).as_posix()] = dpath
            for fname in sorted(files):
                fpath = Path(directory) / fname
                rel = fpath.relative_to(root).as_posix()
                if rel == "trusted/lean/README.md":
                    continue
                out[rel] = fpath
    return out


def verify_root_manifest(checkout: Path) -> dict[str, str] | None:
    """Verify `trusted/root-manifest.sha256` against the checkout before any Lean child runs.

    The manifest is required whenever it exists or the checkout carries the repository markers
    (`flake.nix` and `lakefile.toml`); a bare fixture without either has nothing to verify and
    returns `None`. Every entry must be a canonical relative path naming a regular, non-symlinked
    file inside the checkout (no symlinked parent directory either) whose SHA-256 matches; the
    entries must be unique and must include `ROOT_MANIFEST_REQUIRED`. Any violation is
    `Failure(1, "root-manifest", ...)`. Returns `{path: sha256}` of the covered files.
    """
    phase = ROOT_MANIFEST_PHASE
    manifest = checkout / ROOT_MANIFEST
    has_markers = any((checkout / m).exists() or (checkout / m).is_symlink()
                      for m in ("flake.nix", "lakefile.toml"))
    if not (manifest.exists() or manifest.is_symlink()):
        if has_markers:
            raise Failure(1, phase, f"missing {ROOT_MANIFEST} in a repository checkout")
        return None
    root = checkout.resolve()
    for component in (checkout / "trusted", manifest):
        if component.is_symlink():
            raise Failure(1, phase, f"symlinked root-manifest path: {component}")
    try:
        mode = manifest.lstat().st_mode
        raw = manifest.read_bytes()
    except OSError as error:
        raise Failure(1, phase, f"cannot read {ROOT_MANIFEST}: {error}") from error
    if not stat.S_ISREG(mode):
        raise Failure(1, phase, f"{ROOT_MANIFEST} is not a regular file")
    covered: dict[str, str] = {}
    for number, line in enumerate(raw.splitlines(), 1):
        if line.startswith(b"#") or not line.strip():
            continue
        match = re.fullmatch(rb"([0-9a-f]{64})( [ *])([^\r\n]+)", line)
        if match is None:
            raise Failure(1, phase, f"{ROOT_MANIFEST}:{number}: malformed checksum entry")
        try:
            name = match[3].decode("utf-8")
        except UnicodeDecodeError as error:
            raise Failure(1, phase, f"{ROOT_MANIFEST}:{number}: non-UTF-8 path") from error
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or str(rel) != name or name == ROOT_MANIFEST:
            raise Failure(1, phase, f"{ROOT_MANIFEST}:{number}: expected a canonical relative path: {name!r}")
        if name in covered:
            raise Failure(1, phase, f"{ROOT_MANIFEST}:{number}: duplicate covered file: {name}")
        path = checkout
        for part in rel.parts:
            path = path / part
            if path.is_symlink():
                raise Failure(1, phase, f"covered file traverses a symlink: {name}")
        try:
            file_mode = path.lstat().st_mode
        except OSError as error:
            raise Failure(1, phase, f"missing covered file: {name}") from error
        if not stat.S_ISREG(file_mode) or not path.resolve().is_relative_to(root):
            raise Failure(1, phase, f"covered file is not a regular file inside the checkout: {name}")
        actual = digest(path)
        if actual != match[1].decode("ascii"):
            raise Failure(1, phase, f"root-manifest drift: {name} does not match its pinned SHA-256")
        covered[name] = actual
    required = ROOT_MANIFEST_REPO_REQUIRED if has_markers else ROOT_MANIFEST_REQUIRED
    missing = [name for name in required if name not in covered]
    if missing:
        raise Failure(1, phase, f"{ROOT_MANIFEST} does not cover required TCB files: {', '.join(missing)}")
    return covered


def verify_base_snapshot(checkout: Path, snapshot: Path, expected_drift=()) -> dict[str, str]:
    """Verify the checkout's TCB files against an immutable, read-only base snapshot.

    `snapshot` mirrors checkout-relative paths (`<snapshot>/trusted/audit/check_trusted.py`,
    ...). Every snapshot entry must be a regular file without write permission bits
    (`Failure(2, "base-snapshot", ...)` otherwise). Any TCB file missing from either side or
    differing in SHA-256 is unauthorized drift (`Failure(1, "base-snapshot", ...)`) unless its
    relative path is listed in `expected_drift`. Returns the snapshot's `{path: sha256}`.
    """
    phase = BASE_SNAPSHOT_PHASE
    if snapshot.is_symlink() or not snapshot.is_dir():
        raise Failure(2, phase, f"base snapshot is not a directory: {snapshot}")
    snap = tcb_snapshot_files(snapshot)
    if not snap:
        raise Failure(2, phase, f"base snapshot contains no TCB files: {snapshot}")
    hashes: dict[str, str] = {}
    for rel, path in snap.items():
        mode = path.lstat().st_mode
        if not stat.S_ISREG(mode):
            raise Failure(2, phase, f"base snapshot entry is not a regular file: {rel}")
        if mode & _WRITE_BITS:
            raise Failure(2, phase, f"base snapshot is not read-only (writable entry {rel})")
        hashes[rel] = digest(path)
    current = tcb_snapshot_files(checkout)
    allowed = set(expected_drift)
    drift = []
    for rel in sorted(set(snap) | set(current)):
        if rel in allowed:
            continue
        if rel not in current:
            drift.append(f"missing from checkout: {rel}")
        elif rel not in snap:
            drift.append(f"absent from base snapshot: {rel}")
        else:
            regular(current[rel], phase)
            if digest(current[rel]) != hashes[rel]:
                drift.append(f"changed: {rel}")
    if drift:
        more = f" (+{len(drift) - 10} more)" if len(drift) > 10 else ""
        raise Failure(1, phase, "unauthorized TCB drift against base snapshot: " + "; ".join(drift[:10]) + more)
    return hashes


def waiver_vacuity_gate(checkout: Path) -> dict[str, dict[str, int]]:
    """`--audit-vacuity`: the pure-Python waiver-pin / vacuity audit of the checkout's
    `trusted/lean` sources, `trusted/rustc-capture` Rust sources, and `DOWNSTREAM_TARGETS`
    (no Lean process; the full gate also audits the staged copies it compiles)."""
    source = checkout / "trusted/lean"
    _inventory, modules = snapshot(source)
    trusted = audit_waivers_and_vacuity([(f"trusted/lean/{rel}", source / rel) for rel in modules.values()])
    rust = audit_waivers_and_vacuity(rustc_capture_sources(checkout), vacuity=False)
    downstream = audit_waivers_and_vacuity(
        [(path, checkout / path) for _, path, _, _ in DOWNSTREAM_TARGETS if (checkout / path).exists()]
    )
    return {"trusted": trusted, "rustcCapture": rust, "downstream": downstream}


def main() -> int:
    try:
        return _main()
    finally:
        remove_process_binaries()


def _main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="absolute path to an already installed pinned Lean executable")
    parser.add_argument("--self-test", action="store_true", help="run the bounded regression fixtures")
    parser.add_argument("--fast", action="store_true", help="enable content-addressed incremental caching outside the checkout")
    parser.add_argument("--cache-dir", type=Path, help="directory outside the checkout for --fast incremental cache")
    parser.add_argument("--audit-vacuity", action="store_true",
                        help="only run the pure-Python waiver-pin and annotated-claim vacuity audit (no Lean)")
    parser.add_argument("--base-snapshot", type=Path,
                        help="immutable read-only directory mirroring the expected TCB files "
                             "(default: $ANNEAL_TRUSTED_BASE_SNAPSHOT); any other TCB drift fails")
    parser.add_argument("--expected-tcb-drift", action="append", default=[], metavar="RELPATH",
                        help="checkout-relative TCB path allowed to differ from --base-snapshot (repeatable)")
    parser.add_argument("--audit-olean", type=Path, metavar="REQUEST",
                        help="audit the compiled modules named by a JSON request with OleanEnvAuditor "
                             "(trust-gating policy) and print its verdict")
    args = parser.parse_args()
    checkout = Path(__file__).resolve().parent.parent.parent
    if args.lean is not None and not args.lean.is_absolute():
        parser.error("--lean must be absolute")
    if args.self_test:
        sys.path.insert(0, str(checkout / "tests/trusted-boundary"))
        from test_boundary import self_test
        return self_test(checkout, args.lean)
    base_snapshot = args.base_snapshot
    if base_snapshot is None and os.environ.get("ANNEAL_TRUSTED_BASE_SNAPSHOT"):
        base_snapshot = Path(os.environ["ANNEAL_TRUSTED_BASE_SNAPSHOT"])
    if args.audit_vacuity:
        try:
            verify_root_manifest(checkout)
            if base_snapshot is not None:
                verify_base_snapshot(checkout, base_snapshot, tuple(args.expected_tcb_drift))
            summary = waiver_vacuity_gate(checkout)
        except Failure as error:
            print(f"Trusted check failed ({error.phase}): {error}", file=sys.stderr)
            return error.code
        except OSError as error:
            print(f"Trusted check failed (waiver-pin): {error}", file=sys.stderr)
            return 2
        print(f"PASS: waiver pins and annotated-claim vacuity; {json.dumps(summary, sort_keys=True)}")
        return 0
    if args.audit_olean is not None:
        try:
            if base_snapshot is not None:
                verify_base_snapshot(checkout, base_snapshot, tuple(args.expected_tcb_drift))
            request = json.loads(args.audit_olean.read_text())
        except Failure as error:
            print(f"Trusted check failed ({error.phase}): {error}", file=sys.stderr)
            return error.code
        except (OSError, ValueError) as error:
            print(f"Trusted check failed (olean-audit): cannot read request: {error}", file=sys.stderr)
            return 2
        try:
            olean_checker = Checker(checkout, args.lean, fast=args.fast, cache_dir=args.cache_dir)
        except (Failure, OSError) as error:
            print(f"Trusted check failed (admission): {error}", file=sys.stderr)
            return error.code if isinstance(error, Failure) else 2
        try:
            # Compile and audit `Trusted` from the checkout first: requests are audited against
            # the checker's own `Trusted` artifacts, never caller-supplied ones.
            olean_checker.run()
            spec_lib_rel = next((p for m, p, _, _ in DOWNSTREAM_TARGETS if m == SPEC_LIB_MODULE), None)
            has_checkout_spec_lib = spec_lib_rel is not None and (checkout / spec_lib_rel).is_file()
            if (isinstance(request, dict) and request.get("specStrengthChecks")) or has_checkout_spec_lib:
                # Spec-strength checks (and any caller importing `SPEC_LIB_MODULE`) are judged
                # against the checkout's own specification-strength library, compiled and audited here.
                olean_checker.compile_spec_library()
            verdict = olean_checker.audit_olean_request(request)
            olean_checker.freshness()
        except (Failure, OSError, ValueError, KeyError, TypeError) as error:
            code = error.code if isinstance(error, Failure) else 2
            phase = error.phase if isinstance(error, Failure) else olean_checker.phase
            print(f"Trusted check failed ({phase}): {error}\npreserved logs: {olean_checker.stage}", file=sys.stderr)
            return code
        except KeyboardInterrupt:
            print(f"Trusted check interrupted; preserved logs: {olean_checker.stage}", file=sys.stderr)
            return 2
        print(json.dumps(verdict, indent=2, sort_keys=True))
        make_tree_writable(olean_checker.stage)
        shutil.rmtree(olean_checker.stage)
        return 0
    try:
        checker = Checker(checkout, args.lean, fast=args.fast, cache_dir=args.cache_dir,
                          base_snapshot=base_snapshot, expected_tcb_drift=tuple(args.expected_tcb_drift))
    except Failure as error:
        print(f"Trusted check failed ({error.phase}): {error}", file=sys.stderr)
        return error.code
    except OSError as error:
        print(f"Trusted check could not create its private temporary directory: {error}", file=sys.stderr)
        return 2
    try:
        report = checker.run(check_downstream=True)
    except (Failure, OSError, ValueError, KeyError, TypeError) as error:
        code = error.code if isinstance(error, Failure) else 2
        phase = error.phase if isinstance(error, Failure) else checker.phase
        print(f"Trusted check failed ({phase}): {error}\nTarget execution began: {checker.execution_began}; "
              f"preserved logs: {checker.stage}\nRetry only after resolving/reobserving the reported failure.", file=sys.stderr)
        return code
    except KeyboardInterrupt:
        print(f"Trusted check interrupted; preserved logs: {checker.stage}", file=sys.stderr)
        return 2
    downstream = report.get("downstream", {})
    audited = report.get("waiverVacuityAudit", {})
    staged_lean = audited.get("trusted", {}).get("leanFiles", 0) + downstream.get("waiverVacuityAudit", {}).get("leanFiles", 0)
    print(f"PASS: {report['guarantee']}\n{len(checker.modules)} Trusted modules; "
          f"{report['kernelDeclarations']} Trusted kernel declarations; "
          f"{downstream.get('replayedDeclarations', 0)} total replayed declarations; "
          f"{downstream.get('claimTheoremsChecked', 0)} claim theorem statements origin-checked; "
          f"axioms={report['axioms']}\n"
          f"OleanEnvAuditor: {report['oleanAudit']['auditedDeclarations']} Trusted / "
          f"{downstream.get('oleanAudit', {}).get('auditedDeclarations', 0)} downstream declarations audited from "
          f"compiled artifacts; {downstream.get('oleanAudit', {}).get('intrinsicTagsChecked', 0)} compiler-intrinsic tags, "
          f"{downstream.get('oleanAudit', {}).get('kernelTagConfirmations', 0)} kernel-confirmed tag equations, "
          f"replay={report['oleanAudit']['replay'] and downstream.get('oleanAudit', {}).get('replay', False)}\n"
          f"Source {report['sourceSha256']}; tools/policy {report['toolsSha256']}\n"
          f"Waiver pins and annotated-claim vacuity: {staged_lean} staged Lean files, "
          f"{audited.get('rustcCapture', {}).get('rustFiles', 0)} trusted/rustc-capture Rust files\n"
          f"{report['toolchain']}")
    if report["kernelDeclarations"] == 0:
        print("0 Trusted declarations; no semantics")
    make_tree_writable(checker.stage)
    shutil.rmtree(checker.stage)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
