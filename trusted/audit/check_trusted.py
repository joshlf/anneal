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
from pathlib import Path
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
    ("Anneal", "theory/Anneal.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.MirLoops", "Anneal.Scalars", "Anneal.Memory", "Anneal.BitValidity", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.Rustc.V2026_06_01.SymReflect", "Anneal.Rustc.V2026_06_01.TraceCheck", "Anneal.FunctionalTranslation", "Anneal.MirFuelFree", "Anneal.PureMirExec", "Anneal.MirLiftCore", "Anneal.MirLiftBench", "Anneal.SepLogicLenses", "Anneal.PureLift"], "theory"),
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
        self.stage = Path(tempfile.mkdtemp(prefix="anneal-trusted-", dir=temp_parent))
        self.phase, self.execution_began, self.counter = "admission", False, 0
        self.environment = {k: v for k, v in os.environ.items()
                            if not k.startswith(("LEAN", "LAKE", "ELAN", "DYLD_"))}
        self.environment["PATH"] = os.defpath
        self.artifacts: dict[str, list[list[str]]] = {}
        self.graph: dict = {}
        self.expected_artifacts: dict[str, str] = {}
        self.last_status = None

    def budget(self) -> None:
        size = sum(p.stat().st_size for p in self.stage.rglob("*") if p.is_file())
        if size > MAX_BYTES:
            raise Failure(2, self.phase, "512 MiB retained-build envelope exceeded")

    def process(self, label: str, arguments: list[str], *, executable: Path | None = None) -> str:
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
                                               stdout=out, stderr=err, timeout=CHILD_TIMEOUT_SECS, check=False)
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
            raise Failure(2, label, f"direct Lean child exceeded {CHILD_TIMEOUT_SECS} seconds; no retry")
        if code != 0:
            raise Failure(2, label, f"Lean exited {code}; see {stem}.stdout/.stderr")
        return stdout.read_text(encoding="utf-8", errors="strict")

    def _get_compiled_inspector(self) -> Path | None:
        if not self.fast or self.cache_dir is None or self.expected_lean_sha is None:
            return None
        if self._compiled_inspector is not None and self._compiled_inspector.is_file():
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
        if bin_path.is_file() and os.access(bin_path, os.X_OK):
            self._compiled_inspector = bin_path
            return bin_path
        try:
            bin_dir.mkdir(parents=True, exist_ok=True)
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
        if mode in ("audit", "downstream-audit"):
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
                "graph": self.graph,
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
        if not meta_path.is_file():
            return False
        try:
            meta = json.loads(meta_path.read_text())
        except (ValueError, OSError):
            return False
        if not isinstance(meta, dict) or "olean" not in meta or not set(meta).issubset(set(PARTS)):
            return False
        for part, expected_sha in meta.items():
            cached_part = entry_dir / f"artifact.{part}"
            if not cached_part.is_file() or digest(cached_part) != expected_sha:
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
        entry_dir = olean_root / cache_key
        if entry_dir.exists():
            return
        try:
            olean_root.mkdir(parents=True, exist_ok=True)
            tmp_dir = Path(tempfile.mkdtemp(prefix=f"tmp-{cache_key[:12]}-", dir=olean_root))
        except OSError:
            return
        try:
            meta = {}
            for part, path_str in available.items():
                shutil.copyfile(path_str, tmp_dir / f"artifact.{part}")
                meta[part] = self.expected_artifacts[path_str]
            (tmp_dir / "meta.json").write_text(json.dumps(meta, sort_keys=True))
            if entry_dir.exists():
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
            if cache_file.is_file():
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
        stem = self.stage / f"request-{self.counter + 1:03d}-{mode}"
        request_path, result_path = Path(str(stem) + ".json"), Path(str(stem) + ".result.json")
        request_path.write_text(json.dumps(request, sort_keys=True))
        self.last_status = None
        compiled_inspector = self._get_compiled_inspector()
        try:
            if compiled_inspector is not None:
                self.process(mode, [str(request_path), str(result_path)], executable=compiled_inspector)
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
            try:
                inspect_dir.mkdir(parents=True, exist_ok=True)
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
        else:
            raise Failure(2, mode, "unknown inspector result mode")

    def tool_admission(self) -> None:
        self.initial, self.modules = snapshot(self.source)
        self.tool_paths = [
            self.checkout / "trusted/audit/check_trusted.py",
            self.checkout / "trusted/audit/TrustedBoundary.lean",
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
        downstream_flags = (
            ["-j4", "-M2048", "-t0", "-DElab.async=true", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
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
        result["waiverVacuityAudit"] = waiver_audit
        return result

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
            val_int = int(s[start:i])
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

_LEAN_THM_NAME_RE = re.compile(r"[ \t\r\n]+([^ \t\r\n({\[:]+)")


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
_CHAR_LITERAL_RE = re.compile(r"(?<![\w'.!?])'(?:\\[^\n]{1,8}?|[^\\'\n])'")
_ARROW_SCAN_RE = re.compile(
    r"«[^»]*»|(?<![\w'.!?])'(?:\\[^\n]{1,8}?|[^\\'\n])'|[(){}\[\]⟨⟩]|↔|<->|<\|>|<\||\$|→|->|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)
_PIPE_ARM_RE = re.compile(r"\n[ \t]*\|")


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
    """For a bracket group opening at `seg[p]`, return `(offset past its matching close,
    offset of its first depth-1 `:` that is not `:=`, or -1)` using C-level `str.find`."""
    end_lim = len(seg) if limit is None else limit
    ch = seg[p]
    close_ch = ")" if ch == "(" else ("}" if ch == "{" else "]")
    find = seg.find
    cur = p + 1
    depth = 1
    while depth > 0 and cur < end_lim:
        c_close = find(close_ch, cur, end_lim)
        if c_close == -1:
            cur = end_lim
            break
        c_open = find(ch, cur, c_close)
        target = c_open if c_open != -1 else c_close
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


def _typed_binder_parts(inner: str) -> tuple[str, str] | None:
    """`(names, type)` for the inside of a `names : T` binder group; `None` when it is untyped
    (`x y`) or its first `:` opens a `:=` default."""
    b_n, col, b_t = inner.partition(":")
    if not col or b_t.startswith("="):
        return None
    b_n = b_n.strip()
    b_t = b_t.strip()
    if not b_n or not b_t:
        return None
    return b_n, b_t


def _arrow_premise_binder(prem: str) -> tuple[str, str]:
    """The hypothesis a `→` premise contributes. A premise that is exactly one `(names : T)` group
    is a dependent-arrow binder (`(h : False) → P`, `(n : Nat) → n < 0 → P`): it binds `names`
    like a header binder, so it is returned as `(names, T)`. Anything else -- including a subtype
    or set-builder brace `{x : T // p}` -- is the anonymous premise `("", prem)`. `[adv B2]`:
    A0-A1 kept `("", "(h : False)")`, whose text matches no contradiction and binds no `Nat`
    variable, so the dependent-arrow spelling evaded every scope."""
    if len(prem) >= 5 and prem[0] == "(" and prem[-1] == ")" and ":" in prem:
        q, col = _scan_binder_group(prem, 0, len(prem))
        if q == len(prem) and col != -1:
            names = prem[1:col].strip()
            b_type = prem[col + 1 : q - 1].strip()
            if b_type and _BARE_BINDER_NAMES_RE.fullmatch(names) is not None:
                return names, b_type
    return "", prem


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
    while p < n:
        ch = code_segment[p]
        if ch in " \t\r\n":
            p += 1
            while p < n and code_segment[p] in " \t\r\n":
                p += 1
            continue
        if ch == ":":
            if p + 1 < n and code_segment[p + 1] == "=":
                return None
            colon_pos = p
            break
        if ch == "⦃":
            # `[adv B2]` Strict-implicit binder `⦃x : T⦄`. A0-A1 read its inner `:` as the
            # statement colon, so every later binder (`(h : False)`) fell into the "conclusion".
            close_s = find("⦄", p + 1, n)
            if close_s == -1:
                return None
            inner = code_segment[p + 1 : close_s]
            typed_s = _typed_binder_parts(inner)
            if typed_s is not None:
                binders.append(typed_s)
            elif inner.strip():
                extra_binders.append(f"untyped:{inner.strip()}")
            p = close_s + 1
            continue
        if ch in "({[":
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
                    ):
                        binders.append(
                            (
                                prefix_b.strip(),
                                code_segment[col_idx + 1 : fast_close].strip(),
                            )
                        )
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
            if colon_in_binder != -1:
                binders.append(
                    (
                        code_segment[p + 1 : colon_in_binder].strip(),
                        code_segment[colon_in_binder + 1 : q - 1].strip(),
                    )
                )
            else:
                inner = code_segment[p + 1 : q - 1].strip() if q > p + 1 else ""
                if inner:
                    extra_binders.append(f"[{inner}]" if ch == "[" else f"untyped:{inner}")
            p = q
            continue
        if ch == "w" and code_segment.startswith("where", p):
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
    while search_eq < n:
        eq_pos = find(":=", search_eq, n)
        if eq_pos == -1:
            break
        prefix_slice = code_segment[stmt_start:eq_pos]
        bal_slice = _neutralize_char_literals(prefix_slice) if "'" in prefix_slice else prefix_slice
        if (
            bal_slice.count("(") == bal_slice.count(")")
            and bal_slice.count("{") == bal_slice.count("}")
            and bal_slice.count("[") == bal_slice.count("]")
        ):
            if "let " in prefix_slice:
                last_let = prefix_slice.rfind("let ")
                if "\n" not in prefix_slice[last_let:] and ";" not in prefix_slice[last_let:]:
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
            decl_end_bound = pipe_m.start()
            # A line-leading `|` normally opens an equation arm, but `||` / `|>` / `|x|` open one
            # just as well for this scan: the statement may continue past the cut.
            extra_binders.append("stmt-cut")
        else:
            decl_end_bound = (
                stmt_end if stmt_end != -1 else min(_find_lean_decl_end(code_segment, stmt_start), n)
            )
            w_pos = find("where", stmt_start, decl_end_bound)
            if w_pos != -1 and (w_pos == stmt_start or code_segment[w_pos - 1] in " \t\r\n"):
                decl_end_bound = w_pos
        stmt = code_segment[stmt_start:decl_end_bound].strip()
    else:
        stmt = prefix_slice.strip()
    if not stmt:
        return None

    hyps = list(binders)
    cur_stmt = stmt
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
                    close_s = find_cur("⦄", idx_q + 1, n_cur)
                    if close_s != -1:
                        if not saw_q_bare_colon:
                            saw_q_group = True
                            inner = cur_stmt[idx_q + 1 : close_s]
                            typed_s = _typed_binder_parts(inner)
                            if typed_s is not None:
                                hyps.append(typed_s)
                            elif inner.strip():
                                extra_binders.append(f"untyped:{inner.strip()}")
                        idx_q = close_s + 1
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
                                ):
                                    hyps.append(
                                        (
                                            prefix_qb.strip(),
                                            cur_stmt[col_in + 1 : fast_close].strip(),
                                        )
                                    )
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
                    if not saw_q_bare_colon:
                        if col_in != -1:
                            hyps.append(
                                (
                                    cur_stmt[idx_q + 1 : col_in].strip(),
                                    cur_stmt[col_in + 1 : r - 1].strip(),
                                )
                            )
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
            and "exists" not in cur_stmt
            and not cur_stmt.startswith("∃")
        ):
            arrow_parts = cur_stmt.split("→")
            if all(
                "∀" not in p_seg
                and "∃" not in p_seg
                and "forall" not in p_seg
                and p_seg.count("(") == p_seg.count(")")
                and p_seg.count("{") == p_seg.count("}")
                and p_seg.count("[") == p_seg.count("]")
                for p_seg in arrow_parts[:-1]
            ):
                for p_seg in arrow_parts[:-1]:
                    hyps.append(_arrow_premise_binder(p_seg.strip()))
                cur_stmt = arrow_parts[-1].strip()
                if (
                    cur_stmt.startswith("(")
                    or cur_stmt.startswith("∀")
                    or (cur_stmt.startswith("forall") and len(cur_stmt) > 6 and not _is_lean_ident_char(cur_stmt[6]))
                ):
                    continue
                break

        # Single-pass scan for all top-level `→` / `->` premises up to any top-level binder.
        # If a looser infix connective (`↔`, `<->`, `<|>`, `<|`, `$`) appears at depth 0 before
        # any depth-0 prefix binder, it governs the whole statement, so `→` is not top-level.
        depth_a = 0
        arrow_spans: list[tuple[int, int]] = []
        looser_hit = False
        re_loop = False
        for m_a in _ARROW_SCAN_RE.finditer(cur_stmt):
            t_a = m_a.group(0)
            if t_a[0] == "«" or t_a[0] == "'":
                continue
            if t_a in "({[⟨":
                depth_a += 1
            elif t_a in ")}]⟩":
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

    Results are memoized in `_NORM_CACHE`, which `audit_lean_text` clears at the start of every
    scan (deduplication within one file only; no state survives across scans)."""
    hit = _NORM_CACHE.get(s)
    if hit is not None:
        return hit
    res = _norm_expr_uncached(s)
    _NORM_CACHE[s] = res
    return res


def _norm_expr_uncached(s: str) -> str:
    if "\n" not in s and "  " not in s and "\t" not in s and "\r" not in s:
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


_SPLIT_RE_CACHE: dict[str, re.Pattern[str]] = {}
_TOP_SPLIT_RE_CACHE: dict[str, re.Pattern[str]] = {}


def _split_top_level(expr: str, sep: str) -> list[str]:
    """Split `expr` on `sep` occurrences outside `()`, `[]`, `{}`, `⟨⟩`, and `«...»` (C-level `finditer`)."""
    if sep not in expr:
        return [_norm_expr(expr)]
    pat = _TOP_SPLIT_RE_CACHE.get(sep)
    if pat is None:
        pat = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|" + re.escape(sep))
        _TOP_SPLIT_RE_CACHE[sep] = pat
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


_TOP_LEVEL_LOOSER_THAN_NOT_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|↔|<->|<\|>|<\||\$|→|->|∨|\\/|∧|/\\|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)
_CONJ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|∧|/\\")
_CONJ_TOP_BOUND_RE = re.compile(
    r"«[^»]*»|[()\[\]{}⟨⟩]|↔|<->|→|->|<\|>|<\||\|>|\$|∨|\\/|∀|∃|λ|"
    r"(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
)


def _arrow_false_antecedent(expr: str) -> str | None:
    """If normalized `expr` is exactly `X → False` / `X -> False` (including `X → (False)`) --
    one top-level implication whose whole consequent is `False`, the term `¬ X` unfolds to --
    return normalized `X`, else `None`. `A → B → False` (`A → ¬ B`), `A ↔ B → False` (`↔`
    governs), `f <| P → False` (`<|` governs) and `∀ x, P x → False` (the arrow belongs to the
    binder body) are not negations of one proposition."""
    if "False" not in expr or ("→" not in expr and "->" not in expr):
        return None
    depth = 0
    for m in _TOP_LEVEL_LOOSER_THAN_NOT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t == "→" or t == "->":
                if _norm_expr(expr[m.end() :]) != "False":
                    return None
                return _norm_expr(expr[: m.start()]) or None
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
    """`True` iff `expr` contains a top-level (depth-0 outside `()[]{}⟨⟩` and `«...»`)
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
    for m in _TOP_LEVEL_LOOSER_THAN_NOT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return t in ("↔", "<->", "<|>", "<|", "$", "→", "->", "∨", "\\/", "∧", "/\\")
    return False


_PREFIX_BINDER_HINT_SEARCH = re.compile(
    r"[∀∃λ]|(?<![\w'.!?])(?:forall|exists|fun|if|match|let|have|show|by)(?![\w'!?])"
).search


def _has_top_level_prefix_binder(expr: str) -> bool:
    """`True` iff `expr` has a depth-0 (outside `()[]{}⟨⟩` and `«...»`) prefix binder or keyword
    (`∀`, `∃`, `λ`, `forall`, `exists`, `fun`, `if`, `match`, `let`, `have`, `show`, `by`), whose
    body runs to the end of `expr`. Such an expression is not one relation between two terms:
    in `∀ x ∈ s, x :: xs = []` or `if c then True else n < 0` the `=` / `<` belongs to the body,
    which holds vacuously over an empty domain or in the other branch."""
    if _PREFIX_BINDER_HINT_SEARCH(expr) is None:
        return False
    depth = 0
    for m in _TOP_LEVEL_LOOSER_THAN_NOT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0 and t not in (
            "↔", "<->", "<|>", "<|", "$", "→", "->", "∨", "\\/", "∧", "/\\"
        ):
            return True
    return False


def _split_top_level_conjuncts(expr: str) -> list[str]:
    """Split `expr` on top-level `∧` / `/\\` conjuncts outside `()[]{}⟨⟩` and `«...»`,
    only when no looser connective (`↔`, `<->`, `→`, `->`, `∨`, `\\/`, `<|>`, `<|`, `|>`, `$`)
    governs `expr` at depth 0, recursively flattening parenthesized conjunctions."""
    if "∧" not in expr and "/\\" not in expr:
        return [expr]
    bound = len(expr)
    depth = 0
    for m in _CONJ_TOP_BOUND_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
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
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
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


_QUANT_COMMA_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|,")
_BARE_BINDER_NAMES_RE = re.compile(r"(?:[^\W\d][\w'!?]*\s*)+")
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
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            return c0, expr[q_len : m.start()], expr[m.end() :]
    return None


def _parse_quantifier_binder_groups(binders: str) -> list[tuple[list[str], str | None]] | None:
    """Parse a quantifier's binder section into `[(names, type_or_None), ...]` in telescope order,
    returning `None` if it contains a binder predicate (`i < n`, `x ∈ s`), instance bracket
    (`[inst : C]`), pattern (`⟨a, b⟩`), or unrecognised syntax. Handles unparenthesised types with
    parenthesised arguments (`x : List (Fin 0)`, `b : BitVec (n + 1)`)."""
    b = binders.strip()
    if not b:
        return None
    fullmatch = _BARE_BINDER_NAMES_RE.fullmatch
    if fullmatch(b) is not None:
        return [(b.split(), None)]
    if b[0] not in "({[" and ":" in b:
        col = b.find(":")
        if (
            col != -1
            and (col + 1 >= len(b) or b[col + 1] != "=")
            and "(" not in b[:col]
            and "{" not in b[:col]
            and "[" not in b[:col]
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
        if ch == "(" or ch == "{":
            q, col = _scan_binder_group(b, p, n)
            if q > n or b[q - 1] != (")" if ch == "(" else "}"):
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
) -> bool:
    """`True` iff a quantifier's binder section only introduces variables that range over data in
    telescope order: optionally bare/untyped names (`x y`, when `allow_untyped=True`), `names : T`,
    or `(names : T)` / `{names : T}` groups with `T` accepted by `_is_non_prop_binder_type`
    (respecting shadowing of both `type_vars` and reserved base/container names). A binder
    predicate (`x > 0`, `x ∈ s`), an instance bracket, a proof binder (`h : P`) or an
    unrecognised domain (`Fin n`) restricts the quantifier and is not plain."""
    groups = _parse_quantifier_binder_groups(binders)
    if groups is None:
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


_BOUND_NAME_SCAN_RE = re.compile(r"[(\[{⟨]|[)\]}⟩]|:|[^\W\d][\w'!?]*")


def _quantifier_bound_names(binders: str) -> frozenset[str]:
    """The variables a quantifier's binder section binds: every identifier outside a type
    annotation (`x y : T`, `(x : T) {y : U}`, `⟨a, b⟩`). A binder predicate's operand
    (`x ∈ s`) is included too: over-approximating only makes the caller more conservative."""
    names: list[str] = []
    depth = 0
    skip_depth = -1
    for m in _BOUND_NAME_SCAN_RE.finditer(binders):
        t = m.group(0)
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
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


def _top_level_arrow_domains(expr: str) -> list[str]:
    """Return the leading domain types `[D1, D2, ...]` of a top-level `D1 → D2 → ... → R` type."""
    ne = _norm_expr(expr)
    if not ne or ("→" not in ne and "->" not in ne):
        return []
    domains: list[str] = []
    depth = 0
    seg_start = 0
    for m in _ARROW_SCAN_RE.finditer(ne):
        t = m.group(0)
        if t[0] == "«" or t[0] == "'":
            continue
        if t in "({[⟨":
            depth += 1
        elif t in ")}]⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if t in ("→", "->"):
                domains.append(_norm_expr(ne[seg_start : m.start()]))
                seg_start = m.end()
            else:
                break
    return domains


def _untyped_binders_inhabited_by_calls(
    untyped_names: set[str],
    body: str,
    fn_domains: dict[str, tuple[bool, ...]],
    shadowed_fns: frozenset[str],
) -> bool:
    """`True` iff every untyped `∀` binder name in `untyped_names` is passed as an argument to
    some unshadowed outer function binder `f` in `fn_domains` at a parameter position whose domain
    is unconditionally inhabited (e.g. `(R : Nat → Prop) (h : ∀ s, R s ∧ False)`)."""
    if not untyped_names or not fn_domains:
        return False
    remaining = set(untyped_names)
    n_body = len(body)
    for f_name, dom_flags in fn_domains.items():
        if f_name in shadowed_fns or not any(dom_flags) or f_name not in body:
            continue
        # Do not rely on `f_name` if an inner binder inside `body` rebinds it.
        if (
            ("∀" in body or "∃" in body or "λ" in body or "forall" in body or "exists" in body or "fun" in body)
            and re.search(
                rf"(?:∀|∃|λ|(?:forall|exists|fun)(?![\w'!?]))[^,=>]*(?<![\w'.!?]){re.escape(f_name)}(?![\w'!?])",
                body,
            )
        ):
            continue
        pos = 0
        f_len = len(f_name)
        while pos < n_body and remaining:
            idx = body.find(f_name, pos)
            if idx == -1:
                break
            pos = idx + f_len
            if idx > 0 and (_is_lean_ident_char(body[idx - 1]) or body[idx - 1] == "."):
                continue
            if pos < n_body and _is_lean_ident_char(body[pos]):
                continue
            # Ensure `f_name` is in function-head position (not itself an argument to an outer call
            # like `Apply R s` where `s` is an argument to `Apply`, not `R`).
            prev_i = idx - 1
            while prev_i >= 0 and body[prev_i] in " \t\r\n":
                prev_i -= 1
            if prev_i >= 0 and (
                _is_lean_ident_char(body[prev_i]) or body[prev_i] in ")]}⟩"
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
                if ch in "([{⟨":
                    close_map = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
                    close_c = close_map[ch]
                    d = 1
                    q = arg_pos + 1
                    while q < n_body and d > 0:
                        if body[q] == ch:
                            d += 1
                        elif body[q] == close_c:
                            d -= 1
                        q += 1
                    arg_pos = q
                    continue
                m_id = _IDENT_EXTRACT_RE.match(body, arg_pos)
                if m_id is None:
                    break
                tok = m_id.group(0)
                if tok in _LEAN_EXPR_KW_STOP:
                    break
                if is_inhab and tok in remaining:
                    remaining.discard(tok)
                arg_pos = m_id.end()
        if not remaining:
            return True
    return not remaining


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
    scope_counter: list[int] | None = None,
) -> None:
    """Append to `out` the atoms that must ALL hold for normalized hypothesis `expr` to hold, as
    `(atom, quantifier-bound names in scope, enclosing quantifier binder sections, quantifier-typed
    Nat-like vars in scope, unique quantifier scope path)`: its top-level conjuncts
    (`_split_top_level_conjuncts`), descending through every `∃ binders,` prefix (an existential is
    unsatisfiable whenever its body is) and through `∀ binders,` prefixes whose domains are
    provably inhabited (explicit unshadowed inhabited types, or untyped names applied to an
    unshadowed outer binder with an inhabited domain; `∀ h : P, False`, `∀ i < n, False`,
    `∀ a : α, False`, and `∀ a, R a ∧ False` over `R : α → Prop` stay one opaque atom)."""
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
                            binders, shadowed=shadowed, allow_untyped=False
                        ):
                            can_descend = True
                        elif (
                            groups is not None
                            and fn_domains
                            and _plain_quantifier_binders(
                                binders, shadowed=shadowed, allow_untyped=True
                            )
                        ):
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
                                else:
                                    next_nat.difference_update(g_names)
                                next_sh.update(g_names)
                        else:
                            next_sh.update(q_bound)
                        child_id = scope_counter[0]
                        scope_counter[0] = child_id + 1
                        _hyp_atoms(
                            body_n,
                            bound | q_bound,
                            q_chain + (binders,),
                            frozenset(next_nat),
                            scope_path + (child_id,),
                            out,
                            shadowed=frozenset(next_sh),
                            fn_domains=fn_domains,
                            scope_counter=scope_counter,
                        )
                        continue
        out.append((part, bound, q_chain, q_nat_vars, scope_path))


_SIMPLE_TERM_TOKEN_RE = re.compile(
    r"\s+|«[^»]*»|(?<![\w'.!?])'[^'\n]*'|\.?[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*"
    r"|\.?\d+(?:\.\d+)*|::|\+\+|[-+*/%^@#]|!(?!=)|([(\[⟨])|([)\]⟩])"
)
_SIMPLE_RELATION_RE = re.compile(
    r"«[^»]*»|(?<![\w'.!?])'[^'\n]*'|[()\[\]{}⟨⟩]|≠|≤|≥|<|>|="
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
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if rel is not None:
                return False
            rel = m
    if rel is None:
        return False
    return _is_simple_term(h[: rel.start()].strip()) and _is_simple_term(h[rel.end() :].strip())


_TOP_BOUND_RE = re.compile(
    r"[()\[\]{}]|↔|→|->|<\|>|<\||\|>|\$|∨|∃|∀|λ|"
    r"(?<![\w'.!?])(?:fun|forall|exists|if|match|let|have|show|by)(?![\w'!?])"
)


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
    for m in _TOP_BOUND_RE.finditer(expr):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
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


def _all_conjuncts_trivial(expr: str) -> bool:
    """`True` iff `expr` has >= 2 top-level `∧` conjuncts and all are trivially true; stops at
    the first non-trivial conjunct (so long genuine conclusions cost one conjunct check)."""
    idx = expr.find("∧")
    if idx == -1:
        return False
    first = expr[:idx]
    if (
        first.count("(") == first.count(")")
        and first.count("[") == first.count("]")
        and first.count("{") == first.count("}")
        and not _is_trivially_true(first)
    ):
        return False
    bound = _find_top_level_bound(expr, allow_or=False)
    if bound <= 0:
        return False
    pat = _SPLIT_RE_CACHE.get("∧")
    if pat is None:
        pat = re.compile(r"[()\[\]{}]|∧")
        _SPLIT_RE_CACHE["∧"] = pat
    depth = 0
    start = 0
    count = 0
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if not _is_trivially_true(expr[start : m.start()]):
                return False
            count += 1
            start = m.end()
    return count >= 1 and _is_trivially_true(expr[start:])


def _any_disjunct_trivial(expr: str) -> bool:
    """`True` iff `expr` has >= 2 top-level `∨` disjuncts and at least one is trivially true
    (e.g. `P ∨ True`, `x = x ∨ P`, or `True ∨ ∀ x, P x`, which can be discharged by
    `Or.inr trivial` / `Or.inl rfl` without proving `P`)."""
    bound = _find_top_level_bound(expr, allow_or=True)
    if bound <= 0:
        return False
    pat = _SPLIT_RE_CACHE.get("∨")
    if pat is None:
        pat = re.compile(r"[()\[\]{}]|∨")
        _SPLIT_RE_CACHE["∨"] = pat
    depth = 0
    start = 0
    count = 0
    found_trivial = False
    for m in pat.finditer(expr, 0, bound):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            count += 1
            if _is_trivially_true(expr[start : m.start()]):
                found_trivial = True
            start = m.end()
    if count == 0:
        return False
    return found_trivial or _is_trivially_true(expr[start:])


_STANDALONE_EQ_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|(?<![=!<>:])=(?!=)")


def _split_top_level_eq(expr: str) -> list[str]:
    """Split `expr` on top-level standalone `=` (excluding `==`, `:=`, `!=`, `<=`, `>=`) outside `()[]{}⟨⟩` and `«...»`."""
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _STANDALONE_EQ_SPLIT_RE.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


def _is_trivially_true(conj: str) -> bool:
    """`True`, `¬ False`, a reflexive `a = a` / `a ↔ a` / `a ≤ a` conjunct, a parenthesized
    trivial conjunction/disjunction, or a universally quantified `∀ ..., <trivial>` whose body is
    itself trivially true."""
    raw = conj.strip()
    if raw in ("True", "¬ False", "¬False"):
        return True
    if "=" not in raw and "↔" not in raw and "≤" not in raw and "True" not in raw and "False" not in raw:
        return False
    c = _norm_expr(raw)
    if c in ("True", "¬ False", "¬False"):
        return True
    if len(c) < len(raw):
        if "∧" in c and _all_conjuncts_trivial(c):
            return True
        if "∨" in c and _any_disjunct_trivial(c):
            return True
    if c.startswith("∀") or (
        c.startswith("forall") and len(c) > 6 and not _is_lean_ident_char(c[6])
    ):
        q_len = 1 if c.startswith("∀") else 6
        idx_q = q_len
        n_c = len(c)
        while idx_q < n_c:
            ch = c[idx_q]
            if ch in "({[":
                idx_q, _ = _scan_binder_group(c, idx_q, n_c)
                continue
            if ch == ",":
                body = _norm_expr(c[idx_q + 1 :])
                return (
                    _is_trivially_true(body)
                    or ("∧" in body and _all_conjuncts_trivial(body))
                    or ("∨" in body and _any_disjunct_trivial(body))
                )
            idx_q += 1
    for op in ("↔", "≤", "="):
        if op not in c:
            continue
        if op == "=":
            if c.count("=") == 1 and ":=" not in c:
                lhs, _, rhs = c.partition("=")
                if (
                    lhs.count("(") == lhs.count(")")
                    and lhs.count("[") == lhs.count("]")
                    and lhs.count("{") == lhs.count("}")
                ):
                    nl = _norm_expr(lhs)
                    if nl and nl == _norm_expr(rhs):
                        return True
                continue
            sides = _split_top_level_eq(c)
            if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
                return True
            continue
        if c.count(op) == 1:
            lhs, _, rhs = c.partition(op)
            if (
                lhs.count("(") == lhs.count(")")
                and lhs.count("[") == lhs.count("]")
                and lhs.count("{") == lhs.count("}")
            ):
                nl = _norm_expr(lhs)
                if nl and nl == _norm_expr(rhs):
                    return True
            continue
        sides = _split_top_level(c, op)
        if len(sides) == 2 and sides[0] and sides[0] == sides[1]:
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
_NAT_ARITH_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|[-+*/%^]")


def _has_depth0_space(e: str) -> bool:
    """`True` iff normalized `e` has a space outside `()[]{}⟨⟩`: an application (`f xs.length`),
    not one projection chain (`xs.length`, `(xs.map f).length`)."""
    if " " not in e:
        return False
    depth = 0
    for ch in e:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif ch == " " and depth == 0:
            return True
    return False


def _is_atomic_nat_like(e: str, nat_vars: frozenset[str]) -> bool:
    """`e` (normalized, no depth-0 arithmetic operator) is a numeral, a `Nat`-like binder, an
    application headed by a known `Nat`-valued function (`sumSizes xs`), or a single projection
    chain ending in a known `Nat`-valued field (`xs.length`). `[adv B2]`: the suffix test alone
    accepted `f xs.length` -- an application of an arbitrary `f : Nat → Int`."""
    if e in nat_vars or _NUM_LIT_RE.match(e) is not None or e.startswith(_NAT_VALUED_PREFIXES):
        return True
    return e.endswith(_NAT_VALUED_SUFFIXES) and not _has_depth0_space(e)


def _is_nat_like_operand(e: str, nat_vars: frozenset[str]) -> bool:
    """`True` iff `e` is syntactically `Nat`-valued: a numeral, a binder declared `Nat`-like, a
    known `Nat`-valued projection/function (`.length`, `.size`, `.toNat`, `.totalPad`, `.totalSize`,
    `sumSizes ...`, etc.), or a depth-0 `+`/`-`/`*`/`/`/`%`/`^` combination whose operands are ALL
    `Nat`-like (parenthesised operands recurse). Anything else (`f x`, an `Int` / `Real` binder, an
    undeclared name) may be negative, so `e < 0` is NOT a syntactic contradiction for it.

    `[adv B2]`: A0-A1 applied the prefix / suffix tests to the whole operand and split on
    operators at any depth, so `x - y.toNat`, `sumSizes xs - z` (`x z : Int`), `-↑xs.length`
    and `g (a.size + b.size)` all read as `Nat`-valued."""
    e = _norm_expr(e)
    if not e:
        return False
    parts: list[str] | None = None
    depth = 0
    start = 0
    for m in _NAT_ARITH_SPLIT_RE.finditer(e):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            if parts is None:
                parts = []
            parts.append(e[start : m.start()])
            start = m.end()
    if parts is not None:
        parts.append(e[start:])
        return all(_is_nat_like_operand(p, nat_vars) for p in parts)
    return _is_atomic_nat_like(e, nat_vars)


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


_LT_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|(?<![<])<(?![<=|\-$*])")
_GT_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|(?<![->=|*$])>(?![>=])")
_LE_TOP_SPLIT_RE = re.compile(r"«[^»]*»|[()\[\]{}⟨⟩]|≤")


def _split_top_level_pat(expr: str, pat: re.Pattern[str]) -> list[str]:
    """Split `expr` at depth-0 matches of `pat` outside `()[]{}⟨⟩` and `«...»`."""
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t[0] == "«":
            continue
        if t in "([{⟨":
            depth += 1
        elif t in ")]}⟩":
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


def _check_hypothesis_contradiction(
    hyp_expr: str, nat_vars: frozenset[str] = frozenset()
) -> str | None:
    """Return a description if `hyp_expr` is a syntactic contradiction, else `None`.

    `nat_vars` are binders of a `Nat`-like type; the vacuous `x < 0` / `0 > x` rule fires only for
    `Nat`-valued operands (`_is_nat_like_operand`). A0-A1 fired for every operand not declared
    `Int`, a false positive on `(x : Real) (h : x < 0)` or `(f : Nat → Int) (h : f 0 < 0)`."""
    if (
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
    h = _norm_expr(hyp_expr)
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
    if _has_top_level_prefix_binder(h):
        return None

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
                    if len(le_sides) == 2 and le_sides[0] and le_sides[0] == le_sides[1]:
                        return f"negated reflexive `{le_op}` `{h}`"
        return None

    if h in (
        "true = false",
        "false = true",
        "Bool.true = Bool.false",
        "Bool.false = Bool.true",
    ):
        return f"contradictory boolean equality `{h}`"

    # Check `lhs ≠ rhs`
    if "≠" in h:
        neq_sides = _split_top_level(h, "≠")
        if len(neq_sides) == 2 and neq_sides[0] and neq_sides[0] == neq_sides[1]:
            return f"irreflexive inequality `{h}`"

    # Check `lhs < rhs` for `x < x`, `< 0`, or numeric `5 < 3`
    if "<" in h:
        lt_sides = _split_top_level_pat(h, _LT_TOP_SPLIT_RE)
        if len(lt_sides) == 2:
            nl, nr = lt_sides
            if nl and nl == nr:
                return f"irreflexive strict inequality `{h}`"
            if nr == "0" and _is_nat_like_operand(nl, nat_vars):
                return f"vacuous `< 0` bound `{h}`"
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) >= int(nr):
                return f"contradictory numeric inequality `{nl} < {nr}`"

    # Check `lhs ≤ rhs` for numeric `5 ≤ 3`
    if "≤" in h:
        le_sides = _split_top_level_pat(h, _LE_TOP_SPLIT_RE)
        if len(le_sides) == 2:
            nl, nr = le_sides
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) > int(nr):
                return f"contradictory numeric inequality `{nl} ≤ {nr}`"

    # Check `lhs ≥ rhs` for numeric `3 ≥ 5` (`[adv B2]`: the one relation A0-A1 never read)
    if "≥" in h:
        ge_sides = _split_top_level(h, "≥")
        if len(ge_sides) == 2:
            nl, nr = ge_sides
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) < int(nr):
                return f"contradictory numeric inequality `{nl} ≥ {nr}`"

    # Check `lhs > rhs` for `x > x`, `0 > n`, or numeric `3 > 5`
    if ">" in h:
        gt_sides = _split_top_level_pat(h, _GT_TOP_SPLIT_RE)
        if len(gt_sides) == 2:
            nl, nr = gt_sides
            if nl and nl == nr:
                return f"irreflexive strict inequality `{h}`"
            if nl == "0" and _is_nat_like_operand(nr, nat_vars):
                return f"vacuous `0 > ...` bound `{h}`"
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) <= int(nr):
                return f"contradictory numeric inequality `{nl} > {nr}`"

    # Check `lhs = rhs`
    if "=" in h:
        eq_sides = _split_top_level_eq(h)
        if len(eq_sides) == 2:
            nl, nr = eq_sides
            if (nl, nr) in _BOOL_CONTRADICTORY_PAIRS:
                return f"contradictory boolean equality `{nl} = {nr}`"
            if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) != int(nr):
                return f"distinct numeric literal equality `{nl} = {nr}`"
            if (nl == "none" and (nr == "some" or nr.startswith("some "))) or (
                nr == "none" and (nl == "some" or nl.startswith("some "))
            ):
                return f"disjoint `Option` constructor equality `{h}`"
            if (
                nl == "[]"
                and (
                    ("::" in nr and len(_split_top_level(nr, "::")) >= 2)
                    or _is_nonempty_list_literal(nr)
                )
            ) or (
                nr == "[]"
                and (
                    ("::" in nl and len(_split_top_level(nl, "::")) >= 2)
                    or _is_nonempty_list_literal(nl)
                )
            ):
                return f"disjoint `List` constructor equality `{h}`"
            if (
                (nl.startswith(".inl ") or nl.startswith("Sum.inl "))
                and (nr.startswith(".inr ") or nr.startswith("Sum.inr "))
            ) or (
                (nr.startswith(".inl ") or nr.startswith("Sum.inl "))
                and (nl.startswith(".inr ") or nl.startswith("Sum.inr "))
            ):
                return f"disjoint `Sum` constructor equality `{h}`"
            if (
                (nl.startswith(".ok ") or nl.startswith("Except.ok "))
                and (nr.startswith(".error ") or nr.startswith("Except.error "))
            ) or (
                (nr.startswith(".ok ") or nr.startswith("Except.ok "))
                and (nl.startswith(".error ") or nl.startswith("Except.error "))
            ):
                return f"disjoint `Except` constructor equality `{h}`"

    return None


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


def _quantifier_context_before(
    all_hyps: list[tuple[str, str]], limit_idx: int
) -> tuple[frozenset[str], dict[str, tuple[bool, ...]]]:
    """Return `(shadowed_reserved, fn_domains)` in scope right before `all_hyps[limit_idx]`,
    tracked in telescope order: `shadowed_reserved` are reserved data/container/typeclass names
    rebound by earlier binders; `fn_domains` maps each earlier arrow-typed binder to a tuple of
    booleans recording whether each leading domain type is unconditionally inhabited."""
    shadowed: set[str] = set()
    fn_domains: dict[str, tuple[bool, ...]] = {}
    for b_names, b_type in all_hyps[:limit_idx]:
        names = b_names.split()
        if not names:
            continue
        doms = _top_level_arrow_domains(b_type) if ("→" in b_type or "->" in b_type) else []
        dom_flags = (
            tuple(_is_non_prop_binder_type(d, _NO_BOUND_NAMES, shadowed=frozenset(shadowed)) for d in doms)
            if doms
            else ()
        )
        for tok in names:
            if dom_flags:
                fn_domains[tok] = dom_flags
            else:
                fn_domains.pop(tok, None)
            if tok in _FALSE_ELIM_RESERVED_NAMES:
                shadowed.add(tok)
    return frozenset(shadowed), fn_domains


def _record_pos_neg_atom(part: str, pos_set: set[str], neg_set: set[str]) -> None:
    """Record normalized `part` and any proposition it denies (`¬ X`, `X → False`, `a ≠ b`,
    symmetric on `=`/`≠`) into `pos_set` / `neg_set`."""
    denied = _negated_operand(part)
    if denied is not None:
        neg_set.add(denied)
        if "=" in denied and not _has_top_level_looser_than_not(denied):
            d_eq = _split_top_level_eq(denied)
            if len(d_eq) == 2 and d_eq[0] and d_eq[1]:
                neg_set.add(f"{d_eq[0]} = {d_eq[1]}")
                neg_set.add(f"{d_eq[1]} = {d_eq[0]}")
    elif "≠" in part and not _has_top_level_looser_than_not(part):
        neq_sides = _split_top_level(part, "≠")
        if len(neq_sides) == 2 and neq_sides[0] and neq_sides[1]:
            neg_set.add(f"{neq_sides[0]} = {neq_sides[1]}")
            neg_set.add(f"{neq_sides[1]} = {neq_sides[0]}")
    elif "=" in part and not _has_top_level_looser_than_not(part):
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
        indexed_hyps = list(enumerate(all_hyps))
    findings: list[WaiverPinFinding] = []
    norm_conc = "" if contradiction_only else _norm_expr(conclusion)
    is_false_conc = (
        norm_conc == "False"
        if not contradiction_only
        else ("False" in conclusion and _norm_expr(conclusion) == "False")
    )

    kind_raw = meta.get("kind", "")
    witness_raw = meta.get("witness", "")
    assumes_raw = meta.get("assumes", "")
    subject_raw = meta.get("subject", "")

    kind = kind_raw.lower() if kind_raw else ""
    witness = witness_raw.lower() if witness_raw else ""

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

    canon_tier = VALID_3AXIS_ASSUMES.get(assumes_raw, "")
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
    conc_head = norm_conc.split(" ", 1)[0].lstrip("(¬") if norm_conc else ""
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

    has_any_ineq_or_neg_in_all = (
        any_neg
        or "<" in all_hyps_text
        or "≤" in all_hyps_text
        or ">" in all_hyps_text
        or "≥" in all_hyps_text
        or "False" in all_hyps_text
    )
    has_eq_in_all = "=" in all_hyps_text
    conc_head_in_all = bool(conc_head and conc_head in all_hyps_text)

    if has_any_ineq_or_neg_in_all or has_eq_in_all or conc_head_in_all:
        for orig_idx, (_, t) in indexed_hyps:
            has_ineq_or_neg = (
                has_any_ineq_or_neg_in_all
                and (
                    "≠" in t
                    or "<" in t
                    or "≤" in t
                    or ">" in t
                    or "≥" in t
                    or "False" in t
                    or "¬" in t
                )
            )
            has_eq = "=" in t
            if not has_ineq_or_neg and not has_eq and not has_non_eq_neg and not (conc_head_in_all and conc_head in t):
                continue
            # If the only trigger in `t` is `=`, and there are no `¬`/`≠` hypotheses in the theorem,
            # and `t` cannot match `norm_conc`, check if `t` can be a constructor/literal equality clash
            if (
                not has_ineq_or_neg
                and has_eq
                and not any_neg
                and not (conc_head_in_all and conc_head in t)
                and "false" not in t
                and "none" not in t
                and "[]" not in t
                and "inl" not in t
                and "ok" not in t
                and _DIGIT_SEARCH(t) is None
            ):
                continue
            nh = _norm_expr(t)
            if not tautology_hit and nh and nh == norm_conc:
                tautology_hit = True
            if not nh or (not has_ineq_or_neg and not has_eq and not has_non_eq_neg):
                continue
            if "'" in nh:
                nh = _neutralize_char_literals(nh)
            seen_pos_hyps.add(nh)
            atoms: list[
                tuple[str, frozenset[str], tuple[str, ...], frozenset[str], tuple[int, ...]]
            ] = []
            has_quant = (
                "∃" in nh or "∀" in nh or "exists" in nh or "forall" in nh
            )
            if has_quant or "∧" in nh or "/\\" in nh:
                if has_quant:
                    q_shadowed, fn_domains = _quantifier_context_before(all_hyps, orig_idx)
                    _hyp_atoms(
                        nh,
                        _NO_BOUND_NAMES,
                        (),
                        _NO_BOUND_NAMES,
                        (),
                        atoms,
                        shadowed=q_shadowed,
                        fn_domains=fn_domains,
                    )
                else:
                    _hyp_atoms(nh, _NO_BOUND_NAMES, (), _NO_BOUND_NAMES, (), atoms)
            else:
                atoms.append((nh, _NO_BOUND_NAMES, (), _NO_BOUND_NAMES, ()))
            hyp_nat_vars: frozenset[str] | None = None
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
                    if hyp_nat_vars is None and "0" in part and ("<" in part or ">" in part):
                        hyp_nat_vars = _nat_vars_before(all_hyps, orig_idx)
                    part_nat_vars = hyp_nat_vars or _NO_BOUND_NAMES
                    if bound:
                        # A quantifier may rebind a `Nat` binder's name at another type, or bind
                        # its own `Nat`-typed variable (`∃ n : Nat, n < 0`).
                        part_nat_vars = (part_nat_vars - bound) | q_nat_vars
                    reason = _check_hypothesis_contradiction(part, part_nat_vars)
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
                if bound and not bound.isdisjoint(_IDENT_EXTRACT_RE.findall(part)):
                    # Mentions a quantified variable: not a fact about the theorem's own context,
                    # but contradictory conjuncts in the exact same quantifier body (`∃ x, P x ∧ ¬ P x`)
                    # share the same witness/value and still contradict each other.
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
        if "∧" in norm_conc and _all_conjuncts_trivial(norm_conc):
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
        elif "∨" in norm_conc and _any_disjunct_trivial(norm_conc):
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
        elif "∧" not in norm_conc and "∨" not in norm_conc and _is_trivially_true(norm_conc):
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
            # The audit is a pure function of (name, metadata comment, the exact bounded text
            # `_split_lean_theorem_header` reads, the check scope), so the cache key must be that
            # full slice: A1 truncated it at the first `:=`, which can sit inside a binder's
            # structure literal (`(h : ({ a := 1 } : S).P)`), letting a later edit to the conclusion
            # or to a later hypothesis hit a stale entry (false negatives across scans in one process).
            cache_key = (thm_name, comment_str, code_only[name_end:next_thm_bound], contradiction_only)
            cached_f = _THM_AUDIT_CACHE.get(cache_key)
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
            parsed = _split_lean_theorem_header(code_only, name_end, next_thm_bound)
            if parsed is not None:
                hyps, conc, extra_binders = parsed
                local_findings.extend(
                    _audit_lean_theorem(
                        thm_name, 0, meta, hyps, conc, contradiction_only, extra_binders
                    )
                )
            _THM_AUDIT_CACHE[cache_key] = tuple(local_findings)
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
    `trusted/audit/{check_trusted.py,TrustedBoundary.lean}`, every non-doc file or symlink
    under `trusted/lean/`, and `trusted/rustc-capture/Cargo.toml`."""
    out: dict[str, Path] = {}
    for rel in ("trusted/audit/check_trusted.py", "trusted/audit/TrustedBoundary.lean",
                "trusted/lean/lean-toolchain", "trusted/rustc-capture/Cargo.toml"):
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
          f"axioms={report['axioms']}\nSource {report['sourceSha256']}; tools/policy {report['toolsSha256']}\n"
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
