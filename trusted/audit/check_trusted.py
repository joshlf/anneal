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
    ("Anneal.FaultSiteCensus", "theory/Anneal/FaultSiteCensus.lean", ["Trusted"], "theory"),
    ("Anneal.UnsafeObligations", "theory/Anneal/UnsafeObligations.lean", ["Trusted", "Anneal.Memory", "Anneal.FaultSiteCensus"], "theory"),
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
    ("Anneal.PureLift.Canaries", "theory/Anneal/PureLift/Canaries.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter"], "theory"),
    ("Anneal.PureLift.MirLiftCoreInterop", "theory/Anneal/PureLift/MirLiftCoreInterop.lean", ["Anneal.BitValidity", "Anneal.MirLiftCore", "Anneal.SepLogicLenses", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Canaries"], "theory"),
    ("Anneal.PureLift.V2026_06_01Bridge", "theory/Anneal/PureLift/V2026_06_01Bridge.lean", ["Anneal.PureLift.MirLiftCoreInterop"], "theory"),
    ("Anneal.PureLift", "theory/Anneal/PureLift.lean", ["Anneal.PureLift.Lens", "Anneal.PureLift.PermTree", "Anneal.PureLift.LoanGraph", "Anneal.PureLift.SpatialPin", "Anneal.PureLift.Plan", "Anneal.PureLift.BlockCfg", "Anneal.PureLift.Adapter", "Anneal.PureLift.Canaries", "Anneal.PureLift.MirLiftCoreInterop", "Anneal.PureLift.V2026_06_01Bridge"], "theory"),
    ("Anneal", "theory/Anneal.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.MirLoops", "Anneal.Scalars", "Anneal.Memory", "Anneal.BitValidity", "Anneal.FaultSiteCensus", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.Rustc.V2026_06_01.SymReflect", "Anneal.Rustc.V2026_06_01.TraceCheck", "Anneal.FunctionalTranslation", "Anneal.MirFuelFree", "Anneal.PureMirExec", "Anneal.MirLiftCore", "Anneal.MirLiftBench", "Anneal.SepLogicLenses", "Anneal.PureLift"], "theory"),
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


def verify_capture_manifest(
    manifest_path: Path,
    root: Path,
    *,
    registry: object = None,
    require_fault_coverage: bool = False,
) -> dict:
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
    if _should_audit_manifest_fault_coverage(
        root, lean_audit_targets, require_fault_coverage=require_fault_coverage
    ):
        _audit_manifest_targets_fault_coverage(
            manifest,
            root,
            lean_audit_targets,
            registry=registry,
            require_receipts=require_fault_coverage
            or (root / "FaultCensus").exists()
            or (root / ".anneal/generated/FaultCensus").exists(),
        )
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
        fault_coverage_audit = audit_checkout_fault_coverage_gate(
            self.checkout,
            self.source_copy,
            require_source_pins=fault_census_source_pins_required(
                self.checkout, self.source_copy
            ),
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
        report["faultCoverageAudit"] = fault_coverage_audit
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
_ARROW_SCAN_RE = re.compile(r"[(){}\[\]]|→|->|∀|∃")
_PIPE_ARM_RE = re.compile(r"\n[ \t]*\|")


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
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            cur = c_close + 1
    # Find the binder's `:` before any nested bracket
    col_idx = find(":", p + 1, cur - 1 if cur > p + 1 else cur)
    if col_idx != -1 and (col_idx + 1 >= cur or seg[col_idx + 1] != "="):
        # Verify no unclosed bracket opened before `col_idx`
        prefix = seg[p + 1 : col_idx]
        if (
            prefix.count("(") == prefix.count(")")
            and prefix.count("{") == prefix.count("}")
            and prefix.count("[") == prefix.count("]")
        ):
            return cur, col_idx
    return cur, -1


def _is_outer_paren_wrapped(t: str) -> bool:
    """Return `True` iff `t` starts with `(` and that opening `(` closes at `len(t) - 1`."""
    n = len(t)
    if n < 2 or t[0] != "(" or t[-1] != ")":
        return False
    find = t.find
    cur = 1
    depth = 1
    while depth > 0 and cur < n:
        c_close = find(")", cur, n)
        if c_close == -1:
            return False
        c_open = find("(", cur, c_close)
        if c_open != -1:
            depth += 1
            cur = c_open + 1
        else:
            depth -= 1
            if depth == 0:
                return c_close == n - 1
            cur = c_close + 1
    return False


def _split_lean_theorem_header(
    code_segment: str, after_name_pos: int, limit_end: int | None = None
) -> tuple[list[tuple[str, str]], str] | None:
    """Given `code_segment`, parse starting at `after_name_pos` (up to `limit_end`):
    - explicit/implicit binders `(x : T)`, `{x : T}`, `[C]` before `:`,
    - top-level `∀ ...,` and `→` (`->`) premises inside the theorem statement, and
    - the final conclusion before top-level `:=`, `where`, or `|`.
    Returns `(hypotheses_as_(binder_names, type_str), conclusion_str)`.
    """
    n = len(code_segment) if limit_end is None else min(len(code_segment), limit_end)
    i = after_name_pos
    if i < n and code_segment[i] == "." and code_segment.startswith(".{", i):
        close_u = code_segment.find("}", i + 2, n)
        if close_u != -1:
            i = close_u + 1

    binders: list[tuple[str, str]] = []
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
        if ch in "({[":
            close_ch = ")" if ch == "(" else ("}" if ch == "{" else "]")
            fast_close = find(close_ch, p + 1, n)
            if fast_close != -1 and find(ch, p + 1, fast_close) == -1:
                col_idx = find(":", p + 1, fast_close)
                if col_idx != -1 and (
                    col_idx + 1 >= fast_close or code_segment[col_idx + 1] != "="
                ):
                    binders.append(
                        (
                            code_segment[p + 1 : col_idx].strip(),
                            code_segment[col_idx + 1 : fast_close].strip(),
                        )
                    )
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
            p = q
            continue
        if ch == "w" and code_segment.startswith("where", p):
            return None
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
        if (
            prefix_slice.count("(") == prefix_slice.count(")")
            and prefix_slice.count("{") == prefix_slice.count("}")
            and prefix_slice.count("[") == prefix_slice.count("]")
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
            while idx_q < n_cur:
                c2 = cur_stmt[idx_q]
                if c2 in " \t\r\n":
                    idx_q += 1
                    continue
                if c2 in "({[":
                    close_ch = ")" if c2 == "(" else ("}" if c2 == "{" else "]")
                    fast_close = find_cur(close_ch, idx_q + 1, n_cur)
                    if fast_close != -1 and find_cur(c2, idx_q + 1, fast_close) == -1:
                        col_in = find_cur(":", idx_q + 1, fast_close)
                        if col_in != -1 and (
                            col_in + 1 >= fast_close or cur_stmt[col_in + 1] != "="
                        ):
                            hyps.append(
                                (
                                    cur_stmt[idx_q + 1 : col_in].strip(),
                                    cur_stmt[col_in + 1 : fast_close].strip(),
                                )
                            )
                        idx_q = fast_close + 1
                        continue
                    r, col_in = _scan_binder_group(cur_stmt, idx_q, n_cur)
                    if col_in != -1:
                        hyps.append(
                            (
                                cur_stmt[idx_q + 1 : col_in].strip(),
                                cur_stmt[col_in + 1 : r - 1].strip(),
                            )
                        )
                    idx_q = r
                    continue
                if c2 == ",":
                    comma_idx = idx_q
                    break
                idx_q += 1
            if comma_idx != -1:
                raw_q_binders = cur_stmt[q_len:comma_idx].strip()
                if ":" in raw_q_binders and raw_q_binders[0] not in "({[":
                    b_n, _, b_t = raw_q_binders.partition(":")
                    hyps.append((b_n.strip(), b_t.strip()))
                cur_stmt = cur_stmt[comma_idx + 1 :].strip()
                continue

        if "→" not in cur_stmt and "->" not in cur_stmt:
            break

        if "->" not in cur_stmt and not cur_stmt.startswith(("∃", "exists")):
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
                    hyps.append(("", p_seg.strip()))
                cur_stmt = arrow_parts[-1].strip()
                if (
                    cur_stmt.startswith("(")
                    or cur_stmt.startswith("∀")
                    or (cur_stmt.startswith("forall") and len(cur_stmt) > 6 and not _is_lean_ident_char(cur_stmt[6]))
                ):
                    continue
                break

        # Single-pass scan for all top-level `→` / `->` premises up to any top-level `∀`/`∃` or `(` wrapper
        depth_a = 0
        seg_start = 0
        advanced = False
        re_loop = False
        for m_a in _ARROW_SCAN_RE.finditer(cur_stmt):
            t_a = m_a.group(0)
            if t_a in "({[":
                depth_a += 1
            elif t_a in ")}]":
                if depth_a > 0:
                    depth_a -= 1
            elif depth_a == 0:
                if t_a == "∀" or t_a == "∃":
                    if m_a.start() == seg_start and t_a == "∀":
                        re_loop = True
                    break
                hyps.append(("", cur_stmt[seg_start : m_a.start()].strip()))
                seg_start = m_a.end()
                advanced = True
                while seg_start < len(cur_stmt) and cur_stmt[seg_start] in " \t\r\n":
                    seg_start += 1
                if seg_start < len(cur_stmt) and (
                    cur_stmt[seg_start] in "(∀"
                    or (cur_stmt[seg_start] == "f" and cur_stmt.startswith("forall", seg_start))
                ):
                    re_loop = True
                    break

        if advanced:
            cur_stmt = cur_stmt[seg_start:].strip()
            if re_loop:
                continue
        break

    return hyps, cur_stmt


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


def _split_top_level(expr: str, sep: str) -> list[str]:
    """Split `expr` on `sep` occurrences outside `()`, `[]`, and `{}` (C-level `finditer`)."""
    if sep not in expr:
        return [_norm_expr(expr)]
    pat = _SPLIT_RE_CACHE.get(sep)
    if pat is None:
        pat = re.compile(r"[()\[\]{}]|" + re.escape(sep))
        _SPLIT_RE_CACHE[sep] = pat
    parts: list[str] = []
    depth = 0
    start = 0
    for m in pat.finditer(expr):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
            if depth > 0:
                depth -= 1
        elif depth == 0:
            parts.append(expr[start : m.start()])
            start = m.end()
    parts.append(expr[start:])
    return [_norm_expr(p) for p in parts]


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


_STANDALONE_EQ_SPLIT_RE = re.compile(r"[()\[\]{}]|(?<![=!<>:])=(?!=)")


def _split_top_level_eq(expr: str) -> list[str]:
    """Split `expr` on top-level standalone `=` (excluding `==`, `:=`, `!=`, `<=`, `>=`) outside `()[]{}`."""
    parts: list[str] = []
    depth = 0
    start = 0
    for m in _STANDALONE_EQ_SPLIT_RE.finditer(expr):
        t = m.group(0)
        if t in "([{":
            depth += 1
        elif t in ")]}":
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
_NAT_ARITH_SPLIT_RE = re.compile(r"[+*/%^]")


def _is_atomic_nat_like(e: str, nat_vars: frozenset[str]) -> bool:
    return (
        e in nat_vars
        or _NUM_LIT_RE.match(e) is not None
        or e.endswith(_NAT_VALUED_SUFFIXES)
        or e.startswith(_NAT_VALUED_PREFIXES)
    )


def _is_nat_like_operand(e: str, nat_vars: frozenset[str]) -> bool:
    """`True` iff `e` is syntactically `Nat`-valued: a numeral, a binder declared `Nat`-like, a
    known `Nat`-valued projection/function (`.length`, `.size`, `.toNat`, `.totalPad`, `.totalSize`,
    `sumSizes ...`, etc.), or a `+`/`*`/`/`/`%`/`^` combination of `Nat`-like operands. Anything
    else (`f x`, an `Int` / `Real` binder, an undeclared name) may be negative, so `e < 0` is NOT
    a syntactic contradiction for it."""
    if _is_atomic_nat_like(e, nat_vars):
        return True
    if any(op in e for op in ("+", "*", "/", "%", "^")):
        atoms = [a.strip("() ") for a in _NAT_ARITH_SPLIT_RE.split(e)]
        return bool(atoms) and all(a and _is_atomic_nat_like(a, nat_vars) for a in atoms)
    return False


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
        and "False" not in hyp_expr
        and "¬" not in hyp_expr
    ):
        return None
    h = _norm_expr(hyp_expr)
    if not h:
        return None
    if h == "False":
        return "`False` hypothesis"
    if h in (
        "true = false",
        "false = true",
        "Bool.true = Bool.false",
        "Bool.false = Bool.true",
    ):
        return f"contradictory boolean equality `{h}`"

    # Check `lhs ≠ rhs` or `¬ lhs = rhs` or `¬ (lhs = rhs)`
    if "≠" in h:
        lhs, _, rhs = h.partition("≠")
        if _norm_expr(lhs) and _norm_expr(lhs) == _norm_expr(rhs):
            return f"irreflexive inequality `{h}`"
    if h.startswith("¬"):
        inner = _norm_expr(h[1:])
        if inner == "True":
            return f"negated `True` hypothesis `{h}`"
        if "=" in inner:
            eq_sides = _split_top_level_eq(inner)
            if len(eq_sides) == 2 and eq_sides[0] and eq_sides[0] == eq_sides[1]:
                return f"negated reflexive equality `{h}`"

    # Check `lhs < rhs` for `x < x`, `< 0`, or numeric `5 < 3`
    if "<" in h and "≤" not in h and "<<" not in h and "←" not in h and "↔" not in h:
        lhs, _, rhs = h.partition("<")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if nl and nl == nr:
            return f"irreflexive strict inequality `{h}`"
        if nr == "0" and _is_nat_like_operand(nl, nat_vars):
            return f"vacuous `< 0` bound `{h}`"
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) >= int(nr):
            return f"contradictory numeric inequality `{nl} < {nr}`"

    # Check `lhs ≤ rhs` for numeric `5 ≤ 3`
    if "≤" in h and "↔" not in h:
        lhs, _, rhs = h.partition("≤")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) > int(nr):
            return f"contradictory numeric inequality `{nl} ≤ {nr}`"

    # Check `lhs > rhs` for `x > x` or numeric `3 > 5`
    if ">" in h and "->" not in h and "=>" not in h and ">>" not in h and "≥" not in h:
        lhs, _, rhs = h.partition(">")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if nl and nl == nr:
            return f"irreflexive strict inequality `{h}`"
        if nl == "0" and _is_nat_like_operand(nr, nat_vars):
            return f"vacuous `0 > ...` bound `{h}`"
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) <= int(nr):
            return f"contradictory numeric inequality `{nl} > {nr}`"

    # Check `lhs = rhs`
    if "=" in h and "==" not in h and "≠" not in h and "≤" not in h and "≥" not in h and ":=" not in h:
        lhs, _, rhs = h.partition("=")
        nl = _norm_expr(lhs)
        nr = _norm_expr(rhs)
        if _NUM_LIT_RE.match(nl) and _NUM_LIT_RE.match(nr) and int(nl) != int(nr):
            return f"distinct numeric literal equality `{nl} = {nr}`"
        if (nl == "none" and (nr == "some" or nr.startswith("some "))) or (
            nr == "none" and (nl == "some" or nl.startswith("some "))
        ):
            return f"disjoint `Option` constructor equality `{h}`"
        if (
            nl == "[]"
            and ("::" in nr or (nr.startswith("[") and nr.endswith("]") and nr != "[]"))
        ) or (
            nr == "[]"
            and ("::" in nl or (nl.startswith("[") and nl.endswith("]") and nl != "[]"))
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


def _audit_lean_theorem(
    name: str,
    line: int,
    meta: dict[str, str],
    hyps: list[tuple[str, str]],
    conclusion: str,
    contradiction_only: bool = False,
) -> list[WaiverPinFinding]:
    """Run all 5 `TRIVIAL_PROOF` and 3-axis metadata checks on a Lean `theorem`/`lemma`.

    With `contradiction_only`, only the hypothesis-contradiction check (step 2) runs, and only
    over named hypotheses (binders such as `(h : False)` / `(h : 0 = 1)` and named `∀`
    binders; anonymous `→` premises are left to the full audit): the scope applied to
    unannotated theorems by default, where a `True` / reflexive conclusion may be a
    deliberate smoke or sanity lemma but an explicitly assumed, syntactically unsatisfiable
    hypothesis is always a vacuity hazard.
    """
    if contradiction_only:
        hyps = [h for h in hyps if h[0]]
    findings: list[WaiverPinFinding] = []
    norm_conc = "" if contradiction_only else _norm_expr(conclusion)

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
    nat_vars: frozenset[str] | None = None
    conc_head = norm_conc.split(" ", 1)[0].lstrip("(¬") if norm_conc else ""
    has_non_eq_neg = "¬" in all_hyps_text
    has_neq = "≠" in all_hyps_text
    any_neg = has_non_eq_neg or has_neq
    seen_pos_hyps: set[str] = set()
    seen_neg_hyps: set[str] = set()
    tautology_hit = False

    has_any_ineq_or_neg_in_all = (
        any_neg
        or "<" in all_hyps_text
        or "≤" in all_hyps_text
        or ">" in all_hyps_text
        or "False" in all_hyps_text
    )
    has_eq_in_all = "=" in all_hyps_text
    conc_head_in_all = bool(conc_head and conc_head in all_hyps_text)

    if has_any_ineq_or_neg_in_all or has_eq_in_all or conc_head_in_all:
        for _, t in hyps:
            has_ineq_or_neg = (
                has_any_ineq_or_neg_in_all
                and (
                    "≠" in t
                    or "<" in t
                    or "≤" in t
                    or ">" in t
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
            if not has_ineq_or_neg and not has_eq and not has_non_eq_neg:
                continue
            parts = [_norm_expr(p) for p in nh.split("∧")] if "∧" in nh else [nh]
            for part in parts:
                if (
                    "=" in part
                    or "≠" in part
                    or "<" in part
                    or "≤" in part
                    or ">" in part
                    or "False" in part
                    or "¬" in part
                ):
                    if nat_vars is None and "0" in part and ("<" in part or ">" in part):
                        nat_vars = frozenset(
                            tok
                            for b_names, b_type in hyps
                            if b_type in _NAT_LIKE_TYPES or b_type.startswith("Fin ")
                            for tok in b_names.split()
                        )
                    reason = _check_hypothesis_contradiction(part, nat_vars or frozenset())
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
                if part.startswith("¬"):
                    inner = _norm_expr(part[1:])
                    seen_neg_hyps.add(inner)
                elif "≠" in part:
                    lhs, _, rhs = part.partition("≠")
                    seen_neg_hyps.add(f"{_norm_expr(lhs)} = {_norm_expr(rhs)}")
                else:
                    seen_pos_hyps.add(part)

        contradictory_pairs = seen_pos_hyps & seen_neg_hyps
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
                hyps, conc = parsed
                local_findings.extend(
                    _audit_lean_theorem(thm_name, 0, meta, hyps, conc, contradiction_only)
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


# ===========================================================================
# Episode 2: Independent MIR Fault-Site Census, Unified PropertyRegistry,
# Cross-Language Source Pins, False-Proof Mutation Probes & Coverage Reconciler
# ===========================================================================

FAULT_COVERAGE_PHASE = "fault-coverage"

MIR_FAULT_CLASSES: tuple[str, ...] = (
    "arith_overflow",
    "div_rem_by_zero",
    "shift_overflow",
    "bounds_check",
    "ptr_deref_invalid",
    "ptr_align_mismatch",
    "tree_borrows_violation",
    "scalar_niche_invalid",
    "uninit_read",
    "storage_live_protected",
    "call_abi_mismatch",
    "unreachable_terminator",
)

FAULT_CLASS_RANK: dict[str, int] = {cls: idx for idx, cls in enumerate(MIR_FAULT_CLASSES)}

LEAN_CTOR_TO_FAULT_CLASS: dict[str, str] = {
    "arithOverflow": "arith_overflow",
    "divRemByZero": "div_rem_by_zero",
    "shiftOverflow": "shift_overflow",
    "boundsCheck": "bounds_check",
    "ptrDerefInvalid": "ptr_deref_invalid",
    "ptrAlignMismatch": "ptr_align_mismatch",
    "treeBorrowsViolation": "tree_borrows_violation",
    "scalarNicheInvalid": "scalar_niche_invalid",
    "uninitRead": "uninit_read",
    "storageLiveProtected": "storage_live_protected",
    "callAbiMismatch": "call_abi_mismatch",
    "unreachableTerminator": "unreachable_terminator",
}

FAULT_CLASS_TO_LEAN_CTOR: dict[str, str] = {
    v: k for k, v in LEAN_CTOR_TO_FAULT_CLASS.items()
}

PROPERTY_STATUS_EMITTED_AND_VERIFIED = "emitted_and_verified"
PROPERTY_STATUS_UNSUPPORTED_FAIL_CLOSED = "unsupported_fail_closed"
PROPERTY_STATUS_UNEMITTED_GAP = "unemitted_gap"

VALID_PROPERTY_STATUSES: frozenset[str] = frozenset((
    PROPERTY_STATUS_EMITTED_AND_VERIFIED,
    PROPERTY_STATUS_UNSUPPORTED_FAIL_CLOSED,
    PROPERTY_STATUS_UNEMITTED_GAP,
))

PROPERTY_REGISTRY: dict[str, dict[str, str]] = {
    "arith_overflow": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Checked/unchecked integer arithmetic and negation overflow",
    },
    "div_rem_by_zero": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Integer division/remainder by zero and signed MIN / -1",
    },
    "shift_overflow": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Bit shift distance >= bit_width or < 0",
    },
    "bounds_check": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Array/slice indexing, pointer offset, and CFG target bounds",
    },
    "ptr_deref_invalid": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Pointer dereference liveness, bounds, and provenance validity",
    },
    "ptr_align_mismatch": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Pointer dereference and copy_nonoverlapping byte alignment",
    },
    "tree_borrows_violation": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Tree Borrows permission and active protector conflicts",
    },
    "scalar_niche_invalid": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Scalar validity range, enum discriminant, transmute, and assume",
    },
    "uninit_read": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Initialized local slot and memory byte reads",
    },
    "storage_live_protected": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Local slot liveness and StorageLive/StorageDead protector checks",
    },
    "call_abi_mismatch": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Function call signature/ABI compatibility and unwind ABI checks",
    },
    "unreachable_terminator": {
        "status": PROPERTY_STATUS_EMITTED_AND_VERIFIED,
        "description": "Unreachable terminator and unreachable_unchecked non-reachability",
    },
}

NATIVE_CONVERGING_CALL_CALLEES: tuple[str, ...] = (
    "core::intrinsics::exact_div",
    "core::intrinsics::ub_checks",
    "core::intrinsics::arith_offset",
    "core::intrinsics::ctlz",
    "core::intrinsics::ctlz_nonzero",
    "core::intrinsics::cttz",
    "core::intrinsics::cttz_nonzero",
    "core::intrinsics::ctpop",
    "core::intrinsics::bswap",
    "core::intrinsics::bitreverse",
    "core::intrinsics::wrapping_add",
    "core::intrinsics::wrapping_sub",
    "core::intrinsics::wrapping_mul",
    "core::intrinsics::saturating_add",
    "core::intrinsics::saturating_sub",
    "core::intrinsics::unchecked_shl",
    "core::intrinsics::unchecked_shr",
    "core::intrinsics::unchecked_add",
    "core::intrinsics::unchecked_sub",
    "core::intrinsics::unchecked_mul",
    "core::intrinsics::unchecked_div",
    "core::intrinsics::unchecked_rem",
    "core::intrinsics::three_way_compare",
    "core::intrinsics::size_of_val",
    "core::intrinsics::align_of_val",
)

NATIVE_DIVERGING_CALL_CALLEES: tuple[str, ...] = (
    "core::hint::unreachable_unchecked",
    "std::hint::unreachable_unchecked",
    "core::intrinsics::unreachable",
    "core::panicking::panic_nounwind",
    "core::panicking::panic_nounwind_fmt",
    "core::panicking::panic_nounwind_fmt::panic_impl",
    "core::panicking::panic_nounwind_nobacktrace",
    "core::panicking::panic_in_cleanup",
    "core::panicking::panic_cannot_unwind",
    "core::panicking::panic_misaligned_pointer_dereference",
    "core::panicking::panic_null_pointer_dereference",
    "core::panicking::panic_invalid_enum_construction",
    "core::intrinsics::abort",
    "core::panicking::panic",
    "core::panicking::panic_fmt",
    "core::panicking::panic_fmt::panic_impl",
    "core::panicking::const_panic_fmt",
    "core::panicking::assert_failed",
    "core::panicking::assert_failed_inner",
    "core::panicking::assert_matches_failed",
    "core::slice::index::slice_index_fail",
    "core::panicking::panic_bounds_check",
    "core::panicking::panic_explicit",
    "core::panicking::panic_display",
    "core::panicking::panic_str_2015",
    "core::panicking::unreachable_display",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::result::unwrap_failed",
    "core::panicking::panic_const::panic_const_add_overflow",
    "core::panicking::panic_const::panic_const_sub_overflow",
    "core::panicking::panic_const::panic_const_mul_overflow",
    "core::panicking::panic_const::panic_const_div_overflow",
    "core::panicking::panic_const::panic_const_rem_overflow",
    "core::panicking::panic_const::panic_const_neg_overflow",
    "core::panicking::panic_const::panic_const_shr_overflow",
    "core::panicking::panic_const::panic_const_shl_overflow",
    "core::panicking::panic_const::panic_const_div_by_zero",
    "core::panicking::panic_const::panic_const_rem_by_zero",
)

_NATIVE_CONVERGING_SET: frozenset[str] = frozenset(NATIVE_CONVERGING_CALL_CALLEES)
_NATIVE_DIVERGING_SET: frozenset[str] = frozenset(NATIVE_DIVERGING_CALL_CALLEES)


class FaultSite:
    __slots__ = ("block_idx", "stmt_idx", "fault_class")

    def __init__(self, block_idx: int, stmt_idx: int, fault_class: str) -> None:
        if type(block_idx) is not int or block_idx < 0:
            raise ValueError(f"invalid FaultSite block_idx: {block_idx!r}")
        if type(stmt_idx) is not int or stmt_idx < 0:
            raise ValueError(f"invalid FaultSite stmt_idx: {stmt_idx!r}")
        if not isinstance(fault_class, str) or fault_class not in FAULT_CLASS_RANK:
            raise ValueError(f"invalid FaultSite fault_class: {fault_class!r}")
        self.block_idx = block_idx
        self.stmt_idx = stmt_idx
        self.fault_class = fault_class

    def _key(self) -> tuple[int, int, int]:
        return (self.block_idx, self.stmt_idx, FAULT_CLASS_RANK[self.fault_class])

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FaultSite):
            return NotImplemented
        return (
            self.block_idx == other.block_idx
            and self.stmt_idx == other.stmt_idx
            and self.fault_class == other.fault_class
        )

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, FaultSite):
            return NotImplemented
        return self._key() < other._key()

    def __le__(self, other: object) -> bool:
        if not isinstance(other, FaultSite):
            return NotImplemented
        return self._key() <= other._key()

    def __hash__(self) -> int:
        return hash((self.block_idx, self.stmt_idx, self.fault_class))

    def __repr__(self) -> str:
        return f"FaultSite({self.block_idx}, {self.stmt_idx}, {self.fault_class!r})"

    def __str__(self) -> str:
        return f"(bb{self.block_idx}, stmt{self.stmt_idx}, {self.fault_class})"

    def to_dict(self) -> dict[str, Any]:
        return {
            "block_idx": self.block_idx,
            "stmt_idx": self.stmt_idx,
            "fault_class": self.fault_class,
        }

    @classmethod
    def from_dict(cls, obj: object) -> "FaultSite":
        if not isinstance(obj, dict) or set(obj) != {"block_idx", "stmt_idx", "fault_class"}:
            raise ValueError(f"malformed FaultSite object: {obj!r}")
        return cls(obj["block_idx"], obj["stmt_idx"], obj["fault_class"])


class CensusScanError(ValueError):
    def __init__(self, kind: str, message: str) -> None:
        super().__init__(message)
        self.kind = kind
        self.message = message


def validate_property_registry(
    registry: object = None, *, require_all_verified: bool = False
) -> dict[str, dict[str, str]]:
    if registry is None:
        registry = PROPERTY_REGISTRY
    if not isinstance(registry, dict):
        raise Failure(1, FAULT_COVERAGE_PHASE, "PropertyRegistry must be a dict")
    missing = [cls for cls in MIR_FAULT_CLASSES if cls not in registry]
    extra = [k for k in registry if k not in FAULT_CLASS_RANK]
    if missing or extra:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"PropertyRegistry keys do not match canonical 12 MirFaultClasses (missing={missing}, extra={extra})",
        )
    out: dict[str, dict[str, str]] = {}
    unverified: list[str] = []
    for cls in MIR_FAULT_CLASSES:
        entry = registry[cls]
        if isinstance(entry, str):
            status = entry
            desc = PROPERTY_REGISTRY[cls]["description"]
        elif isinstance(entry, dict):
            status = entry.get("status")
            desc = entry.get("description", PROPERTY_REGISTRY[cls]["description"])
        else:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"malformed PropertyRegistry descriptor for {cls}: {entry!r}"
            )
        if not isinstance(status, str) or status not in VALID_PROPERTY_STATUSES:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"invalid PropertyStatus {status!r} for {cls} in PropertyRegistry",
            )
        if not isinstance(desc, str) or not desc.strip():
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing description for {cls} in PropertyRegistry",
            )
        if status != PROPERTY_STATUS_EMITTED_AND_VERIFIED:
            unverified.append(f"{cls}={status}")
        out[cls] = {"status": status, "description": desc}
    if require_all_verified and unverified:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"PropertyRegistry has non-verified fault classes: {', '.join(unverified)}",
        )
    return out


def _is_lean_ident_continue(ch: str) -> bool:
    return ch.isalnum() or ch in ("_", "'", "!", "?")


def _lex_dotted_ident(
    src: str, start: int, *, allow_any_guillemet: bool = False
) -> tuple[str, int]:
    n = len(src)
    i = start
    parts: list[str] = []
    while True:
        if i < n and src[i] == "«":
            i += 1
            seg_start = i
            while i < n and src[i] != "»" and src[i] != "\n":
                i += 1
            if i >= n or src[i] != "»":
                raise CensusScanError(
                    "unterminated_guillemet_ident",
                    "unterminated or multi-line Lean guillemet identifier `«...»`",
                )
            seg = src[seg_start:i]
            if not allow_any_guillemet and (
                not seg
                or "." in seg
                or any(c.isspace() for c in seg)
                or seg in _LEAN_GUILLEMET_FORBIDDEN_SEGMENTS
            ):
                raise CensusScanError(
                    "malformed_syntax",
                    f"disallowed guillemet identifier segment `«{seg}»`",
                )
            parts.append(seg)
            i += 1
        else:
            seg_start = i
            while i < n and _is_lean_ident_continue(src[i]):
                i += 1
            if i == seg_start:
                raise CensusScanError(
                    "malformed_syntax", "empty identifier segment"
                )
            parts.append(src[seg_start:i])
        if (
            i + 1 < n
            and src[i] == "."
            and (src[i + 1].isalpha() or src[i + 1] in ("_", "«"))
        ):
            parts.append(".")
            i += 1
        else:
            break
    return ("".join(parts), i)


def _lex_string_escape(
    src: str, i: int, out: list[str], interpolated: bool
) -> int:
    n = len(src)
    if i >= n:
        raise CensusScanError(
            "unterminated_string_literal", "unterminated Lean string literal"
        )
    ch = src[i]
    if ch == "\\":
        out.append("\\")
        return i + 1
    if ch == '"':
        out.append('"')
        return i + 1
    if ch == "'":
        out.append("'")
        return i + 1
    if ch == "n":
        out.append("\n")
        return i + 1
    if ch == "r":
        out.append("\r")
        return i + 1
    if ch == "t":
        out.append("\t")
        return i + 1
    if ch == "x":
        if i + 3 > n or not all(c in "0123456789abcdefABCDEF" for c in src[i + 1 : i + 3]):
            raise CensusScanError(
                "malformed_syntax", "invalid Lean string escape (expected hex digits)"
            )
        code = int(src[i + 1 : i + 3], 16)
        out.append(chr(code))
        return i + 3
    if ch == "u":
        if i + 5 > n or not all(c in "0123456789abcdefABCDEF" for c in src[i + 1 : i + 5]):
            raise CensusScanError(
                "malformed_syntax", "invalid Lean string escape (expected hex digits)"
            )
        code = int(src[i + 1 : i + 5], 16)
        if 0xD800 <= code <= 0xDFFF:
            raise CensusScanError(
                "malformed_syntax", "invalid Lean string escape (surrogate code point)"
            )
        out.append(chr(code))
        return i + 5
    if ch == "\n":
        j = i + 1
        while j < n and src[j].isspace():
            j += 1
        return j
    if ch == "{" and interpolated:
        out.append("{")
        return i + 1
    raise CensusScanError(
        "malformed_syntax", f"invalid Lean string escape `\\{ch}`"
    )


def _lex_char_literal(src: str, open_quote: int) -> tuple[str, int] | None:
    n = len(src)
    prev_is_ident = open_quote > 0 and _is_lean_ident_continue(src[open_quote - 1])
    if prev_is_ident or open_quote + 2 >= n:
        return None
    if src[open_quote + 1] == "\\":
        decoded: list[str] = []
        after_esc = _lex_string_escape(src, open_quote + 2, decoded, False)
        s = "".join(decoded)
        if len(s) != 1 or after_esc >= n or src[after_esc] != "'":
            raise CensusScanError(
                "malformed_syntax", "unterminated escaped character literal"
            )
        return (s, after_esc + 1)
    if src[open_quote + 2] == "'" and src[open_quote + 1] not in ("'", "\n"):
        return (src[open_quote + 1], open_quote + 3)
    return None


def _lex_raw_string(src: str, start: int) -> tuple[str, int] | None:
    n = len(src)
    prev_is_ident = start > 0 and _is_lean_ident_continue(src[start - 1])
    if prev_is_ident or start + 1 >= n or src[start] != "r" or src[start + 1] not in ('"', "#"):
        return None
    hashes = 0
    k = start + 1
    while k < n and src[k] == "#":
        hashes += 1
        k += 1
    if k >= n or src[k] != '"':
        return None
    k += 1
    closing = '"' + ("#" * hashes)
    end_pos = src.find(closing, k)
    if end_pos < 0:
        raise CensusScanError(
            "unterminated_raw_string", "unterminated Lean raw string literal"
        )
    return (src[k:end_pos], end_pos + len(closing))


def _lex_standard_string(src: str, after_open_quote: int) -> tuple[str, int]:
    n = len(src)
    i = after_open_quote
    out: list[str] = []
    while i < n:
        ch = src[i]
        if ch == '"':
            return ("".join(out), i + 1)
        if ch == "\\":
            i = _lex_string_escape(src, i + 1, out, False)
        else:
            out.append(ch)
            i += 1
    raise CensusScanError(
        "unterminated_string_literal", "unterminated Lean string literal"
    )


def _lex_interpolated_string(src: str, after_open_quote: int) -> tuple[str, int]:
    n = len(src)
    i = after_open_quote
    out: list[str] = []
    while i < n:
        ch = src[i]
        if ch == '"':
            return ("".join(out), i + 1)
        if ch == "\\":
            try:
                i = _lex_string_escape(src, i + 1, out, True)
            except CensusScanError as err:
                if err.kind == "unterminated_string_literal":
                    raise CensusScanError(
                        "unterminated_interpolated_string",
                        "unterminated Lean interpolated string literal",
                    ) from err
                raise
            continue
        if ch == "{":
            brace_depth = 1
            out.append("{")
            i += 1
            while i < n and brace_depth > 0:
                if (src[i] == "-" and i + 1 < n and src[i + 1] == "-") or (
                    src[i] == "/" and i + 1 < n and src[i + 1] == "-"
                ):
                    raise CensusScanError(
                        "malformed_syntax", "comment inside string interpolation"
                    )
                if src[i] == "'":
                    ch_res = _lex_char_literal(src, i)
                    if ch_res is not None:
                        lit_ch, next_i = ch_res
                        out.append(f"'{lit_ch}'")
                        i = next_i
                        continue
                if src[i] == "«":
                    ident, next_i = _lex_dotted_ident(
                        src, i, allow_any_guillemet=True
                    )
                    out.append(f"«{ident}»")
                    i = next_i
                    continue
                raw_res = _lex_raw_string(src, i)
                if raw_res is not None:
                    raw_s, next_i = raw_res
                    out.append(f'"{raw_s}"')
                    i = next_i
                    continue
                if src[i].isalpha() or src[i] == "_":
                    ident, next_i = _lex_dotted_ident(src, i)
                    out.append(ident)
                    if ident.endswith("!") and next_i < n and src[next_i] == '"':
                        inner_interp, after_interp = _lex_interpolated_string(
                            src, next_i + 1
                        )
                        out.append(f'"{inner_interp}"')
                        i = after_interp
                    else:
                        i = next_i
                    continue
                if src[i] == '"':
                    try:
                        inner_s, next_i = _lex_standard_string(src, i + 1)
                    except CensusScanError as err:
                        raise CensusScanError(
                            "unterminated_interpolated_string",
                            "unterminated Lean interpolated string literal",
                        ) from err
                    out.append(f'"{inner_s}"')
                    i = next_i
                elif src[i] == "{":
                    brace_depth += 1
                    out.append("{")
                    i += 1
                elif src[i] == "}":
                    brace_depth -= 1
                    out.append("}")
                    i += 1
                else:
                    out.append(src[i])
                    i += 1
            if brace_depth != 0:
                raise CensusScanError(
                    "unterminated_interpolated_string",
                    "unterminated Lean interpolated string literal",
                )
            continue
        out.append(ch)
        i += 1
    raise CensusScanError(
        "unterminated_interpolated_string",
        "unterminated Lean interpolated string literal",
    )


def tokenize_lean_source(src: str) -> list[tuple[str, Any]]:
    n = len(src)
    i = 0
    tokens: list[tuple[str, Any]] = []
    punct_map = {
        "(": ("LParen", "("),
        ")": ("RParen", ")"),
        "{": ("LBrace", "{"),
        "}": ("RBrace", "}"),
        "[": ("LBracket", "["),
        "]": ("RBracket", "]"),
        ",": ("Comma", ","),
        ";": ("Semicolon", ";"),
        ".": ("Dot", "."),
    }

    while i < n:
        ch = src[i]
        if ch.isspace():
            i += 1
            continue
        if ch == "-" and i + 1 < n and src[i + 1] == "-":
            nl = src.find("\n", i + 2)
            i = n if nl < 0 else nl + 1
            continue
        if ch == "/" and i + 1 < n and src[i + 1] == "-":
            i += 2
            depth = 1
            while i < n and depth > 0:
                if src[i] == "/" and i + 1 < n and src[i + 1] == "-":
                    depth += 1
                    i += 2
                elif src[i] == "-" and i + 1 < n and src[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth != 0:
                raise CensusScanError(
                    "unterminated_block_comment",
                    "unterminated Lean block comment `/- ... -/`",
                )
            continue
        if ch == "'":
            ch_res = _lex_char_literal(src, i)
            if ch_res is not None:
                lit_ch, next_i = ch_res
                tokens.append(("CharLit", lit_ch))
                i = next_i
                continue
        if ch == "«":
            ident, next_i = _lex_dotted_ident(src, i)
            tokens.append(("Ident", ident))
            i = next_i
            continue
        raw_res = _lex_raw_string(src, i)
        if raw_res is not None:
            content, next_i = raw_res
            tokens.append(("StrLit", content))
            i = next_i
            continue
        if ch in ("s", "f") and i + 2 < n and src[i + 1] == "!" and src[i + 2] == '"':
            content, next_i = _lex_interpolated_string(src, i + 3)
            tokens.append(("StrLit", content))
            i = next_i
            continue
        if ch == '"':
            content, next_i = _lex_standard_string(src, i + 1)
            tokens.append(("StrLit", content))
            i = next_i
            continue
        if ch in punct_map:
            tokens.append(punct_map[ch])
            i += 1
            continue
        if ch == ":":
            if i + 1 < n and src[i + 1] == "=":
                tokens.append(("ColonEq", ":="))
                i += 2
            else:
                tokens.append(("Colon", ":"))
                i += 1
            continue
        if ch.isdigit() and ch.isascii():
            start = i
            i += 1
            while i < n and ((src[i].isalnum() and src[i].isascii()) or src[i] == "_"):
                i += 1
            raw_num = src[start:i].replace("_", "")
            try:
                if raw_num.startswith(("0x", "0X")):
                    val = int(raw_num[2:], 16)
                elif raw_num.startswith(("0b", "0B")):
                    val = int(raw_num[2:], 2)
                elif raw_num.startswith(("0o", "0O")):
                    val = int(raw_num[2:], 8)
                else:
                    if not raw_num.isdigit():
                        raise ValueError("non-digit in decimal literal")
                    val = int(raw_num, 10)
            except ValueError as err:
                raise CensusScanError(
                    "malformed_syntax", f"invalid numeric literal `{raw_num}`"
                ) from err
            if val < 0 or val >= (1 << 128):
                raise CensusScanError(
                    "malformed_syntax", f"u128 overflow in numeric literal `{raw_num}`"
                )
            tokens.append(("NatLit", val))
            continue
        if ch.isalpha() or ch == "_":
            ident, next_i = _lex_dotted_ident(src, i)
            if ident.endswith("!") and next_i < n and src[next_i] == '"':
                content, after = _lex_interpolated_string(src, next_i + 1)
                tokens.append(("StrLit", content))
                i = after
                continue
            tokens.append(("Ident", ident))
            i = next_i
            continue
        start = i
        i += 1
        while (
            i < n
            and not src[i].isspace()
            and src[i] not in ("(", ")", "{", "}", "[", "]", ",", ";", ":", ".", '"', "«")
        ):
            if (src[i] == "-" and i + 1 < n and src[i + 1] == "-") or (
                src[i] == "/" and i + 1 < n and src[i + 1] == "-"
            ):
                break
            i += 1
        tokens.append(("Ident", src[start:i]))

    return tokens


_MIR_AST_NAMESPACES: tuple[str, ...] = (
    "MirAst",
    "Trusted.MirAst",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "_root_.Trusted.Rustc.V2026_06_01.MirAst",
)

_STRICT_MODULE_OPENS: frozenset[str] = frozenset((
    "Trusted.Rustc.V2026_06_01.Layout",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "Trusted.Rustc.V2026_06_01.MirSemantics",
    "Trusted.VerificationResult",
    "Trusted.MirAst",
    "Trusted.MirSemantics",
))

_STRICT_MODULE_IMPORTS: frozenset[str] = frozenset((
    "Trusted",
    "Trusted.MirAst",
    "Trusted.MirSemantics",
    "Trusted.VerificationResult",
    "Trusted.Rustc.V2026_06_01.Layout",
    "Trusted.Rustc.V2026_06_01.MirAst",
    "Trusted.Rustc.V2026_06_01.MirSemantics",
    "Trusted.Rustc.V2026_06_01",
    "Trusted.Rustc",
))

_MIR_AST_TYPE_NAMES: frozenset[str] = frozenset((
    "AggregateKind",
    "BasicBlockData",
    "BinOp",
    "Bool",
    "BorrowKind",
    "CapturedMir",
    "CastKind",
    "ConstOperand",
    "ConstScalar",
    "ConstValue",
    "ContractRole",
    "List",
    "LocalDecl",
    "MirPhaseTag",
    "Mutability",
    "Nat",
    "NonDivergingIntrinsic",
    "NullOp",
    "Operand",
    "Option",
    "Place",
    "ProjectionElem",
    "ProvenancePtr",
    "RetagKind",
    "RigidTy",
    "Rvalue",
    "ScalarInt",
    "Statement",
    "StatementKind",
    "SwitchTargets",
    "Terminator",
    "TerminatorKind",
    "Ty",
    "UnOp",
    "UnwindAction",
))

# `[adv ep2-B2]` `Trusted.VerificationResult` names that a strict `Mir/<Item>.lean`
# declaration may not reuse. Kept separate from `_MIR_AST_TYPE_NAMES` so that the
# namespace-segment check (which sees the CamelCase crate name, e.g. a crate named
# `item_spec` -> `Mir.ItemSpec.<item>`) does not reject legitimate crates; qualified
# (`_root_.` / dotted) declarations are rejected outright, so these plain names can never
# leak out of the module's own `Mir.<Item>` namespace anyway.
_MIR_SHADOW_DECL_NAMES: frozenset[str] = _MIR_AST_TYPE_NAMES | frozenset((
    "CrateClaim",
    "CrateVerificationResult",
    "ItemProof",
    "ItemSpec",
    "MirCallContract",
    "ModularItemProof",
    "ModularItemSpec",
    "ModularVerificationClaim",
    "ModularVerificationResult",
    "StatefulEquivClaim",
    "StatefulEquivItemProof",
    "StatefulEquivItemSpec",
    "StatefulEquivVerificationResult",
    "StatefulItemProof",
    "StatefulItemSpec",
    "StatefulVerificationClaim",
    "StatefulVerificationResult",
    "TotalItemProof",
    "TotalItemSpec",
    "TotalVerificationClaim",
    "TotalVerificationResult",
    "UbExceptionClaim",
    "UbExceptionItemProof",
    "UbExceptionItemSpec",
    "UbExceptionVerificationResult",
    "VerificationClaim",
    "VerificationResult",
))

_LEAN_COMMAND_KEYWORDS: frozenset[str] = frozenset((
    "def",
    "theorem",
    "lemma",
    "abbrev",
    "example",
    "instance",
    "structure",
    "inductive",
    "class",
    "opaque",
    "axiom",
    "namespace",
    "end",
    "section",
    "open",
    "import",
    "export",
    "set_option",
    "attribute",
    "local",
    "scoped",
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "mutual",
    "variable",
    "universe",
    "macro",
    "macro_rules",
    "syntax",
    "notation",
    "elab",
    "elab_rules",
    "deriving",
    "initialize",
    "builtin_initialize",
))

_LEAN_GUILLEMET_FORBIDDEN_SEGMENTS: frozenset[str] = _LEAN_COMMAND_KEYWORDS | frozenset((
    "_root_",
    "where",
    "with",
    "in",
    "fun",
    "forall",
    "match",
    "let",
    "have",
    "by",
    "do",
    "if",
    "then",
    "else",
))


def _is_valid_captured_mir_type(ty: str) -> bool:
    if ty == "CapturedMir":
        return True
    for ns in _MIR_AST_NAMESPACES:
        if ty == f"{ns}.CapturedMir":
            return True
    return False


def _check_ctor_qualifier(full: str, short: str, type_name: str) -> None:
    if full == f".{short}":
        return
    qualified = f"{type_name}.{short}"
    if full == qualified:
        return
    for ns in _MIR_AST_NAMESPACES:
        if full == f"{ns}.{qualified}":
            return
    raise CensusScanError(
        "malformed_syntax",
        f"constructor head `{full}` is not a `{type_name}` constructor (expected `.{short}` or `{type_name}.{short}`)",
    )


def _fc_is_lean_command_start(tok: tuple[str, Any]) -> bool:
    if tok[0] != "Ident":
        return False
    kw: str = tok[1]
    return kw.startswith("#") or kw.startswith("@") or kw in _LEAN_COMMAND_KEYWORDS


def _shadows_mir_ast_name(name: str) -> bool:
    return any(seg in _MIR_AST_TYPE_NAMES for seg in name.split("."))


def _shadows_mir_decl_name(name: str) -> bool:
    return any(seg in _MIR_SHADOW_DECL_NAMES for seg in name.split("."))


class _MirTokenCursor:
    def __init__(self, tokens: list[tuple[str, Any]], pos: int = 0) -> None:
        self.tokens = tokens
        self.pos = pos

    def peek(self) -> tuple[str, Any] | None:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def next(self) -> tuple[str, Any] | None:
        if self.pos < len(self.tokens):
            tok = self.tokens[self.pos]
            self.pos += 1
            return tok
        return None

    def expect(self, kind: str) -> Any:
        tok = self.next()
        if tok is None:
            raise CensusScanError(
                "malformed_syntax", f"unexpected EOF while expecting {kind}"
            )
        if tok[0] != kind:
            raise CensusScanError(
                "malformed_syntax", f"expected {kind}, found {tok!r}"
            )
        return tok[1]

    def parse_ctor_head(self) -> tuple[str, str]:
        had_leading_dot = False
        pk = self.peek()
        if pk is not None and pk[0] == "Dot":
            self.next()
            had_leading_dot = True
        tok = self.next()
        if tok is None or tok[0] != "Ident":
            raise CensusScanError(
                "malformed_syntax", f"expected constructor identifier, found {tok!r}"
            )
        full: str = tok[1]
        short = full.rsplit(".", 1)[-1]
        full_norm = f".{full}" if had_leading_dot else full
        return (full_norm, short)

    def with_optional_parens(self, fn):
        paren_depth = 0
        while True:
            pk = self.peek()
            if pk is not None and pk[0] == "LParen":
                self.next()
                paren_depth += 1
            else:
                break
        val = fn(self)
        for _ in range(paren_depth):
            self.expect("RParen")
        return val

    def skip_balanced_expr(self) -> None:
        tok = self.next()
        if tok is None:
            raise CensusScanError(
                "malformed_syntax", "unexpected EOF while skipping expression"
            )
        kind = tok[0]
        if kind in ("LParen", "LBrace", "LBracket"):
            close_kind = {
                "LParen": "RParen",
                "LBrace": "RBrace",
                "LBracket": "RBracket",
            }[kind]
            depth = 1
            while depth > 0:
                nxt = self.next()
                if nxt is None:
                    raise CensusScanError(
                        "malformed_syntax", f"unbalanced {kind} in expression"
                    )
                if nxt[0] == kind:
                    depth += 1
                elif nxt[0] == close_kind:
                    depth -= 1
            return
        if kind == "Dot":
            nxt = self.next()
            if nxt is None or nxt[0] != "Ident":
                raise CensusScanError(
                    "malformed_syntax", f"expected identifier after `.`, found {nxt!r}"
                )
            while True:
                pk = self.peek()
                if pk is not None and pk[0] in (
                    "LParen",
                    "LBrace",
                    "LBracket",
                    "NatLit",
                    "StrLit",
                    "CharLit",
                    "Dot",
                ):
                    self.skip_balanced_expr()
                else:
                    break
            return
        if kind == "Ident":
            while True:
                pk = self.peek()
                if pk is not None and pk[0] in (
                    "LParen",
                    "LBrace",
                    "LBracket",
                    "NatLit",
                    "StrLit",
                    "CharLit",
                    "Dot",
                ):
                    self.skip_balanced_expr()
                else:
                    break
            return
        if kind in ("NatLit", "StrLit", "CharLit"):
            return
        raise CensusScanError(
            "malformed_syntax", f"unexpected token while skipping expression: {tok!r}"
        )

    def skip_atomic_expr(self) -> None:
        pk = self.peek()
        if pk is None:
            raise CensusScanError(
                "malformed_syntax", "unexpected EOF while skipping atomic expression"
            )
        if pk[0] in ("LParen", "LBrace", "LBracket"):
            self.skip_balanced_expr()
            return
        if pk[0] == "Dot":
            self.next()
            nxt = self.next()
            if nxt is None or nxt[0] != "Ident":
                raise CensusScanError(
                    "malformed_syntax", f"expected identifier after `.`, found {nxt!r}"
                )
            return
        if pk[0] in ("Ident", "NatLit", "StrLit", "CharLit"):
            self.next()
            return
        raise CensusScanError(
            "malformed_syntax",
            f"unexpected token while skipping atomic expression: {pk!r}",
        )

    def parse_usize(self) -> int:
        def _inner(cur: "_MirTokenCursor") -> int:
            tok = cur.next()
            if tok is None:
                raise CensusScanError("malformed_syntax", "unexpected EOF expecting usize")
            if tok[0] == "NatLit":
                val = int(tok[1])
                if val < 0 or val >= (1 << 64):
                    raise CensusScanError("malformed_syntax", f"usize overflow: {val}")
                return val
            if tok[0] == "Dot":
                nxt = cur.next()
                if nxt == ("Ident", "zero"):
                    return 0
                raise CensusScanError(
                    "malformed_syntax", f"expected Nat literal, found `.{nxt!r}`"
                )
            if tok == ("Ident", "Nat.zero"):
                return 0
            raise CensusScanError(
                "malformed_syntax", f"expected usize literal, found {tok!r}"
            )

        return self.with_optional_parens(_inner)

    def parse_u64(self) -> int:
        return self.parse_usize()

    def parse_u128(self) -> int:
        def _inner(cur: "_MirTokenCursor") -> int:
            tok = cur.next()
            if tok is not None and tok[0] == "NatLit":
                val = int(tok[1])
                if val < 0 or val >= (1 << 128):
                    raise CensusScanError("malformed_syntax", f"u128 overflow: {val}")
                return val
            raise CensusScanError(
                "malformed_syntax", f"expected u128 literal, found {tok!r}"
            )

        return self.with_optional_parens(_inner)

    def parse_bool(self) -> bool:
        def _inner(cur: "_MirTokenCursor") -> bool:
            full, short = cur.parse_ctor_head()
            if full != short:
                _check_ctor_qualifier(full, short, "Bool")
            if short == "true":
                return True
            if short == "false":
                return False
            raise CensusScanError(
                "malformed_syntax", f"expected `true` or `false`, found `{short}`"
            )

        return self.with_optional_parens(_inner)

    def parse_string(self) -> str:
        def _inner(cur: "_MirTokenCursor") -> str:
            tok = cur.next()
            if tok is not None and tok[0] == "StrLit":
                return str(tok[1])
            raise CensusScanError(
                "malformed_syntax", f"expected string literal, found {tok!r}"
            )

        return self.with_optional_parens(_inner)

    def parse_list(self, parse_elem) -> list[Any]:
        pk = self.peek()
        if pk is not None and pk[0] == "LBracket":
            self.next()
            items: list[Any] = []
            while True:
                pk2 = self.peek()
                if pk2 is not None and pk2[0] == "RBracket":
                    break
                items.append(parse_elem(self))
                pk3 = self.peek()
                if pk3 is not None and pk3[0] == "Comma":
                    self.next()
                else:
                    break
            self.expect("RBracket")
            return items

        def _inner(cur: "_MirTokenCursor") -> list[Any]:
            pk_in = cur.peek()
            if pk_in is not None and pk_in[0] == "LBracket":
                return cur.parse_list(parse_elem)
            full, short = cur.parse_ctor_head()
            if short == "nil" and full in ("List.nil", ".nil"):
                return []
            if short == "cons" and full in ("List.cons", ".cons"):
                head = parse_elem(cur)
                tail = cur.parse_list(parse_elem)
                return [head, *tail]
            raise CensusScanError(
                "malformed_syntax",
                f"expected inline `List.nil`, `List.cons`, or `[...]`, found `{full}`",
            )

        return self.with_optional_parens(_inner)

    def parse_option(self, parse_inner):
        def _inner(cur: "_MirTokenCursor"):
            full, short = cur.parse_ctor_head()
            if short == "none" and full in ("Option.none", ".none", "none"):
                return None
            if short == "some" and full in ("Option.some", ".some", "some"):
                return parse_inner(cur)
            raise CensusScanError(
                "malformed_syntax",
                f"expected `Option.some` or `Option.none`, found `{full}`",
            )

        return self.with_optional_parens(_inner)

    def parse_record(self, on_field) -> None:
        def _inner(cur: "_MirTokenCursor") -> None:
            cur.expect("LBrace")
            seen_fields: set[str] = set()
            while True:
                pk = cur.peek()
                if pk is not None and pk[0] == "RBrace":
                    break
                tok = cur.next()
                if tok is None or tok[0] != "Ident":
                    raise CensusScanError(
                        "malformed_syntax", f"expected record field name, found {tok!r}"
                    )
                field_name: str = tok[1]
                if field_name in seen_fields:
                    raise CensusScanError(
                        "malformed_syntax", f"duplicate record field `{field_name}`"
                    )
                seen_fields.add(field_name)
                cur.expect("ColonEq")
                on_field(field_name, cur)
                pk2 = cur.peek()
                if pk2 is not None and pk2[0] in ("Comma", "Semicolon"):
                    cur.next()
            cur.expect("RBrace")

        self.with_optional_parens(_inner)

    def parse_captured_mir_metadata(self) -> dict[str, Any]:
        state: dict[str, Any] = {
            "def_path": None,
            "has_phase": False,
            "role": None,
            "has_arg_count": False,
            "has_local_decls": False,
            "basic_blocks": None,
            "has_fn_abi": False,
            "has_layouts": False,
            "has_allocations": False,
            "trait_impls": [],
        }

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "defPath":
                state["def_path"] = cur.parse_string()
            elif field == "phase":
                cur.parse_mir_phase_tag()
                state["has_phase"] = True
            elif field == "role":
                state["role"] = cur.parse_contract_role()
            elif field == "argCount":
                cur.parse_usize()
                state["has_arg_count"] = True
            elif field == "localDecls":
                cur.parse_list(lambda c: c.skip_atomic_expr())
                state["has_local_decls"] = True
            elif field == "basicBlocks":
                state["basic_blocks"] = cur.parse_list(lambda c: c.parse_basic_block())
            elif field == "fnAbi":
                cur.skip_balanced_expr()
                state["has_fn_abi"] = True
            elif field == "layouts":
                cur.skip_balanced_expr()
                state["has_layouts"] = True
            elif field == "allocations":
                cur.parse_list(lambda c: c.skip_atomic_expr())
                state["has_allocations"] = True
            elif field == "typeParamCount":
                cur.parse_usize()
            elif field == "genericParams":
                cur.parse_list(lambda c: c.skip_atomic_expr())
            elif field == "traitImpls":
                state["trait_impls"] = cur.parse_list(
                    lambda c: c.parse_trait_impl_entry()
                )
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown CapturedMir field `{field}`"
                )

        self.parse_record(_on_field)
        if state["def_path"] is None:
            raise CensusScanError(
                "malformed_syntax",
                "CapturedMir record is missing required `defPath` field",
            )
        if state["role"] is None:
            raise CensusScanError(
                "malformed_syntax",
                "CapturedMir record is missing required `role` field",
            )
        for key, name in (
            ("has_phase", "phase"),
            ("has_arg_count", "argCount"),
            ("has_local_decls", "localDecls"),
            ("has_fn_abi", "fnAbi"),
            ("has_layouts", "layouts"),
            ("has_allocations", "allocations"),
        ):
            if not state[key]:
                raise CensusScanError(
                    "malformed_syntax",
                    f"CapturedMir record is missing required `{name}` field",
                )
        if state["basic_blocks"] is None:
            raise CensusScanError(
                "malformed_syntax",
                "CapturedMir record is missing required `basicBlocks` field",
            )
        return {
            "body": {
                "def_path": state["def_path"],
                "basic_blocks": state["basic_blocks"],
            },
            "role": state["role"],
            "trait_impls": state["trait_impls"],
        }

    def parse_mir_phase_tag(self) -> None:
        def _inner(cur: "_MirTokenCursor") -> None:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "MirPhaseTag")
            if short in ("runtimePostCleanup", "runtimeOptimized"):
                return
            if short == "other":
                cur.parse_string()
                return
            raise CensusScanError(
                "malformed_syntax", f"unknown MirPhaseTag constructor `{full}`"
            )

        self.with_optional_parens(_inner)

    def parse_contract_role(self) -> tuple[str, str | None]:
        def _inner(cur: "_MirTokenCursor") -> tuple[str, str | None]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "ContractRole")
            if short == "subject":
                return ("subject", None)
            if short == "model":
                return ("model", None)
            if short in ("requires", "ensures", "externalSpec"):
                return (short, cur.parse_string())
            raise CensusScanError(
                "malformed_syntax", f"unknown ContractRole constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_trait_impl_entry(self) -> dict[str, str]:
        state: dict[str, str | None] = {"trait_method_def_path": None, "impl_path": None}

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "traitRef":
                tr: dict[str, Any] = {"def_path": None, "has_args": False}

                def _on_tr(tr_field: str, tr_cur: "_MirTokenCursor") -> None:
                    if tr_field == "defPath":
                        tr["def_path"] = tr_cur.parse_string()
                    elif tr_field == "args":
                        tr_cur.parse_list(lambda c: c.skip_atomic_expr())
                        tr["has_args"] = True
                    else:
                        raise CensusScanError(
                            "malformed_syntax", f"unknown TraitRef field `{tr_field}`"
                        )

                cur.parse_record(_on_tr)
                if not tr["has_args"]:
                    raise CensusScanError(
                        "malformed_syntax", "TraitRef missing `args` field"
                    )
                if tr["def_path"] is None:
                    raise CensusScanError(
                        "malformed_syntax", "TraitRef missing `defPath` field"
                    )
                state["trait_method_def_path"] = tr["def_path"]
            elif field == "implPath":
                state["impl_path"] = cur.parse_string()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown TraitImplEntry field `{field}`"
                )

        self.parse_record(_on_field)
        if state["trait_method_def_path"] is None:
            raise CensusScanError(
                "malformed_syntax", "TraitImplEntry missing `traitRef` field"
            )
        if state["impl_path"] is None:
            raise CensusScanError(
                "malformed_syntax", "TraitImplEntry missing `implPath` field"
            )
        return {
            "trait_method_def_path": state["trait_method_def_path"],
            "impl_path": state["impl_path"],
        }

    def parse_basic_block(self) -> dict[str, Any]:
        state: dict[str, Any] = {
            "statements": None,
            "terminator": None,
            "is_cleanup": None,
        }

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "statements":
                state["statements"] = cur.parse_list(lambda c: c.parse_statement())
            elif field == "terminator":
                state["terminator"] = cur.parse_terminator()
            elif field == "isCleanup":
                state["is_cleanup"] = cur.parse_bool()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown BasicBlockData field `{field}`"
                )

        self.parse_record(_on_field)
        for key, label in (
            ("statements", "statements"),
            ("terminator", "terminator"),
            ("is_cleanup", "isCleanup"),
        ):
            if state[key] is None:
                raise CensusScanError(
                    "malformed_syntax", f"BasicBlockData missing `{label}`"
                )
        return state

    def parse_statement(self) -> dict[str, Any]:
        state: dict[str, Any] = {"kind": None, "span": None}

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "kind":
                state["kind"] = cur.parse_statement_kind()
            elif field == "span":
                state["span"] = cur.parse_string()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown Statement field `{field}`"
                )

        self.parse_record(_on_field)
        if state["kind"] is None:
            raise CensusScanError("malformed_syntax", "Statement missing `kind`")
        if state["span"] is None:
            raise CensusScanError("malformed_syntax", "Statement missing `span`")
        return state

    def parse_statement_kind(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "StatementKind")
            if short == "assign":
                place = cur.parse_place()
                rv = cur.parse_rvalue()
                return ("assign", place, rv)
            if short == "setDiscriminant":
                place = cur.parse_place()
                idx = cur.parse_usize()
                return ("setDiscriminant", place, idx)
            if short == "deinit":
                return ("deinit", cur.parse_place())
            if short == "storageLive":
                return ("storageLive", cur.parse_usize())
            if short == "storageDead":
                return ("storageDead", cur.parse_usize())
            if short == "retag":
                cur.parse_retag_kind()
                return ("retag", cur.parse_place())
            if short == "placeMention":
                return ("placeMention", cur.parse_place())
            if short == "intrinsic":
                return ("intrinsic", cur.parse_intrinsic())
            if short in ("coverage", "constEvalCounter", "nop"):
                return (short,)
            if short == "backwardIncompatibleDropHint":
                return ("backwardIncompatibleDropHint", cur.parse_place())
            raise CensusScanError(
                "malformed_syntax", f"unknown StatementKind constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_retag_kind(self) -> None:
        def _inner(cur: "_MirTokenCursor") -> None:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "RetagKind")
            if short not in ("fnEntry", "twoPhase", "raw", "default"):
                raise CensusScanError(
                    "malformed_syntax", f"unknown RetagKind constructor `{full}`"
                )

        self.with_optional_parens(_inner)

    def parse_intrinsic(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "NonDivergingIntrinsic")
            if short == "assume":
                return ("assume", cur.parse_operand())
            if short == "copyNonOverlapping":
                src = cur.parse_operand()
                dst = cur.parse_operand()
                count = cur.parse_operand()
                return ("copyNonOverlapping", src, dst, count)
            raise CensusScanError(
                "malformed_syntax",
                f"unknown NonDivergingIntrinsic constructor `{full}`",
            )

        return self.with_optional_parens(_inner)

    def parse_place(self) -> dict[str, Any]:
        state: dict[str, Any] = {"local_": None, "projection": None}

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "local_":
                state["local_"] = cur.parse_usize()
            elif field == "projection":
                state["projection"] = cur.parse_list(
                    lambda c: c.parse_projection_elem()
                )
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown Place field `{field}`"
                )

        self.parse_record(_on_field)
        if state["local_"] is None:
            raise CensusScanError("malformed_syntax", "Place missing `local_`")
        if state["projection"] is None:
            raise CensusScanError("malformed_syntax", "Place missing `projection`")
        return state

    def parse_projection_elem(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "ProjectionElem")
            if short == "deref":
                return ("deref",)
            if short == "field":
                idx = cur.parse_usize()
                cur.skip_balanced_expr()
                return ("field", idx)
            if short == "index":
                return ("index", cur.parse_usize())
            if short == "constantIndex":
                offset = cur.parse_u64()
                min_length = cur.parse_u64()
                from_end = cur.parse_bool()
                return ("constantIndex", offset, min_length, from_end)
            if short == "subslice":
                from_idx = cur.parse_u64()
                to_idx = cur.parse_u64()
                from_end = cur.parse_bool()
                return ("subslice", from_idx, to_idx, from_end)
            if short == "downcast":
                sym = cur.parse_option(lambda c: c.parse_string())
                idx = cur.parse_usize()
                return ("downcast", sym, idx)
            if short in ("opaqueCast", "unwrapUnsafeBinder"):
                cur.skip_balanced_expr()
                return (short,)
            raise CensusScanError(
                "malformed_syntax", f"unknown ProjectionElem constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_operand(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "Operand")
            if short == "copy":
                return ("copy", cur.parse_place())
            if short == "move":
                return ("move", cur.parse_place())
            if short == "constant":
                return ("constant", cur.parse_const_operand())
            raise CensusScanError(
                "malformed_syntax", f"unknown Operand constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_const_operand(self) -> tuple[Any, ...]:
        state: dict[str, Any] = {
            "has_ty": False,
            "fn_def_path": None,
            "is_type_param": False,
            "val": None,
        }

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "ty":
                fn_def, is_param = cur.parse_ty_extract_fn_def()
                state["fn_def_path"] = fn_def
                state["is_type_param"] = is_param
                state["has_ty"] = True
            elif field == "val":
                state["val"] = cur.parse_const_value()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown ConstOperand field `{field}`"
                )

        self.parse_record(_on_field)
        if not state["has_ty"]:
            raise CensusScanError("malformed_syntax", "ConstOperand missing `ty`")
        cv = state["val"]
        if cv is None:
            raise CensusScanError("malformed_syntax", "ConstOperand missing `val`")
        if cv[0] == "zeroSized":
            cv = ("zeroSized", state["fn_def_path"])
        elif state["fn_def_path"] is not None:
            raise CensusScanError(
                "malformed_syntax",
                "`RigidTy.fnDef`-typed constant with a non-zero-sized value",
            )
        if state["is_type_param"]:
            return ("paramTypedConst", cv)
        return cv

    def parse_ty_extract_fn_def(self) -> tuple[str | None, bool]:
        state: dict[str, Any] = {
            "has_kind": False,
            "has_layout_idx": False,
            "fn_def": None,
            "is_type_param": False,
        }

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "kind":
                fd, is_param = cur.parse_rigid_ty_extract_fn_def()
                state["fn_def"] = fd
                state["is_type_param"] = is_param
                state["has_kind"] = True
            elif field == "layoutIdx":
                cur.parse_usize()
                state["has_layout_idx"] = True
            else:
                raise CensusScanError("malformed_syntax", f"unknown Ty field `{field}`")

        self.parse_record(_on_field)
        if not state["has_kind"]:
            raise CensusScanError("malformed_syntax", "Ty missing `kind`")
        if not state["has_layout_idx"]:
            raise CensusScanError("malformed_syntax", "Ty missing `layoutIdx`")
        return (state["fn_def"], state["is_type_param"])

    def parse_rigid_ty_extract_fn_def(self) -> tuple[str | None, bool]:
        def _inner(cur: "_MirTokenCursor") -> tuple[str | None, bool]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "RigidTy")
            if short == "fnDef":
                path = cur.parse_string()
                cur.parse_list(lambda c: c.skip_atomic_expr())
                return (path, False)
            is_param = short == "param"
            while True:
                pk = cur.peek()
                if pk is None or pk[0] in ("Comma", "Semicolon", "RBrace", "RParen"):
                    break
                cur.skip_balanced_expr()
            return (None, is_param)

        return self.with_optional_parens(_inner)

    def parse_const_value(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "ConstValue")
            if short == "zeroSized":
                return ("zeroSized", None)
            if short == "scalar":
                return cur.parse_const_scalar()
            if short == "slice":
                cur.parse_const_scalar()
                meta = cur.parse_u64()
                return ("slice", meta)
            if short == "indirect":
                alloc_id = cur.parse_u64()
                offset_bytes = cur.parse_u64()
                return ("indirect", alloc_id, offset_bytes)
            if short == "unevaluated":
                return ("unevaluated", cur.parse_string())
            raise CensusScanError(
                "malformed_syntax", f"unknown ConstValue constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_const_scalar(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "ConstScalar")
            if short == "int":
                st: dict[str, int | None] = {"bits": None, "size_bytes": None}

                def _on_f(f: str, c: "_MirTokenCursor") -> None:
                    if f == "bits":
                        st["bits"] = c.parse_u128()
                    elif f == "sizeBytes":
                        st["size_bytes"] = c.parse_u64()
                    else:
                        raise CensusScanError(
                            "malformed_syntax", f"unknown ScalarInt field `{f}`"
                        )

                cur.parse_record(_on_f)
                if st["bits"] is None:
                    raise CensusScanError("malformed_syntax", "ScalarInt missing `bits`")
                if st["size_bytes"] is None:
                    raise CensusScanError(
                        "malformed_syntax", "ScalarInt missing `sizeBytes`"
                    )
                return ("scalarInt", st["bits"], st["size_bytes"])
            if short == "ptr":
                st_ptr: dict[str, int | None] = {"alloc_id": None, "offset_bytes": None}

                def _on_pf(f: str, c: "_MirTokenCursor") -> None:
                    if f == "allocId":
                        st_ptr["alloc_id"] = c.parse_u64()
                    elif f == "offsetBytes":
                        st_ptr["offset_bytes"] = c.parse_u64()
                    elif f == "tag":
                        c.parse_u64()
                    else:
                        raise CensusScanError(
                            "malformed_syntax", f"unknown ProvenancePtr field `{f}`"
                        )

                cur.parse_record(_on_pf)
                if st_ptr["alloc_id"] is None:
                    raise CensusScanError(
                        "malformed_syntax", "ProvenancePtr missing `allocId`"
                    )
                if st_ptr["offset_bytes"] is None:
                    raise CensusScanError(
                        "malformed_syntax", "ProvenancePtr missing `offsetBytes`"
                    )
                size = cur.parse_u64()
                return (
                    "scalarPtr",
                    st_ptr["alloc_id"],
                    st_ptr["offset_bytes"],
                    size,
                )
            raise CensusScanError(
                "malformed_syntax", f"unknown ConstScalar constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_aggregate_kind(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "AggregateKind")
            if short == "array":
                cur.skip_balanced_expr()
                return ("array",)
            if short == "tuple":
                return ("tuple",)
            if short == "adt":
                def_id = cur.parse_string()
                variant_idx = cur.parse_usize()
                active_field = cur.parse_option(lambda c: c.parse_usize())
                return ("adt", def_id, variant_idx, active_field)
            if short in ("closure", "coroutine"):
                return (short, cur.parse_string())
            if short == "rawPtr":
                cur.skip_balanced_expr()
                mutable = cur.parse_mutability()
                return ("rawPtr", mutable)
            raise CensusScanError(
                "malformed_syntax", f"unknown AggregateKind constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_rvalue(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "Rvalue")
            if short == "use":
                return ("use", cur.parse_operand())
            if short == "repeat":
                op = cur.parse_operand()
                cnt = cur.parse_u64()
                return ("repeat", op, cnt)
            if short == "ref":
                mutable = cur.parse_borrow_kind()
                place = cur.parse_place()
                return ("ref", mutable, place)
            if short == "threadLocalRef":
                return ("threadLocalRef", cur.parse_string())
            if short == "rawPtr":
                mutable = cur.parse_mutability()
                place = cur.parse_place()
                return ("rawPtr", mutable, place)
            if short == "len":
                return ("len", cur.parse_place())
            if short == "cast":
                kind = cur.parse_cast_kind()
                op = cur.parse_operand()
                cur.skip_balanced_expr()
                return ("cast", kind, op)
            if short == "binaryOp":
                op = cur.parse_bin_op()
                lhs = cur.parse_operand()
                rhs = cur.parse_operand()
                return ("binaryOp", op, lhs, rhs)
            if short == "nullaryOp":
                op = cur.parse_null_op()
                cur.skip_balanced_expr()
                return ("nullaryOp", op)
            if short == "unaryOp":
                op = cur.parse_un_op()
                val = cur.parse_operand()
                return ("unaryOp", op, val)
            if short == "discriminant":
                return ("discriminant", cur.parse_place())
            if short == "aggregate":
                kind = cur.parse_aggregate_kind()
                ops = cur.parse_list(lambda c: c.parse_operand())
                return ("aggregate", kind, ops)
            if short == "shallowInitBox":
                op = cur.parse_operand()
                cur.skip_balanced_expr()
                return ("shallowInitBox", op)
            if short == "copyForDeref":
                return ("copyForDeref", cur.parse_place())
            if short == "wrapUnsafeBinder":
                op = cur.parse_operand()
                cur.skip_balanced_expr()
                return ("wrapUnsafeBinder", op)
            raise CensusScanError(
                "malformed_syntax", f"unknown Rvalue constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_borrow_kind(self) -> bool:
        def _inner(cur: "_MirTokenCursor") -> bool:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "BorrowKind")
            if short == "shared":
                return False
            if short == "mut":
                cur.parse_bool()
                return True
            raise CensusScanError(
                "malformed_syntax", f"unknown BorrowKind constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_mutability(self) -> bool:
        def _inner(cur: "_MirTokenCursor") -> bool:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "Mutability")
            if short == "not":
                return False
            if short == "mut":
                return True
            raise CensusScanError(
                "malformed_syntax", f"unknown Mutability constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_cast_kind(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "CastKind")
            if short == "pointerCoercion":
                return ("pointerCoercion", cur.parse_string())
            if short in (
                "pointerExposeProvenance",
                "pointerWithExposedProvenance",
                "intToInt",
                "floatToInt",
                "floatToFloat",
                "intToFloat",
                "ptrToPtr",
                "fnPtrToPtr",
                "transmute",
                "subtype",
            ):
                return (short,)
            raise CensusScanError(
                "malformed_syntax", f"unknown CastKind constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_bin_op(self) -> str:
        def _inner(cur: "_MirTokenCursor") -> str:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "BinOp")
            if short in (
                "add",
                "addUnchecked",
                "addWithOverflow",
                "sub",
                "subUnchecked",
                "subWithOverflow",
                "mul",
                "mulUnchecked",
                "mulWithOverflow",
                "div",
                "rem",
                "bitXor",
                "bitAnd",
                "bitOr",
                "shl",
                "shlUnchecked",
                "shr",
                "shrUnchecked",
                "eq",
                "lt",
                "le",
                "ne",
                "ge",
                "gt",
                "cmp",
                "offset",
            ):
                return short
            raise CensusScanError(
                "malformed_syntax", f"unknown BinOp constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_un_op(self) -> str:
        def _inner(cur: "_MirTokenCursor") -> str:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "UnOp")
            if short in ("not", "neg", "ptrMetadata"):
                return short
            raise CensusScanError(
                "malformed_syntax", f"unknown UnOp constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_null_op(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "NullOp")
            if short in ("sizeOf", "alignOf", "ubChecks", "contractChecks"):
                return (short,)
            if short == "offsetOf":
                def _parse_pair(c: "_MirTokenCursor") -> tuple[int, int]:
                    c.expect("LParen")
                    v = c.parse_usize()
                    c.expect("Comma")
                    f = c.parse_usize()
                    c.expect("RParen")
                    return (v, f)

                return ("offsetOf", cur.parse_list(_parse_pair))
            raise CensusScanError(
                "malformed_syntax", f"unknown NullOp constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_terminator(self) -> dict[str, Any]:
        state: dict[str, Any] = {"kind": None, "span": None}

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "kind":
                state["kind"] = cur.parse_terminator_kind()
            elif field == "span":
                state["span"] = cur.parse_string()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown Terminator field `{field}`"
                )

        self.parse_record(_on_field)
        if state["kind"] is None:
            raise CensusScanError("malformed_syntax", "Terminator missing `kind`")
        if state["span"] is None:
            raise CensusScanError("malformed_syntax", "Terminator missing `span`")
        return state

    def parse_terminator_kind(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "TerminatorKind")
            if short == "goto":
                return ("goto", cur.parse_usize())
            if short == "switchInt":
                discr = cur.parse_operand()
                targets = cur.parse_switch_targets()
                return ("switchInt", discr, targets)
            if short in ("unwindResume", "unwindTerminate", "return_", "unreachable"):
                return (short,)
            if short == "drop":
                place = cur.parse_place()
                target = cur.parse_usize()
                unwind = cur.parse_unwind_action()
                return ("drop", place, target, unwind)
            if short == "call":
                func = cur.parse_operand()
                args = cur.parse_list(lambda c: c.parse_operand())
                destination = cur.parse_place()
                target = cur.parse_option(lambda c: c.parse_usize())
                unwind = cur.parse_unwind_action()
                return ("call", func, args, destination, target, unwind)
            if short == "tailCall":
                func = cur.parse_operand()
                args = cur.parse_list(lambda c: c.parse_operand())
                return ("tailCall", func, args)
            if short == "assert":
                cond = cur.parse_operand()
                expected = cur.parse_bool()
                target = cur.parse_usize()
                unwind = cur.parse_unwind_action()
                return ("assert", cond, expected, target, unwind)
            if short == "inlineAsm":
                template = cur.parse_string()
                targets = cur.parse_list(lambda c: c.parse_usize())
                unwind = cur.parse_unwind_action()
                return ("inlineAsm", template, targets, unwind)
            raise CensusScanError(
                "malformed_syntax", f"unknown TerminatorKind constructor `{full}`"
            )

        return self.with_optional_parens(_inner)

    def parse_switch_targets(self) -> dict[str, Any]:
        state: dict[str, Any] = {"branches": None, "otherwise": None}

        def _parse_branch(c: "_MirTokenCursor") -> tuple[int, int]:
            c.expect("LParen")
            val = c.parse_u128()
            c.expect("Comma")
            bb = c.parse_usize()
            c.expect("RParen")
            return (val, bb)

        def _on_field(field: str, cur: "_MirTokenCursor") -> None:
            if field == "branches":
                state["branches"] = cur.parse_list(_parse_branch)
            elif field == "otherwise":
                state["otherwise"] = cur.parse_usize()
            else:
                raise CensusScanError(
                    "malformed_syntax", f"unknown SwitchTargets field `{field}`"
                )

        self.parse_record(_on_field)
        if state["branches"] is None:
            raise CensusScanError(
                "malformed_syntax", "SwitchTargets missing `branches`"
            )
        if state["otherwise"] is None:
            raise CensusScanError(
                "malformed_syntax", "SwitchTargets missing `otherwise`"
            )
        return state

    def parse_unwind_action(self) -> tuple[Any, ...]:
        def _inner(cur: "_MirTokenCursor") -> tuple[Any, ...]:
            full, short = cur.parse_ctor_head()
            _check_ctor_qualifier(full, short, "UnwindAction")
            if short == "cleanup":
                return ("cleanup", cur.parse_usize())
            if short in ("unreachable", "terminate", "continue_"):
                return (short,)
            raise CensusScanError(
                "malformed_syntax", f"unknown UnwindAction constructor `{full}`"
            )

        return self.with_optional_parens(_inner)


def check_strict_mir_module_grammar(tokens: list[tuple[str, Any]]) -> None:
    def _ident_at(idx: int) -> str | None:
        if idx < len(tokens) and tokens[idx][0] == "Ident":
            return str(tokens[idx][1])
        return None

    scope_stack: list[tuple[str, str]] = []
    top_level_namespaces = 0
    body_defs = 0
    i = 0
    n = len(tokens)
    while i < n:
        kw = _ident_at(i)
        if kw is None:
            raise CensusScanError(
                "malformed_syntax",
                f"unexpected top-level token {tokens[i]!r} in strict Mir module",
            )
        if kw == "import":
            imp = _ident_at(i + 1)
            if imp is None:
                raise CensusScanError(
                    "malformed_syntax", "`import` without module"
                )
            if imp not in _STRICT_MODULE_IMPORTS:
                raise CensusScanError(
                    "malformed_syntax",
                    f"unsupported `import {imp}` in strict Mir module (only `Trusted` / `V2026_06_01` allowed)",
                )
            i += 2
        elif kw in ("namespace", "section"):
            name = _ident_at(i + 1)
            if name is None or _fc_is_lean_command_start(tokens[i + 1]):
                raise CensusScanError(
                    "malformed_syntax", f"`{kw}` without an explicit scope name"
                )
            if _shadows_mir_ast_name(name):
                raise CensusScanError(
                    "malformed_syntax",
                    f"namespace `{name}` shadows a MIR AST type name",
                )
            if kw == "namespace" and not scope_stack:
                if top_level_namespaces >= 1:
                    raise CensusScanError(
                        "malformed_syntax",
                        f"multiple top-level `namespace` blocks (`{name}`) in strict Mir module",
                    )
                top_level_namespaces += 1
            scope_stack.append((kw, name))
            i += 2
        elif kw == "end":
            name = _ident_at(i + 1)
            if name is None or _fc_is_lean_command_start(tokens[i + 1]):
                raise CensusScanError(
                    "malformed_syntax", "`end` without an explicit scope name"
                )
            if not scope_stack:
                raise CensusScanError(
                    "malformed_syntax",
                    f"unmatched `end {name}` with no open namespace or section",
                )
            open_kw, open_name = scope_stack.pop()
            if open_name != name:
                raise CensusScanError(
                    "malformed_syntax",
                    f"mismatched `end {name}` for open `{open_kw} {open_name}`",
                )
            i += 2
        elif kw == "open":
            i += 1
            count = 0
            while True:
                name = _ident_at(i)
                if name is None or _fc_is_lean_command_start(tokens[i]):
                    break
                if name in ("renaming", "hiding", "in", "scoped"):
                    raise CensusScanError(
                        "malformed_syntax", f"`open ... {name}` is not supported"
                    )
                if name not in _STRICT_MODULE_OPENS:
                    raise CensusScanError(
                        "malformed_syntax",
                        f"unsupported `open {name}` in strict Mir module (only `Trusted` namespaces allowed)",
                    )
                count += 1
                i += 1
            if count == 0:
                raise CensusScanError(
                    "malformed_syntax", "`open` without namespaces"
                )
        elif kw == "set_option":
            if _ident_at(i + 1) is None:
                raise CensusScanError(
                    "malformed_syntax", "`set_option` without name"
                )
            if i + 2 >= n or tokens[i + 2][0] not in (
                "Ident",
                "NatLit",
                "StrLit",
                "CharLit",
            ):
                raise CensusScanError(
                    "malformed_syntax", "`set_option` with invalid value"
                )
            i += 3
        elif kw == "def":
            name = _ident_at(i + 1)
            if name is None:
                raise CensusScanError(
                    "malformed_syntax", "`def` without a plain identifier name"
                )
            if _shadows_mir_decl_name(name) or _fc_is_lean_command_start(tokens[i + 1]):
                raise CensusScanError(
                    "malformed_syntax",
                    f"declaration `{name}` shadows a MIR AST name or keyword",
                )
            if name.endswith(".body"):
                raise CensusScanError(
                    "malformed_syntax",
                    f"qualified `def {name}` is not allowed in strict Mir module (expected bare `def body`)",
                )
            if "." in name:
                # `[adv ep2-B2]`: `def _root_.X` / `def A.B` escapes the module's own
                # `Mir.<Item>` namespace and can shadow names resolved inside the
                # `Obligations` / `Verify` namespaces of every importing module.
                raise CensusScanError(
                    "malformed_syntax",
                    f"qualified `def {name}` is not allowed in strict Mir module (declarations must be plain identifiers)",
                )
            if i + 2 >= n or tokens[i + 2][0] != "Colon":
                raise CensusScanError(
                    "malformed_syntax",
                    f"`def {name}` must carry an explicit `: <type>` ascription",
                )
            is_body = name == "body"
            j = i + 3
            ty_start = j
            depth = 0
            while j < n:
                tk = tokens[j][0]
                if tk in ("LParen", "LBrace", "LBracket"):
                    depth += 1
                elif tk in ("RParen", "RBrace", "RBracket"):
                    depth -= 1
                elif tk == "ColonEq" and depth == 0:
                    break
                elif depth == 0 and _fc_is_lean_command_start(tokens[j]):
                    raise CensusScanError(
                        "malformed_syntax", f"`def {name}` has no `:=` body"
                    )
                j += 1
            if j >= n:
                raise CensusScanError(
                    "malformed_syntax", f"`def {name}` has no `:=` body"
                )
            if is_body:
                if len(scope_stack) != 1 or scope_stack[0][0] != "namespace":
                    raise CensusScanError(
                        "malformed_syntax",
                        "`def body : CapturedMir` must appear directly inside the module's single top-level `namespace`",
                    )
                ty_ok = (
                    j == ty_start + 1
                    and tokens[ty_start][0] == "Ident"
                    and _is_valid_captured_mir_type(str(tokens[ty_start][1]))
                )
                if not ty_ok:
                    raise CensusScanError(
                        "malformed_syntax",
                        f"`def {name}` must be ascribed `: CapturedMir` (in `V2026_06_01` dialect)",
                    )
                body_defs += 1
            cursor = _MirTokenCursor(tokens, j + 1)
            cursor.skip_balanced_expr()
            if not is_body:
                for tok in tokens[i + 3 : cursor.pos]:
                    if tok[0] == "StrLit" and ("{" in tok[1] or "}" in tok[1]):
                        raise CensusScanError(
                            "malformed_syntax",
                            f"brace-carrying string in skipped `def {name}`",
                        )
                    if tok[0] == "Ident" and str(tok[1]).endswith("!"):
                        raise CensusScanError(
                            "malformed_syntax",
                            f"macro invocation `{tok[1]}` in skipped `def {name}`",
                        )
            nxt_tok = cursor.peek()
            if nxt_tok is not None and not _fc_is_lean_command_start(nxt_tok):
                raise CensusScanError(
                    "malformed_syntax",
                    f"unexpected token {nxt_tok!r} after the value of `def {name}`",
                )
            i = cursor.pos
        else:
            raise CensusScanError(
                "malformed_syntax",
                f"unsupported top-level command `{kw}` in strict Mir module",
            )
    if scope_stack:
        open_kw, open_name = scope_stack[-1]
        raise CensusScanError(
            "malformed_syntax",
            f"unclosed `{open_kw} {open_name}` at end of strict Mir module",
        )
    if body_defs != 1:
        raise CensusScanError(
            "missing_or_duplicate_def",
            f"expected exactly one `def body : CapturedMir`, found {body_defs}",
        )


def parse_lean_captured_mir_def_metadata(
    lean_src: str, def_name: str = "body", *, tokens: list[tuple[str, Any]] | None = None
) -> dict[str, Any]:
    if tokens is None:
        tokens = tokenize_lean_source(lean_src)
    found_body: dict[str, Any] | None = None
    idx = 0
    n = len(tokens)
    delim_depth = 0
    while idx + 4 < n:
        tk = tokens[idx][0]
        if tk in ("LParen", "LBrace", "LBracket"):
            delim_depth += 1
            idx += 1
            continue
        if tk in ("RParen", "RBrace", "RBracket"):
            delim_depth -= 1
            idx += 1
            continue
        is_def = (
            delim_depth == 0
            and tokens[idx][0] == "Ident"
            and tokens[idx][1] in ("def", "abbrev")
        )
        name_matches = tokens[idx + 1][0] == "Ident" and (
            tokens[idx + 1][1] == def_name
            or str(tokens[idx + 1][1]).endswith(f".{def_name}")
        )
        is_colon = tokens[idx + 2][0] == "Colon"
        is_captured_mir = tokens[idx + 3][0] == "Ident" and _is_valid_captured_mir_type(
            str(tokens[idx + 3][1])
        )
        is_assign = tokens[idx + 4][0] == "ColonEq"
        if is_def and name_matches and is_colon and is_captured_mir and is_assign:
            if found_body is not None:
                raise CensusScanError(
                    "missing_or_duplicate_def",
                    f"multiple `def {def_name} : CapturedMir` declarations found",
                )
            cursor = _MirTokenCursor(tokens, idx + 5)
            parsed = cursor.parse_captured_mir_metadata()
            nxt = cursor.peek()
            if nxt is not None and not _fc_is_lean_command_start(nxt):
                raise CensusScanError(
                    "malformed_syntax",
                    f"unexpected token {nxt!r} after `def {def_name} : CapturedMir` record",
                )
            found_body = parsed
            idx = cursor.pos
        else:
            idx += 1
    if found_body is None:
        raise CensusScanError(
            "missing_or_duplicate_def",
            f"`def {def_name} : CapturedMir := ...` not found",
        )
    return found_body


def parse_lean_captured_mir_def(lean_src: str, def_name: str = "body") -> dict[str, Any]:
    return parse_lean_captured_mir_def_metadata(lean_src, def_name)["body"]


def parse_lean_mir_module_metadata_strict(lean_src: str) -> dict[str, Any]:
    tokens = tokenize_lean_source(lean_src)
    check_strict_mir_module_grammar(tokens)
    return parse_lean_captured_mir_def_metadata(lean_src, "body", tokens=tokens)


def parse_lean_mir_module_body_strict(lean_src: str) -> dict[str, Any]:
    return parse_lean_mir_module_metadata_strict(lean_src)["body"]


def dedup_fault_classes(raw: Iterable[str]) -> list[str]:
    seen = set(raw)
    return sorted(seen, key=lambda c: FAULT_CLASS_RANK[c])


def _extract_operand_callee_def_path(op: tuple[Any, ...]) -> str | None:
    if op[0] != "constant":
        return None
    cv = op[1]
    if cv[0] == "zeroSized" and cv[1] is not None:
        return str(cv[1])
    if cv[0] == "unevaluated":
        return str(cv[1])
    if cv[0] == "paramTypedConst":
        inner = cv[1]
        if inner[0] == "unevaluated":
            return str(inner[1])
    return None


def _operand_has_no_param_const_ty(op: tuple[Any, ...]) -> bool:
    return not (op[0] == "constant" and op[1][0] == "paramTypedConst")


def body_has_no_param_call_const(body: dict[str, Any]) -> bool:
    for bb in body["basic_blocks"]:
        tk = bb["terminator"]["kind"]
        if tk[0] in ("call", "tailCall"):
            if not _operand_has_no_param_const_ty(tk[1]):
                return False
    return True


def _unwind_targets(unwind: tuple[Any, ...]) -> list[int]:
    if unwind[0] == "cleanup":
        return [int(unwind[1])]
    return []


def terminator_targets(kind: tuple[Any, ...]) -> list[int]:
    tag = kind[0]
    if tag == "goto":
        return [int(kind[1])]
    if tag == "switchInt":
        targets = kind[2]
        out = [int(targets["otherwise"])]
        out.extend(int(t) for _, t in targets["branches"])
        return out
    if tag in ("unwindResume", "unwindTerminate", "return_", "unreachable", "tailCall"):
        return []
    if tag == "drop":
        return [int(kind[2]), *_unwind_targets(kind[3])]
    if tag == "assert":
        return [int(kind[3]), *_unwind_targets(kind[4])]
    if tag == "call":
        target_opt = kind[4]
        unwind = kind[5]
        if target_opt is not None:
            return [int(target_opt), *_unwind_targets(unwind)]
        return _unwind_targets(unwind)
    if tag == "inlineAsm":
        return [*[int(t) for t in kind[2]], *_unwind_targets(kind[3])]
    return []


def cfg_targets_in_bounds(body: dict[str, Any]) -> bool:
    bbs = body["basic_blocks"]
    num_blocks = len(bbs)
    if num_blocks == 0:
        return False
    for bb in bbs:
        if any(t < 0 or t >= num_blocks for t in terminator_targets(bb["terminator"]["kind"])):
            return False
    return True


def census_projection_elem_fault_classes(proj: tuple[Any, ...]) -> list[str]:
    tag = proj[0]
    if tag == "deref":
        return [
            "ptr_deref_invalid",
            "ptr_align_mismatch",
            "tree_borrows_violation",
        ]
    if tag in ("field", "opaqueCast", "unwrapUnsafeBinder"):
        return []
    if tag == "index":
        return ["bounds_check", "uninit_read"]
    if tag in ("constantIndex", "subslice"):
        return ["bounds_check"]
    if tag == "downcast":
        return ["scalar_niche_invalid"]
    return []


def census_read_projected_fault_classes(proj: tuple[Any, ...]) -> list[str]:
    tag = proj[0]
    if tag in ("deref", "field", "opaqueCast", "unwrapUnsafeBinder"):
        return []
    if tag == "downcast":
        return ["scalar_niche_invalid"]
    if tag == "subslice":
        return ["bounds_check"]
    if tag in ("index", "constantIndex"):
        return ["bounds_check", "scalar_niche_invalid", "uninit_read"]
    return []


def census_place_read_fault_classes(place: dict[str, Any]) -> list[str]:
    out = ["uninit_read"]
    for proj in place["projection"]:
        out.extend(census_projection_elem_fault_classes(proj))
    return out


def census_place_write_fault_classes(place: dict[str, Any]) -> list[str]:
    if not place["projection"]:
        return ["storage_live_protected", "tree_borrows_violation"]
    out = ["storage_live_protected", "tree_borrows_violation", "uninit_read"]
    for proj in place["projection"]:
        out.extend(census_projection_elem_fault_classes(proj))
    return out


def census_place_ref_fault_classes(place: dict[str, Any]) -> list[str]:
    projs = place["projection"]
    if not projs or projs[0][0] != "deref":
        if any(p[0] == "subslice" for p in projs):
            return ["uninit_read", "bounds_check", "ptr_align_mismatch"]
        return ["uninit_read"]
    out = [
        "uninit_read",
        "ptr_deref_invalid",
        "ptr_align_mismatch",
        "tree_borrows_violation",
    ]
    for proj in projs:
        out.extend(census_projection_elem_fault_classes(proj))
    return out


def census_const_value_fault_classes(cv: tuple[Any, ...]) -> list[str]:
    if cv[0] == "indirect":
        return ["bounds_check", "scalar_niche_invalid", "uninit_read"]
    if cv[0] == "paramTypedConst":
        return census_const_value_fault_classes(cv[1])
    return []


def census_operand_fault_classes(op: tuple[Any, ...]) -> list[str]:
    if op[0] in ("copy", "move"):
        return census_place_read_fault_classes(op[1])
    return census_const_value_fault_classes(op[1])


def census_loaded_operand_fault_classes(op: tuple[Any, ...]) -> list[str]:
    if op[0] in ("copy", "move"):
        out = census_place_read_fault_classes(op[1])
        out.append("scalar_niche_invalid")
        return out
    return census_const_value_fault_classes(op[1])


def census_bin_op_fault_classes(op: str) -> list[str]:
    if op in ("addUnchecked", "subUnchecked", "mulUnchecked"):
        return ["arith_overflow"]
    if op in ("div", "rem"):
        return ["arith_overflow", "div_rem_by_zero"]
    if op in ("shlUnchecked", "shrUnchecked"):
        return ["shift_overflow"]
    if op == "offset":
        return [
            "arith_overflow",
            "bounds_check",
            "ptr_deref_invalid",
            "tree_borrows_violation",
        ]
    return []


def census_un_op_fault_classes(op: str) -> list[str]:
    if op == "neg":
        return []
    if op == "not":
        return ["scalar_niche_invalid"]
    if op == "ptrMetadata":
        return ["ptr_deref_invalid"]
    return []


def census_cast_kind_fault_classes(kind: tuple[Any, ...]) -> list[str]:
    tag = kind[0]
    if tag in ("intToInt", "floatToInt", "floatToFloat", "intToFloat"):
        return []
    if tag == "pointerExposeProvenance":
        return ["ptr_deref_invalid", "scalar_niche_invalid"]
    if tag == "pointerWithExposedProvenance":
        return ["scalar_niche_invalid"]
    if tag in ("transmute", "subtype"):
        return ["scalar_niche_invalid", "uninit_read"]
    if tag == "pointerCoercion":
        coercion = kind[1]
        if coercion == "MutToConstPointer":
            return ["ptr_deref_invalid", "scalar_niche_invalid"]
        if coercion in ("Unsize", "ArrayToPointer"):
            return [
                "bounds_check",
                "ptr_deref_invalid",
                "ptr_align_mismatch",
                "tree_borrows_violation",
                "scalar_niche_invalid",
            ]
        return ["ptr_deref_invalid", "scalar_niche_invalid", "call_abi_mismatch"]
    if tag == "ptrToPtr":
        return [
            "bounds_check",
            "ptr_deref_invalid",
            "ptr_align_mismatch",
            "tree_borrows_violation",
            "scalar_niche_invalid",
        ]
    if tag == "fnPtrToPtr":
        return ["ptr_deref_invalid", "scalar_niche_invalid", "call_abi_mismatch"]
    return []


def census_aggregate_kind_fault_classes(kind: tuple[Any, ...]) -> list[str]:
    tag = kind[0]
    if tag == "adt" and kind[3] is not None:
        return ["scalar_niche_invalid"]
    if tag == "rawPtr":
        return ["ptr_deref_invalid", "scalar_niche_invalid"]
    return []


def rvalue_unevaluated(rv: tuple[Any, ...]) -> bool:
    tag = rv[0]
    if tag in ("threadLocalRef", "nullaryOp", "shallowInitBox"):
        return True
    if tag == "aggregate" and rv[1][0] == "coroutine":
        return True
    return False


def census_rvalue_fault_classes(rv: tuple[Any, ...]) -> list[str]:
    tag = rv[0]
    if tag in ("use", "wrapUnsafeBinder"):
        return census_loaded_operand_fault_classes(rv[1])
    if tag == "repeat":
        return census_operand_fault_classes(rv[1])
    if tag in ("ref", "rawPtr"):
        return census_place_ref_fault_classes(rv[2])
    if tag in ("threadLocalRef", "nullaryOp", "shallowInitBox"):
        return []
    if tag == "len":
        return [*census_place_read_fault_classes(rv[1]), "bounds_check"]
    if tag == "cast":
        return [
            *census_operand_fault_classes(rv[2]),
            *census_cast_kind_fault_classes(rv[1]),
        ]
    if tag == "binaryOp":
        return [
            *census_operand_fault_classes(rv[2]),
            *census_operand_fault_classes(rv[3]),
            *census_bin_op_fault_classes(rv[1]),
        ]
    if tag == "unaryOp":
        return [
            *census_operand_fault_classes(rv[2]),
            *census_un_op_fault_classes(rv[1]),
        ]
    if tag == "discriminant":
        return [*census_place_read_fault_classes(rv[1]), "scalar_niche_invalid"]
    if tag == "aggregate":
        kind = rv[1]
        if kind[0] == "coroutine":
            return []
        out: list[str] = []
        for op in rv[2]:
            out.extend(census_operand_fault_classes(op))
        out.extend(census_aggregate_kind_fault_classes(kind))
        return out
    if tag == "copyForDeref":
        return census_place_read_fault_classes(rv[1])
    return []


def census_intrinsic_fault_classes(intr: tuple[Any, ...]) -> list[str]:
    if intr[0] == "assume":
        return [*census_operand_fault_classes(intr[1]), "scalar_niche_invalid"]
    if intr[0] == "copyNonOverlapping":
        return [
            *census_operand_fault_classes(intr[1]),
            *census_operand_fault_classes(intr[2]),
            *census_operand_fault_classes(intr[3]),
            "arith_overflow",
            "bounds_check",
            "ptr_deref_invalid",
            "ptr_align_mismatch",
            "tree_borrows_violation",
            "scalar_niche_invalid",
            "uninit_read",
        ]
    return []


def census_stmt_fault_classes(kind: tuple[Any, ...]) -> list[str]:
    tag = kind[0]
    raw: list[str] = []
    if tag in ("nop", "coverage", "constEvalCounter", "backwardIncompatibleDropHint"):
        raw = []
    elif tag in ("storageLive", "storageDead"):
        raw = ["storage_live_protected"]
    elif tag == "placeMention":
        raw = ["uninit_read"]
    elif tag == "deinit":
        place = kind[1]
        if not place["projection"]:
            raw = ["storage_live_protected"]
        else:
            raw = ["uninit_read"]
            for proj in place["projection"]:
                raw.extend(census_read_projected_fault_classes(proj))
    elif tag == "retag":
        raw = [
            *census_place_read_fault_classes(kind[1]),
            "bounds_check",
            "ptr_deref_invalid",
            "tree_borrows_violation",
        ]
    elif tag == "setDiscriminant":
        place = kind[1]
        if not place["projection"]:
            raw = ["scalar_niche_invalid", "uninit_read"]
        else:
            raw = [
                *census_place_read_fault_classes(place),
                *census_place_write_fault_classes(place),
                "scalar_niche_invalid",
            ]
    elif tag == "intrinsic":
        raw = census_intrinsic_fault_classes(kind[1])
    elif tag == "assign":
        dst, rv = kind[1], kind[2]
        if not rvalue_unevaluated(rv):
            raw = [
                *census_place_write_fault_classes(dst),
                *census_rvalue_fault_classes(rv),
            ]
    return dedup_fault_classes(raw)


def census_callee_def_path_fault_classes(def_path: str) -> list[str]:
    if def_path in (
        "core::hint::unreachable_unchecked",
        "std::hint::unreachable_unchecked",
        "core::intrinsics::unreachable",
    ):
        return ["unreachable_terminator"]
    if def_path == "core::intrinsics::exact_div":
        return ["arith_overflow", "div_rem_by_zero"]
    if not def_path.startswith("core::intrinsics::"):
        return []
    suffix = def_path[len("core::intrinsics::") :]
    if suffix == "arith_offset":
        return ["ptr_deref_invalid", "scalar_niche_invalid"]
    if suffix in ("unchecked_add", "unchecked_sub", "unchecked_mul"):
        return ["arith_overflow"]
    if suffix in ("unchecked_div", "unchecked_rem"):
        return ["arith_overflow", "div_rem_by_zero"]
    if suffix in ("unchecked_shl", "unchecked_shr"):
        return ["shift_overflow"]
    if suffix in ("ctlz_nonzero", "cttz_nonzero"):
        return ["scalar_niche_invalid"]
    if suffix in ("size_of_val", "align_of_val"):
        return ["arith_overflow", "ptr_deref_invalid", "scalar_niche_invalid"]
    if suffix == "const_eval_select":
        return [
            "arith_overflow",
            "div_rem_by_zero",
            "shift_overflow",
            "ptr_deref_invalid",
            "scalar_niche_invalid",
            "call_abi_mismatch",
            "unreachable_terminator",
        ]
    return []


def census_terminator_fault_classes(
    num_blocks: int, kind: tuple[Any, ...]
) -> list[str]:
    target_oob = (
        ["bounds_check"]
        if any(t < 0 or t >= num_blocks for t in terminator_targets(kind))
        else []
    )
    tag = kind[0]
    raw: list[str] = []
    if tag == "goto":
        raw = target_oob
    elif tag in ("unwindTerminate", "inlineAsm"):
        raw = []
    elif tag == "unreachable":
        raw = ["unreachable_terminator"]
    elif tag == "unwindResume":
        raw = ["call_abi_mismatch"]
    elif tag == "return_":
        raw = ["uninit_read", "tree_borrows_violation", "call_abi_mismatch"]
    elif tag == "switchInt":
        raw = [
            *census_operand_fault_classes(kind[1]),
            "scalar_niche_invalid",
            *target_oob,
        ]
    elif tag == "drop":
        place = kind[1]
        if not place["projection"]:
            raw = ["storage_live_protected", *target_oob]
        else:
            raw = ["uninit_read"]
            for proj in place["projection"]:
                raw.extend(census_read_projected_fault_classes(proj))
            raw.extend(target_oob)
    elif tag == "assert":
        cond, unwind = kind[1], kind[4]
        raw = [*census_operand_fault_classes(cond), "scalar_niche_invalid"]
        if unwind[0] == "unreachable":
            raw.append("unreachable_terminator")
        elif unwind[0] == "continue_":
            raw.append("call_abi_mismatch")
        raw.extend(target_oob)
    elif tag == "call":
        func, args, destination, target, unwind = (
            kind[1],
            kind[2],
            kind[3],
            kind[4],
            kind[5],
        )
        raw = list(census_operand_fault_classes(func))
        for arg in args:
            raw.extend(census_operand_fault_classes(arg))
        if target is not None:
            raw.extend(census_place_write_fault_classes(destination))
        raw.append("call_abi_mismatch")
        def_path = _extract_operand_callee_def_path(func)
        if def_path is not None:
            if target is not None:
                raw.extend(census_callee_def_path_fault_classes(def_path))
            elif def_path in (
                "core::hint::unreachable_unchecked",
                "std::hint::unreachable_unchecked",
                "core::intrinsics::unreachable",
            ):
                raw.append("unreachable_terminator")
        else:
            raw.append("ptr_deref_invalid")
        if unwind[0] == "unreachable":
            raw.append("unreachable_terminator")
        raw.extend(target_oob)
    elif tag == "tailCall":
        func, args = kind[1], kind[2]
        raw = list(census_operand_fault_classes(func))
        for arg in args:
            raw.extend(census_operand_fault_classes(arg))
        raw.extend([
            "tree_borrows_violation",
            "uninit_read",
            "storage_live_protected",
            "call_abi_mismatch",
        ])
        if _extract_operand_callee_def_path(func) is None:
            raw.append("ptr_deref_invalid")
    return dedup_fault_classes(raw)


def census_mir_fault_sites(body: dict[str, Any]) -> list[FaultSite]:
    bbs = body["basic_blocks"]
    num_blocks = len(bbs)
    sites: list[FaultSite] = []
    for block_idx, bb in enumerate(bbs):
        stmts = bb["statements"]
        for stmt_idx, stmt in enumerate(stmts):
            for fc in census_stmt_fault_classes(stmt["kind"]):
                sites.append(FaultSite(block_idx, stmt_idx, fc))
        term_idx = len(stmts)
        for fc in census_terminator_fault_classes(num_blocks, bb["terminator"]["kind"]):
            sites.append(FaultSite(block_idx, term_idx, fc))
    return sites


def census_lean_mir_def(lean_src: str, def_name: str = "body") -> list[FaultSite]:
    body = parse_lean_captured_mir_def(lean_src, def_name)
    return census_mir_fault_sites(body)


def census_lean_mir_module(lean_src: str) -> list[FaultSite]:
    body = parse_lean_mir_module_body_strict(lean_src)
    return census_mir_fault_sites(body)


def _emit_ob_proj_sites(
    proj: tuple[Any, ...], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    tag = proj[0]
    if tag == "deref":
        for fc in ("ptr_deref_invalid", "ptr_align_mismatch", "tree_borrows_violation"):
            out.add(FaultSite(bb_idx, stmt_idx, fc))
    elif tag == "index":
        out.add(FaultSite(bb_idx, stmt_idx, "bounds_check"))
        out.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
    elif tag in ("constantIndex", "subslice"):
        out.add(FaultSite(bb_idx, stmt_idx, "bounds_check"))
    elif tag == "downcast":
        out.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))


def _emit_ob_read_projected_sites(
    proj: tuple[Any, ...], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    tag = proj[0]
    if tag == "downcast":
        out.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
    elif tag == "subslice":
        out.add(FaultSite(bb_idx, stmt_idx, "bounds_check"))
    elif tag in ("index", "constantIndex"):
        for fc in ("bounds_check", "scalar_niche_invalid", "uninit_read"):
            out.add(FaultSite(bb_idx, stmt_idx, fc))


def _emit_ob_place_read_sites(
    place: dict[str, Any], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    out.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
    for proj in place["projection"]:
        _emit_ob_proj_sites(proj, bb_idx, stmt_idx, out)


def _emit_ob_place_write_sites(
    place: dict[str, Any], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    out.add(FaultSite(bb_idx, stmt_idx, "storage_live_protected"))
    out.add(FaultSite(bb_idx, stmt_idx, "tree_borrows_violation"))
    if place["projection"]:
        out.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
        for proj in place["projection"]:
            _emit_ob_proj_sites(proj, bb_idx, stmt_idx, out)


def _emit_ob_place_ref_sites(
    place: dict[str, Any], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    projs = place["projection"]
    if not projs or projs[0][0] != "deref":
        out.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
        if any(p[0] == "subslice" for p in projs):
            out.add(FaultSite(bb_idx, stmt_idx, "bounds_check"))
            out.add(FaultSite(bb_idx, stmt_idx, "ptr_align_mismatch"))
        return
    for fc in (
        "uninit_read",
        "ptr_deref_invalid",
        "ptr_align_mismatch",
        "tree_borrows_violation",
    ):
        out.add(FaultSite(bb_idx, stmt_idx, fc))
    for proj in projs:
        _emit_ob_proj_sites(proj, bb_idx, stmt_idx, out)


def _emit_ob_const_sites(
    cv: tuple[Any, ...], bb_idx: int, stmt_idx: int, out: set[FaultSite]
) -> None:
    if cv[0] == "indirect":
        for fc in ("bounds_check", "scalar_niche_invalid", "uninit_read"):
            out.add(FaultSite(bb_idx, stmt_idx, fc))
    elif cv[0] == "paramTypedConst":
        _emit_ob_const_sites(cv[1], bb_idx, stmt_idx, out)


def _emit_ob_operand_sites(
    op: tuple[Any, ...], bb_idx: int, stmt_idx: int, out: set[FaultSite], *, loaded: bool = False
) -> None:
    if op[0] in ("copy", "move"):
        _emit_ob_place_read_sites(op[1], bb_idx, stmt_idx, out)
        if loaded:
            out.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
    else:
        _emit_ob_const_sites(op[1], bb_idx, stmt_idx, out)


def emit_mir_obligation_fault_sites(body: dict[str, Any]) -> list[FaultSite]:
    bbs = body["basic_blocks"]
    num_blocks = len(bbs)
    sites: set[FaultSite] = set()
    for bb_idx, bb in enumerate(bbs):
        stmts = bb["statements"]
        for stmt_idx, stmt in enumerate(stmts):
            sk = stmt["kind"]
            stag = sk[0]
            if stag in ("storageLive", "storageDead"):
                sites.add(FaultSite(bb_idx, stmt_idx, "storage_live_protected"))
            elif stag == "placeMention":
                sites.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
            elif stag == "deinit":
                place = sk[1]
                if not place["projection"]:
                    sites.add(FaultSite(bb_idx, stmt_idx, "storage_live_protected"))
                else:
                    sites.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
                    for proj in place["projection"]:
                        _emit_ob_read_projected_sites(proj, bb_idx, stmt_idx, sites)
            elif stag == "retag":
                _emit_ob_place_read_sites(sk[1], bb_idx, stmt_idx, sites)
                for fc in ("bounds_check", "ptr_deref_invalid", "tree_borrows_violation"):
                    sites.add(FaultSite(bb_idx, stmt_idx, fc))
            elif stag == "setDiscriminant":
                place = sk[1]
                if not place["projection"]:
                    sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                    sites.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
                else:
                    _emit_ob_place_read_sites(place, bb_idx, stmt_idx, sites)
                    _emit_ob_place_write_sites(place, bb_idx, stmt_idx, sites)
                    sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
            elif stag == "intrinsic":
                intr = sk[1]
                if intr[0] == "assume":
                    _emit_ob_operand_sites(intr[1], bb_idx, stmt_idx, sites)
                    sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                elif intr[0] == "copyNonOverlapping":
                    _emit_ob_operand_sites(intr[1], bb_idx, stmt_idx, sites)
                    _emit_ob_operand_sites(intr[2], bb_idx, stmt_idx, sites)
                    _emit_ob_operand_sites(intr[3], bb_idx, stmt_idx, sites)
                    for fc in (
                        "arith_overflow",
                        "bounds_check",
                        "ptr_deref_invalid",
                        "ptr_align_mismatch",
                        "tree_borrows_violation",
                        "scalar_niche_invalid",
                        "uninit_read",
                    ):
                        sites.add(FaultSite(bb_idx, stmt_idx, fc))
            elif stag == "assign":
                dst, rv = sk[1], sk[2]
                rtag = rv[0]
                uneval = rtag in ("threadLocalRef", "nullaryOp", "shallowInitBox") or (
                    rtag == "aggregate" and rv[1][0] == "coroutine"
                )
                if not uneval:
                    _emit_ob_place_write_sites(dst, bb_idx, stmt_idx, sites)
                    if rtag in ("use", "wrapUnsafeBinder"):
                        _emit_ob_operand_sites(rv[1], bb_idx, stmt_idx, sites, loaded=True)
                    elif rtag == "repeat":
                        _emit_ob_operand_sites(rv[1], bb_idx, stmt_idx, sites)
                    elif rtag in ("ref", "rawPtr"):
                        _emit_ob_place_ref_sites(rv[2], bb_idx, stmt_idx, sites)
                    elif rtag == "len":
                        _emit_ob_place_read_sites(rv[1], bb_idx, stmt_idx, sites)
                        sites.add(FaultSite(bb_idx, stmt_idx, "bounds_check"))
                    elif rtag == "cast":
                        ck, op = rv[1], rv[2]
                        _emit_ob_operand_sites(op, bb_idx, stmt_idx, sites)
                        ctag = ck[0]
                        if ctag == "pointerExposeProvenance":
                            sites.add(FaultSite(bb_idx, stmt_idx, "ptr_deref_invalid"))
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                        elif ctag == "pointerWithExposedProvenance":
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                        elif ctag in ("transmute", "subtype"):
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                            sites.add(FaultSite(bb_idx, stmt_idx, "uninit_read"))
                        elif ctag == "pointerCoercion":
                            coerc = ck[1]
                            if coerc == "MutToConstPointer":
                                sites.add(FaultSite(bb_idx, stmt_idx, "ptr_deref_invalid"))
                                sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                            elif coerc in ("Unsize", "ArrayToPointer"):
                                for fc in (
                                    "bounds_check",
                                    "ptr_deref_invalid",
                                    "ptr_align_mismatch",
                                    "tree_borrows_violation",
                                    "scalar_niche_invalid",
                                ):
                                    sites.add(FaultSite(bb_idx, stmt_idx, fc))
                            else:
                                for fc in (
                                    "ptr_deref_invalid",
                                    "scalar_niche_invalid",
                                    "call_abi_mismatch",
                                ):
                                    sites.add(FaultSite(bb_idx, stmt_idx, fc))
                        elif ctag == "ptrToPtr":
                            for fc in (
                                "bounds_check",
                                "ptr_deref_invalid",
                                "ptr_align_mismatch",
                                "tree_borrows_violation",
                                "scalar_niche_invalid",
                            ):
                                sites.add(FaultSite(bb_idx, stmt_idx, fc))
                        elif ctag == "fnPtrToPtr":
                            for fc in (
                                "ptr_deref_invalid",
                                "scalar_niche_invalid",
                                "call_abi_mismatch",
                            ):
                                sites.add(FaultSite(bb_idx, stmt_idx, fc))
                    elif rtag == "binaryOp":
                        bop, lhs, rhs = rv[1], rv[2], rv[3]
                        _emit_ob_operand_sites(lhs, bb_idx, stmt_idx, sites)
                        _emit_ob_operand_sites(rhs, bb_idx, stmt_idx, sites)
                        if bop in ("addUnchecked", "subUnchecked", "mulUnchecked"):
                            sites.add(FaultSite(bb_idx, stmt_idx, "arith_overflow"))
                        elif bop in ("div", "rem"):
                            sites.add(FaultSite(bb_idx, stmt_idx, "arith_overflow"))
                            sites.add(FaultSite(bb_idx, stmt_idx, "div_rem_by_zero"))
                        elif bop in ("shlUnchecked", "shrUnchecked"):
                            sites.add(FaultSite(bb_idx, stmt_idx, "shift_overflow"))
                        elif bop == "offset":
                            for fc in (
                                "arith_overflow",
                                "bounds_check",
                                "ptr_deref_invalid",
                                "tree_borrows_violation",
                            ):
                                sites.add(FaultSite(bb_idx, stmt_idx, fc))
                    elif rtag == "unaryOp":
                        uop, val = rv[1], rv[2]
                        _emit_ob_operand_sites(val, bb_idx, stmt_idx, sites)
                        if uop == "not":
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                        elif uop == "ptrMetadata":
                            sites.add(FaultSite(bb_idx, stmt_idx, "ptr_deref_invalid"))
                    elif rtag == "discriminant":
                        _emit_ob_place_read_sites(rv[1], bb_idx, stmt_idx, sites)
                        sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                    elif rtag == "aggregate":
                        ak, ops = rv[1], rv[2]
                        for op in ops:
                            _emit_ob_operand_sites(op, bb_idx, stmt_idx, sites)
                        if ak[0] == "adt" and ak[3] is not None:
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                        elif ak[0] == "rawPtr":
                            sites.add(FaultSite(bb_idx, stmt_idx, "ptr_deref_invalid"))
                            sites.add(FaultSite(bb_idx, stmt_idx, "scalar_niche_invalid"))
                    elif rtag == "copyForDeref":
                        _emit_ob_place_read_sites(rv[1], bb_idx, stmt_idx, sites)

        term_idx = len(stmts)
        tk = bb["terminator"]["kind"]
        ttag = tk[0]
        if any(t < 0 or t >= num_blocks for t in terminator_targets(tk)) and ttag not in (
            "unwindTerminate",
            "inlineAsm",
            "unreachable",
            "unwindResume",
            "return_",
            "tailCall",
        ):
            sites.add(FaultSite(bb_idx, term_idx, "bounds_check"))
        if ttag == "unreachable":
            sites.add(FaultSite(bb_idx, term_idx, "unreachable_terminator"))
        elif ttag == "unwindResume":
            sites.add(FaultSite(bb_idx, term_idx, "call_abi_mismatch"))
        elif ttag == "return_":
            for fc in ("uninit_read", "tree_borrows_violation", "call_abi_mismatch"):
                sites.add(FaultSite(bb_idx, term_idx, fc))
        elif ttag == "switchInt":
            _emit_ob_operand_sites(tk[1], bb_idx, term_idx, sites)
            sites.add(FaultSite(bb_idx, term_idx, "scalar_niche_invalid"))
        elif ttag == "drop":
            place = tk[1]
            if not place["projection"]:
                sites.add(FaultSite(bb_idx, term_idx, "storage_live_protected"))
            else:
                sites.add(FaultSite(bb_idx, term_idx, "uninit_read"))
                for proj in place["projection"]:
                    _emit_ob_read_projected_sites(proj, bb_idx, term_idx, sites)
        elif ttag == "assert":
            cond, unwind = tk[1], tk[4]
            _emit_ob_operand_sites(cond, bb_idx, term_idx, sites)
            sites.add(FaultSite(bb_idx, term_idx, "scalar_niche_invalid"))
            if unwind[0] == "unreachable":
                sites.add(FaultSite(bb_idx, term_idx, "unreachable_terminator"))
            elif unwind[0] == "continue_":
                sites.add(FaultSite(bb_idx, term_idx, "call_abi_mismatch"))
        elif ttag == "call":
            func, args, dest, target, unwind = tk[1], tk[2], tk[3], tk[4], tk[5]
            _emit_ob_operand_sites(func, bb_idx, term_idx, sites)
            for arg in args:
                _emit_ob_operand_sites(arg, bb_idx, term_idx, sites)
            if target is not None:
                _emit_ob_place_write_sites(dest, bb_idx, term_idx, sites)
            sites.add(FaultSite(bb_idx, term_idx, "call_abi_mismatch"))
            dp = _extract_operand_callee_def_path(func)
            if dp is not None:
                if target is not None:
                    for fc in census_callee_def_path_fault_classes(dp):
                        sites.add(FaultSite(bb_idx, term_idx, fc))
                elif dp in (
                    "core::hint::unreachable_unchecked",
                    "std::hint::unreachable_unchecked",
                    "core::intrinsics::unreachable",
                ):
                    sites.add(FaultSite(bb_idx, term_idx, "unreachable_terminator"))
            else:
                sites.add(FaultSite(bb_idx, term_idx, "ptr_deref_invalid"))
            if unwind[0] == "unreachable":
                sites.add(FaultSite(bb_idx, term_idx, "unreachable_terminator"))
        elif ttag == "tailCall":
            func, args = tk[1], tk[2]
            _emit_ob_operand_sites(func, bb_idx, term_idx, sites)
            for arg in args:
                _emit_ob_operand_sites(arg, bb_idx, term_idx, sites)
            for fc in (
                "tree_borrows_violation",
                "uninit_read",
                "storage_live_protected",
                "call_abi_mismatch",
            ):
                sites.add(FaultSite(bb_idx, term_idx, fc))
            if _extract_operand_callee_def_path(func) is None:
                sites.add(FaultSite(bb_idx, term_idx, "ptr_deref_invalid"))
    return sorted(sites)


def direct_callee_def_paths(body: dict[str, Any]) -> list[str]:
    out: set[str] = set()
    for bb in body["basic_blocks"]:
        tk = bb["terminator"]["kind"]
        if tk[0] == "call":
            func, args, _dest, target, _unwind = tk[1], tk[2], tk[3], tk[4], tk[5]
            path = _extract_operand_callee_def_path(func)
            if path is not None:
                if (
                    target is not None
                    and path == "core::intrinsics::const_eval_select"
                    and len(args) == 3
                ):
                    rt = _extract_operand_callee_def_path(args[2])
                    out.add(rt if rt is not None else path)
                else:
                    out.add(path)
        elif tk[0] == "tailCall":
            path = _extract_operand_callee_def_path(tk[1])
            if path is not None:
                out.add(path)
    return sorted(out)


def reified_fn_def_paths(body: dict[str, Any]) -> list[str]:
    out: set[str] = set()
    for bb in body["basic_blocks"]:
        for stmt in bb["statements"]:
            sk = stmt["kind"]
            if sk[0] == "assign":
                rv = sk[2]
                if rv[0] == "cast":
                    ck, op = rv[1], rv[2]
                    if ck[0] == "pointerCoercion":
                        coercion: str = ck[1]
                        if (
                            coercion == "ReifyFnPointer"
                            or coercion.startswith("ReifyFnPointer(")
                            or coercion == "ClosureFnPointer"
                            or coercion.startswith("ClosureFnPointer(")
                        ):
                            path = _extract_operand_callee_def_path(op)
                            if path is not None:
                                out.add(path)
    return sorted(out)


def reconcile_obligation_coverage(
    census: Iterable[FaultSite],
    discharged: Iterable[FaultSite],
    registry: object = None,
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=False)
    discharged_set = set(discharged)
    missing_sites: list[FaultSite] = []
    unemitted_set: set[str] = set()
    reasons: list[str] = []

    for site in census:
        status = reg[site.fault_class]["status"]
        in_discharged = site in discharged_set
        is_cls_verified = status == PROPERTY_STATUS_EMITTED_AND_VERIFIED
        if not in_discharged or not is_cls_verified:
            missing_sites.append(site)
            if not in_discharged:
                reasons.append(
                    f"unmapped fault site {site}: present in MIR census but omitted by obligation generator"
                )
            if not is_cls_verified and site.fault_class not in unemitted_set:
                unemitted_set.add(site.fault_class)
                reasons.append(
                    f"fault class `{site.fault_class}` at {site} has non-verified registry status {status}"
                )

    unemitted_classes = sorted(unemitted_set, key=lambda c: FAULT_CLASS_RANK[c])
    is_verified = not missing_sites and not unemitted_classes
    return {
        "verdict": "VERIFIED" if is_verified else "UNKNOWN(UNMAPPED_FAULT_SITE)",
        "is_verified": is_verified,
        "missing_sites": missing_sites,
        "unemitted_classes": unemitted_classes,
        "reasons": reasons,
    }


def reconcile_lean_mir_coverage(
    lean_src: str,
    discharged: Iterable[FaultSite],
    registry: object = None,
) -> dict[str, Any]:
    try:
        census = census_lean_mir_module(lean_src)
    except CensusScanError as err:
        return {
            "verdict": "UNKNOWN(UNMAPPED_FAULT_SITE)",
            "is_verified": False,
            "missing_sites": [],
            "unemitted_classes": [],
            "reasons": [f"census scan failed closed: {err}"],
        }
    return reconcile_obligation_coverage(census, discharged, registry)


def reconcile_multi_item_coverage(
    items: list[dict[str, Any]],
    closure: dict[str, Any] | None = None,
    registry: object = None,
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=False)
    if closure is None:
        closure = {
            "inline_callees": [],
            "external_callees": [],
            "allow_unresolved_indirect_calls": False,
        }
    if not items:
        return {
            "verdict": "UNKNOWN(UNMAPPED_FAULT_SITE)",
            "is_verified": False,
            "failed_items": [],
            "reasons": [
                "multi-item coverage batch is empty (at least one subject item required)"
            ],
        }

    seen_paths: set[str] = set()
    failed_items: list[tuple[str, dict[str, Any]]] = []
    reasons: list[str] = []

    for item in items:
        def_path = str(item.get("def_path", ""))
        body = item["body"]
        body_def_path = str(body.get("def_path", ""))
        discharged = list(item.get("discharged", ()))
        if not def_path:
            reasons.append("batch item has an empty `def_path`")
        if def_path in seen_paths:
            reasons.append(
                f"duplicate item def_path `{def_path}` in multi-item coverage batch"
            )
        seen_paths.add(def_path)
        if def_path != body_def_path:
            reasons.append(
                f"item label `{def_path}` does not match its body def_path `{body_def_path}`"
            )
        census = census_mir_fault_sites(body)
        verdict = reconcile_obligation_coverage(census, discharged, reg)
        if not verdict["is_verified"]:
            for r in verdict["reasons"]:
                reasons.append(f"[{def_path}] {r}")
            failed_items.append((def_path, verdict))

    inline_list = list(closure.get("inline_callees", ()))
    external_list = list(closure.get("external_callees", ()))
    allow_unresolved = bool(closure.get("allow_unresolved_indirect_calls", False))

    external_set: set[str] = set()
    for ext in external_list:
        if ext in external_set:
            reasons.append(f"duplicate external callee `{ext}` in CalleeClosure")
        external_set.add(ext)

    inline_set: set[str] = set()
    for callee in inline_list:
        if callee in inline_set:
            reasons.append(f"duplicate inline callee `{callee}` in CalleeClosure")
        inline_set.add(callee)
        if callee not in seen_paths:
            reasons.append(
                f"inline callee `{callee}` has no batch item: its body can become `activeCallee` but its census was never reconciled"
            )
        if callee in external_set:
            reasons.append(f"callee `{callee}` is declared both inline and external")

    for item in items:
        def_path = str(item["def_path"])
        body = item["body"]
        if def_path in external_set:
            reasons.append(
                f"batch item `{def_path}` is declared in `closure.external_callees` (a verified batch item cannot be treated as an uninterpreted external callee)"
            )
        if not body_has_no_param_call_const(body):
            reasons.append(
                f"[{def_path}] body contains a `Call` or `TailCall` terminator whose `func` operand is a `RigidTy.param`-typed constant (`bodyHasNoParamCallConst` violated)"
            )
        if not cfg_targets_in_bounds(body):
            reasons.append(
                f"[{def_path}] body violates `cfgTargetsInBounds` (empty `basicBlocks` or out-of-bounds terminator/unwind target)"
            )
        for bb_idx, bb in enumerate(body["basic_blocks"]):
            tk = bb["terminator"]["kind"]
            if tk[0] == "call":
                func, args, _dest, target, _unwind = tk[1], tk[2], tk[3], tk[4], tk[5]
                callee = _extract_operand_callee_def_path(func)
                if target is not None:
                    if callee is not None:
                        if callee == "core::intrinsics::const_eval_select":
                            rt_ok = False
                            if len(args) == 3:
                                rt = _extract_operand_callee_def_path(args[2])
                                if rt is not None:
                                    rt_ok = (
                                        rt in inline_set
                                        or rt in external_set
                                        or rt in _NATIVE_CONVERGING_SET
                                        or rt in _NATIVE_DIVERGING_SET
                                    )
                                else:
                                    rt_ok = allow_unresolved
                            if not rt_ok:
                                reasons.append(
                                    f"[{def_path}] bb{bb_idx} `const_eval_select` runtime target is not classified in CalleeClosure"
                                )
                        else:
                            classified = (
                                callee in inline_set
                                or callee in external_set
                                or callee in _NATIVE_CONVERGING_SET
                            )
                            if not classified:
                                reasons.append(
                                    f"[{def_path}] direct callee `{callee}` is neither a declared inline callee, a declared external callee, nor a natively modeled converging-call intrinsic"
                                )
                    elif not allow_unresolved:
                        reasons.append(
                            f"[{def_path}] bb{bb_idx} indirect call through a non-constant `func` operand has an unresolved target and CalleeClosure does not permit unresolved indirect calls"
                        )
                else:
                    if callee is not None:
                        classified = (
                            callee in inline_set
                            or callee in external_set
                            or callee in _NATIVE_DIVERGING_SET
                        )
                        if not classified:
                            reasons.append(
                                f"[{def_path}] direct callee `{callee}` is neither a declared inline callee, a declared external callee, nor a natively modeled diverging-call target"
                            )
                    elif not allow_unresolved:
                        reasons.append(
                            f"[{def_path}] bb{bb_idx} indirect diverging call through a non-constant `func` operand has an unresolved target and CalleeClosure does not permit unresolved indirect calls"
                        )
            elif tk[0] == "tailCall":
                callee = _extract_operand_callee_def_path(tk[1])
                if callee is not None:
                    if callee not in inline_set and callee not in external_set:
                        reasons.append(
                            f"[{def_path}] direct tail-call callee `{callee}` is neither a declared inline callee nor a declared external callee"
                        )
                elif not allow_unresolved:
                    reasons.append(
                        f"[{def_path}] bb{bb_idx} indirect tail call through a non-constant `func` operand has an unresolved target and CalleeClosure does not permit unresolved indirect calls"
                    )
        for reified in reified_fn_def_paths(body):
            if reified not in inline_set and reified not in external_set:
                reasons.append(
                    f"[{def_path}] reified function pointer target `{reified}` (`ReifyFnPointer`) is neither a declared inline callee nor a declared external callee"
                )

    is_verified = not failed_items and not reasons
    return {
        "verdict": "VERIFIED" if is_verified else "UNKNOWN(UNMAPPED_FAULT_SITE)",
        "is_verified": is_verified,
        "failed_items": failed_items,
        "reasons": reasons,
    }


# ---------------------------------------------------------------------------
# 4 + 2 False-Proof Mutation Probes
# ---------------------------------------------------------------------------

FAULT_MUTATION_PROBES: tuple[str, ...] = (
    "CallArgBlindProbe",
    "SwitchBreakStripProbe",
    "LoopUpdateOverflowProbe",
    "DerefAliasProbe",
)

ALL_FALSE_PROOF_PROBES: tuple[str, ...] = (
    "CallArgBlindProbe",
    "SwitchBreakStripProbe",
    "LoopUpdateOverflowProbe",
    "DerefAliasProbe",
    "PropertyRegistryUnemittedProbe",
    "CalleeCoordinateMaskProbe",
)


def _place_has_deref(place: dict[str, Any]) -> bool:
    return any(p[0] == "deref" for p in place["projection"])


def _operand_has_deref(op: tuple[Any, ...]) -> bool:
    return op[0] in ("copy", "move") and _place_has_deref(op[1])


def _rvalue_has_deref(rv: tuple[Any, ...]) -> bool:
    tag = rv[0]
    if tag in ("use", "repeat", "shallowInitBox", "wrapUnsafeBinder"):
        return _operand_has_deref(rv[1])
    if tag == "cast":
        return _operand_has_deref(rv[2])
    if tag == "unaryOp":
        return _operand_has_deref(rv[2])
    if tag == "binaryOp":
        return _operand_has_deref(rv[2]) or _operand_has_deref(rv[3])
    if tag == "aggregate":
        return any(_operand_has_deref(op) for op in rv[2])
    if tag in ("ref", "rawPtr"):
        return _place_has_deref(rv[2])
    if tag in ("len", "discriminant", "copyForDeref"):
        return _place_has_deref(rv[1])
    return False


def _stmt_has_deref(kind: tuple[Any, ...]) -> bool:
    tag = kind[0]
    if tag == "assign":
        return _place_has_deref(kind[1]) or _rvalue_has_deref(kind[2])
    if tag in ("setDiscriminant", "deinit", "retag", "placeMention"):
        return _place_has_deref(kind[1])
    if tag == "intrinsic":
        intr = kind[1]
        if intr[0] == "assume":
            return _operand_has_deref(intr[1])
        if intr[0] == "copyNonOverlapping":
            return True
    return False


def _strip_deref_projections(op: tuple[Any, ...]) -> tuple[Any, ...]:
    if op[0] in ("copy", "move"):
        p = op[1]
        return (
            op[0],
            {
                "local_": p["local_"],
                "projection": [e for e in p["projection"] if e[0] != "deref"],
            },
        )
    return op


def mock_emit_obligations(
    body: dict[str, Any], mutation: str | None = None
) -> list[FaultSite]:
    bbs = body["basic_blocks"]
    num_blocks = len(bbs)
    reachable = [False] * num_blocks
    work = [0]
    while work:
        b = work.pop()
        if b < 0 or b >= num_blocks or reachable[b]:
            continue
        reachable[b] = True
        tk = bbs[b]["terminator"]["kind"]
        if tk[0] == "switchInt" and mutation == "SwitchBreakStripProbe":
            work.extend(int(t) for _, t in tk[2]["branches"])
        else:
            work.extend(terminator_targets(tk))

    out: list[FaultSite] = []
    for b, bb in enumerate(bbs):
        if not reachable[b]:
            continue
        is_latch = any(t <= b for t in terminator_targets(bb["terminator"]["kind"]))
        for i, stmt in enumerate(bb["statements"]):
            classes = list(census_stmt_fault_classes(stmt["kind"]))
            if mutation == "LoopUpdateOverflowProbe" and is_latch:
                classes = [c for c in classes if c != "arith_overflow"]
            elif mutation == "DerefAliasProbe" and _stmt_has_deref(stmt["kind"]):
                classes = [
                    c
                    for c in classes
                    if c
                    not in (
                        "ptr_deref_invalid",
                        "ptr_align_mismatch",
                        "tree_borrows_violation",
                    )
                ]
            for c in classes:
                out.append(FaultSite(b, i, c))
        term_idx = len(bb["statements"])
        tk = bb["terminator"]["kind"]
        if tk[0] == "call" and mutation == "CallArgBlindProbe":
            stripped_tk = (
                "call",
                tk[1],
                [_strip_deref_projections(a) for a in tk[2]],
                tk[3],
                tk[4],
                tk[5],
            )
            term_classes = census_terminator_fault_classes(num_blocks, stripped_tk)
        else:
            term_classes = census_terminator_fault_classes(num_blocks, tk)
        for c in term_classes:
            out.append(FaultSite(b, term_idx, c))
    return out


def _mk_local_place(local_: int) -> dict[str, Any]:
    return {"local_": local_, "projection": []}


def _mk_deref_local_place(local_: int) -> dict[str, Any]:
    return {"local_": local_, "projection": [("deref",)]}


def _mk_const_u32(bits: int) -> tuple[Any, ...]:
    return ("constant", ("scalarInt", bits, 4))


def _mk_const_fn(def_path: str) -> tuple[Any, ...]:
    return ("constant", ("zeroSized", def_path))


def build_probe_scenario(
    probe: str,
) -> tuple[dict[str, Any], list[FaultSite], list[FaultSite], list[FaultSite]]:
    if probe == "CallArgBlindProbe":
        body = {
            "def_path": "proto::witness_call_arg_blind",
            "basic_blocks": [
                {
                    "statements": [],
                    "terminator": {
                        "kind": (
                            "call",
                            _mk_const_fn("proto::callee_u32"),
                            [("copy", _mk_deref_local_place(1))],
                            _mk_local_place(0),
                            1,
                            ("continue_",),
                        ),
                        "span": "proto.rs:10:5",
                    },
                    "is_cleanup": False,
                },
                {
                    "statements": [],
                    "terminator": {"kind": ("return_",), "span": "proto.rs:11:5"},
                    "is_cleanup": False,
                },
            ],
        }
        expected_missing = [
            FaultSite(0, 0, "ptr_deref_invalid"),
            FaultSite(0, 0, "ptr_align_mismatch"),
        ]
    elif probe == "SwitchBreakStripProbe":
        body = {
            "def_path": "proto::witness_switch_break_strip",
            "basic_blocks": [
                {
                    "statements": [],
                    "terminator": {
                        "kind": (
                            "switchInt",
                            ("copy", _mk_local_place(1)),
                            {"branches": [(0, 1)], "otherwise": 2},
                        ),
                        "span": "proto.rs:20:5",
                    },
                    "is_cleanup": False,
                },
                {
                    "statements": [
                        {
                            "kind": (
                                "assign",
                                _mk_local_place(0),
                                ("use", _mk_const_u32(42)),
                            ),
                            "span": "proto.rs:21:9",
                        }
                    ],
                    "terminator": {"kind": ("return_",), "span": "proto.rs:21:15"},
                    "is_cleanup": False,
                },
                {
                    "statements": [
                        {
                            "kind": (
                                "assign",
                                _mk_local_place(0),
                                (
                                    "binaryOp",
                                    "div",
                                    ("copy", _mk_local_place(1)),
                                    ("copy", _mk_local_place(2)),
                                ),
                            ),
                            "span": "proto.rs:22:9",
                        }
                    ],
                    "terminator": {"kind": ("return_",), "span": "proto.rs:22:15"},
                    "is_cleanup": False,
                },
            ],
        }
        expected_missing = [
            FaultSite(2, 0, "arith_overflow"),
            FaultSite(2, 0, "div_rem_by_zero"),
            FaultSite(2, 0, "tree_borrows_violation"),
            FaultSite(2, 0, "uninit_read"),
            FaultSite(2, 0, "storage_live_protected"),
            FaultSite(2, 1, "tree_borrows_violation"),
            FaultSite(2, 1, "uninit_read"),
            FaultSite(2, 1, "call_abi_mismatch"),
        ]
    elif probe == "LoopUpdateOverflowProbe":
        body = {
            "def_path": "proto::witness_loop_update_overflow",
            "basic_blocks": [
                {
                    "statements": [],
                    "terminator": {"kind": ("goto", 1), "span": "proto.rs:30:5"},
                    "is_cleanup": False,
                },
                {
                    "statements": [],
                    "terminator": {
                        "kind": (
                            "switchInt",
                            ("copy", _mk_local_place(1)),
                            {"branches": [(0, 3)], "otherwise": 2},
                        ),
                        "span": "proto.rs:31:5",
                    },
                    "is_cleanup": False,
                },
                {
                    "statements": [
                        {
                            "kind": (
                                "assign",
                                _mk_local_place(1),
                                (
                                    "binaryOp",
                                    "addUnchecked",
                                    ("copy", _mk_local_place(1)),
                                    _mk_const_u32(1),
                                ),
                            ),
                            "span": "proto.rs:32:9",
                        },
                        {
                            "kind": (
                                "assign",
                                _mk_local_place(0),
                                (
                                    "binaryOp",
                                    "add",
                                    ("copy", _mk_local_place(0)),
                                    ("copy", _mk_local_place(1)),
                                ),
                            ),
                            "span": "proto.rs:33:9",
                        },
                    ],
                    "terminator": {"kind": ("goto", 1), "span": "proto.rs:33:20"},
                    "is_cleanup": False,
                },
                {
                    "statements": [],
                    "terminator": {"kind": ("return_",), "span": "proto.rs:34:5"},
                    "is_cleanup": False,
                },
            ],
        }
        expected_missing = [FaultSite(2, 0, "arith_overflow")]
    elif probe == "DerefAliasProbe":
        body = {
            "def_path": "proto::witness_deref_alias",
            "basic_blocks": [
                {
                    "statements": [
                        {
                            "kind": (
                                "assign",
                                _mk_deref_local_place(1),
                                ("use", ("copy", _mk_deref_local_place(2))),
                            ),
                            "span": "proto.rs:40:5",
                        }
                    ],
                    "terminator": {"kind": ("return_",), "span": "proto.rs:41:5"},
                    "is_cleanup": False,
                }
            ],
        }
        expected_missing = [
            FaultSite(0, 0, "ptr_deref_invalid"),
            FaultSite(0, 0, "ptr_align_mismatch"),
            FaultSite(0, 0, "tree_borrows_violation"),
        ]
    else:
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"unknown false-proof mutation probe `{probe}`"
        )
    # `[adv ep2-B1]`: the baseline is the REAL independent obligation emitter
    # (`emit_mir_obligation_fault_sites`), never a census-derived mock, so a
    # regression in the emitter (e.g. dropping call-argument or deref obligations)
    # fails the probe instead of being masked by `baseline == census` by construction.
    baseline = emit_mir_obligation_fault_sites(body)
    mutant = mock_emit_obligations(body, probe)
    return (body, baseline, mutant, expected_missing)


def build_callee_storage_witness_body() -> dict[str, Any]:
    return {
        "def_path": "proto::witness_callee_storage",
        "basic_blocks": [
            {
                "statements": [
                    {"kind": ("storageDead", 1), "span": "proto.rs:50:5"}
                ],
                "terminator": {"kind": ("return_",), "span": "proto.rs:51:5"},
                "is_cleanup": False,
            }
        ],
    }


def run_false_proof_probe(
    probe: str, *, registry: object = None
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=False)
    body, baseline_discharged, mutant_discharged, expected_missing = (
        build_probe_scenario(probe)
    )
    census = census_mir_fault_sites(body)
    baseline_verdict = reconcile_obligation_coverage(
        census, baseline_discharged, reg
    )
    mutant_verdict = reconcile_obligation_coverage(
        census, mutant_discharged, reg
    )
    passed = (
        baseline_discharged == census
        and baseline_verdict["is_verified"]
        and not mutant_verdict["is_verified"]
        and mutant_verdict["missing_sites"] == expected_missing
        and mutant_verdict["unemitted_classes"] == []
    )
    return {
        "probe": probe,
        "census": census,
        "baseline_discharged": baseline_discharged,
        "baseline_verdict": baseline_verdict,
        "mutant_verdict": mutant_verdict,
        "expected_missing_sites": expected_missing,
        "passed": passed,
    }


def build_all_fault_classes_witness_body() -> dict[str, Any]:
    """`[adv ep2-B1]` One body whose census reaches every `MIR_FAULT_CLASSES` member.

    The four mutation-probe bodies never reach `shift_overflow`, `bounds_check`, or
    `unreachable_terminator`, so an obligation emitter (or reconciler) that silently
    dropped one of those classes passed every probe. This witness is reconciled with
    the REAL emitter and swept class-by-class by `PropertyRegistryUnemittedProbe`.
    """
    return {
        "def_path": "proto::witness_all_fault_classes",
        "basic_blocks": [
            {
                "statements": [
                    {"kind": ("storageLive", 1), "span": "proto.rs:60:5"},
                    {
                        "kind": (
                            "assign",
                            _mk_local_place(0),
                            (
                                "binaryOp",
                                "shlUnchecked",
                                ("copy", _mk_local_place(1)),
                                _mk_const_u32(3),
                            ),
                        ),
                        "span": "proto.rs:61:5",
                    },
                    {
                        "kind": (
                            "assign",
                            _mk_local_place(0),
                            (
                                "binaryOp",
                                "div",
                                ("copy", _mk_local_place(1)),
                                ("copy", _mk_local_place(2)),
                            ),
                        ),
                        "span": "proto.rs:62:5",
                    },
                    {
                        "kind": (
                            "assign",
                            _mk_local_place(0),
                            (
                                "use",
                                ("copy", {"local_": 3, "projection": [("index", 4)]}),
                            ),
                        ),
                        "span": "proto.rs:63:5",
                    },
                    {
                        "kind": (
                            "assign",
                            _mk_deref_local_place(5),
                            ("use", ("copy", _mk_deref_local_place(6))),
                        ),
                        "span": "proto.rs:64:5",
                    },
                ],
                "terminator": {
                    "kind": (
                        "call",
                        _mk_const_fn("proto::callee_u32"),
                        [("copy", _mk_local_place(1))],
                        _mk_local_place(0),
                        1,
                        ("continue_",),
                    ),
                    "span": "proto.rs:65:5",
                },
                "is_cleanup": False,
            },
            {
                "statements": [],
                "terminator": {"kind": ("unreachable",), "span": "proto.rs:66:5"},
                "is_cleanup": False,
            },
        ],
    }


def run_property_registry_unemitted_probe() -> dict[str, Any]:
    body, discharged, _mutant, _expected_missing = build_probe_scenario(
        "DerefAliasProbe"
    )
    census = census_mir_fault_sites(body)
    baseline_verdict = reconcile_obligation_coverage(
        census, discharged, PROPERTY_REGISTRY
    )
    unemitted_reg = {
        cls: dict(desc) for cls, desc in PROPERTY_REGISTRY.items()
    }
    unemitted_reg["tree_borrows_violation"]["status"] = PROPERTY_STATUS_UNEMITTED_GAP
    mutant_verdict = reconcile_obligation_coverage(census, discharged, unemitted_reg)
    expected_missing = [
        FaultSite(0, 0, "tree_borrows_violation"),
        FaultSite(0, 1, "tree_borrows_violation"),
    ]
    passed = (
        discharged == census
        and baseline_verdict["is_verified"]
        and not mutant_verdict["is_verified"]
        and mutant_verdict["missing_sites"] == expected_missing
        and mutant_verdict["unemitted_classes"] == ["tree_borrows_violation"]
    )
    # `[adv ep2-B1]`: sweep EVERY registry class over a witness body that reaches all
    # twelve classes: the real emitter must discharge the full census, and flipping
    # any single class to UNEMITTED_GAP must fail closed on exactly that class's sites.
    witness = build_all_fault_classes_witness_body()
    witness_census = census_mir_fault_sites(witness)
    witness_discharged = emit_mir_obligation_fault_sites(witness)
    witness_classes = [
        cls for cls in MIR_FAULT_CLASSES if any(s.fault_class == cls for s in witness_census)
    ]
    witness_baseline = reconcile_obligation_coverage(
        witness_census, witness_discharged, PROPERTY_REGISTRY
    )
    per_class: dict[str, bool] = {}
    for cls in MIR_FAULT_CLASSES:
        cls_reg = {c: dict(desc) for c, desc in PROPERTY_REGISTRY.items()}
        cls_reg[cls]["status"] = PROPERTY_STATUS_UNEMITTED_GAP
        cls_verdict = reconcile_obligation_coverage(
            witness_census, witness_discharged, cls_reg
        )
        per_class[cls] = (
            not cls_verdict["is_verified"]
            and cls_verdict["missing_sites"]
            == [s for s in witness_census if s.fault_class == cls]
            and cls_verdict["unemitted_classes"] == [cls]
        )
    passed = (
        passed
        and witness_classes == list(MIR_FAULT_CLASSES)
        and witness_discharged == witness_census
        and witness_baseline["is_verified"]
        and all(per_class.values())
    )
    return {
        "probe": "PropertyRegistryUnemittedProbe",
        "baseline_verdict": baseline_verdict,
        "mutant_verdict": mutant_verdict,
        "expected_missing_sites": expected_missing,
        "witnessClasses": witness_classes,
        "perClassFailClosed": per_class,
        "passed": passed,
    }


def run_callee_coordinate_mask_probe() -> dict[str, Any]:
    caller_body, caller_discharged, _mutant, _expected = build_probe_scenario(
        "DerefAliasProbe"
    )
    callee_body = build_callee_storage_witness_body()
    callee_census = census_mir_fault_sites(callee_body)
    callee_discharged = emit_mir_obligation_fault_sites(callee_body)
    closure = {
        "inline_callees": [callee_body["def_path"]],
        "external_callees": [],
        "allow_unresolved_indirect_calls": False,
    }
    flattened_census = [*census_mir_fault_sites(caller_body), *callee_census]
    flattened_verdict = reconcile_obligation_coverage(
        flattened_census, caller_discharged, PROPERTY_REGISTRY
    )
    baseline_batch = reconcile_multi_item_coverage(
        [
            {
                "def_path": caller_body["def_path"],
                "body": caller_body,
                "discharged": caller_discharged,
            },
            {
                "def_path": callee_body["def_path"],
                "body": callee_body,
                "discharged": callee_discharged,
            },
        ],
        closure,
        PROPERTY_REGISTRY,
    )
    masked_batch = reconcile_multi_item_coverage(
        [
            {
                "def_path": caller_body["def_path"],
                "body": caller_body,
                "discharged": caller_discharged,
            },
            {
                "def_path": callee_body["def_path"],
                "body": callee_body,
                "discharged": [],
            },
        ],
        closure,
        PROPERTY_REGISTRY,
    )
    passed = (
        callee_discharged == callee_census
        and caller_discharged == census_mir_fault_sites(caller_body)
        and flattened_verdict["is_verified"]
        and baseline_batch["is_verified"]
        and not masked_batch["is_verified"]
        and len(masked_batch["failed_items"]) == 1
        and masked_batch["failed_items"][0][0] == "proto::witness_callee_storage"
        and masked_batch["failed_items"][0][1]["missing_sites"] == callee_census
    )
    return {
        "probe": "CalleeCoordinateMaskProbe",
        "flattened_verdict": flattened_verdict,
        "baseline_verdict": baseline_batch,
        "mutant_verdict": masked_batch,
        "expected_missing_sites": callee_census,
        "passed": passed,
    }


def run_false_proof_mutation_probes(
    *, registry: object = None
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=True)
    passed_probes: list[str] = []
    for probe_name in FAULT_MUTATION_PROBES:
        rep = run_false_proof_probe(probe_name, registry=reg)
        if not rep["passed"]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"false-proof mutation probe `{probe_name}` failed: baseline={rep['baseline_verdict']['verdict']}, mutant={rep['mutant_verdict']['verdict']}",
            )
        passed_probes.append(probe_name)

    reg_probe = run_property_registry_unemitted_probe()
    if not reg_probe["passed"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            "false-proof mutation probe `PropertyRegistryUnemittedProbe` failed",
        )
    passed_probes.append("PropertyRegistryUnemittedProbe")

    mask_probe = run_callee_coordinate_mask_probe()
    if not mask_probe["passed"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            "false-proof mutation probe `CalleeCoordinateMaskProbe` failed",
        )
    passed_probes.append("CalleeCoordinateMaskProbe")

    return {
        "faultClasses": len(MIR_FAULT_CLASSES),
        "propertyRegistryVerified": len(reg),
        "probesPassed": passed_probes,
    }


def _trusted_string_eq_literals(src: str, def_name: str) -> set[str]:
    try:
        tokens = tokenize_lean_source(src)
    except CensusScanError as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"malformed syntax in Terminators.lean while scanning `{def_name}`: {err}",
        ) from err
    top_indices = _top_level_token_indices(tokens)
    top_set = set(top_indices)
    start_idx: int | None = None
    for idx in top_indices:
        if (
            idx + 1 < len(tokens)
            and tokens[idx] == ("Ident", "def")
            and tokens[idx + 1] == ("Ident", def_name)
        ):
            if start_idx is not None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"duplicate `def {def_name}` in Terminators.lean",
                )
            start_idx = idx
    if start_idx is None:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing trusted definition `def {def_name}` in Terminators.lean",
        )
    end_idx = len(tokens)
    for k in range(start_idx + 2, len(tokens)):
        if k in top_set and _fc_is_lean_command_start(tokens[k]):
            end_idx = k
            break
    body_tokens = tokens[start_idx:end_idx]
    out: set[str] = set()
    for i in range(len(body_tokens) - 1):
        if body_tokens[i] == ("Ident", "stringEq"):
            for j in range(i + 1, min(i + 4, len(body_tokens))):
                if body_tokens[j][0] == "StrLit":
                    out.add(str(body_tokens[j][1]))
                    break
    return out


def _parse_lean_expected_fault_site_list(
    tokens: list[tuple[str, Any]], def_name: str
) -> list[FaultSite]:
    n = len(tokens)
    top_set = set(_top_level_token_indices(tokens))
    found: list[FaultSite] | None = None
    idx = 0
    while idx + 5 < n:
        if (
            idx in top_set
            and tokens[idx] == ("Ident", "def")
            and tokens[idx + 1] == ("Ident", def_name)
            and tokens[idx + 2][0] == "Colon"
            and tokens[idx + 5][0] == "ColonEq"
        ):
            if found is not None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"duplicate `def {def_name}` in FaultSiteCensus.lean",
                )
            cur = _MirTokenCursor(tokens, idx + 6)

            def _parse_site(c: _MirTokenCursor) -> FaultSite:
                c.expect("LParen")
                b = c.parse_usize()
                c.expect("Comma")
                s = c.parse_usize()
                c.expect("Comma")
                full, short = c.parse_ctor_head()
                cls = LEAN_CTOR_TO_FAULT_CLASS.get(short)
                if cls is None:
                    raise CensusScanError(
                        "malformed_syntax", f"unknown MirFaultClass `{full}`"
                    )
                c.expect("RParen")
                return FaultSite(b, s, cls)

            sites = cur.parse_list(_parse_site)
            nxt = cur.peek()
            if nxt is not None and not _fc_is_lean_command_start(nxt):
                raise CensusScanError(
                    "malformed_syntax",
                    f"unexpected trailing token {nxt!r} after `def {def_name}` in FaultSiteCensus.lean",
                )
            found = sites
            idx = cur.pos
        else:
            idx += 1
    if found is None:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing `def {def_name} : List FaultSite` in FaultSiteCensus.lean",
        )
    return found


def _check_fault_site_census_lean_pins(src: str) -> None:
    all_marker = "def all : List MirFaultClass :="
    all_pos = src.find(all_marker)
    if all_pos < 0:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            "missing `def all : List MirFaultClass :=` in FaultSiteCensus.lean",
        )
    end_ns_pos = src.find("end MirFaultClass", all_pos)
    if end_ns_pos < 0:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            "missing `end MirFaultClass` in FaultSiteCensus.lean",
        )
    header_window = src[all_pos : end_ns_pos + len("end MirFaultClass")]
    try:
        hdr_tokens = tokenize_lean_source(header_window)
    except CensusScanError as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"failed to tokenize MirFaultClass definitions in FaultSiteCensus.lean: {err}",
        ) from err

    # 1. Parse `def all : List MirFaultClass := [ ... ]`
    cur = _MirTokenCursor(hdr_tokens, 6)
    try:
        ctors = cur.parse_list(lambda c: c.parse_ctor_head()[1])
        nxt_all = cur.peek()
        if nxt_all is not None and not _fc_is_lean_command_start(nxt_all):
            raise CensusScanError(
                "malformed_syntax",
                f"unexpected trailing token {nxt_all!r} after `MirFaultClass.all`",
            )
    except CensusScanError as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"malformed `MirFaultClass.all` in FaultSiteCensus.lean: {err}",
        ) from err
    expected_ctors = [FAULT_CLASS_TO_LEAN_CTOR[cls] for cls in MIR_FAULT_CLASSES]
    if ctors != expected_ctors:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`MirFaultClass.all` in FaultSiteCensus.lean ({ctors}) drifted from MIR_FAULT_CLASSES ({expected_ctors})",
        )

    # 2. Verify `def toRank` arms and `def asStr` arms over comment-free `hdr_tokens`
    to_rank_matches: list[tuple[str, int]] = []
    as_str_matches: list[tuple[str, str]] = []
    for i in range(len(hdr_tokens) - 4):
        if (
            hdr_tokens[i] == ("Ident", "|")
            and hdr_tokens[i + 1][0] == "Dot"
            and hdr_tokens[i + 2][0] == "Ident"
            and hdr_tokens[i + 3] == ("Ident", "=>")
        ):
            ctor = str(hdr_tokens[i + 2][1])
            rhs = hdr_tokens[i + 4]
            if rhs[0] == "NatLit":
                to_rank_matches.append((ctor, int(rhs[1])))
            elif rhs[0] == "StrLit":
                as_str_matches.append((ctor, str(rhs[1])))
    if len(to_rank_matches) != len(MIR_FAULT_CLASSES):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`MirFaultClass.toRank` arm count ({len(to_rank_matches)}) != {len(MIR_FAULT_CLASSES)} in FaultSiteCensus.lean",
        )
    for ctor, rank in to_rank_matches:
        expected_cls = LEAN_CTOR_TO_FAULT_CLASS.get(ctor)
        if expected_cls is None or FAULT_CLASS_RANK.get(expected_cls) != rank:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`MirFaultClass.toRank` drift for `.{ctor} => {rank}` in FaultSiteCensus.lean",
            )

    if len(as_str_matches) != len(MIR_FAULT_CLASSES):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`MirFaultClass.asStr` arm count ({len(as_str_matches)}) != {len(MIR_FAULT_CLASSES)} in FaultSiteCensus.lean",
        )
    for ctor, snake_str in as_str_matches:
        if LEAN_CTOR_TO_FAULT_CLASS.get(ctor) != snake_str:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`MirFaultClass.asStr` drift for `.{ctor} => \"{snake_str}\"` in FaultSiteCensus.lean",
            )

    # 3. Parse the witness definitions in the tail of `FaultSiteCensus.lean`
    wit_pos = src.find("def witnessPureNoopBody : CapturedMir :=")
    if wit_pos < 0:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            "missing `witnessPureNoopBody` in FaultSiteCensus.lean",
        )
    witness_slice = src[wit_pos:]
    try:
        wit_tokens = tokenize_lean_source(witness_slice)
        noop_body = parse_lean_captured_mir_def_metadata(
            witness_slice, "witnessPureNoopBody", tokens=wit_tokens
        )["body"]
        if census_mir_fault_sites(noop_body) != []:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                "witnessPureNoopBody census is non-empty",
            )
        for body_def, expected_def, probe_name in (
            (
                "witnessCallArgBlindBody",
                "witnessCallArgBlindExpectedCensus",
                "CallArgBlindProbe",
            ),
            (
                "witnessSwitchBreakStripBody",
                "witnessSwitchBreakStripExpectedCensus",
                "SwitchBreakStripProbe",
            ),
            (
                "witnessLoopUpdateOverflowBody",
                "witnessLoopUpdateOverflowExpectedCensus",
                "LoopUpdateOverflowProbe",
            ),
            (
                "witnessDerefAliasBody",
                "witnessDerefAliasExpectedCensus",
                "DerefAliasProbe",
            ),
        ):
            parsed_w = parse_lean_captured_mir_def_metadata(
                witness_slice, body_def, tokens=wit_tokens
            )["body"]
            lean_expected = _parse_lean_expected_fault_site_list(
                wit_tokens, expected_def
            )
            py_census = census_mir_fault_sites(parsed_w)
            probe_body, _, _, _ = build_probe_scenario(probe_name)
            if parsed_w != probe_body or py_census != lean_expected:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Lean witness `{body_def}` / `{expected_def}` drifted from Python `{probe_name}`",
                )
        for body_def, expected_def in (
            ("witnessWrappingArithBody", "witnessWrappingArithExpectedCensus"),
            ("witnessCalleeStorageBody", "witnessCalleeStorageExpectedCensus"),
        ):
            parsed_w = parse_lean_captured_mir_def_metadata(
                witness_slice, body_def, tokens=wit_tokens
            )["body"]
            lean_expected = _parse_lean_expected_fault_site_list(
                wit_tokens, expected_def
            )
            if census_mir_fault_sites(parsed_w) != lean_expected:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Lean witness `{body_def}` census drifted from `{expected_def}`",
                )
    except CensusScanError as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"failed to parse witness definitions in FaultSiteCensus.lean: {err}",
        ) from err


def check_fault_census_source_pins(
    checkout: Path, staged_source: Path | None = None
) -> dict[str, bool]:
    validate_property_registry(PROPERTY_REGISTRY, require_all_verified=True)
    terminators_rel = Path(
        "Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean"
    )
    term_candidates: list[Path] = []
    if staged_source is not None:
        term_candidates.append(staged_source / terminators_rel)
    term_candidates.append(checkout / "trusted/lean" / terminators_rel)

    checked_terminators = False
    for term_path in term_candidates:
        if term_path.exists() or term_path.is_symlink():
            regular(term_path, FAULT_COVERAGE_PHASE)
            try:
                term_src = term_path.read_text(encoding="utf-8", errors="strict")
            except (OSError, UnicodeDecodeError) as err:
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"cannot read {term_path}: {err}"
                ) from err
            intrinsics = _trusted_string_eq_literals(
                term_src, "classifyRustIntrinsic?"
            )
            exact_div = _trusted_string_eq_literals(
                term_src, "isDirectExactDivTarget"
            )
            converging = (
                intrinsics - {"core::intrinsics::const_eval_select"}
            ) | exact_div
            if len(intrinsics) != 25 or converging != _NATIVE_CONVERGING_SET:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Terminators.lean native converging call callees drifted from NATIVE_CONVERGING_CALL_CALLEES (diff={ sorted(converging ^ _NATIVE_CONVERGING_SET) })",
                )
            diverging: set[str] = set()
            for def_name in (
                "isUnreachableCallTarget",
                "isAbortingPanicDefPath",
                "isUnwindingPanicDefPath",
            ):
                diverging |= _trusted_string_eq_literals(term_src, def_name)
            if diverging != _NATIVE_DIVERGING_SET:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Terminators.lean native diverging call callees drifted from NATIVE_DIVERGING_CALL_CALLEES (diff={ sorted(diverging ^ _NATIVE_DIVERGING_SET) })",
                )
            checked_terminators = True
            break

    census_lean_path = checkout / "theory/Anneal/FaultSiteCensus.lean"
    checked_census_lean = False
    if census_lean_path.exists() or census_lean_path.is_symlink():
        regular(census_lean_path, FAULT_COVERAGE_PHASE)
        try:
            census_src = census_lean_path.read_text(
                encoding="utf-8", errors="strict"
            )
        except (OSError, UnicodeDecodeError) as err:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"cannot read {census_lean_path}: {err}",
            ) from err
        _check_fault_site_census_lean_pins(census_src)
        checked_census_lean = True

    return {
        "terminators": checked_terminators,
        "faultSiteCensus": checked_census_lean,
    }


def fault_census_source_pins_required(
    checkout: Path, staged_source: Path | None = None
) -> bool:
    """`[adv ep2-B1]` The cross-language source pins are mandatory whenever the checkout
    ships any part of the census theory: `theory/Anneal.lean` importing
    `Anneal.FaultSiteCensus`, or either pinned source (`Terminators.lean`,
    `theory/Anneal/FaultSiteCensus.lean`) being present, in which case BOTH must be present
    and agree. Only minimal `--self-test` fixture trees (no census theory at all) skip them.
    """
    anneal_root = checkout / "theory/Anneal.lean"
    if anneal_root.exists() or anneal_root.is_symlink():
        text = _read_regular_text(anneal_root, "theory/Anneal.lean")
        if "Anneal.FaultSiteCensus" in _scan_lean_module_imports(text, str(anneal_root)):
            return True
    terminators_rel = Path("Trusted/Rustc/V2026_06_01/MirSemantics/Terminators.lean")
    candidates = [
        checkout / "theory/Anneal/FaultSiteCensus.lean",
        checkout / "trusted/lean" / terminators_rel,
    ]
    if staged_source is not None:
        candidates.append(staged_source / terminators_rel)
    return any(c.exists() or c.is_symlink() for c in candidates)


def audit_checkout_fault_coverage_gate(
    checkout: Path,
    staged_source: Path | None = None,
    *,
    require_source_pins: bool = False,
) -> dict[str, Any]:
    """Run the pure-Python fault-coverage gate (source pins + 4+2 mutation probes).

    `[adv ep2-B1]`: when `require_source_pins` is set (the standalone
    `--audit-fault-coverage` CLI, and `Checker.run()` on a real checkout that ships
    `theory/Anneal.lean`), a missing `Terminators.lean` or
    `theory/Anneal/FaultSiteCensus.lean` fails closed instead of silently skipping
    the cross-language pins; only minimal `--self-test` fixture trees may skip them.
    """
    pins = check_fault_census_source_pins(checkout, staged_source)
    if require_source_pins and not (pins["terminators"] and pins["faultSiteCensus"]):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"cross-language fault-census source pins could not run (Terminators.lean / theory/Anneal/FaultSiteCensus.lean missing): {pins}",
        )
    probes = run_false_proof_mutation_probes()
    return {
        **probes,
        "sourcePinsChecked": pins,
    }


_OB_DEFAULT_CALLEES_SHADOW_KWS: frozenset[str] = frozenset((
    "abbrev",
    "theorem",
    "lemma",
    "axiom",
    "opaque",
    "instance",
    "example",
    "structure",
    "inductive",
    "class",
))

_OB_DECL_MODIFIER_KWS: frozenset[str] = frozenset((
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
))


def _top_level_token_indices(tokens: list[tuple[str, Any]]) -> list[int]:
    """Indices of tokens at bracket depth 0 (outside every `(`, `{`, and `[`)."""
    out: list[int] = []
    depth = 0
    for idx, (tk, _val) in enumerate(tokens):
        cur_depth = depth
        if tk in ("LParen", "LBrace", "LBracket"):
            depth += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            depth = max(0, depth - 1)
        if cur_depth == 0:
            out.append(idx)
    return out


def _tokenize_lean_or_fail(text: str, label: str) -> list[tuple[str, Any]]:
    try:
        return tokenize_lean_source(text)
    except CensusScanError as err:
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"malformed Lean module {label}: {err}"
        ) from err


def _read_regular_text(path: Path, label: str) -> str:
    if not (path.exists() or path.is_symlink()):
        raise Failure(1, FAULT_COVERAGE_PHASE, f"missing {label}: {path}")
    regular(path, FAULT_COVERAGE_PHASE)
    try:
        return path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeDecodeError) as err:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"cannot read {path}: {err}") from err


def _is_default_callees_name(name: str) -> bool:
    return name == "defaultCallees" or name.endswith(".defaultCallees")


def _parse_obligations_default_callee_suffixes(ob_text: str, ob_label: str) -> list[str]:
    """`[adv ep2-B1]` Strict port of Rust `parse_obligations_default_callees`.

    Fails closed (instead of returning `[]`) on a missing table, a shadowing or
    modified declaration (`abbrev defaultCallees`, `private def defaultCallees`,
    `def X.defaultCallees`), duplicate tables, a header other than
    `def defaultCallees : List CapturedMir :=`, entries other than
    `Mir.<Suffix>.body`, or trailing expressions after the table
    (`[...] ++ [...]`, `[...].drop 1`, ...).
    """
    tokens = _tokenize_lean_or_fail(ob_text, ob_label)
    n = len(tokens)
    def_positions: list[int] = []
    for idx in _top_level_token_indices(tokens):
        tk, val = tokens[idx]
        if tk != "Ident":
            continue
        nxt = tokens[idx + 1] if idx + 1 < n else None
        names_default = (
            nxt is not None and nxt[0] == "Ident" and _is_default_callees_name(str(nxt[1]))
        )
        if val in _OB_DEFAULT_CALLEES_SHADOW_KWS and names_default:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`defaultCallees` declared via `{val}` instead of `def` in {ob_label}",
            )
        if val in _OB_DECL_MODIFIER_KWS:
            j = idx + 1
            while j < n and tokens[j][0] == "Ident" and tokens[j][1] in _OB_DECL_MODIFIER_KWS:
                j += 1
            if (
                j + 1 < n
                and tokens[j][0] == "Ident"
                and (tokens[j][1] == "def" or tokens[j][1] in _OB_DEFAULT_CALLEES_SHADOW_KWS)
                and tokens[j + 1][0] == "Ident"
                and _is_default_callees_name(str(tokens[j + 1][1]))
            ):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`{val}` modifier on `defaultCallees` in {ob_label}",
                )
        if val == "def" and names_default:
            if nxt[1] != "defaultCallees":
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"qualified `def {nxt[1]}` shadows `defaultCallees` in {ob_label}",
                )
            def_positions.append(idx)
    if not def_positions:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing `def defaultCallees : List CapturedMir :=` table in {ob_label}",
        )
    if len(def_positions) > 1:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"multiple `def defaultCallees` tables in {ob_label}",
        )
    pos = def_positions[0]
    header_ok = (
        pos + 6 < n
        and tokens[pos + 2][0] == "Colon"
        and tokens[pos + 3][0] == "Ident"
        and (tokens[pos + 3][1] == "List" or str(tokens[pos + 3][1]).endswith(".List"))
        and tokens[pos + 4][0] == "Ident"
        and _is_valid_captured_mir_type(str(tokens[pos + 4][1]))
        and tokens[pos + 5][0] == "ColonEq"
    )
    if not header_ok:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"malformed `def defaultCallees` header in {ob_label} (expected `def defaultCallees : List CapturedMir :=`)",
        )

    def ensure_no_trailing(after_idx: int) -> None:
        if after_idx < n and not _fc_is_lean_command_start(tokens[after_idx]):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unexpected trailing token {tokens[after_idx]!r} after `defaultCallees` table in {ob_label}",
            )

    val_idx = pos + 6
    if tokens[val_idx] in (("Ident", ".nil"), ("Ident", "List.nil")):
        ensure_no_trailing(val_idx + 1)
        return []
    if (
        val_idx + 1 < n
        and tokens[val_idx][0] == "Dot"
        and tokens[val_idx + 1] == ("Ident", "nil")
    ):
        ensure_no_trailing(val_idx + 2)
        return []
    if tokens[val_idx][0] != "LBracket":
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"unrecognized `defaultCallees` table in {ob_label}",
        )
    if val_idx + 1 < n and tokens[val_idx + 1][0] == "RBracket":
        ensure_no_trailing(val_idx + 2)
        return []
    out: list[str] = []
    cur = val_idx + 1
    while True:
        if cur >= n or tokens[cur][0] != "Ident":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unrecognized `defaultCallees` entry {tokens[cur] if cur < n else None!r} in {ob_label}",
            )
        entry = str(tokens[cur][1])
        suffix = (
            entry[len("Mir.") : -len(".body")]
            if entry.startswith("Mir.") and entry.endswith(".body")
            else ""
        )
        if not suffix or not all(c.isalnum() or c in "_." for c in suffix):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unrecognized `defaultCallees` entry `{entry}` in {ob_label}",
            )
        out.append(suffix)
        cur += 1
        if cur < n and tokens[cur][0] == "Comma":
            cur += 1
            continue
        if cur < n and tokens[cur][0] == "RBracket":
            ensure_no_trailing(cur + 1)
            return out
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"unterminated or malformed `defaultCallees` list in {ob_label}",
        )


def _scan_lean_module_imports(text: str, label: str) -> list[str]:
    tokens = _tokenize_lean_or_fail(text, label)
    out: list[str] = []
    for idx in _top_level_token_indices(tokens):
        if tokens[idx] == ("Ident", "import"):
            if idx + 1 >= len(tokens) or tokens[idx + 1][0] != "Ident":
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"malformed `import` command in {label}"
                )
            mod = str(tokens[idx + 1][1])
            if mod not in out:
                out.append(mod)
    return out


_DECL_COMMAND_KWS: frozenset[str] = frozenset((
    "def",
    "abbrev",
    "theorem",
    "lemma",
    "instance",
    "opaque",
    "axiom",
    "structure",
    "inductive",
    "class",
    "example",
))


def _check_module_scope_confinement(
    tokens: list[tuple[str, Any]],
    own_ns: str,
    label: str,
    *,
    allow_nested: bool = False,
    allow_sections: bool = False,
) -> None:
    """`[adv ep2-B2]` / `[adv ep2-A2]` Confine every declaration of an audited workspace
    module to its own namespace using Lean 4's exact multi-segment scope stack.

    Lean resolves an identifier inside `namespace N` by trying every prefix of `N` BEFORE
    any `open`ed namespace, and `namespace A.B` / `end A.B` push/pop multiple scope frames
    at once. Track each individual namespace/section/mutual frame so multi-segment `end`
    commands cannot pop out of `own_ns` into a parent prefix (`Proof.Demo` or `_root_`),
    require every declaration to sit at `own_ns` (or `own_ns.<child>` when `allow_nested`),
    and reject `_root_` escapes, dotted declarations when `not allow_nested`, and `export`.
    """
    stack: list[tuple[str, str | None]] = []
    n = len(tokens)
    top = _top_level_token_indices(tokens)

    def active_ns() -> str:
        return ".".join(seg for kind, seg in stack if kind == "namespace" and seg is not None)

    def ns_allowed(ns: str) -> bool:
        return ns == own_ns or (allow_nested and ns.startswith(own_ns + "."))

    pos = 0
    while pos < len(top):
        idx = top[pos]
        tk, val = tokens[idx]
        if tk != "Ident":
            pos += 1
            continue
        nxt = tokens[idx + 1] if idx + 1 < n else None
        nxt_name = (
            str(nxt[1])
            if nxt is not None and nxt[0] == "Ident" and not _fc_is_lean_command_start(nxt)
            else None
        )
        if val == "export":
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"`export` aliasing is not allowed in {label}"
            )
        if val == "namespace":
            if nxt_name is None:
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"`namespace` without a name in {label}"
                )
            segs = nxt_name.split(".")
            if "_root_" in segs or any(not s for s in segs):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`namespace {nxt_name}` escapes the module namespace via `_root_` in {label}",
                )
            had_ns = any(kind == "namespace" for kind, _ in stack)
            if had_ns and not allow_nested:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"nested `namespace {nxt_name}` is not allowed in {label}",
                )
            for seg in segs:
                stack.append(("namespace", seg))
            cur = active_ns()
            if not ns_allowed(cur):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`namespace {nxt_name}` in {label} escapes its own namespace `{own_ns}`",
                )
            pos += 2 if pos + 1 < len(top) and top[pos + 1] == idx + 1 else 1
            continue
        if val == "section":
            if not allow_sections:
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"unexpected `section` command in {label}"
                )
            if nxt_name is not None:
                segs = nxt_name.split(".")
                if "_root_" in segs or any(not s for s in segs):
                    raise Failure(
                        1, FAULT_COVERAGE_PHASE, f"invalid `section {nxt_name}` in {label}"
                    )
                for seg in segs:
                    stack.append(("section", seg))
                pos += 2 if pos + 1 < len(top) and top[pos + 1] == idx + 1 else 1
            else:
                stack.append(("section", None))
                pos += 1
            continue
        if val == "mutual":
            if not allow_sections:
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"disallowed top-level `mutual` command in {label}"
                )
            stack.append(("mutual", None))
            pos += 1
            continue
        if val == "end":
            if nxt_name is None:
                if not stack or stack[-1][0] not in ("section", "mutual") or stack[-1][1] is not None:
                    raise Failure(
                        1, FAULT_COVERAGE_PHASE, f"unmatched or unnamed `end` in {label}"
                    )
                stack.pop()
                pos += 1
            else:
                for seg in reversed(nxt_name.split(".")):
                    if not stack or stack[-1][0] not in ("namespace", "section") or stack[-1][1] != seg:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"mismatched `end {nxt_name}` in {label} (expected `{own_ns}`)",
                        )
                    stack.pop()
                pos += 2 if pos + 1 < len(top) and top[pos + 1] == idx + 1 else 1
            cur = active_ns()
            if cur and not ns_allowed(cur):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`end {nxt_name or ''}` in {label} partially closes `{own_ns}` into `{cur}`",
                )
            continue
        if val in _DECL_COMMAND_KWS:
            cur = active_ns()
            if not cur or not ns_allowed(cur):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`{val}` declaration outside `namespace {own_ns}` in {label}",
                )
            if nxt_name is not None:
                if "_root_" in nxt_name.split("."):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{val} {nxt_name}` escapes the module namespace via `_root_` in {label}",
                    )
                if not allow_nested and "." in nxt_name:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"qualified `{val} {nxt_name}` shadows or escapes the module namespace in {label}",
                    )
        pos += 1
    if stack:
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"unclosed `{stack[-1][0]}` scope in {label}"
        )


def _check_mir_module_namespace_binding(mir_text: str, stem: str, label: str) -> None:
    """`[adv ep2-B2]` `Mir/<A>/<B>.lean` must declare everything inside exactly
    `namespace Mir.<A>.<B>`: otherwise a sibling `Mir/` module could define
    `Mir.<Subject>.body` (the body every `Obligations`/`Verify` claim actually binds) while
    the audit census reads the file named after the subject."""
    tokens = _tokenize_lean_or_fail(mir_text, label)
    _check_module_scope_confinement(tokens, "Mir." + stem.replace("/", "."), label)


def _check_single_namespace(
    tokens: list[tuple[str, Any]], expected_ns: str, label: str
) -> None:
    opens = 0
    closes = 0
    n = len(tokens)
    for idx in _top_level_token_indices(tokens):
        tok = tokens[idx]
        if tok in (("Ident", "namespace"), ("Ident", "end"), ("Ident", "section")):
            nxt = tokens[idx + 1] if idx + 1 < n else None
            if tok[1] == "section":
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"unexpected `section` command in {label}"
                )
            if nxt != ("Ident", expected_ns):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"unexpected `{tok[1]} {nxt[1] if nxt else ''}` in {label} (expected only `{expected_ns}`)",
                )
            if tok[1] == "namespace":
                opens += 1
            else:
                closes += 1
    if opens != 1 or closes != 1:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"{label} must contain exactly one `namespace {expected_ns} ... end {expected_ns}` block",
        )


_VERIFY_MONO_CERT_CLAIMS: dict[str, str] = {
    "VerificationResult": "claim",
    "StatefulVerificationResult": "statefulClaim",
    "TotalVerificationResult": "totalClaim",
    "StatefulEquivVerificationResult": "equivClaim",
    "ModularVerificationResult": "modularClaim",
    "UbExceptionVerificationResult": "ubExceptionClaim",
}

_VERIFY_POLY_CLAIMS: frozenset[str] = frozenset((
    "polyClaim",
    "polyStatefulClaim",
    "polyTotalClaim",
    "polyModularClaim",
    "polyUbExceptionClaim",
))

_POLY_CLAIM_TO_FOR: dict[str, tuple[str, str]] = {
    "polyClaim": ("VerificationResult", "claimFor"),
    "polyStatefulClaim": ("StatefulVerificationResult", "statefulClaimFor"),
    "polyTotalClaim": ("TotalVerificationResult", "totalClaimFor"),
    "polyModularClaim": ("ModularVerificationResult", "modularClaimFor"),
    "polyUbExceptionClaim": ("UbExceptionVerificationResult", "ubExceptionClaimFor"),
}

_OB_RECORD_CLAIMS: frozenset[str] = frozenset((
    "claim",
    "statefulClaim",
    "totalClaim",
    "equivClaim",
    "modularClaim",
    "ubExceptionClaim",
    "claimFor",
    "statefulClaimFor",
    "totalClaimFor",
    "modularClaimFor",
    "ubExceptionClaimFor",
))

_OB_CANONICAL_CLAIM_NAMES: frozenset[str] = frozenset((
    *_OB_RECORD_CLAIMS,
    *_VERIFY_POLY_CLAIMS,
))

_OB_RESERVED_HELPER_DEFS: frozenset[str] = frozenset((
    "defaultCallContract",
    "defaultSpecCallees",
    "defaultPre",
    "defaultPost",
    "defaultPreFor",
    "defaultPostFor",
    "rustRequires",
    "rustEnsures",
    "sigPre",
    "sigPost",
    "artifactIdentity",
    "polyCertificate",
    "refineSpec",
    "refineStatefulSpec",
    "refineSafeSpec",
    "refineSafeStatefulSpec",
    "refineTotalSpec",
    "refineEquivSpec",
    "refineModularSpec",
    "refineUbExceptionSpec",
))

_OB_DEFAULT_SPEC_INSTANCE_NAMES: frozenset[str] = frozenset((
    "defaultSpec",
    "defaultStatefulSpec",
    "defaultTotalSpec",
    "defaultModularSpec",
    "defaultUbExceptionSpec",
))

_OB_ALL_SPEC_INSTANCE_NAMES: frozenset[str] = _OB_DEFAULT_SPEC_INSTANCE_NAMES | frozenset((
    "rustSafeTotalSpec",
    "rustSafeTotalStatefulSpec",
    "rustEquivSpec",
    "legacySpec",
))

_CLAIM_EXPECTED_SPEC_CLASS: dict[str, str] = {
    "claim": "ItemSpec",
    "statefulClaim": "StatefulItemSpec",
    "totalClaim": "TotalItemSpec",
    "equivClaim": "StatefulEquivItemSpec",
    "modularClaim": "ModularItemSpec",
    "ubExceptionClaim": "UbExceptionItemSpec",
    "claimFor": "ItemSpec",
    "modularClaimFor": "ModularItemSpec",
    "ubExceptionClaimFor": "UbExceptionItemSpec",
    "polyClaim": "ItemSpec",
    "polyModularClaim": "ModularItemSpec",
    "polyUbExceptionClaim": "UbExceptionItemSpec",
}


def _strip_verification_result_qual(name: str) -> str:
    for prefix in ("_root_.", "Trusted.", "VerificationResult."):
        if name.startswith(prefix):
            name = name[len(prefix) :]
    return name


_VERIFY_DISALLOWED_TOP_LEVEL: frozenset[str] = frozenset((
    "axiom",
    "opaque",
    "macro",
    "macro_rules",
    "syntax",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "elab",
    "elab_rules",
    "deriving",
    "initialize",
    "builtin_initialize",
    "mutual",
    "local",
    "scoped",
    "attribute",
    "class",
    "structure",
    "inductive",
    "unsafe",
    "partial",
    "export",
    "section",
    "private",
    "protected",
    "noncomputable",
    "nonrec",
))

_OB_DISALLOWED_TOP_LEVEL: frozenset[str] = frozenset((
    "axiom",
    "opaque",
    "macro",
    "macro_rules",
    "syntax",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "elab",
    "elab_rules",
    "deriving",
    "initialize",
    "builtin_initialize",
    "mutual",
    "local",
    "scoped",
    "attribute",
    "unsafe",
    "partial",
    "export",
    "section",
))

_VERIFY_CERTIFICATE_TYPE_NAMES: frozenset[str] = frozenset((
    *_VERIFY_MONO_CERT_CLAIMS,
    "CrateVerificationResult",
))

_VERIFY_SPEC_CLASS_NAMES: frozenset[str] = frozenset((
    "ItemSpec",
    "StatefulItemSpec",
    "TotalItemSpec",
    "StatefulEquivItemSpec",
    "ModularItemSpec",
    "UbExceptionItemSpec",
))

_VERIFY_PROOF_CLASS_NAMES: frozenset[str] = frozenset((
    "ItemProof",
    "StatefulItemProof",
    "TotalItemProof",
    "StatefulEquivItemProof",
    "ModularItemProof",
    "UbExceptionItemProof",
))

_VERIFY_REFINE_SPEC_HELPERS: frozenset[str] = frozenset((
    "refineSpec",
    "refineStatefulSpec",
    "refineSafeSpec",
    "refineSafeStatefulSpec",
    "refineTotalSpec",
    "refineEquivSpec",
    "refineModularSpec",
    "refineUbExceptionSpec",
))


_META_ATTRIBUTE_NAMES: frozenset[str] = frozenset((
    "macro",
    "term_elab",
    "command_elab",
    "tactic",
    "init",
    "implemented_by",
    "extern",
    "csimp",
    "class",
))


def _is_meta_attribute_name(name: str) -> bool:
    """`[adv ep2-B3]` Attributes that change how *importing* modules are parsed or elaborated
    (`macro` / `*_elab` / `tactic` / `*_parser` / `builtin_*` expanders), run code at import
    time (`init`), or swap compiled implementations (`implemented_by` / `extern` / `csimp`)."""
    short = name.rsplit(".", 1)[-1]
    return (
        short in _META_ATTRIBUTE_NAMES
        or short.endswith(("_parser", "_elab"))
        or short.startswith("builtin_")
    )


def _verify_detect_instance_attribute(tokens: list[tuple[str, Any]]) -> str | None:
    """Port of Rust `detect_instance_attribute`: `@[... instance ...]` registers a typeclass
    instance without a top-level `instance` keyword.

    `[adv ep2-B3]`: also reject the attribute spelling of the commands every audited module
    already bans at top level (`macro`, `syntax`, `elab`, `initialize`, `class`, ...). E.g. a
    Proof module's `@[macro Lean.Parser.Term.app] def h : Lean.Macro := ...` registers a macro
    that rewrites `VerificationResult Obligations.<I>.claim` while `Verify/<I>.lean` (which
    imports it) is elaborated, so every token of the Verify module still looks canonical.
    """
    i = 0
    n = len(tokens)
    while i + 2 < n:
        if tokens[i] == ("Ident", "@") and tokens[i + 1][0] == "LBracket":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                tk, val = tokens[j]
                if tk == "LBracket":
                    depth += 1
                elif tk == "RBracket":
                    depth -= 1
                elif tk == "Ident" and (
                    val in ("instance", "default_instance") or _is_meta_attribute_name(str(val))
                ):
                    return str(val)
                j += 1
            i = j
        else:
            i += 1
    return None


_META_RUN_COMMANDS: frozenset[str] = frozenset(("run_cmd", "run_elab", "run_meta", "run_tac"))
_HASH_COMMAND_RE = re.compile(r"#[A-Za-z_][A-Za-z0-9_]*")


def _reject_meta_commands(tokens: list[tuple[str, Any]], label: str) -> None:
    """`[adv ep2-B3]` Reject elaboration-time code execution and kernel/elaborator debug
    switches anywhere in an audited module: `#eval` / `#exit` / any `#<command>`, `run_cmd` /
    `run_elab` / `run_meta` / `run_tac`, and `set_option debug.*` (e.g.
    `set_option debug.skipKernelTC true in`). `#eval` and `run_*` run arbitrary `IO` / `CoreM`
    code while the importing `Verify` module is built, and `#exit` hides the rest of a module
    from Lean while this scanner still reads it. (`#[...]` array literals lex as a bare `#`.)
    """
    for i, (tk, val) in enumerate(tokens):
        if tk != "Ident":
            continue
        v = str(val)
        if v in _META_RUN_COMMANDS or _HASH_COMMAND_RE.fullmatch(v):
            raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed meta command `{v}` in {label}")
        if (
            v == "set_option"
            and i + 1 < len(tokens)
            and tokens[i + 1][0] == "Ident"
            and str(tokens[i + 1][1]).startswith("debug.")
        ):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed `set_option {tokens[i + 1][1]}` in {label}"
            )


def _strip_enclosing_parens_tokens(
    seq: list[tuple[str, Any]]
) -> list[tuple[str, Any]]:
    while len(seq) >= 2 and seq[0][0] == "LParen" and seq[-1][0] == "RParen":
        bal = 0
        enclosed = True
        for pos, (tk, _v) in enumerate(seq):
            if tk in ("LParen", "LBrace", "LBracket"):
                bal += 1
            elif tk in ("RParen", "RBrace", "RBracket"):
                bal -= 1
            if bal <= 0 and pos + 1 < len(seq):
                enclosed = False
                break
        if enclosed and bal == 0:
            seq = seq[1:-1]
        else:
            break
    return seq


def _take_one_balanced_lean_arg(
    seq: list[tuple[str, Any]]
) -> tuple[list[tuple[str, Any]], list[tuple[str, Any]]] | None:
    if not seq:
        return None
    tk0 = seq[0][0]
    if tk0 in ("LParen", "LBrace", "LBracket"):
        bal = 0
        for idx, (tk, _v) in enumerate(seq):
            if tk in ("LParen", "LBrace", "LBracket"):
                bal += 1
            elif tk in ("RParen", "RBrace", "RBracket"):
                bal -= 1
                if bal == 0:
                    return (seq[: idx + 1], seq[idx + 1 :])
        return None
    if tk0 in ("Ident", "StrLit", "NatLit", "CharLit"):
        return (seq[:1], seq[1:])
    return None


def _take_exact_n_balanced_args(
    seq: list[tuple[str, Any]], count: int
) -> list[list[tuple[str, Any]]] | None:
    args: list[list[tuple[str, Any]]] = []
    cur = seq
    for _ in range(count):
        res = _take_one_balanced_lean_arg(cur)
        if res is None:
            return None
        arg, cur = res
        args.append(arg)
    return args if not cur else None


def _parse_env_assumed_conjuncts(
    expr: list[tuple[str, Any]], binder: str, out: list[str], label: str
) -> None:
    expr = _strip_enclosing_parens_tokens(expr)
    if not expr:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"empty clause in `envAssumed` in {label}")
    depth = 0
    for idx, (tk, val) in enumerate(expr):
        if tk in ("LParen", "LBrace", "LBracket"):
            depth += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            depth = max(0, depth - 1)
        elif tk == "Ident" and depth == 0 and val == "∧":
            _parse_env_assumed_conjuncts(expr[:idx], binder, out, label)
            _parse_env_assumed_conjuncts(expr[idx + 1 :], binder, out, label)
            return
    if expr[0] == ("Ident", "And"):
        args2 = _take_exact_n_balanced_args(expr[1:], 2)
        if args2 is None:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"malformed `And` clause in `envAssumed` in {label}"
            )
        _parse_env_assumed_conjuncts(args2[0], binder, out, label)
        _parse_env_assumed_conjuncts(args2[1], binder, out, label)
        return
    if (
        len(expr) == 2
        and expr[0][0] == "Ident"
        and expr[1] == ("Ident", binder)
    ):
        holds_ident = str(expr[0][1])
        if holds_ident == "defaultModularSpec.envAssumed" or holds_ident.endswith(
            ".defaultModularSpec.envAssumed"
        ):
            if holds_ident not in out:
                out.append(holds_ident)
            return
        if holds_ident.endswith(".holdsOn") and len(holds_ident) > len(".holdsOn"):
            stem = holds_ident[: -len(".holdsOn")]
            if stem not in out:
                out.append(stem)
            return
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"expected `<contract>.holdsOn {binder}` in `envAssumed` in {label}, found `{holds_ident} {binder}`",
        )
    if (
        len(expr) == 3
        and expr[0][0] == "Ident"
        and str(expr[0][1])
        in ("MirCallContract.holdsOn", "Trusted.VerificationResult.MirCallContract.holdsOn")
        and expr[1][0] == "Ident"
        and expr[2] == ("Ident", binder)
    ):
        c_ident = str(expr[1][1])
        if c_ident not in out:
            out.append(c_ident)
        return
    raise Failure(
        1,
        FAULT_COVERAGE_PHASE,
        f"unsupported or non-canonical `envAssumed` clause {expr!r} in {label}",
    )


def _parse_env_assumed_holds_on_stems(
    env_rhs: list[tuple[str, Any]], label: str
) -> list[str]:
    env_rhs = _strip_enclosing_parens_tokens(env_rhs)
    if len(env_rhs) == 1 and env_rhs[0][0] == "Ident":
        holds_ident = str(env_rhs[0][1])
        if holds_ident == "defaultModularSpec.envAssumed" or holds_ident.endswith(
            ".defaultModularSpec.envAssumed"
        ):
            return [holds_ident]
        if holds_ident.endswith(".holdsOn") and len(holds_ident) > len(".holdsOn"):
            return [holds_ident[: -len(".holdsOn")]]
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"expected `<contract>.holdsOn` in `envAssumed` in {label}, found `{holds_ident}`",
        )
    if (
        len(env_rhs) == 2
        and env_rhs[0][0] == "Ident"
        and str(env_rhs[0][1])
        in ("MirCallContract.holdsOn", "Trusted.VerificationResult.MirCallContract.holdsOn")
        and env_rhs[1][0] == "Ident"
    ):
        return [str(env_rhs[1][1])]
    if (
        len(env_rhs) >= 4
        and env_rhs[0][0] == "Ident"
        and env_rhs[0][1] in ("fun", "λ")
        and env_rhs[1][0] == "Ident"
        and env_rhs[2][0] == "Ident"
        and env_rhs[2][1] in ("=>", "↦")
    ):
        binder = str(env_rhs[1][1])
        body = _strip_enclosing_parens_tokens(env_rhs[3:])
        if body == [("Ident", "True")]:
            return []
        if binder == "_":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`envAssumed := fun _ => ...` may only have body `True` in {label}",
            )
        stems: list[str] = []
        _parse_env_assumed_conjuncts(body, binder, stems, label)
        return stems
    raise Failure(
        1,
        FAULT_COVERAGE_PHASE,
        f"non-canonical `envAssumed` expression {env_rhs!r} in {label}",
    )


def _check_strict_open_command(
    tokens: list[tuple[str, Any]], start_idx: int, label: str
) -> None:
    n = len(tokens)
    k = start_idx + 1
    count = 0
    while k < n and tokens[k][0] == "Ident":
        ns_name = str(tokens[k][1])
        if _fc_is_lean_command_start(tokens[k]):
            break
        if ns_name in ("renaming", "hiding", "in", "scoped"):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"`open ... {ns_name}` is not supported in {label}"
            )
        if ns_name not in _STRICT_MODULE_OPENS:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed `open {ns_name}` in {label}"
            )
        count += 1
        k += 1
    if count == 0:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"`open` without namespaces in {label}")


def _parse_record_literal_fields(
    rhs: list[tuple[str, Any]], def_name: str, label: str
) -> dict[str, list[tuple[str, Any]]]:
    if len(rhs) < 2 or rhs[0][0] != "LBrace" or rhs[-1][0] != "RBrace":
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"canonical `def {def_name}` in {label} must be a `{{ ... }}` record literal (positional constructors and trailing expressions are forbidden)",
        )
    bal = 0
    for pos, (tk, _v) in enumerate(rhs):
        if tk in ("LParen", "LBrace", "LBracket"):
            bal += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            bal -= 1
        if bal <= 0 and pos + 1 < len(rhs):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"canonical `def {def_name}` in {label} has trailing tokens after closing `}}`",
            )
    if bal != 0:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"unbalanced delimiters in `def {def_name}` of {label}",
        )
    inner = rhs[1:-1]
    fields: dict[str, list[tuple[str, Any]]] = {}
    p = 0
    m = len(inner)
    while p < m:
        if inner[p][0] != "Ident":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unexpected token {inner[p]!r} in record literal of `def {def_name}` in {label}",
            )
        fname = str(inner[p][1])
        if fname == "with":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"struct-update `with` syntax is forbidden in `def {def_name}` of {label}",
            )
        if p + 1 >= m or inner[p + 1][0] != "ColonEq":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"expected `:=` after field `{fname}` in `def {def_name}` of {label} (struct-update syntax is forbidden)",
            )
        val_start = p + 2
        q = val_start
        fdepth = 0
        while q < m:
            tk_q, val_q = inner[q]
            if fdepth == 0:
                if tk_q in ("Comma", "Semicolon"):
                    break
                if q > val_start and tk_q == "Ident" and q + 1 < m and inner[q + 1][0] == "ColonEq":
                    break
                if tk_q == "Ident" and val_q == "with":
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"struct-update `with` syntax is forbidden in `def {def_name}` of {label}",
                    )
            if tk_q in ("LParen", "LBrace", "LBracket"):
                fdepth += 1
            elif tk_q in ("RParen", "RBrace", "RBracket"):
                fdepth = max(0, fdepth - 1)
            q += 1
        if fname in fields:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"duplicate field `{fname}` in `def {def_name}` of {label}",
            )
        fields[fname] = inner[val_start:q]
        p = q + 1 if q < m and inner[q][0] in ("Comma", "Semicolon") else q
    return fields


_OB_POLY_FORALL = (
    "∀ (typeArgs : Trusted.MirAst.TypeSubst), "
    "typeArgs.length = Mir.{S}.body.typeParamCount → "
)

# `[adv ep2-B2]` Exact generated forms (`render_obligations_module` in
# `crates/cargo-anneal/src/obligations.rs`) of every canonical claim / certificate helper
# of `Obligations/<Item>.lean`, compared token-for-token (whitespace/comment-insensitive)
# with `{S}` = item suffix, `{DID}` = subject `defPath`, `{SHA}` = `Mir/<Item>.lean` SHA-256.
# Field-wise checks of only `body` / `callees` let a tampered claim keep those while
# binding `pre := fun _ => False` (a vacuous claim that `Verify` proves trivially), adding
# fields, or rewriting the instantiated `pre`/`post` of the polymorphic `*ClaimFor` claims.
_OB_CANONICAL_DEF_TEMPLATES: dict[str, tuple[str, ...]] = {
    "claim": (
        'def claim [spec : ItemSpec "{DID}"] : Claim := { body := Mir.{S}.body, pre := spec.pre, '
        "post := spec.post, callees := defaultCallees }",
    ),
    "statefulClaim": (
        'def statefulClaim [spec : StatefulItemSpec "{DID}"] : StatefulClaim := { body := Mir.{S}.body, '
        "pre := spec.pre, post := spec.post, callees := defaultCallees }",
    ),
    "totalClaim": (
        'def totalClaim [spec : TotalItemSpec "{DID}"] : TotalClaim := { body := Mir.{S}.body, '
        "pre := spec.pre, post := spec.post, callees := defaultCallees }",
    ),
    "equivClaim": (
        'def equivClaim [spec : StatefulEquivItemSpec "{DID}"] : StatefulEquivClaim := { implBody := '
        "Mir.{S}.body, specBody := spec.specBody, pre := spec.pre, post := spec.post, implCallees := "
        "defaultCallees, specCallees := defaultCallees }",
    ),
    "modularClaim": (
        'def modularClaim [spec : ModularItemSpec "{DID}"] : ModularClaim := { body := Mir.{S}.body, '
        "envAssumed := spec.envAssumed, pre := spec.pre, post := spec.post, callees := defaultCallees }",
    ),
    "ubExceptionClaim": (
        'def ubExceptionClaim [spec : UbExceptionItemSpec "{DID}"] : UbExceptionClaim := { body := '
        "Mir.{S}.body, pre := spec.pre, strictSafetyPre := spec.strictSafetyPre, post := spec.post, "
        "callees := defaultCallees }",
    ),
    "claimFor": tuple(
        f'def claimFor [{binder} : ItemSpec "{{DID}}"] (typeArgs : Trusted.MirAst.TypeSubst) : Claim := '
        "{ body := Mir.{S}.body.instantiate typeArgs "
        f"pre := fun args => And ({pre_head}) (Trusted.VerificationResult.argsMatchSignature "
        "(Mir.{S}.body.instantiate typeArgs) args (initMachineState (Mir.{S}.body.instantiate typeArgs) "
        "args).memory) "
        f"post := fun args ret => And ({post_head}) (Trusted.VerificationResult.retMatchesSignature "
        "(Mir.{S}.body.instantiate typeArgs) ret (initMachineState (Mir.{S}.body.instantiate typeArgs) "
        "args).memory) callees := defaultCallees }"
        for binder, pre_head, post_head in (
            ("spec", "spec.pre args", "spec.post args ret"),
            ("_spec", "defaultPreFor typeArgs args", "defaultPostFor typeArgs args ret"),
        )
    ),
    "statefulClaimFor": (
        "def statefulClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : StatefulClaim := "
        "{ body := Mir.{S}.body.instantiate typeArgs pre := fun args mem => sigPre typeArgs args mem "
        "post := fun args _ ret mem => sigPost typeArgs args ret mem callees := defaultCallees }",
    ),
    "totalClaimFor": (
        "def totalClaimFor (typeArgs : Trusted.MirAst.TypeSubst) : TotalClaim := "
        "{ body := Mir.{S}.body.instantiate typeArgs pre := fun args mem => And (And (defaultPreFor "
        "typeArgs args) (mem = (initMachineState (Mir.{S}.body.instantiate typeArgs) args).memory)) "
        "(Trusted.VerificationResult.argsMatchSignature (Mir.{S}.body.instantiate typeArgs) args mem) "
        "post := fun args _ ret mem => sigPost typeArgs args ret mem callees := defaultCallees }",
    ),
    "modularClaimFor": (
        'def modularClaimFor [spec : ModularItemSpec "{DID}"] (typeArgs : Trusted.MirAst.TypeSubst) : '
        "ModularClaim := { body := Mir.{S}.body.instantiate typeArgs envAssumed := spec.envAssumed "
        "pre := fun args mem => sigPre typeArgs args mem post := fun args _ ret m1 => sigPost typeArgs "
        "args ret m1 callees := defaultCallees }",
    ),
    "ubExceptionClaimFor": (
        'def ubExceptionClaimFor [spec : UbExceptionItemSpec "{DID}"] (typeArgs : '
        "Trusted.MirAst.TypeSubst) : UbExceptionClaim := { body := Mir.{S}.body.instantiate typeArgs "
        "pre := fun args mem => sigPre typeArgs args mem strictSafetyPre := spec.strictSafetyPre "
        "post := fun args _ ret m1 => sigPost typeArgs args ret m1 callees := defaultCallees }",
    ),
    "polyClaim": (
        'def polyClaim [spec : ItemSpec "{DID}"] : Prop := '
        + _OB_POLY_FORALL
        + "VerificationResult (claimFor typeArgs)",
    ),
    "polyStatefulClaim": (
        "def polyStatefulClaim : Prop := "
        + _OB_POLY_FORALL
        + "StatefulVerificationResult (statefulClaimFor typeArgs)",
    ),
    "polyTotalClaim": (
        "def polyTotalClaim : Prop := "
        + _OB_POLY_FORALL
        + "TotalVerificationResult (totalClaimFor typeArgs)",
    ),
    "polyModularClaim": (
        'def polyModularClaim [spec : ModularItemSpec "{DID}"] : Prop := '
        + _OB_POLY_FORALL
        + "ModularVerificationResult (modularClaimFor typeArgs)",
    ),
    "polyUbExceptionClaim": (
        'def polyUbExceptionClaim [spec : UbExceptionItemSpec "{DID}"] : Prop := '
        + _OB_POLY_FORALL
        + "UbExceptionVerificationResult (ubExceptionClaimFor typeArgs)",
    ),
    "artifactIdentity": (
        'def artifactIdentity : ArtifactIdentity where defPath := "{DID}" mirDialect := '
        '"V2026_06_01" mirModuleSha256 := "{SHA}"',
    ),
    "polyCertificate": (
        'def polyCertificate (P : Prop) : CrateClaim where crateName := "{DID}" mirDialect := '
        '"V2026_06_01" items := [{ identity := artifactIdentity, certificate := P }]',
    ),
    "sigPre": (
        "def sigPre (typeArgs : Trusted.MirAst.TypeSubst) (args : List Value) (mem : Memory) : Prop := "
        "And (defaultPreFor typeArgs args) (Trusted.VerificationResult.argsMatchSignature "
        "(Mir.{S}.body.instantiate typeArgs) args mem)",
    ),
    "sigPost": (
        "def sigPost (typeArgs : Trusted.MirAst.TypeSubst) (args : List Value) (ret : Value) "
        "(mem : Memory) : Prop := And (defaultPostFor typeArgs args ret) "
        "(Trusted.VerificationResult.retMatchesSignature (Mir.{S}.body.instantiate typeArgs) ret mem)",
    ),
    "refineSpec": (
        'def refineSpec (extraPre : List Value → Prop) (extraPost : List Value → Value → Prop) : '
        'ItemSpec "{DID}" where pre args := And (rustRequires args) (extraPre args) '
        "post args ret := And (rustEnsures args ret) (extraPost args ret)",
    ),
    "refineStatefulSpec": (
        "def refineStatefulSpec (extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'StatefulItemSpec "{DID}" where pre args m := And (rustRequires args) (extraPre args m) '
        "post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
    "refineSafeSpec": (
        "def refineSafeSpec (safetyDomain : List Value → Prop) (extraPre : List Value → Prop) "
        '(extraPost : List Value → Value → Prop) : ItemSpec "{DID}" where '
        "pre args := safetyDomain args post args ret := And (rustRequires args) (extraPre args) → "
        "And (rustEnsures args ret) (extraPost args ret)",
    ),
    "refineSafeStatefulSpec": (
        "def refineSafeStatefulSpec (safetyDomain : List Value → Memory → Prop) "
        "(extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'StatefulItemSpec "{DID}" where pre args m := safetyDomain args m '
        "post args m0 ret m1 := And (rustRequires args) (extraPre args m0) → "
        "And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
    "refineTotalSpec": (
        "def refineTotalSpec (extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'TotalItemSpec "{DID}" where pre args m := And (rustRequires args) (extraPre args m) '
        "post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
    "refineEquivSpec": (
        "def refineEquivSpec (specBody : CapturedMir) (extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'StatefulEquivItemSpec "{DID}" where specBody := specBody '
        "pre args m := And (rustRequires args) (extraPre args m) "
        "post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
    "refineModularSpec": (
        "def refineModularSpec (envAssumed : ExternalCallHandler → Prop) "
        "(extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'ModularItemSpec "{DID}" where envAssumed := envAssumed '
        "pre args m := And (rustRequires args) (extraPre args m) "
        "post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
    "refineUbExceptionSpec": (
        "def refineUbExceptionSpec (strictSafetyPre : List Value → Memory → Prop) "
        "(extraPre : List Value → Memory → Prop) "
        "(extraPost : List Value → Memory → Value → Memory → Prop) : "
        'UbExceptionItemSpec "{DID}" where pre args m := And (rustRequires args) (extraPre args m) '
        "strictSafetyPre := strictSafetyPre "
        "post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)",
    ),
}

_OB_SPEC_INSTANCE_TEMPLATES: dict[str, tuple[str, ...]] = {
    "defaultSpec": (
        'instance (priority := low) defaultSpec : ItemSpec "{DID}" where '
        "pre := defaultPre post := defaultPost",
        'instance (priority := low) defaultSpec : ItemSpec "{DID}" where '
        "pre := fun args => And (defaultPre args) "
        "(Trusted.VerificationResult.argsMatchCalleeParamTys Mir.{S}.body args) "
        "post := defaultPost",
    ),
    "defaultStatefulSpec": (
        'instance (priority := low) defaultStatefulSpec : StatefulItemSpec "{DID}" where '
        "pre := fun args mem => sigPre List.nil args mem "
        "post := fun args _ ret mem => sigPost List.nil args ret mem",
    ),
    "defaultTotalSpec": (
        'instance (priority := low) defaultTotalSpec : TotalItemSpec "{DID}" where '
        "pre := fun args mem => And (And (defaultPre args) "
        "(mem = (initMachineState Mir.{S}.body args).memory)) "
        "(Trusted.VerificationResult.argsMatchSignature (Mir.{S}.body.instantiate List.nil) args mem) "
        "post := fun args _ ret _ => defaultPost args ret",
    ),
    "defaultUbExceptionSpec": (
        'instance (priority := low) defaultUbExceptionSpec : UbExceptionItemSpec "{DID}" where '
        "pre := fun args mem => sigPre List.nil args mem "
        "strictSafetyPre := fun _ _ => False "
        "post := fun args _ ret mem => sigPost List.nil args ret mem",
    ),
    "rustSafeTotalSpec": (
        'instance rustSafeTotalSpec : ItemSpec "{DID}" := refineSafeSpec '
        "(fun args => Trusted.Sequence.length args = Mir.{S}.body.argCount) "
        "(fun _ => True) (fun _ _ => True)",
        'instance (priority := low) rustSafeTotalSpec : ItemSpec "{DID}" := refineSafeSpec '
        "(fun args => Trusted.Sequence.length args = Mir.{S}.body.argCount) "
        "(fun _ => True) (fun _ _ => True)",
    ),
    "rustSafeTotalStatefulSpec": (
        'instance rustSafeTotalStatefulSpec : StatefulItemSpec "{DID}" := refineSafeStatefulSpec '
        "(fun args _ => Trusted.Sequence.length args = Mir.{S}.body.argCount) "
        "(fun _ _ => True) (fun _ _ _ _ => True)",
        'instance (priority := low) rustSafeTotalStatefulSpec : StatefulItemSpec "{DID}" := refineSafeStatefulSpec '
        "(fun args _ => Trusted.Sequence.length args = Mir.{S}.body.argCount) "
        "(fun _ _ => True) (fun _ _ _ _ => True)",
    ),
    "legacySpec": (
        'instance legacySpec : ItemSpec "{DID}" where '
        "pre := Specs.{S}.pre post := Specs.{S}.post",
        'instance (priority := low) legacySpec : ItemSpec "{DID}" where '
        "pre := Specs.{S}.pre post := Specs.{S}.post",
    ),
}

_OB_TEMPLATE_DID = "__ANNEAL_TEMPLATE_DEF_PATH__"
_OB_TEMPLATE_SHA = "__ANNEAL_TEMPLATE_MIR_SHA256__"


def _matches_obligation_template(
    templates: tuple[str, ...],
    cmd_tokens: list[tuple[str, Any]],
    suffix: str,
    expected_def_path: str | None,
    expected_mir_sha256: str | None,
) -> bool:
    for template in templates:
        text = (
            template.replace("{S}", suffix)
            .replace("{DID}", _OB_TEMPLATE_DID)
            .replace("{SHA}", _OB_TEMPLATE_SHA)
        )
        expected = tokenize_lean_source(text)
        if len(expected) != len(cmd_tokens):
            continue
        ok = True
        for exp_tok, act_tok in zip(expected, cmd_tokens):
            if exp_tok == ("StrLit", _OB_TEMPLATE_DID):
                ok = act_tok[0] == "StrLit" and (
                    expected_def_path is None or act_tok[1] == expected_def_path
                )
            elif exp_tok == ("StrLit", _OB_TEMPLATE_SHA):
                ok = (
                    act_tok[0] == "StrLit"
                    and re.fullmatch(r"[0-9a-f]{64}", str(act_tok[1])) is not None
                    and (expected_mir_sha256 is None or act_tok[1] == expected_mir_sha256)
                )
            else:
                ok = exp_tok == act_tok
            if not ok:
                break
        if ok:
            return True
    return False


def _check_canonical_obligation_def(
    name: str,
    cmd_tokens: list[tuple[str, Any]],
    suffix: str,
    expected_def_path: str | None,
    expected_mir_sha256: str | None,
    label: str,
) -> None:
    """`[adv ep2-B2]` / `[adv ep2-A2]` Require `def <name>` to equal one of its generated templates."""
    if _matches_obligation_template(
        _OB_CANONICAL_DEF_TEMPLATES[name],
        cmd_tokens,
        suffix,
        expected_def_path,
        expected_mir_sha256,
    ):
        return
    raise Failure(
        1,
        FAULT_COVERAGE_PHASE,
        f"canonical `def {name}` in {label} differs from its generated form (claims must bind exactly "
        f"`Mir.{suffix}.body`, the spec's `pre`/`post`, and `defaultCallees`)",
    )


def _check_canonical_obligation_instance(
    name: str,
    cmd_tokens: list[tuple[str, Any]],
    suffix: str,
    expected_def_path: str | None,
    label: str,
) -> None:
    """`[adv ep2-A2]` Require `instance <name>` in `Obligations` to equal one of its generated templates."""
    if _matches_obligation_template(
        _OB_SPEC_INSTANCE_TEMPLATES[name],
        cmd_tokens,
        suffix,
        expected_def_path,
        None,
    ):
        return
    raise Failure(
        1,
        FAULT_COVERAGE_PHASE,
        f"canonical `instance {name}` in {label} differs from its generated form",
    )


def _validate_companion_predicate_clause(
    clause: list[tuple[str, Any]],
    *,
    is_post: bool,
    is_poly: bool,
    suffix: str,
    imported_mir: list[str],
    label: str,
    context: str,
) -> list[str]:
    """`[adv ep2-A2]` Validate an `And`-tree of lowered `#[spec]` / `#[external_spec]`
    companion predicate clauses (`defaultPre`, `defaultPost`, `defaultPreFor`, `defaultPostFor`),
    rejecting `False` or arbitrary predicates and returning referenced companion suffixes."""
    clause = _strip_enclosing_parens_tokens(clause)
    if not clause:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"empty `{context}` clause in {label}")
    if clause == [("Ident", "True")]:
        return []
    if clause[0] == ("Ident", "And"):
        args2 = _take_exact_n_balanced_args(clause[1:], 2)
        if args2 is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"malformed `And` clause in `{context}` of {label}",
            )
        lhs = _strip_enclosing_parens_tokens(args2[0])
        rhs = _strip_enclosing_parens_tokens(args2[1])
        if lhs == [("Ident", "True")] or rhs == [("Ident", "True")]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unsimplified `True` conjunct in `{context}` of {label}",
            )
        return _validate_companion_predicate_clause(
            lhs,
            is_post=is_post,
            is_poly=is_poly,
            suffix=suffix,
            imported_mir=imported_mir,
            label=label,
            context=context,
        ) + _validate_companion_predicate_clause(
            rhs,
            is_post=is_post,
            is_poly=is_poly,
            suffix=suffix,
            imported_mir=imported_mir,
            label=label,
            context=context,
        )
    if not is_post:
        len_mono = tokenize_lean_source(
            f"Trusted.Sequence.length args = Mir.{suffix}.body.argCount"
        )
        len_poly = tokenize_lean_source(
            f"Trusted.Sequence.length args = (Mir.{suffix}.body.instantiate typeArgs).argCount"
        )
        if clause == (len_poly if is_poly else len_mono):
            return []
    expected_args = (
        tokenize_lean_source("(List.append args (List.cons ret List.nil))")
        if is_post
        else [("Ident", "args")]
    )
    head = str(clause[0][1]) if clause[0][0] == "Ident" else ""
    short_head = _strip_verification_result_qual(head)
    if short_head == "MirBoolPredicateHolds":
        args_pred = _take_exact_n_balanced_args(clause[1:], 2)
        if args_pred is None or args_pred[1] != expected_args:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"malformed `MirBoolPredicateHolds` in `{context}` of {label}",
            )
        body_arg = args_pred[0]
    elif short_head == "MirBoolPredicateHoldsWithCallees":
        args_pred = _take_exact_n_balanced_args(clause[1:], 3)
        if (
            args_pred is None
            or args_pred[1] != [("Ident", "defaultSpecCallees")]
            or args_pred[2] != expected_args
        ):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"malformed `MirBoolPredicateHoldsWithCallees` in `{context}` of {label}",
            )
        body_arg = args_pred[0]
    else:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"canonical `def {context}` in {label} differs from its generated form",
        )
    body_stripped = _strip_enclosing_parens_tokens(body_arg)
    comp_suf = ""
    if not is_poly and len(body_stripped) == 1 and body_stripped[0][0] == "Ident":
        b_s = str(body_stripped[0][1])
        if b_s.startswith("Mir.") and b_s.endswith(".body"):
            comp_suf = b_s[len("Mir.") : -len(".body")]
    elif (
        is_poly
        and len(body_stripped) == 2
        and body_stripped[0][0] == "Ident"
        and body_stripped[1] == ("Ident", "typeArgs")
    ):
        b_s = str(body_stripped[0][1])
        if b_s.startswith("Mir.") and b_s.endswith(".body.instantiate"):
            comp_suf = b_s[len("Mir.") : -len(".body.instantiate")]
    if not comp_suf or comp_suf == suffix or comp_suf not in imported_mir:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`def {context}` in {label} references unimported or invalid companion `Mir.{comp_suf}.body`",
        )
    req_marker = "__anodized_fn_ensures_" if is_post else "__anodized_fn_requires_"
    if req_marker not in comp_suf:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`def {context}` in {label} references non-companion `Mir.{comp_suf}.body`",
        )
    return [comp_suf]


def _validate_default_pre_post_def(
    name: str,
    cmd_tokens: list[tuple[str, Any]],
    suffix: str,
    imported_mir: list[str],
    label: str,
) -> list[str]:
    header_map = {
        "defaultPre": "def defaultPre (args : List Value) : Prop :=",
        "defaultPost": "def defaultPost (args : List Value) (ret : Value) : Prop :=",
        "defaultPreFor": "def defaultPreFor (typeArgs : Trusted.MirAst.TypeSubst) (args : List Value) : Prop :=",
        "defaultPostFor": "def defaultPostFor (typeArgs : Trusted.MirAst.TypeSubst) (args : List Value) (ret : Value) : Prop :=",
    }
    expected_hdr = tokenize_lean_source(header_map[name])
    if len(cmd_tokens) <= len(expected_hdr) or cmd_tokens[: len(expected_hdr)] != expected_hdr:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"canonical `def {name}` in {label} differs from its generated form",
        )
    rhs = cmd_tokens[len(expected_hdr) :]
    return _validate_companion_predicate_clause(
        rhs,
        is_post=name in ("defaultPost", "defaultPostFor"),
        is_poly=name in ("defaultPreFor", "defaultPostFor"),
        suffix=suffix,
        imported_mir=imported_mir,
        label=label,
        context=name,
    )


def _validate_external_spec_extra_clause(
    arg_tokens: list[tuple[str, Any]],
    *,
    is_post: bool,
    sidecar_suf: str,
    imported_mir: list[str],
    label: str,
    def_name: str,
) -> str | None:
    """`[adv ep2-A2]` Validate `<extraPre>` / `<extraPost>` in `externalSpecCallContract`."""
    stripped = _strip_enclosing_parens_tokens(arg_tokens)
    if not is_post and stripped in (
        tokenize_lean_source("fun _ => True"),
        tokenize_lean_source("fun args => True"),
    ):
        return None
    if is_post and stripped in (
        tokenize_lean_source("fun _ _ => True"),
        tokenize_lean_source("fun args ret => True"),
    ):
        return None
    prefix = (
        tokenize_lean_source("fun args ret =>")
        if is_post
        else tokenize_lean_source("fun args =>")
    )
    if len(stripped) <= len(prefix) or stripped[: len(prefix)] != prefix:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`externalSpecCallContract` `{def_name}` in {label} has non-canonical `{'extraPost' if is_post else 'extraPre'}`",
        )
    comps = _validate_companion_predicate_clause(
        stripped[len(prefix) :],
        is_post=is_post,
        is_poly=False,
        suffix=sidecar_suf,
        imported_mir=imported_mir,
        label=label,
        context=def_name,
    )
    if len(comps) != 1:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`externalSpecCallContract` `{def_name}` in {label} must reference at most one companion predicate",
        )
    return comps[0]


def _scan_obligations_module(
    ob_text: str,
    suffix: str,
    ob_label: str,
    *,
    expected_def_path: str | None = None,
    expected_mir_sha256: str | None = None,
) -> dict[str, Any]:
    """`[adv ep2-A1]` Independently verify the claim definitions, `defaultCallees`,
    `defaultModularSpec.envAssumed`, `externalSpecCallContract` sidecar bindings,
    `defaultCallContract`, and `rustEquivSpec` of `Obligations/<Item>.lean`."""
    tokens = _tokenize_lean_or_fail(ob_text, ob_label)
    _check_single_namespace(tokens, f"Obligations.{suffix}", ob_label)
    _check_module_scope_confinement(tokens, f"Obligations.{suffix}", ob_label)
    attr = _verify_detect_instance_attribute(tokens)
    if attr is not None:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `@[{attr}]` attribute in {ob_label}")
    _reject_meta_commands(tokens, ob_label)
    default_callee_suffixes = _parse_obligations_default_callee_suffixes(ob_text, ob_label)
    imports = _scan_lean_module_imports(ob_text, ob_label)
    imported_mir: list[str] = []
    imported_obligations: list[str] = []
    has_legacy_spec_override = False
    for mod in imports:
        if mod.startswith("Mir."):
            msuf = mod[len("Mir.") :]
            if msuf and msuf not in imported_mir:
                imported_mir.append(msuf)
        elif mod.startswith("Obligations."):
            sib = mod[len("Obligations.") :]
            if sib == suffix:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} self-imports `Obligations.{suffix}`",
                )
            if sib not in imported_obligations:
                imported_obligations.append(sib)
        elif mod == f"Specs.{suffix}":
            has_legacy_spec_override = True
        elif not any(
            mod == root or mod.startswith(root + ".")
            for root in ("Init", "Std", "Trusted", "Anneal")
        ):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed `import {mod}` in {ob_label}"
            )
    if suffix not in imported_mir:
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"{ob_label} must `import Mir.{suffix}`"
        )
    for dsuf in default_callee_suffixes:
        if dsuf not in imported_mir:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} lists `Mir.{dsuf}.body` in `defaultCallees` without `import Mir.{dsuf}`",
            )

    n = len(tokens)
    top = _top_level_token_indices(tokens)
    top_set = set(top)

    def command_end(start: int) -> int:
        k = start + 1
        while k < n and not (k in top_set and _fc_is_lean_command_start(tokens[k])):
            k += 1
        return k

    def find_field_rhs_end(start: int) -> int:
        depth = 0
        k = start
        while k < n:
            tk_k = tokens[k][0]
            if depth == 0:
                if tk_k in ("Comma", "RBrace") or _fc_is_lean_command_start(tokens[k]):
                    break
                if k > start and tk_k == "Ident" and k + 1 < n and tokens[k + 1][0] == "ColonEq":
                    break
            if tk_k in ("LParen", "LBrace", "LBracket"):
                depth += 1
            elif tk_k in ("RParen", "RBrace", "RBracket"):
                depth = max(0, depth - 1)
            k += 1
        return k

    claim_defs: dict[str, list[tuple[str, Any]]] = {}
    canonical_def_cmds: dict[str, list[tuple[str, Any]]] = {}
    default_pre_post_cmds: dict[str, list[tuple[str, Any]]] = {}
    declared_spec_instances: set[str] = set()
    declared_abbrevs: set[str] = set()
    default_modular_uses_default_pre_post = False
    referenced_companion_mir_suffixes: set[str] = set()
    default_spec_callee_suffixes: list[str] = []
    companion_bindings: list[tuple[str, str, str | None, str]] = []
    claim_sigs: dict[str, list[tuple[str, Any]]] = {}
    helper_cmds: dict[str, list[tuple[str, Any]]] = {}
    linked_ext_positions: set[int] = set()
    external_spec_contracts: list[dict[str, str]] = []
    default_ext_alias: str | None = None
    default_modular_spec_count = 0
    raw_holds_on_stems: list[str] = []
    rust_equiv_spec_body_suffix: str | None = None
    default_call_contract_def_path: str | None = None

    for idx in top:
        tk, val = tokens[idx]
        if tk != "Ident":
            continue
        if val in _OB_DISALLOWED_TOP_LEVEL:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed top-level `{val}` command in {ob_label}"
            )
        if val == "open":
            _check_strict_open_command(tokens, idx, ob_label)
            continue
        if val in _OB_DECL_MODIFIER_KWS:
            j = idx + 1
            while j < n and tokens[j][0] == "Ident" and tokens[j][1] in _OB_DECL_MODIFIER_KWS:
                j += 1
            if j + 1 < n and tokens[j][0] == "Ident" and tokens[j + 1][0] == "Ident":
                next_name = str(tokens[j + 1][1])
                if (
                    next_name in _OB_CANONICAL_CLAIM_NAMES
                    or next_name in _OB_RESERVED_HELPER_DEFS
                    or next_name in _OB_ALL_SPEC_INSTANCE_NAMES
                    or next_name == "externalSpecCallContract"
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{val}` modifier on canonical `{next_name}` in {ob_label}",
                    )
        if val in ("abbrev", "theorem", "lemma", "instance", "structure", "inductive", "class"):
            if idx + 1 < n and tokens[idx + 1][0] == "Ident":
                nm = str(tokens[idx + 1][1])
                if (
                    nm in _OB_CANONICAL_CLAIM_NAMES
                    or (nm in _OB_RESERVED_HELPER_DEFS and not (val == "abbrev" and nm in ("rustRequires", "rustEnsures")))
                    or nm == "externalSpecCallContract"
                    or (val != "instance" and nm in _OB_ALL_SPEC_INSTANCE_NAMES)
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"canonical `{nm}` shadowed as `{val}` in {ob_label}",
                    )
        if val == "instance":
            cmd_slice = tokens[idx : command_end(idx)]
            header_end = len(cmd_slice)
            h_depth = 0
            for h_pos, (t_h, v_h) in enumerate(cmd_slice):
                if h_depth == 0 and (t_h == "ColonEq" or (t_h, v_h) == ("Ident", "where")):
                    header_end = h_pos
                    break
                if t_h in ("LParen", "LBrace", "LBracket"):
                    h_depth += 1
                elif t_h in ("RParen", "RBrace", "RBracket"):
                    h_depth = max(0, h_depth - 1)
            header = cmd_slice[:header_end]
            inst_name = next(
                (
                    str(v_h)
                    for t_h, v_h in header
                    if t_h == "Ident" and str(v_h) in _OB_ALL_SPEC_INSTANCE_NAMES
                ),
                None,
            )
            if inst_name is not None:
                if inst_name in declared_spec_instances:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"duplicate `instance {inst_name}` in {ob_label}",
                    )
                declared_spec_instances.add(inst_name)
                if inst_name in _OB_DEFAULT_SPEC_INSTANCE_NAMES:
                    prio_low = [
                        ("LParen", "("),
                        ("Ident", "priority"),
                        ("ColonEq", ":="),
                        ("Ident", "low"),
                        ("RParen", ")"),
                    ]
                    if not any(
                        header[p : p + 5] == prio_low for p in range(max(0, len(header) - 4))
                    ):
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`instance {inst_name}` in {ob_label} must carry `(priority := low)`",
                        )
                if inst_name in _OB_SPEC_INSTANCE_TEMPLATES:
                    _check_canonical_obligation_instance(
                        inst_name, cmd_slice, suffix, expected_def_path, ob_label
                    )
            if inst_name == "legacySpec":
                has_legacy_spec_override = True
            spec_cls_opt: tuple[str, str | None] | None = None
            for h_pos, (t_h, v_h) in enumerate(header):
                if t_h == "Ident":
                    short_cls = _strip_verification_result_qual(str(v_h))
                    if short_cls in _VERIFY_SPEC_CLASS_NAMES:
                        did_opt = (
                            str(header[h_pos + 1][1])
                            if h_pos + 1 < len(header) and header[h_pos + 1][0] == "StrLit"
                            else None
                        )
                        spec_cls_opt = (short_cls, did_opt)
                        break
            if spec_cls_opt is not None:
                cls_name, did_opt = spec_cls_opt
                if inst_name is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"unexpected `{cls_name}` instance in {ob_label}",
                    )
                if did_opt is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{cls_name}` instance in {ob_label} omits explicit `\"<defId>\"` target",
                    )
                if expected_def_path is not None and did_opt != expected_def_path:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{cls_name}` instance in {ob_label} binds `{did_opt}` instead of `{expected_def_path}`",
                    )
            is_default_modular = inst_name == "defaultModularSpec" or (
                spec_cls_opt is not None and spec_cls_opt[0] == "ModularItemSpec"
            )
            if is_default_modular:
                default_modular_spec_count += 1
                if default_modular_spec_count > 1:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"multiple `defaultModularSpec` instances in {ob_label}",
                    )
                if header_end >= len(cmd_slice) or cmd_slice[header_end] != ("Ident", "where"):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`defaultModularSpec` in {ob_label} must be declared with `where envAssumed := ...`",
                    )
                body_tokens = cmd_slice[header_end + 1 :]
                if any((t_b, v_b) == ("Ident", "where") for t_b, v_b in body_tokens):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"nested `where` clause is forbidden inside `defaultModularSpec` in {ob_label}",
                    )
                mod_fields: dict[str, list[tuple[str, Any]]] = {}
                b_idx = 0
                while b_idx < len(body_tokens):
                    t_b, v_b = body_tokens[b_idx]
                    if t_b != "Ident" or v_b not in ("envAssumed", "pre", "post"):
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"unexpected token {body_tokens[b_idx]!r} in `defaultModularSpec` of {ob_label}",
                        )
                    fname_m = str(v_b)
                    if fname_m in mod_fields:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"duplicate `{fname_m}` field in `defaultModularSpec` of {ob_label}",
                        )
                    if b_idx + 1 >= len(body_tokens) or body_tokens[b_idx + 1][0] != "ColonEq":
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`defaultModularSpec.{fname_m}` in {ob_label} must use `{fname_m} := ...` without binders",
                        )
                    rhs_s = b_idx + 2
                    scan_k = rhs_s
                    scan_d = 0
                    while scan_k < len(body_tokens):
                        tk_s, val_s = body_tokens[scan_k]
                        if (
                            scan_d == 0
                            and scan_k > rhs_s
                            and tk_s == "Ident"
                            and val_s in ("pre", "post", "envAssumed")
                        ):
                            break
                        if tk_s in ("LParen", "LBrace", "LBracket"):
                            scan_d += 1
                        elif tk_s in ("RParen", "RBrace", "RBracket"):
                            scan_d = max(0, scan_d - 1)
                        scan_k += 1
                    mod_fields[fname_m] = body_tokens[rhs_s:scan_k]
                    b_idx = scan_k
                if set(mod_fields) != {"envAssumed", "pre", "post"}:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`defaultModularSpec` in {ob_label} must bind exactly `envAssumed`, `pre`, and `post`",
                    )
                for st in _parse_env_assumed_holds_on_stems(
                    mod_fields["envAssumed"], ob_label
                ):
                    if st not in raw_holds_on_stems:
                        raw_holds_on_stems.append(st)
                canon_mod_pre = tokenize_lean_source(
                    f"fun args mem => And (And (defaultPre args) "
                    f"(mem = (initMachineState Mir.{suffix}.body args).memory)) "
                    f"(Trusted.VerificationResult.argsMatchSignature (Mir.{suffix}.body.instantiate List.nil) args mem)"
                )
                canon_mod_post = tokenize_lean_source(
                    "fun args _ ret _ => defaultPost args ret"
                )
                if (
                    mod_fields["pre"] == canon_mod_pre
                    and mod_fields["post"] == canon_mod_post
                ):
                    default_modular_uses_default_pre_post = True
                elif not (
                    mod_fields["pre"] == [("Ident", "spec.pre")]
                    and mod_fields["post"] == [("Ident", "spec.post")]
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`defaultModularSpec` `pre`/`post` in {ob_label} differs from its generated form",
                    )
            if spec_cls_opt is not None and spec_cls_opt[0] == "StatefulEquivItemSpec":
                if rust_equiv_spec_body_suffix is not None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"multiple `StatefulEquivItemSpec` instances in {ob_label}",
                    )
                if header_end >= len(cmd_slice) or cmd_slice[header_end][0] != "ColonEq":
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`StatefulEquivItemSpec` instance in {ob_label} must use `:= refineEquivSpec Mir.<Ref>.body ...`",
                    )
                rhs_eq = _strip_enclosing_parens_tokens(cmd_slice[header_end + 1 :])
                args3 = (
                    _take_exact_n_balanced_args(rhs_eq[1:], 3)
                    if rhs_eq
                    and rhs_eq[0][0] == "Ident"
                    and (
                        rhs_eq[0][1] == "refineEquivSpec"
                        or str(rhs_eq[0][1]).endswith(".refineEquivSpec")
                    )
                    else None
                )
                if args3 is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`StatefulEquivItemSpec` instance in {ob_label} must use `refineEquivSpec Mir.<Ref>.body <pre> <post>` with exact 3 arguments",
                    )
                mir_arg = _strip_enclosing_parens_tokens(args3[0])
                pre_arg = _strip_enclosing_parens_tokens(args3[1])
                post_arg = _strip_enclosing_parens_tokens(args3[2])
                if pre_arg != tokenize_lean_source(
                    "fun _ _ => True"
                ) or post_arg != tokenize_lean_source("fun _ _ _ _ => True"):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`rustEquivSpec` in {ob_label} differs from its generated `(fun _ _ => True) (fun _ _ _ _ => True)` form",
                    )
                if (
                    len(mir_arg) == 1
                    and mir_arg[0][0] == "Ident"
                    and str(mir_arg[0][1]).startswith("Mir.")
                    and str(mir_arg[0][1]).endswith(".body")
                ):
                    ref_suf = str(mir_arg[0][1])[len("Mir.") : -len(".body")]
                    if not ref_suf:
                        raise Failure(
                            1, FAULT_COVERAGE_PHASE, f"empty `Mir.<Ref>.body` in {ob_label}"
                        )
                    rust_equiv_spec_body_suffix = ref_suf
                else:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`StatefulEquivItemSpec` in {ob_label} binds non-`Mir.<Ref>.body` reference {mir_arg!r}",
                    )

        if val == "abbrev" and idx + 1 < n and tokens[idx + 1][0] == "Ident":
            ab_name = str(tokens[idx + 1][1])
            cmd_e = command_end(idx)
            if ab_name in declared_abbrevs:
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"duplicate `abbrev {ab_name}` in {ob_label}"
                )
            declared_abbrevs.add(ab_name)
            if ab_name == "defaultExternalCallContract":
                if not (
                    idx + 5 < n
                    and cmd_e == idx + 6
                    and tokens[idx + 2][0] == "Colon"
                    and tokens[idx + 3][0] == "Ident"
                    and _strip_verification_result_qual(str(tokens[idx + 3][1])) == "MirCallContract"
                    and tokens[idx + 4][0] == "ColonEq"
                    and tokens[idx + 5][0] == "Ident"
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`abbrev defaultExternalCallContract` in {ob_label} has non-canonical form or trailing tokens",
                    )
                default_ext_alias = str(tokens[idx + 5][1])
            elif ab_name == "rustRequires":
                if tokens[idx:cmd_e] != tokenize_lean_source(
                    "abbrev rustRequires : List Value → Prop := defaultPre"
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"canonical `abbrev rustRequires` in {ob_label} differs from `abbrev rustRequires : List Value → Prop := defaultPre`",
                    )
            elif ab_name == "rustEnsures":
                if tokens[idx:cmd_e] != tokenize_lean_source(
                    "abbrev rustEnsures : List Value → Value → Prop := defaultPost"
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"canonical `abbrev rustEnsures` in {ob_label} differs from `abbrev rustEnsures : List Value → Value → Prop := defaultPost`",
                    )

        if val == "def":
            if idx + 1 >= n or tokens[idx + 1][0] != "Ident":
                raise Failure(1, FAULT_COVERAGE_PHASE, f"malformed `def` in {ob_label}")
            def_name = str(tokens[idx + 1][1])
            if def_name in (
                "defaultModularSpec",
                "externalSpecCallContract",
                "rustRequires",
                "rustEnsures",
                *_OB_ALL_SPEC_INSTANCE_NAMES,
            ):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"reserved identifier `{def_name}` shadowed as `def` in {ob_label}",
                )
            cmd_e = command_end(idx)
            if def_name in ("defaultPre", "defaultPost", "defaultPreFor", "defaultPostFor"):
                if def_name in default_pre_post_cmds:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"duplicate `def {def_name}` in {ob_label}",
                    )
                default_pre_post_cmds[def_name] = tokens[idx:cmd_e]
                for c_suf in _validate_default_pre_post_def(
                    def_name, tokens[idx:cmd_e], suffix, imported_mir, ob_label
                ):
                    referenced_companion_mir_suffixes.add(c_suf)
                    # `[adv ep2-B3]`: `None` = the owning subject's own `defPath`.
                    companion_bindings.append((
                        c_suf,
                        "requires" if def_name in ("defaultPre", "defaultPreFor") else "ensures",
                        None,
                        f"def {def_name}",
                    ))
            if def_name == "defaultSpecCallees":
                # Validate `def defaultSpecCallees : List CapturedMir := [Mir.<c>.body, ...]`
                if (
                    idx + 5 >= cmd_e
                    or tokens[idx + 2][0] != "Colon"
                    or tokens[idx + 3] != ("Ident", "List")
                    or tokens[idx + 4] != ("Ident", "CapturedMir")
                    or tokens[idx + 5][0] != "ColonEq"
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"malformed `def defaultSpecCallees` header in {ob_label}",
                    )
                sc_rhs = tokens[idx + 6 : cmd_e]
                if len(sc_rhs) < 2 or sc_rhs[0][0] != "LBracket" or sc_rhs[-1][0] != "RBracket":
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"unrecognized `defaultSpecCallees` table in {ob_label}",
                    )
                sc_inner = sc_rhs[1:-1]
                sc_pos = 0
                while sc_pos < len(sc_inner):
                    if sc_inner[sc_pos][0] != "Ident":
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"unrecognized `defaultSpecCallees` entry in {ob_label}",
                        )
                    sc_entry = str(sc_inner[sc_pos][1])
                    sc_suf = (
                        sc_entry[len("Mir.") : -len(".body")]
                        if sc_entry.startswith("Mir.") and sc_entry.endswith(".body")
                        else ""
                    )
                    if not sc_suf or sc_suf not in imported_mir:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{ob_label} lists `Mir.{sc_suf}.body` in `defaultSpecCallees` without `import Mir.{sc_suf}`",
                        )
                    if sc_suf not in default_spec_callee_suffixes:
                        default_spec_callee_suffixes.append(sc_suf)
                    sc_pos += 1
                    if sc_pos < len(sc_inner):
                        if sc_inner[sc_pos][0] != "Comma":
                            raise Failure(
                                1,
                                FAULT_COVERAGE_PHASE,
                                f"malformed `defaultSpecCallees` list in {ob_label}",
                            )
                        sc_pos += 1
            if def_name in _OB_CANONICAL_DEF_TEMPLATES:
                if def_name in canonical_def_cmds:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"duplicate `def {def_name}` in {ob_label}",
                    )
                canonical_def_cmds[def_name] = tokens[idx:cmd_e]
            if def_name in _OB_RESERVED_HELPER_DEFS:
                if def_name in helper_cmds:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"duplicate `def {def_name}` in {ob_label}",
                    )
                helper_cmds[def_name] = tokens[idx + 2 : cmd_e]
            if def_name in _OB_CANONICAL_CLAIM_NAMES or any(
                def_name.endswith(f".{c}") for c in _OB_CANONICAL_CLAIM_NAMES
            ):
                if "." in def_name:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"qualified `def {def_name}` is not allowed in {ob_label}",
                    )
                if def_name in claim_defs:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"duplicate `def {def_name}` in {ob_label}",
                    )
                j = idx + 2
                while j < cmd_e and not (j in top_set and tokens[j][0] == "ColonEq"):
                    j += 1
                if j >= cmd_e or tokens[j][0] != "ColonEq":
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`def {def_name}` has no `:=` body in {ob_label}",
                    )
                claim_sigs[def_name] = tokens[idx + 2 : j]
                claim_defs[def_name] = tokens[j + 1 : cmd_e]

            # Check `def defaultCallContract : MirCallContract where ...`
            if def_name == "defaultCallContract":
                if (
                    idx + 4 >= cmd_e
                    or tokens[idx + 2][0] != "Colon"
                    or tokens[idx + 3][0] != "Ident"
                    or _strip_verification_result_qual(str(tokens[idx + 3][1])) != "MirCallContract"
                    or tokens[idx + 4] != ("Ident", "where")
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`def defaultCallContract` in {ob_label} must use canonical `: MirCallContract where pre req := And (req.defPath = ...) ...`",
                    )
                sl = tokens[idx + 5 : cmd_e]
                if any((t_s, v_s) == ("Ident", "where") for t_s, v_s in sl):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"nested `where` in `def defaultCallContract` in {ob_label}",
                    )
                post_ok = (
                    any(
                        sl[p : p + 4]
                        == [
                            ("Ident", "post"),
                            ("Ident", "req"),
                            ("Ident", "ans"),
                            ("ColonEq", ":="),
                        ]
                        for p in range(max(0, len(sl) - 3))
                    )
                    and any(
                        sl[p : p + 3]
                        == [
                            ("Ident", "defaultPost"),
                            ("Ident", "req.args"),
                            ("Ident", "retVal"),
                        ]
                        for p in range(max(0, len(sl) - 2))
                    )
                    and any(
                        t_s == "Ident"
                        and _strip_verification_result_qual(str(v_s)) == "retMatchesCalleeReturnTy"
                        for t_s, v_s in sl
                    )
                )
                pre_ok = (
                    post_ok
                    and len(sl) >= 13
                    and sl[0] == ("Ident", "pre")
                    and sl[1] == ("Ident", "req")
                    and sl[2][0] == "ColonEq"
                    and sl[3] == ("Ident", "And")
                    and sl[4][0] == "LParen"
                    and sl[5] == ("Ident", "req.defPath")
                    and sl[6] == ("Ident", "=")
                    and sl[7][0] == "StrLit"
                    and sl[8][0] == "RParen"
                    and sl[9][0] == "LParen"
                    and sl[10] == ("Ident", "defaultPre")
                    and sl[11] == ("Ident", "req.args")
                    and sl[12][0] == "RParen"
                )
                if not pre_ok:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"malformed `def defaultCallContract` in {ob_label}",
                    )
                did_cc = str(sl[7][1])
                if expected_def_path is not None and did_cc != expected_def_path:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`def defaultCallContract` in {ob_label} binds `{did_cc}` instead of `{expected_def_path}`",
                    )
                default_call_contract_def_path = did_cc

            # Check `def <ident> : MirCallContract := externalSpecCallContract "<target>" Mir.<sidecar>.body <pre> <post>`
            if (
                idx + 7 < cmd_e
                and tokens[idx + 2][0] == "Colon"
                and tokens[idx + 3][0] == "Ident"
                and _strip_verification_result_qual(str(tokens[idx + 3][1])) == "MirCallContract"
                and tokens[idx + 4][0] == "ColonEq"
                and tokens[idx + 5] == ("Ident", "externalSpecCallContract")
                and tokens[idx + 6][0] == "StrLit"
                and tokens[idx + 7][0] == "Ident"
            ):
                target_dp = str(tokens[idx + 6][1])
                sidecar_expr = str(tokens[idx + 7][1])
                sidecar_suf = (
                    sidecar_expr[len("Mir.") : -len(".body")]
                    if sidecar_expr.startswith("Mir.") and sidecar_expr.endswith(".body")
                    else ""
                )
                args4 = _take_exact_n_balanced_args(tokens[idx + 6 : cmd_e], 4)
                if sidecar_suf and args4 is not None:
                    if sidecar_suf == suffix:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{ob_label} binds `externalSpecCallContract` `{def_name}` to its own MIR body `Mir.{suffix}.body`",
                        )
                    if sidecar_suf not in imported_mir:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{ob_label} binds `externalSpecCallContract` `{def_name}` to `Mir.{sidecar_suf}.body` without `import Mir.{sidecar_suf}`",
                        )
                    ext_req = _validate_external_spec_extra_clause(
                        args4[2],
                        is_post=False,
                        sidecar_suf=sidecar_suf,
                        imported_mir=imported_mir,
                        label=ob_label,
                        def_name=def_name,
                    )
                    ext_ens = _validate_external_spec_extra_clause(
                        args4[3],
                        is_post=True,
                        sidecar_suf=sidecar_suf,
                        imported_mir=imported_mir,
                        label=ob_label,
                        def_name=def_name,
                    )
                    if ext_req is not None:
                        referenced_companion_mir_suffixes.add(ext_req)
                        companion_bindings.append(
                            (ext_req, "requires", target_dp, f"externalSpecCallContract `{def_name}`")
                        )
                    if ext_ens is not None:
                        referenced_companion_mir_suffixes.add(ext_ens)
                        companion_bindings.append(
                            (ext_ens, "ensures", target_dp, f"externalSpecCallContract `{def_name}`")
                        )
                    linked_ext_positions.add(idx + 5)
                    external_spec_contracts.append(
                        {
                            "def_ident": def_name,
                            "target_def_path": target_dp,
                            "sidecar_mir_suffix": sidecar_suf,
                        }
                    )

    # Reject any unlinked/malformed `externalSpecCallContract` token or detached `body`/`callees` assignment
    for i, (tk_i, val_i) in enumerate(tokens):
        if tk_i != "Ident":
            continue
        if (
            val_i == "externalSpecCallContract"
            or str(val_i).endswith(".externalSpecCallContract")
        ) and i not in linked_ext_positions:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} contains unlinked or malformed `externalSpecCallContract` expression",
            )
        if val_i in ("body", "implBody") and i + 1 < n and tokens[i + 1][0] == "ColonEq":
            rhs_b = tokens[i + 2 : find_field_rhs_end(i + 2)]
            if rhs_b != [("Ident", f"Mir.{suffix}.body")] and rhs_b != [
                ("Ident", f"Mir.{suffix}.body.instantiate"),
                ("Ident", "typeArgs"),
            ]:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} binds `{val_i} := {rhs_b!r}` instead of `Mir.{suffix}.body`",
                )
        if (
            val_i in ("callees", "implCallees", "specCallees")
            and i + 1 < n
            and tokens[i + 1][0] == "ColonEq"
        ):
            rhs_c = tokens[i + 2 : find_field_rhs_end(i + 2)]
            if rhs_c != [("Ident", "defaultCallees")]:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} overrides claim `{val_i} := {rhs_c!r}` instead of `defaultCallees`",
                )

    # Validate every declared canonical claim and helper
    mir_body_tok = [("Ident", f"Mir.{suffix}.body")]
    mir_inst_tok = [("Ident", f"Mir.{suffix}.body.instantiate"), ("Ident", "typeArgs")]
    default_callees_tok = [("Ident", "defaultCallees")]
    spec_env_tok = [("Ident", "spec.envAssumed")]
    spec_body_tok = [("Ident", "spec.specBody")]

    for claim_name, rhs_tokens in claim_defs.items():
        sig_tokens = claim_sigs[claim_name]
        if claim_name in _CLAIM_EXPECTED_SPEC_CLASS and sig_tokens and sig_tokens[0][0] == "LBracket":
            exp_cls = _CLAIM_EXPECTED_SPEC_CLASS[claim_name]
            binder_ok = (
                len(sig_tokens) >= 6
                and sig_tokens[0][0] == "LBracket"
                and sig_tokens[1][0] == "Ident"
                and (
                    sig_tokens[1][1] == "spec"
                    or (claim_name == "claimFor" and sig_tokens[1][1] in ("spec", "_spec"))
                )
                and sig_tokens[2][0] == "Colon"
                and sig_tokens[3][0] == "Ident"
                and _strip_verification_result_qual(str(sig_tokens[3][1])) == exp_cls
                and sig_tokens[4][0] == "StrLit"
                and (expected_def_path is None or str(sig_tokens[4][1]) == expected_def_path)
                and sig_tokens[5][0] == "RBracket"
            )
            if not binder_ok:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"canonical `def {claim_name}` in {ob_label} has non-canonical `[spec : {exp_cls} \"...\"]` binder {sig_tokens!r}",
                )
        if claim_name in ("claim", "statefulClaim", "totalClaim", "ubExceptionClaim"):
            fields = _parse_record_literal_fields(rhs_tokens, claim_name, ob_label)
            expected_f = {"body": mir_body_tok, "callees": default_callees_tok}
        elif claim_name == "modularClaim":
            fields = _parse_record_literal_fields(rhs_tokens, claim_name, ob_label)
            expected_f = {
                "body": mir_body_tok,
                "envAssumed": spec_env_tok,
                "callees": default_callees_tok,
            }
        elif claim_name == "equivClaim":
            fields = _parse_record_literal_fields(rhs_tokens, claim_name, ob_label)
            expected_f = {
                "implBody": mir_body_tok,
                "specBody": spec_body_tok,
                "implCallees": default_callees_tok,
                "specCallees": default_callees_tok,
            }
        elif claim_name in (
            "claimFor",
            "statefulClaimFor",
            "totalClaimFor",
            "ubExceptionClaimFor",
        ):
            fields = _parse_record_literal_fields(rhs_tokens, claim_name, ob_label)
            expected_f = {"body": mir_inst_tok, "callees": default_callees_tok}
        elif claim_name == "modularClaimFor":
            fields = _parse_record_literal_fields(rhs_tokens, claim_name, ob_label)
            expected_f = {
                "body": mir_inst_tok,
                "envAssumed": spec_env_tok,
                "callees": default_callees_tok,
            }
        elif claim_name in _POLY_CLAIM_TO_FOR:
            cert_short, claim_for_name = _POLY_CLAIM_TO_FOR[claim_name]
            expected_tp_count = f"Mir.{suffix}.body.typeParamCount"
            poly_ok = (
                len(rhs_tokens) == 16
                and rhs_tokens[0][0] == "Ident"
                and rhs_tokens[0][1] in ("∀", "forall")
                and rhs_tokens[1][0] == "LParen"
                and rhs_tokens[2] == ("Ident", "typeArgs")
                and rhs_tokens[3][0] == "Colon"
                and rhs_tokens[4][0] == "Ident"
                and rhs_tokens[4][1] in ("Trusted.MirAst.TypeSubst", "TypeSubst")
                and rhs_tokens[5][0] == "RParen"
                and rhs_tokens[6][0] == "Comma"
                and rhs_tokens[7] == ("Ident", "typeArgs.length")
                and rhs_tokens[8] == ("Ident", "=")
                and rhs_tokens[9] == ("Ident", expected_tp_count)
                and rhs_tokens[10][0] == "Ident"
                and rhs_tokens[10][1] in ("→", "->")
                and rhs_tokens[11][0] == "Ident"
                and _strip_verification_result_qual(str(rhs_tokens[11][1])) == cert_short
                and rhs_tokens[12][0] == "LParen"
                and rhs_tokens[13] == ("Ident", claim_for_name)
                and rhs_tokens[14] == ("Ident", "typeArgs")
                and rhs_tokens[15][0] == "RParen"
            )
            if not poly_ok:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"canonical `def {claim_name}` in {ob_label} does not wrap `({claim_for_name} typeArgs)` in `{cert_short}`",
                )
            continue
        else:
            continue
        for req_name, req_val in expected_f.items():
            if fields.get(req_name) != req_val:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"canonical `def {claim_name}` in {ob_label} binds `{req_name} := {fields.get(req_name)!r}` instead of `{req_val!r}`",
                )

    if "polyCertificate" in helper_cmds:
        pc = helper_cmds["polyCertificate"]
        pc_ok = (
            len(pc) >= 21
            and pc[0][0] == "LParen"
            and pc[1] == ("Ident", "P")
            and pc[2][0] == "Colon"
            and pc[3] == ("Ident", "Prop")
            and pc[4][0] == "RParen"
            and pc[5][0] == "Colon"
            and pc[6][0] == "Ident"
            and _strip_verification_result_qual(str(pc[6][1])) == "CrateClaim"
            and pc[-13:]
            == [
                ("Ident", "items"),
                ("ColonEq", ":="),
                ("LBracket", "["),
                ("LBrace", "{"),
                ("Ident", "identity"),
                ("ColonEq", ":="),
                ("Ident", "artifactIdentity"),
                ("Comma", ","),
                ("Ident", "certificate"),
                ("ColonEq", ":="),
                ("Ident", "P"),
                ("RBrace", "}"),
                ("RBracket", "]"),
            ]
        )
        if not pc_ok:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"canonical `def polyCertificate` in {ob_label} was altered from `items := [{{ identity := artifactIdentity, certificate := P }}]`",
            )

    for helper_name, field_name in (
        ("refineEquivSpec", "specBody"),
        ("refineModularSpec", "envAssumed"),
    ):
        if helper_name in helper_cmds:
            hcmd = helper_cmds[helper_name]
            where_idx = next(
                (i for i, t in enumerate(hcmd) if t == ("Ident", "where")), -1
            )
            body_h = hcmd[where_idx + 1 :] if where_idx >= 0 else []
            if not (
                len(body_h) >= 4
                and body_h[0] == ("Ident", field_name)
                and body_h[1][0] == "ColonEq"
                and body_h[2] == ("Ident", field_name)
                and body_h[3][0] == "Ident"
                and body_h[3][1] in ("pre", "post")
            ):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`def {helper_name}` in {ob_label} does not bind `{field_name} := {field_name}`",
                )

    for canon_name, canon_cmd in canonical_def_cmds.items():
        _check_canonical_obligation_def(
            canon_name,
            canon_cmd,
            suffix,
            expected_def_path,
            expected_mir_sha256,
            ob_label,
        )

    # Verify spec-chain completeness and imported companion coverage (`[adv ep2-A2]`)
    if (
        "defaultSpec" in declared_spec_instances
        or "defaultTotalSpec" in declared_spec_instances
        or default_modular_uses_default_pre_post
    ):
        for req_helper in ("defaultPre", "defaultPost"):
            if req_helper not in default_pre_post_cmds:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} references `{req_helper}` in default spec instance without declaring `def {req_helper}`",
                )
    if (
        "defaultStatefulSpec" in declared_spec_instances
        or "defaultUbExceptionSpec" in declared_spec_instances
        or any(
            c in claim_defs
            for c in ("statefulClaimFor", "modularClaimFor", "ubExceptionClaimFor")
        )
    ):
        for req_helper in ("sigPre", "sigPost"):
            if req_helper not in canonical_def_cmds:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} references `{req_helper}` without declaring canonical `def {req_helper}`",
                )
        for req_helper in ("defaultPreFor", "defaultPostFor"):
            if req_helper not in default_pre_post_cmds:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} references `{req_helper}` via `sigPre`/`sigPost` without declaring `def {req_helper}`",
                )
    if "totalClaimFor" in claim_defs:
        if "sigPost" not in canonical_def_cmds:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} declares `totalClaimFor` without canonical `def sigPost`",
            )
        for req_helper in ("defaultPreFor", "defaultPostFor"):
            if req_helper not in default_pre_post_cmds:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} declares `totalClaimFor` without `def {req_helper}`",
                )
    if any(r in canonical_def_cmds for r in _VERIFY_REFINE_SPEC_HELPERS):
        for req_ab in ("rustRequires", "rustEnsures"):
            if req_ab not in declared_abbrevs:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} declares `refine*Spec` helpers without `abbrev {req_ab}`",
                )
        for req_helper in ("defaultPre", "defaultPost"):
            if req_helper not in default_pre_post_cmds:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} declares `refine*Spec` helpers without `def {req_helper}`",
                )
    for m_suf in imported_mir:
        last_seg = m_suf.rsplit(".", 1)[-1]
        if last_seg.startswith(("__anodized_fn_requires_", "__anodized_fn_ensures_")):
            if m_suf not in referenced_companion_mir_suffixes:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{ob_label} imports companion `Mir.{m_suf}` without linking it in `defaultPre`/`defaultPost` or `externalSpecCallContract`",
                )

    referenced_callee_contracts: list[str] = []
    referenced_ext_idents: list[str] = []
    for stem in raw_holds_on_stems:
        if stem.startswith("Obligations.") and stem.endswith(".defaultCallContract"):
            csuf = stem[len("Obligations.") : -len(".defaultCallContract")]
            if csuf and csuf not in referenced_callee_contracts:
                referenced_callee_contracts.append(csuf)
        elif stem == "defaultExternalCallContract":
            if default_ext_alias is None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`defaultModularSpec.envAssumed` in {ob_label} references `defaultExternalCallContract.holdsOn` without an `abbrev defaultExternalCallContract` alias",
                )
            if default_ext_alias not in referenced_ext_idents:
                referenced_ext_idents.append(default_ext_alias)
        elif "." not in stem:
            if stem not in referenced_ext_idents:
                referenced_ext_idents.append(stem)
        else:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`defaultModularSpec.envAssumed` in {ob_label} references unexpected qualified contract `{stem}.holdsOn`",
            )

    for ext in external_spec_contracts:
        if ext["def_ident"] not in referenced_ext_idents:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} declares `def {ext['def_ident']}` (`externalSpecCallContract \"{ext['target_def_path']}\"`) without referencing `{ext['def_ident']}.holdsOn` in `defaultModularSpec.envAssumed`",
            )
    for sib in imported_obligations:
        if sib not in referenced_callee_contracts:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} imports `Obligations.{sib}` without referencing `Obligations.{sib}.defaultCallContract` in `defaultModularSpec.envAssumed`",
            )
    for csuf in referenced_callee_contracts:
        if csuf not in imported_obligations:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{ob_label} references `Obligations.{csuf}.defaultCallContract` without `import Obligations.{csuf}`",
            )

    return {
        "default_callee_suffixes": default_callee_suffixes,
        "default_spec_callee_suffixes": default_spec_callee_suffixes,
        "companion_bindings": companion_bindings,
        "imported_mir_suffixes": imported_mir,
        "imported_obligation_suffixes": imported_obligations,
        "referenced_callee_contracts": referenced_callee_contracts,
        "external_spec_contracts": external_spec_contracts,
        "default_external_contract_alias": default_ext_alias,
        "default_modular_spec_count": default_modular_spec_count,
        "rust_equiv_spec_body_suffix": rust_equiv_spec_body_suffix,
        "default_call_contract_def_path": default_call_contract_def_path,
        "has_legacy_spec_override": has_legacy_spec_override,
        "declared_claims": set(claim_defs),
        "declared_helpers": set(helper_cmds),
        "declared_canonical_defs": set(canonical_def_cmds),
    }


def _scan_verify_module_surface(verify_text: str, suffix: str, label: str) -> dict[str, Any]:
    """`[adv ep2-B1]` / `[adv ep2-A1]` Independently derive the certificate surface of `Verify/<Item>.lean`.

    Ports the Rust `inspect_verify_module_certificate` restrictions (import allowlist,
    mandatory `import Obligations.<Item>`, single `namespace Verify.<Item>` block,
    strict `open` allowlist, no `export` / modifiers / `axiom` / `opaque` / notation /
    macro / `attribute` / `@[instance]` / spec-class or non-`*ItemProof` `instance`
    commands) and rejects declarations shadowing a certificate type or the canonical spec
    classes.
    """
    tokens = _tokenize_lean_or_fail(verify_text, label)
    _check_single_namespace(tokens, f"Verify.{suffix}", label)
    _check_module_scope_confinement(tokens, f"Verify.{suffix}", label)
    attr = _verify_detect_instance_attribute(tokens)
    if attr is not None:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `@[{attr}]` attribute in {label}")
    _reject_meta_commands(tokens, label)
    imports = _scan_lean_module_imports(verify_text, label)
    for mod in imports:
        own = mod in (
            f"Obligations.{suffix}",
            f"Specs.{suffix}",
            f"Proof.{suffix}",
            f"Assumptions.{suffix}",
        )
        allowed = own or mod.startswith("Mir.") or any(
            mod == root or mod.startswith(root + ".")
            for root in ("Init", "Std", "Trusted", "Anneal")
        )
        if not allowed:
            raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `import {mod}` in {label}")
    if f"Obligations.{suffix}" not in imports:
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"{label} must `import Obligations.{suffix}`"
        )
    n = len(tokens)
    top = _top_level_token_indices(tokens)
    top_set = set(top)

    def command_end(start: int) -> int:
        k = start + 1
        while k < n and not (k in top_set and _fc_is_lean_command_start(tokens[k])):
            k += 1
        return k

    def short_name(ident: str) -> str:
        for prefix in ("_root_.", "Trusted.", "VerificationResult."):
            if ident.startswith(prefix):
                ident = ident[len(prefix) :]
        return ident

    verified: list[tuple[list[tuple[str, Any]], list[tuple[str, Any]]]] = []
    for idx in top:
        tk, val = tokens[idx]
        if tk != "Ident":
            continue
        nxt = tokens[idx + 1] if idx + 1 < n else None
        if nxt == ("Ident", "verified") and val != "theorem" and val in _LEAN_COMMAND_KEYWORDS:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`verified` declared via `{val}` instead of `theorem` in {label}",
            )
        if val == "open":
            _check_strict_open_command(tokens, idx, label)
            continue
        if val in _VERIFY_DISALLOWED_TOP_LEVEL:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed top-level `{val}` command in {label}"
            )
        if val in ("def", "abbrev", "lemma", "theorem", "instance", "example"):
            cmd = tokens[idx : command_end(idx)]
            if nxt is not None and nxt[0] == "Ident":
                declared = str(nxt[1])
                last = declared.rsplit(".", 1)[-1]
                if (
                    last in _VERIFY_CERTIFICATE_TYPE_NAMES
                    or last in _VERIFY_SPEC_CLASS_NAMES
                    or last in _VERIFY_PROOF_CLASS_NAMES
                    or "." in declared
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{val} {declared}` shadows or escapes the certificate namespace in {label}",
                    )
            idents = [str(v) for t, v in cmd if t == "Ident"]
            for ident in idents:
                if short_name(ident) in _VERIFY_SPEC_CLASS_NAMES:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} references specification class `{ident}` inside `{val}` (specifications live in `Specs.{suffix}`)",
                    )
                if ident.rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} invokes specification override helper `{ident}` inside `{val}`",
                    )
            if val == "instance":
                header: list[str] = []
                h_depth = 0
                for t, v in cmd:
                    if h_depth == 0 and (t == "ColonEq" or (t, v) == ("Ident", "where")):
                        break
                    if t in ("LParen", "LBrace", "LBracket"):
                        h_depth += 1
                    elif t in ("RParen", "RBrace", "RBracket"):
                        h_depth = max(0, h_depth - 1)
                    if t == "Ident":
                        header.append(str(v))
                if not any(short_name(h) in _VERIFY_PROOF_CLASS_NAMES for h in header):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} declares a non-`*ItemProof` `instance` ({header[:6]})",
                    )
        if val != "theorem" or nxt != ("Ident", "verified"):
            continue
        if idx + 2 >= n or tokens[idx + 2][0] != "Colon":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`theorem verified` in {label} must have an explicit `: <Certificate> :=` signature without binders",
            )
        j = idx + 3
        while j < n and not (j in top_set and tokens[j][0] == "ColonEq"):
            if j in top_set and _fc_is_lean_command_start(tokens[j]):
                break
            j += 1
        if j >= n or tokens[j][0] != "ColonEq":
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"`theorem verified` has no `:=` proof body in {label}"
            )
        verified.append((tokens[idx + 3 : j], tokens[j + 1 : command_end(j)]))
    if len(verified) != 1:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"{label} must declare exactly one `theorem verified` (found {len(verified)})",
        )
    ty, proof = verified[0]
    ob_prefix = f"Obligations.{suffix}."
    claim: str | None = None
    if len(ty) == 2 and ty[0][0] == "Ident" and ty[1][0] == "Ident":
        cert = _strip_verification_result_qual(str(ty[0][1]))
        ref = str(ty[1][1])
        expected_claim = _VERIFY_MONO_CERT_CLAIMS.get(cert)
        if expected_claim is not None and ref == ob_prefix + expected_claim:
            claim = expected_claim
    elif (
        len(ty) == 5
        and ty[0][0] == "Ident"
        and ty[1][0] == "LParen"
        and ty[2][0] == "Ident"
        and ty[3][0] == "Ident"
        and ty[4][0] == "RParen"
        and _strip_verification_result_qual(str(ty[0][1])) == "CrateVerificationResult"
        and ty[2][1] == ob_prefix + "polyCertificate"
        and str(ty[3][1]).startswith(ob_prefix)
        and str(ty[3][1])[len(ob_prefix) :] in _VERIFY_POLY_CLAIMS
    ):
        claim = str(ty[3][1])[len(ob_prefix) :]
    if claim is None:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"{label} proves non-canonical statement {ty!r} instead of `Obligations.{suffix}.<claim>`",
        )
    trusted = (
        proof == [("Ident", f"Assumptions.{suffix}.rust_trusted_contract")]
        and f"Assumptions.{suffix}" in imports
    )
    ub_exception = claim in ("ubExceptionClaim", "polyUbExceptionClaim")
    modular = claim in ("modularClaim", "polyModularClaim")
    equiv = claim == "equivClaim"
    return {
        "claim": claim,
        "modular": modular,
        "equiv": equiv,
        "ub_exception": ub_exception,
        "trusted": trusted,
        "assumed": ub_exception or trusted,
        "imports_specs": f"Specs.{suffix}" in imports,
        "imported_mir_suffixes": [
            m[len("Mir.") :] for m in imports if m.startswith("Mir.")
        ],
        "imported_proof_suffixes": [
            m[len("Proof.") :] for m in imports if m.startswith("Proof.")
        ],
        "imported_assumptions_suffixes": [
            m[len("Assumptions.") :] for m in imports if m.startswith("Assumptions.")
        ],
    }


def _is_allowed_specs_import(module: str) -> bool:
    return (
        module.startswith(("Mir.", "Obligations.", "Specs."))
        or any(
            module == root or module.startswith(root + ".")
            for root in ("Init", "Std", "Trusted", "Anneal")
        )
    )


def _is_allowed_aux_import(module: str) -> bool:
    return _is_allowed_specs_import(module) or module.startswith(("Proof.", "Assumptions."))


_SPEC_PRE_LOWER_PRECEDENCE_OR_BINDERS: frozenset[str] = frozenset((
    "∨",
    "\\/",
    "→",
    "->",
    "↔",
    "<->",
    "∀",
    "∃",
    "forall",
    "exists",
    "fun",
    "λ",
    "if",
    "match",
    "let",
    "have",
    "show",
    "by",
    "do",
))

_SPEC_PRE_BINDERS_ONLY: frozenset[str] = frozenset((
    "∀",
    "∃",
    "forall",
    "exists",
    "fun",
    "λ",
    "if",
    "match",
    "let",
    "have",
    "show",
    "by",
    "do",
))

_SPEC_PRE_ALL_INFIX_OR_BINDERS: frozenset[str] = _SPEC_PRE_LOWER_PRECEDENCE_OR_BINDERS | frozenset((
    "∧",
    "/\\",
    "=",
    "==",
    "≠",
    "!=",
    "<",
    "≤",
    "<=",
    ">",
    "≥",
    ">=",
))


def _is_trivially_true_spec_atom(tokens_slice: list[tuple[str, Any]]) -> bool:
    s = _strip_enclosing_parens_tokens(tokens_slice)
    return len(s) == 1 and s[0][0] == "Ident" and str(s[0][1]) in (
        "True",
        "_root_.True",
        "Prop.True",
    )


def _are_contradictory_eq_sides(
    lhs_raw: list[tuple[str, Any]], rhs_raw: list[tuple[str, Any]]
) -> bool:
    lhs = _strip_enclosing_parens_tokens(lhs_raw)
    rhs = _strip_enclosing_parens_tokens(rhs_raw)
    if len(lhs) != 1 or len(rhs) != 1:
        return False
    lt, lv = lhs[0]
    rt, rv = rhs[0]
    if lt == "NatLit" and rt == "NatLit":
        return lv != rv
    if lt == "StrLit" and rt == "StrLit":
        return lv != rv
    if lt == "Ident" and rt == "Ident":
        pair = {str(lv), str(rv)}
        if pair in (
            {"true", "false"},
            {"Bool.true", "Bool.false"},
            {"_root_.Bool.true", "_root_.Bool.false"},
            {"True", "False"},
            {"_root_.True", "_root_.False"},
            {"Prop.True", "Prop.False"},
        ):
            return True
    return False


def _extract_def_binders_and_is_prop(
    sig_tokens: list[tuple[str, Any]],
) -> tuple[list[str], bool]:
    binder_re = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
    depth = 0
    colon_pos: int | None = None
    for i, (tk, _v) in enumerate(sig_tokens):
        if depth == 0 and tk == "Colon":
            colon_pos = i
            break
        if tk in ("LParen", "LBrace", "LBracket"):
            depth += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            depth = max(0, depth - 1)
    binder_slice = sig_tokens[:colon_pos] if colon_pos is not None else sig_tokens
    ret_slice = (
        _strip_enclosing_parens_tokens(sig_tokens[colon_pos + 1 :])
        if colon_pos is not None
        else []
    )
    is_prop = len(ret_slice) == 1 and ret_slice[0][0] == "Ident" and str(ret_slice[0][1]) in (
        "Prop",
        "_root_.Prop",
    )
    params: list[str] = []
    k = 0
    m = len(binder_slice)
    while k < m:
        tk, val = binder_slice[k]
        if tk == "Ident" and binder_re.fullmatch(str(val)):
            params.append(str(val))
            k += 1
            continue
        if tk == "LParen":
            d = 1
            j = k + 1
            group_idents: list[str] = []
            seen_colon = False
            while j < m and d > 0:
                gt, gv = binder_slice[j]
                if gt in ("LParen", "LBrace", "LBracket"):
                    d += 1
                elif gt in ("RParen", "RBrace", "RBracket"):
                    d -= 1
                elif d == 1 and gt == "Colon":
                    seen_colon = True
                elif d == 1 and not seen_colon and gt == "Ident" and binder_re.fullmatch(str(gv)):
                    group_idents.append(str(gv))
                j += 1
            params.extend(group_idents)
            k = j
            continue
        if tk in ("LBrace", "LBracket"):
            d = 1
            j = k + 1
            while j < m and d > 0:
                if binder_slice[j][0] in ("LParen", "LBrace", "LBracket"):
                    d += 1
                elif binder_slice[j][0] in ("RParen", "RBrace", "RBracket"):
                    d -= 1
                j += 1
            k = j
            continue
        k += 1
    return params, is_prop


def _is_trivially_false_spec_pre(
    tokens_slice: list[tuple[str, Any]],
    local_defs: dict[str, tuple[list[str], list[tuple[str, Any]]]] | None = None,
    _seen: frozenset[str] = frozenset(),
) -> bool:
    """`[adv ep2-A2]` / `[adv ep2-B3]` / `[adv ep2-A3]` Detect a syntactically vacuous
    `False` precondition (`False`, `fun ... => False`, `¬ True`, `Not True`, `0 = 1`,
    `true = false`, `x ≠ x`, `True → False`, `True ↔ False`, `False ∨ False`,
    `And False _`, `And _ False`, `False ∧ _`, `_ ∧ False`, or a local `def`/`abbrev`
    in `Specs/<Item>.lean` unfolding to one of these) in `Specs/<Item>.lean`.
    """
    s = _strip_enclosing_parens_tokens(tokens_slice)
    if not s:
        return False
    if s[0] in (("Ident", "fun"), ("Ident", "λ")):
        depth = 0
        for i, (tk, v) in enumerate(s):
            if tk in ("LParen", "LBrace", "LBracket"):
                depth += 1
            elif tk in ("RParen", "RBrace", "RBracket"):
                depth = max(0, depth - 1)
            elif depth == 0 and tk == "Ident" and v in ("=>", "↦"):
                return _is_trivially_false_spec_pre(s[i + 1 :], local_defs, _seen)
        return False
    if len(s) == 1 and s[0][0] == "Ident":
        ident0 = str(s[0][1])
        if ident0 in ("False", "_root_.False", "Prop.False"):
            return True
        if local_defs is not None and ident0 in local_defs and ident0 not in _seen:
            _params, rhs_d = local_defs[ident0]
            return _is_trivially_false_spec_pre(rhs_d, local_defs, _seen | {ident0})
        return False
    if s[0] in (("Ident", "Not"), ("Ident", "_root_.Not")):
        args1 = _take_exact_n_balanced_args(s[1:], 1)
        if args1 is not None and _is_trivially_true_spec_atom(args1[0]):
            return True
    if s[0] == ("Ident", "¬") and not any(
        tk == "Ident" and str(v) in _SPEC_PRE_ALL_INFIX_OR_BINDERS
        for tk, v in s[1:]
    ):
        if _is_trivially_true_spec_atom(s[1:]):
            return True
    if s[0] in (("Ident", "And"), ("Ident", "_root_.And")):
        args2 = _take_exact_n_balanced_args(s[1:], 2)
        if args2 is not None:
            return _is_trivially_false_spec_pre(
                args2[0], local_defs, _seen
            ) or _is_trivially_false_spec_pre(args2[1], local_defs, _seen)
        return False
    if s[0] in (("Ident", "Or"), ("Ident", "_root_.Or")):
        args2 = _take_exact_n_balanced_args(s[1:], 2)
        if args2 is not None:
            return _is_trivially_false_spec_pre(
                args2[0], local_defs, _seen
            ) and _is_trivially_false_spec_pre(args2[1], local_defs, _seen)
        return False
    if s[0] in (("Ident", "Iff"), ("Ident", "_root_.Iff")):
        args2 = _take_exact_n_balanced_args(s[1:], 2)
        if args2 is not None:
            return (
                _is_trivially_true_spec_atom(args2[0])
                and _is_trivially_false_spec_pre(args2[1], local_defs, _seen)
            ) or (
                _is_trivially_false_spec_pre(args2[0], local_defs, _seen)
                and _is_trivially_true_spec_atom(args2[1])
            )
        return False
    if s[0] in (("Ident", "Eq"), ("Ident", "_root_.Eq")):
        args2 = _take_exact_n_balanced_args(s[1:], 2)
        if args2 is not None and _are_contradictory_eq_sides(args2[0], args2[1]):
            return True
    if s[0] in (("Ident", "Ne"), ("Ident", "_root_.Ne")):
        args2 = _take_exact_n_balanced_args(s[1:], 2)
        if args2 is not None:
            l_ne = _strip_enclosing_parens_tokens(args2[0])
            r_ne = _strip_enclosing_parens_tokens(args2[1])
            if l_ne and l_ne == r_ne:
                return True
    depth = 0
    has_binder = False
    iff_positions: list[int] = []
    imp_positions: list[int] = []
    disj_positions: list[int] = []
    conj_positions: list[int] = []
    eq_positions: list[int] = []
    ne_positions: list[int] = []
    other_infix = False
    for idx, (tk, val) in enumerate(s):
        if tk in ("LParen", "LBrace", "LBracket"):
            depth += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            depth = max(0, depth - 1)
        elif tk == "Ident" and depth == 0:
            v_str = str(val)
            if v_str in _SPEC_PRE_BINDERS_ONLY:
                has_binder = True
            elif v_str in ("↔", "<->"):
                iff_positions.append(idx)
            elif v_str in ("→", "->"):
                imp_positions.append(idx)
            elif v_str in ("∨", "\\/"):
                disj_positions.append(idx)
            elif v_str in ("∧", "/\\"):
                conj_positions.append(idx)
            elif v_str in ("=", "=="):
                eq_positions.append(idx)
            elif v_str in ("≠", "!="):
                ne_positions.append(idx)
            elif v_str in ("<", "≤", "<=", ">", "≥", ">="):
                other_infix = True
    if has_binder:
        return False
    if len(iff_positions) == 1 and not imp_positions:
        idx = iff_positions[0]
        lhs_i, rhs_i = s[:idx], s[idx + 1 :]
        return (
            _is_trivially_true_spec_atom(lhs_i)
            and _is_trivially_false_spec_pre(rhs_i, local_defs, _seen)
        ) or (
            _is_trivially_false_spec_pre(lhs_i, local_defs, _seen)
            and _is_trivially_true_spec_atom(rhs_i)
        )
    if iff_positions:
        return False
    if len(imp_positions) == 1:
        idx = imp_positions[0]
        return _is_trivially_true_spec_atom(s[:idx]) and _is_trivially_false_spec_pre(
            s[idx + 1 :], local_defs, _seen
        )
    if imp_positions:
        return False
    if disj_positions:
        idx = disj_positions[0]
        return _is_trivially_false_spec_pre(
            s[:idx], local_defs, _seen
        ) and _is_trivially_false_spec_pre(s[idx + 1 :], local_defs, _seen)
    if conj_positions:
        idx = conj_positions[0]
        return _is_trivially_false_spec_pre(
            s[:idx], local_defs, _seen
        ) or _is_trivially_false_spec_pre(s[idx + 1 :], local_defs, _seen)
    if len(eq_positions) == 1 and not ne_positions and not other_infix:
        idx = eq_positions[0]
        return _are_contradictory_eq_sides(s[:idx], s[idx + 1 :])
    if len(ne_positions) == 1 and not eq_positions and not other_infix:
        idx = ne_positions[0]
        lhs_n = _strip_enclosing_parens_tokens(s[:idx])
        rhs_n = _strip_enclosing_parens_tokens(s[idx + 1 :])
        return bool(lhs_n and lhs_n == rhs_n)
    if (
        not eq_positions
        and not ne_positions
        and not other_infix
        and local_defs is not None
        and s[0][0] == "Ident"
    ):
        head_name = str(s[0][1])
        if head_name in local_defs and head_name not in _seen:
            param_names, def_rhs = local_defs[head_name]
            next_seen = _seen | {head_name}
            if _is_trivially_false_spec_pre(def_rhs, local_defs, next_seen):
                return True
            if param_names and len(s) > 1:
                call_args = _take_exact_n_balanced_args(s[1:], len(param_names))
                if call_args is not None:
                    subst_map = {
                        p: [("LParen", "("), *arg, ("RParen", ")")]
                        for p, arg in zip(param_names, call_args)
                    }
                    subst_rhs: list[tuple[str, Any]] = []
                    for tk_d, val_d in def_rhs:
                        if tk_d == "Ident" and str(val_d) in subst_map:
                            subst_rhs.extend(subst_map[str(val_d)])
                        else:
                            subst_rhs.append((tk_d, val_d))
                    if _is_trivially_false_spec_pre(subst_rhs, local_defs, next_seen):
                        return True
    return False


_SPEC_STRUCTURE_FIELD_NAMES: frozenset[str] = frozenset((
    "pre",
    "post",
    "envAssumed",
    "specBody",
    "strictSafetyPre",
))

_SPEC_CLASS_ALLOWED_FIELDS: dict[str, frozenset[str]] = {
    "ItemSpec": frozenset(("pre", "post")),
    "StatefulItemSpec": frozenset(("pre", "post")),
    "TotalItemSpec": frozenset(("pre", "post")),
    "ModularItemSpec": frozenset(("envAssumed", "pre", "post")),
    "StatefulEquivItemSpec": frozenset(("specBody", "pre", "post")),
    "UbExceptionItemSpec": frozenset(("pre", "strictSafetyPre", "post")),
}

_SPEC_CLASS_ALLOWED_REFINE_HELPERS: dict[str, frozenset[str]] = {
    "ItemSpec": frozenset(("refineSpec", "refineSafeSpec")),
    "StatefulItemSpec": frozenset(("refineStatefulSpec", "refineSafeStatefulSpec")),
    "TotalItemSpec": frozenset(("refineTotalSpec",)),
    "ModularItemSpec": frozenset(("refineModularSpec",)),
    "StatefulEquivItemSpec": frozenset(("refineEquivSpec",)),
    "UbExceptionItemSpec": frozenset(("refineUbExceptionSpec",)),
}

_SPECS_RESERVED_DECL_NAMES: frozenset[str] = (
    _VERIFY_REFINE_SPEC_HELPERS
    | _OB_ALL_SPEC_INSTANCE_NAMES
    | _VERIFY_SPEC_CLASS_NAMES
    | _VERIFY_PROOF_CLASS_NAMES
    | _VERIFY_CERTIFICATE_TYPE_NAMES
    | frozenset((
        "defaultPre",
        "defaultPost",
        "defaultPreFor",
        "defaultPostFor",
        "rustRequires",
        "rustEnsures",
        "sigPre",
        "sigPost",
        "defaultCallContract",
        "defaultExternalCallContract",
        "defaultCallees",
        "defaultSpecCallees",
        "artifactIdentity",
        "polyCertificate",
        "True",
        "False",
        "And",
        "Or",
        "Not",
        "Iff",
        "Eq",
        "Ne",
        "Prop",
        "Bool",
        "Nat",
        "Int",
        "String",
        "List",
        "Option",
        "Value",
        "Memory",
        "LocalSlot",
        "BorrowEntry",
        "ProvenancePtr",
        "ExternalCallHandler",
        "CapturedMir",
        "MirCallContract",
        "initMachineState",
        "emptyMemory",
    ))
)


def _split_structure_instance_fields(
    body: list[tuple[str, Any]],
) -> list[tuple[str, list[tuple[str, Any]], list[tuple[str, Any]]]] | None:
    """`[adv ep2-B3]` / `[adv ep2-A3]` Split a `where` / `{ ... }` `*ItemSpec` instance body
    into `(field, binder_tokens, rhs)` triples, failing closed (`None`) if any token is
    unconsumed, if `with` struct-update or nested `where` syntax appears at depth 0, or if
    duplicate/empty fields appear.
    """
    if not body:
        return None
    binder_re = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")
    n = len(body)
    depth_at: list[int] = []
    depth = 0
    for tk, v in body:
        # `[adv ep2-B4]`: only a depth-0 `where` is rejected here. A depth-0 `with` is the
        # ordinary `match ... with` of a field value; a `{ s with pre := ... }` struct update
        # is still rejected below because its body does not start with a field header.
        if depth == 0 and tk == "Ident" and v == "where":
            return None
        depth_at.append(depth)
        if tk in ("LParen", "LBrace", "LBracket"):
            depth += 1
        elif tk in ("RParen", "RBrace", "RBracket"):
            if depth <= 0:
                return None
            depth -= 1
    if depth != 0:
        return None

    def header_colon_eq(k: int) -> int | None:
        if (
            depth_at[k] != 0
            or body[k][0] != "Ident"
            or str(body[k][1]) not in _SPEC_STRUCTURE_FIELD_NAMES
            or (k > 0 and body[k - 1] in (("Ident", "let"), ("Ident", "have"), ("Ident", "mut")))
        ):
            return None
        m = k + 1
        while m < n:
            if (
                body[m][0] == "Ident"
                and binder_re.fullmatch(str(body[m][1]))
                and str(body[m][1]) not in _SPEC_STRUCTURE_FIELD_NAMES
            ):
                m += 1
                continue
            if body[m][0] in ("LParen", "LBrace", "LBracket") and depth_at[m] == 0:
                close = m + 1
                while close < n and depth_at[close] != 0:
                    close += 1
                if close <= m + 1 or body[close - 1][0] not in ("RParen", "RBrace", "RBracket"):
                    return None
                m = close
                continue
            break
        if m < n and body[m][0] == "ColonEq" and depth_at[m] == 0:
            return m
        return None

    fields: list[tuple[str, list[tuple[str, Any]], list[tuple[str, Any]]]] = []
    seen_names: set[str] = set()
    k = 0
    while k < n:
        if body[k][0] in ("Comma", "Semicolon") and depth_at[k] == 0:
            k += 1
            continue
        eq = header_colon_eq(k)
        if eq is None:
            return None
        r = eq + 1
        while r < n:
            # `[adv ep2-B4]`: a depth-0 `,` / `;` separates fields only when a field header (or
            # the end of the body) follows; otherwise it belongs to the value
            # (`fun args mem => ∀ x, P x`, `∃ n, ...`, `let x := e; ...`).
            if depth_at[r] == 0 and (
                (
                    body[r][0] in ("Comma", "Semicolon")
                    and (r + 1 == n or header_colon_eq(r + 1) is not None)
                )
                or header_colon_eq(r) is not None
            ):
                break
            r += 1
        fname = str(body[k][1])
        rhs_slice = body[eq + 1 : r]
        if fname in seen_names or not rhs_slice:
            return None
        seen_names.add(fname)
        fields.append((fname, body[k + 1 : eq], rhs_slice))
        k = r
    return fields if fields else None


def _check_specs_or_aux_open_command(
    tokens: list[tuple[str, Any]], start_idx: int, label: str, *, is_aux: bool
) -> None:
    """`[adv ep2-A3]` Validate `open` commands in `Specs`, `Proof`, and `Assumptions`:
    forbid `open ... renaming`, `open ... hiding`, `open ... in`, `open scoped`, or
    parenthesized/bracketed identifier lists, and restrict opened namespaces to
    trusted/workspace module hierarchies."""
    n = len(tokens)
    k = start_idx + 1
    count = 0
    allowed_roots = (
        ("Trusted", "Anneal", "Std", "Init", "Obligations.", "Specs.", "Proof.", "Assumptions.", "Mir.")
        if is_aux
        else ("Trusted", "Anneal", "Std", "Init", "Obligations.", "Specs.", "Mir.")
    )
    while k < n:
        if _fc_is_lean_command_start(tokens[k]):
            break
        if tokens[k][0] != "Ident":
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"unsupported `open` syntax `{tokens[k]!r}` in {label} (selective/renaming `open` is forbidden)",
            )
        ns_name = str(tokens[k][1])
        if ns_name in ("renaming", "hiding", "in", "scoped"):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"`open ... {ns_name}` is not supported in {label}"
            )
        if not any(
            ns_name == r or ns_name.startswith(r if r.endswith(".") else r + ".")
            for r in allowed_roots
        ):
            raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `open {ns_name}` in {label}")
        count += 1
        k += 1
    if count == 0:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"`open` without namespaces in {label}")


def _scan_specs_module(
    specs_text: str, subject_suffix: str, label: str
) -> dict[str, Any]:
    """`[adv ep2-A1]` / `[adv ep2-A2]` / `[adv ep2-A3]` Port of Rust `scan_specs_module`:
    scan `Specs/<Item>.lean` for `*ItemSpec` instances, `ModularItemSpec.envAssumed` contracts,
    `StatefulEquivItemSpec.specBody` reference MIR bodies, and vacuous `False` preconditions."""
    tokens = _tokenize_lean_or_fail(specs_text, label)
    _check_module_scope_confinement(tokens, f"Specs.{subject_suffix}", label)
    attr = _verify_detect_instance_attribute(tokens)
    if attr is not None:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `@[{attr}]` attribute in {label}")
    _reject_meta_commands(tokens, label)
    expected_ns = f"Specs.{subject_suffix}"
    ns_opens = 0
    ns_closes = 0
    local_env_assumed_def: list[tuple[str, Any]] | None = None
    local_defs: dict[str, tuple[list[str], list[tuple[str, Any]]]] = {}
    declared_spec_def_ids: list[str] = []
    declared_spec_classes: list[str] = []
    has_modular_spec_instance = False
    delegates_to_default_modular_spec_env = False
    imported_obligation_suffixes: list[str] = []
    imported_mir_suffixes: list[str] = []
    imported_specs_suffixes: list[str] = []
    sibling_modular_contracts: list[tuple[str, str]] = []
    referenced_subject_external_contract_idents: list[str] = []
    has_equiv_spec_instance = False
    equiv_spec_body_suffix: str | None = None
    raw_modular_stems: list[str] = []

    n = len(tokens)
    top = _top_level_token_indices(tokens)
    top_set = set(top)

    def command_end(start: int) -> int:
        k = start + 1
        while k < n and not (k in top_set and _fc_is_lean_command_start(tokens[k])):
            k += 1
        return k

    for idx in top:
        tk, val = tokens[idx]
        if tk != "Ident":
            continue
        if val in (
            "axiom",
            "opaque",
            "macro",
            "macro_rules",
            "syntax",
            "notation",
            "infix",
            "infixl",
            "infixr",
            "prefix",
            "postfix",
            "elab",
            "elab_rules",
            "deriving",
            "initialize",
            "builtin_initialize",
            "mutual",
            "local",
            "scoped",
            "attribute",
            "class",
            "unsafe",
            "partial",
            "export",
            "section",
        ):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed top-level `{val}` command in {label}"
            )
        if val == "open":
            _check_specs_or_aux_open_command(tokens, idx, label, is_aux=False)
            continue
        if val in ("structure", "inductive"):
            for t_c, v_c in tokens[idx : command_end(idx)]:
                if t_c == "Ident" and (
                    _strip_verification_result_qual(str(v_c)) in _VERIFY_SPEC_CLASS_NAMES
                    or str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} references `{v_c}` inside `{val}` declaration",
                    )
        elif val == "namespace":
            if idx + 1 >= n or tokens[idx + 1] != ("Ident", expected_ns):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"unexpected `namespace` in {label} (expected `{expected_ns}`)",
                )
            ns_opens += 1
        elif val == "end":
            if idx + 1 < n and tokens[idx + 1] == ("Ident", expected_ns):
                ns_closes += 1
            elif ns_opens > ns_closes:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"unexpected `end` in {label} (expected `{expected_ns}`)",
                )
        elif val == "import":
            if idx + 1 >= n or tokens[idx + 1][0] != "Ident":
                raise Failure(1, FAULT_COVERAGE_PHASE, f"malformed `import` in {label}")
            mod = str(tokens[idx + 1][1])
            if not _is_allowed_specs_import(mod):
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"disallowed `import {mod}` in {label}"
                )
            if mod.startswith("Obligations."):
                ob_suf = mod[len("Obligations.") :]
                if ob_suf != subject_suffix and ob_suf not in imported_obligation_suffixes:
                    imported_obligation_suffixes.append(ob_suf)
            elif mod.startswith("Mir."):
                mir_suf = mod[len("Mir.") :]
                if mir_suf and mir_suf not in imported_mir_suffixes:
                    imported_mir_suffixes.append(mir_suf)
            elif mod.startswith("Specs."):
                spec_suf = mod[len("Specs.") :]
                if spec_suf != subject_suffix and spec_suf not in imported_specs_suffixes:
                    imported_specs_suffixes.append(spec_suf)
        elif val in ("def", "abbrev", "theorem", "lemma"):
            cmd_e = command_end(idx)
            cmd_slice = tokens[idx:cmd_e]
            for t_c, v_c in cmd_slice:
                if t_c == "Ident":
                    if _strip_verification_result_qual(str(v_c)) in _VERIFY_SPEC_CLASS_NAMES:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{label} references specification class `{v_c}` inside `{val}` (use `instance`)",
                        )
                    if str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{label} references `{v_c}` inside `{val}` (use `instance`)",
                        )
            if idx + 1 < n and tokens[idx + 1][0] == "Ident":
                decl_name = str(tokens[idx + 1][1])
                if (
                    decl_name.startswith((
                        "Obligations.",
                        "Mir.",
                        "Trusted.",
                        "Anneal.",
                        "Specs.",
                        "Verify.",
                        "Proof.",
                        "Assumptions.",
                        "_root_.",
                        "externalCallContract_",
                    ))
                    or decl_name in _SPECS_RESERVED_DECL_NAMES
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} shadows reserved identifier `{decl_name}`",
                    )
                if val in ("def", "abbrev"):
                    colon_eq_pos: int | None = None
                    s_depth = 0
                    for s_pos in range(2, len(cmd_slice)):
                        t_s = cmd_slice[s_pos][0]
                        if s_depth == 0 and t_s == "ColonEq":
                            colon_eq_pos = s_pos
                            break
                        if t_s in ("LParen", "LBrace", "LBracket"):
                            s_depth += 1
                        elif t_s in ("RParen", "RBrace", "RBracket"):
                            s_depth = max(0, s_depth - 1)
                    if colon_eq_pos is None:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`{val} {decl_name}` in {label} lacks `:=`",
                        )
                    sig_tokens = cmd_slice[2:colon_eq_pos]
                    rhs_tokens = list(cmd_slice[colon_eq_pos + 1 :])
                    param_names, _is_prop = _extract_def_binders_and_is_prop(sig_tokens)
                    # `[adv ep2-B4]`: a `False`-valued `Prop` helper is only vacuous when a
                    # precondition uses it; every `pre` / `refine*Spec` precondition resolves
                    # local helpers through `local_defs`, so an unused helper or one used only
                    # in a postcondition (`post := fun _ _ => ¬ unreachable`) is not rejected.
                    local_defs[decl_name] = (param_names, rhs_tokens)
                    local_defs[f"{expected_ns}.{decl_name}"] = (param_names, rhs_tokens)
                    if decl_name == "envAssumed":
                        if local_env_assumed_def is not None:
                            raise Failure(
                                1,
                                FAULT_COVERAGE_PHASE,
                                f"duplicate `def envAssumed` in {label}",
                            )
                        if (
                            len(sig_tokens) >= 2
                            and sig_tokens[0][0] == "LParen"
                            and sig_tokens[1][0] == "Ident"
                        ):
                            local_env_assumed_def = [
                                ("Ident", "fun"),
                                ("Ident", str(sig_tokens[1][1])),
                                ("Ident", "=>"),
                                *rhs_tokens,
                            ]
                        else:
                            local_env_assumed_def = list(rhs_tokens)
        elif val == "instance":
            if idx + 1 < n and tokens[idx + 1][0] == "Ident":
                inst_name = str(tokens[idx + 1][1])
                if (
                    inst_name.startswith(("Obligations.", "Mir.", "Trusted."))
                    or inst_name in _OB_ALL_SPEC_INSTANCE_NAMES
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{label} shadows reserved instance identifier `{inst_name}`",
                    )
            cmd_slice = tokens[idx : command_end(idx)]
            header_end = len(cmd_slice)
            h_depth = 0
            for h_pos, (t_h, v_h) in enumerate(cmd_slice):
                if h_depth == 0 and (t_h == "ColonEq" or (t_h, v_h) == ("Ident", "where")):
                    header_end = h_pos
                    break
                if t_h in ("LParen", "LBrace", "LBracket"):
                    h_depth += 1
                elif t_h in ("RParen", "RBrace", "RBracket"):
                    h_depth = max(0, h_depth - 1)
            header = cmd_slice[:header_end]
            header_spec_classes: list[str] = []
            for h_pos, (t_h, v_h) in enumerate(header):
                if t_h == "Ident":
                    short_cls = _strip_verification_result_qual(str(v_h))
                    if short_cls in _VERIFY_SPEC_CLASS_NAMES:
                        if h_pos + 1 >= len(header) or header[h_pos + 1][0] != "StrLit":
                            raise Failure(
                                1,
                                FAULT_COVERAGE_PHASE,
                                f"`{short_cls}` instance in {label} must have an explicit string-literal `defId` immediately after `{short_cls}`",
                            )
                        did = str(header[h_pos + 1][1])
                        if did not in declared_spec_def_ids:
                            declared_spec_def_ids.append(did)
                        if short_cls not in declared_spec_classes:
                            declared_spec_classes.append(short_cls)
                        header_spec_classes.append(short_cls)
            if len(header_spec_classes) != 1:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"every `instance` in {label} must declare an explicit `<*ItemSpec> \"<defId>\"` header",
                )
            cls0 = header_spec_classes[0]
            if cls0 == "ModularItemSpec":
                if has_modular_spec_instance:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"multiple `ModularItemSpec` instances in {label}",
                    )
                has_modular_spec_instance = True
            elif cls0 == "StatefulEquivItemSpec":
                if has_equiv_spec_instance:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"multiple `StatefulEquivItemSpec` instances in {label}",
                    )
                has_equiv_spec_instance = True

            def parse_env_with_local(env_slice: list[tuple[str, Any]]) -> list[str]:
                stripped = _strip_enclosing_parens_tokens(env_slice)
                if stripped == [("Ident", "envAssumed")] and local_env_assumed_def is not None:
                    return _parse_env_assumed_holds_on_stems(local_env_assumed_def, label)
                return _parse_env_assumed_holds_on_stems(stripped, label)

            # `[adv ep2-A2]` / `[adv ep2-A3]`: Every `*ItemSpec` instance must use either
            # a complete `where` / `:= { ... }` field list (no positional `⟨...⟩` / `.mk`
            # constructors and no `with` struct updates) or an exact-arity `refine*Spec`
            # call for `cls0`, with non-vacuous `pre`.
            raw_body = cmd_slice[header_end + 1 :] if header_end < len(cmd_slice) else []
            fields_body: list[tuple[str, Any]] | None = None
            used_refine_helper = False
            if header_end < len(cmd_slice) and cmd_slice[header_end] == ("Ident", "where"):
                fields_body = raw_body
            elif header_end < len(cmd_slice) and cmd_slice[header_end][0] == "ColonEq":
                rhs_spec = _strip_enclosing_parens_tokens(raw_body)
                if (
                    len(rhs_spec) >= 2
                    and rhs_spec[0][0] == "LBrace"
                    and rhs_spec[-1][0] == "RBrace"
                ):
                    bal = 0
                    outer_brace_ok = True
                    for pos_b, (tk_b, _vb) in enumerate(rhs_spec):
                        if tk_b in ("LParen", "LBrace", "LBracket"):
                            bal += 1
                        elif tk_b in ("RParen", "RBrace", "RBracket"):
                            bal -= 1
                        if bal <= 0 and pos_b + 1 < len(rhs_spec):
                            outer_brace_ok = False
                            break
                    if outer_brace_ok and bal == 0:
                        fields_body = rhs_spec[1:-1]
                elif rhs_spec and rhs_spec[0][0] == "Ident":
                    ref_full = str(rhs_spec[0][1])
                    short_ref = ref_full.rsplit(".", 1)[-1]
                    if short_ref in _SPEC_CLASS_ALLOWED_REFINE_HELPERS[cls0] and ref_full in (
                        short_ref,
                        f"Obligations.{subject_suffix}.{short_ref}",
                    ):
                        n_args = (
                            2
                            if short_ref in ("refineSpec", "refineStatefulSpec", "refineTotalSpec")
                            else 3
                        )
                        r_args = _take_exact_n_balanced_args(rhs_spec[1:], n_args)
                        if r_args is None:
                            raise Failure(
                                1,
                                FAULT_COVERAGE_PHASE,
                                f"`{short_ref}` in {label} must take exactly {n_args} balanced arguments without trailing tokens",
                            )
                        pre_indices = (
                            (0, 1)
                            if short_ref in ("refineSafeSpec", "refineSafeStatefulSpec")
                            else (
                                (1,)
                                if short_ref
                                in ("refineEquivSpec", "refineModularSpec", "refineUbExceptionSpec")
                                else (0,)
                            )
                        )
                        for p_i in pre_indices:
                            if _is_trivially_false_spec_pre(r_args[p_i], local_defs):
                                raise Failure(
                                    1,
                                    FAULT_COVERAGE_PHASE,
                                    f"vacuous `False` precondition in `{short_ref}` of {label}",
                                )
                        if cls0 == "ModularItemSpec":
                            for st in parse_env_with_local(r_args[0]):
                                if st not in raw_modular_stems:
                                    raw_modular_stems.append(st)
                        elif cls0 == "StatefulEquivItemSpec":
                            arg0 = _strip_enclosing_parens_tokens(r_args[0])
                            if (
                                len(arg0) == 1
                                and arg0[0][0] == "Ident"
                                and str(arg0[0][1]).startswith("Mir.")
                                and str(arg0[0][1]).endswith(".body")
                            ):
                                ref_s = str(arg0[0][1])[len("Mir.") : -len(".body")]
                                if not ref_s:
                                    raise Failure(
                                        1, FAULT_COVERAGE_PHASE, f"empty `Mir.<Ref>.body` in {label}"
                                    )
                                equiv_spec_body_suffix = ref_s
                            else:
                                raise Failure(
                                    1,
                                    FAULT_COVERAGE_PHASE,
                                    f"`refineEquivSpec` in {label} must take `Mir.<Ref>.body` as its first argument",
                                )
                        used_refine_helper = True

            if not used_refine_helper:
                if fields_body is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`{cls0}` instance in {label} must use `where`, `{{ ... }}`, or `refine*Spec` (positional constructors and `with` struct updates are forbidden)",
                    )
                parsed_fields = _split_structure_instance_fields(fields_body)
                if parsed_fields is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"malformed or non-canonical field bindings in `{cls0}` instance of {label} (`with` struct updates, nested `where`, and unparsed tokens are forbidden)",
                    )
                allowed_f = _SPEC_CLASS_ALLOWED_FIELDS[cls0]
                field_map: dict[str, tuple[list[tuple[str, Any]], list[tuple[str, Any]]]] = {}
                for f_name, f_binders, f_rhs in parsed_fields:
                    if f_name not in allowed_f:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"unexpected field `{f_name}` in `{cls0}` instance of {label}",
                        )
                    field_map[f_name] = (f_binders, f_rhs)
                if "pre" in field_map:
                    f_binders, f_rhs = field_map["pre"]
                    pre_expr = (
                        [("Ident", "fun"), *f_binders, ("Ident", "=>"), *f_rhs]
                        if f_binders
                        else f_rhs
                    )
                    if _is_trivially_false_spec_pre(pre_expr, local_defs):
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"vacuous `False` precondition in `{cls0}` instance of {label}",
                        )
                if cls0 == "ModularItemSpec":
                    if "envAssumed" not in field_map:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`ModularItemSpec` instance in {label} omits `envAssumed :=`",
                        )
                    env_binders, env_rhs = field_map["envAssumed"]
                    if env_binders:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`ModularItemSpec.envAssumed` in {label} must use `envAssumed := ...` without binders",
                        )
                    for st in parse_env_with_local(env_rhs):
                        if st not in raw_modular_stems:
                            raw_modular_stems.append(st)
                elif cls0 == "StatefulEquivItemSpec":
                    if "specBody" not in field_map:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`StatefulEquivItemSpec` instance in {label} omits `specBody := Mir.<Ref>.body`",
                        )
                    sb_binders, sb_rhs = field_map["specBody"]
                    if sb_binders:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`StatefulEquivItemSpec.specBody` in {label} must use `specBody := Mir.<Ref>.body` without binders",
                        )
                    spec_rhs = _strip_enclosing_parens_tokens(sb_rhs)
                    if (
                        len(spec_rhs) == 1
                        and spec_rhs[0][0] == "Ident"
                        and str(spec_rhs[0][1]).startswith("Mir.")
                        and str(spec_rhs[0][1]).endswith(".body")
                    ):
                        ref_s = str(spec_rhs[0][1])[len("Mir.") : -len(".body")]
                        if ref_s:
                            equiv_spec_body_suffix = ref_s
                        else:
                            raise Failure(
                                1, FAULT_COVERAGE_PHASE, f"empty `Mir.<Ref>.body` in {label}"
                            )
                    else:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"`StatefulEquivItemSpec.specBody` in {label} must be an exact `Mir.<Ref>.body` reference",
                        )

    if ns_opens != ns_closes or ns_opens > 1:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"{label} has unbalanced or repeated `namespace {expected_ns}` blocks",
        )

    own_ob_prefix = f"Obligations.{subject_suffix}."
    own_default_mod_env = f"Obligations.{subject_suffix}.defaultModularSpec.envAssumed"
    for stem in raw_modular_stems:
        if stem in ("defaultModularSpec.envAssumed", own_default_mod_env):
            delegates_to_default_modular_spec_env = True
        elif stem.startswith("Obligations.") and (
            stem.endswith(".defaultCallContract")
            or stem.endswith(".ubExceptionClaim.callContract")
        ):
            rest = stem[len("Obligations.") :]
            if rest.endswith(".defaultCallContract"):
                callee = rest[: -len(".defaultCallContract")]
                kind = "defaultCallContract"
            else:
                callee = rest[: -len(".ubExceptionClaim.callContract")]
                kind = "ubExceptionCallContract"
            if not callee or callee == subject_suffix:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{label} `ModularItemSpec.envAssumed` cannot self-assume `Obligations.{subject_suffix}`'s own callContract",
                )
            if callee not in imported_obligation_suffixes:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{label} references `{stem}.holdsOn` without `import Obligations.{callee}`",
                )
            if (callee, kind) not in sibling_modular_contracts:
                sibling_modular_contracts.append((callee, kind))
        elif stem.startswith(own_ob_prefix):
            local_ext = stem[len(own_ob_prefix) :]
            if local_ext and "." not in local_ext:
                if local_ext not in referenced_subject_external_contract_idents:
                    referenced_subject_external_contract_idents.append(local_ext)
            else:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{label} `ModularItemSpec.envAssumed` references unsupported contract `{stem}.holdsOn`",
                )
        elif "." not in stem and (
            stem == "defaultExternalCallContract" or stem.startswith("externalCallContract_")
        ):
            if stem not in referenced_subject_external_contract_idents:
                referenced_subject_external_contract_idents.append(stem)
        else:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{label} `ModularItemSpec.envAssumed` references unsupported contract `{stem}.holdsOn`",
            )

    return {
        "declared_spec_def_ids": declared_spec_def_ids,
        "declared_spec_classes": declared_spec_classes,
        "has_modular_spec_instance": has_modular_spec_instance,
        "delegates_to_default_modular_spec_env": delegates_to_default_modular_spec_env,
        "imported_obligation_suffixes": imported_obligation_suffixes,
        "imported_mir_suffixes": imported_mir_suffixes,
        "imported_specs_suffixes": imported_specs_suffixes,
        "sibling_modular_contracts": sibling_modular_contracts,
        "referenced_subject_external_contract_idents": referenced_subject_external_contract_idents,
        "has_equiv_spec_instance": has_equiv_spec_instance,
        "equiv_spec_body_suffix": equiv_spec_body_suffix,
    }


def _validate_auxiliary_module_no_spec_override(
    aux_text: str,
    aux_label: str,
    subject_suffix: str,
    verify_imports_specs: bool,
) -> dict[str, list[str]]:
    """`[adv ep2-A1]` Port of Rust `validate_auxiliary_module_no_spec_override`: verify
    that `Proof/<X>.lean` or `Assumptions/<X>.lean` introduces no `*ItemSpec` overrides,
    `@[instance]`, `attribute`, `local`, `scoped`, or unauthorized imports."""
    tokens = _tokenize_lean_or_fail(aux_text, aux_label)
    # `[adv ep2-B2]`: `aux_label` is the module name (`Proof.<X>` / `Assumptions.<X>`), so
    # it is also the namespace every declaration of this module must live under.
    _check_module_scope_confinement(
        tokens, aux_label, aux_label, allow_nested=True, allow_sections=True
    )
    attr = _verify_detect_instance_attribute(tokens)
    if attr is not None:
        raise Failure(1, FAULT_COVERAGE_PHASE, f"disallowed `@[{attr}]` attribute in {aux_label}")
    _reject_meta_commands(tokens, aux_label)
    imported_sibling_specs: list[str] = []
    imported_proof_suffixes: list[str] = []
    imported_assumptions_suffixes: list[str] = []
    imported_mir_suffixes: list[str] = []
    n = len(tokens)
    top = _top_level_token_indices(tokens)
    top_set = set(top)

    def command_end(start: int) -> int:
        k = start + 1
        while k < n and not (k in top_set and _fc_is_lean_command_start(tokens[k])):
            k += 1
        return k

    for idx in top:
        tk, val = tokens[idx]
        if tk != "Ident":
            continue
        if val in (
            "macro",
            "macro_rules",
            "syntax",
            "notation",
            "infix",
            "infixl",
            "infixr",
            "prefix",
            "postfix",
            "elab",
            "elab_rules",
            "deriving",
            "initialize",
            "builtin_initialize",
            "local",
            "scoped",
            "attribute",
            "class",
            "unsafe",
            "partial",
            "export",
        ):
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"disallowed top-level `{val}` command in {aux_label}"
            )
        if val == "open":
            _check_specs_or_aux_open_command(tokens, idx, aux_label, is_aux=True)
            continue
        if val in ("def", "theorem", "lemma"):
            if idx + 1 < n and tokens[idx + 1][0] == "Ident":
                decl_name = str(tokens[idx + 1][1])
                if decl_name.startswith(("Obligations.", "Mir.", "Trusted.")):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{aux_label} shadows reserved namespace declaration `{decl_name}`",
                    )
            for t_c, v_c in tokens[idx : command_end(idx)]:
                if t_c == "Ident" and (
                    _strip_verification_result_qual(str(v_c)) in _VERIFY_SPEC_CLASS_NAMES
                    or str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{aux_label} references `{v_c}` inside `{val}` declaration",
                    )
        elif val in ("structure", "inductive"):
            for t_c, v_c in tokens[idx : command_end(idx)]:
                if t_c == "Ident" and (
                    _strip_verification_result_qual(str(v_c)) in _VERIFY_SPEC_CLASS_NAMES
                    or str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{aux_label} references `{v_c}` inside `{val}` declaration",
                    )
        elif val == "import":
            if idx + 1 >= n or tokens[idx + 1][0] != "Ident":
                raise Failure(1, FAULT_COVERAGE_PHASE, f"malformed `import` in {aux_label}")
            mod = str(tokens[idx + 1][1])
            if not _is_allowed_aux_import(mod):
                raise Failure(
                    1, FAULT_COVERAGE_PHASE, f"disallowed `import {mod}` in {aux_label}"
                )
            if mod.startswith("Specs."):
                spec_suf = mod[len("Specs.") :]
                if spec_suf == subject_suffix:
                    if not verify_imports_specs:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{aux_label} imports `Specs.{subject_suffix}`, which is not imported by `Verify.{subject_suffix}`",
                        )
                elif spec_suf not in imported_sibling_specs:
                    imported_sibling_specs.append(spec_suf)
            elif mod.startswith("Proof."):
                psuf = mod[len("Proof.") :]
                if psuf not in imported_proof_suffixes:
                    imported_proof_suffixes.append(psuf)
            elif mod.startswith("Assumptions."):
                asuf = mod[len("Assumptions.") :]
                if asuf not in imported_assumptions_suffixes:
                    imported_assumptions_suffixes.append(asuf)
            elif mod.startswith("Mir."):
                msuf = mod[len("Mir.") :]
                if msuf and msuf not in imported_mir_suffixes:
                    imported_mir_suffixes.append(msuf)
        elif val == "abbrev":
            for t_c, v_c in tokens[idx : command_end(idx)]:
                if t_c == "Ident" and (
                    _strip_verification_result_qual(str(v_c)) in _VERIFY_SPEC_CLASS_NAMES
                    or str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"{aux_label} aliases `{v_c}` via `abbrev` (specification instances must reside in `Specs.{subject_suffix}`)",
                    )
        elif val == "instance":
            cmd_slice = tokens[idx : command_end(idx)]
            header_end = len(cmd_slice)
            h_depth = 0
            for h_pos, (t_h, v_h) in enumerate(cmd_slice):
                if h_depth == 0 and (t_h == "ColonEq" or (t_h, v_h) == ("Ident", "where")):
                    header_end = h_pos
                    break
                if t_h in ("LParen", "LBrace", "LBracket"):
                    h_depth += 1
                elif t_h in ("RParen", "RBrace", "RBracket"):
                    h_depth = max(0, h_depth - 1)
            header = cmd_slice[:header_end]
            if not any(t_h == "Colon" for t_h, _ in header):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"{aux_label} declares an `instance` without an explicit `: <ClassName>` type signature",
                )
            for t_c, v_c in cmd_slice:
                if t_c == "Ident":
                    short_cls = _strip_verification_result_qual(str(v_c))
                    if short_cls in _VERIFY_SPEC_CLASS_NAMES:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{aux_label} declares a `{short_cls}` specification override instance (must reside in `Specs.{subject_suffix}`)",
                        )
                    if str(v_c).rsplit(".", 1)[-1] in _VERIFY_REFINE_SPEC_HELPERS:
                        raise Failure(
                            1,
                            FAULT_COVERAGE_PHASE,
                            f"{aux_label} invokes `{v_c}` inside an `instance` declaration",
                        )
    return {
        "imported_sibling_specs": imported_sibling_specs,
        "imported_proof_suffixes": imported_proof_suffixes,
        "imported_assumptions_suffixes": imported_assumptions_suffixes,
        "imported_mir_suffixes": imported_mir_suffixes,
    }


def _validate_sibling_specs_no_subject_override(
    specs_text: str, sibling_suffix: str, subject_def_path: str
) -> list[str]:
    """`[adv ep2-A1]` Port of Rust `validate_sibling_specs_no_subject_override`: verify
    that a transitively imported sibling `Specs.<Other>` module declares no `*ItemSpec`
    instance targeting `subject_def_path`."""
    label = f"sibling Specs.{sibling_suffix}"
    scan = _scan_specs_module(specs_text, sibling_suffix, label)
    if subject_def_path in scan["declared_spec_def_ids"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"imported sibling `Specs.{sibling_suffix}` declares an `*ItemSpec` override for subject `{subject_def_path}`",
        )
    return list(scan["imported_specs_suffixes"])


def _parse_fault_census_receipt_json(receipt_path: Path) -> dict[str, Any]:
    regular(receipt_path, FAULT_COVERAGE_PHASE)
    try:
        raw = json.loads(receipt_path.read_text(encoding="utf-8", errors="strict"))
    except (ValueError, OSError, UnicodeDecodeError) as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"malformed FaultCensus receipt {receipt_path}: {err}",
        ) from err
    expected_keys = {
        "def_path",
        "mir_module_sha256",
        "census_sites",
        "discharged_sites",
        "callee_closure",
        "reconciliation_verdict",
        "is_verified",
        "reasons",
    }
    if not isinstance(raw, dict) or set(raw) != expected_keys:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"unexpected schema keys in FaultCensus receipt {receipt_path}",
        )
    if not isinstance(raw["def_path"], str) or not raw["def_path"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid def_path in FaultCensus receipt {receipt_path}",
        )
    if not isinstance(raw["mir_module_sha256"], str) or not re.fullmatch(
        r"[0-9a-f]{64}", raw["mir_module_sha256"]
    ):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid mir_module_sha256 in FaultCensus receipt {receipt_path}",
        )
    if not isinstance(raw["census_sites"], list) or not isinstance(
        raw["discharged_sites"], list
    ):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"census_sites and discharged_sites must be lists in {receipt_path}",
        )
    try:
        census_sites = [FaultSite.from_dict(s) for s in raw["census_sites"]]
        discharged_sites = [FaultSite.from_dict(s) for s in raw["discharged_sites"]]
    except ValueError as err:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid FaultSite entry in {receipt_path}: {err}",
        ) from err

    cc = raw["callee_closure"]
    if not isinstance(cc, dict) or set(cc) != {
        "inline_callees",
        "external_callees",
        "allow_unresolved_indirect_calls",
    }:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid callee_closure in {receipt_path}",
        )
    if (
        not isinstance(cc["inline_callees"], list)
        or not all(isinstance(x, str) and x for x in cc["inline_callees"])
        or not isinstance(cc["external_callees"], list)
        or not all(isinstance(x, str) and x for x in cc["external_callees"])
        or type(cc["allow_unresolved_indirect_calls"]) is not bool
    ):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid callee_closure field types in {receipt_path}",
        )
    if (
        not isinstance(raw["reconciliation_verdict"], str)
        or type(raw["is_verified"]) is not bool
        or not isinstance(raw["reasons"], list)
        or not all(isinstance(r, str) for r in raw["reasons"])
    ):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"invalid verdict fields in {receipt_path}",
        )
    return {
        "def_path": raw["def_path"],
        "mir_module_sha256": raw["mir_module_sha256"],
        "census_sites": census_sites,
        "discharged_sites": discharged_sites,
        "callee_closure": cc,
        "reconciliation_verdict": raw["reconciliation_verdict"],
        "is_verified": raw["is_verified"],
        "reasons": raw["reasons"],
    }


def _check_trait_impl_closure(
    subject_meta: dict[str, Any],
    callee_metas: list[dict[str, Any]],
    closure: dict[str, Any],
) -> list[str]:
    if closure.get("allow_unresolved_indirect_calls", False):
        return []
    all_metas = [subject_meta, *callee_metas]
    referenced: set[str] = set()
    for meta in all_metas:
        referenced.update(direct_callee_def_paths(meta["body"]))
        referenced.update(reified_fn_def_paths(meta["body"]))
    while True:
        changed = False
        for meta in all_metas:
            for entry in meta.get("trait_impls", ()):
                tm = entry["trait_method_def_path"]
                imp = entry["impl_path"]
                if tm in referenced and imp and imp not in referenced:
                    referenced.add(imp)
                    changed = True
        if not changed:
            break
    inline_set = set(closure.get("inline_callees", ()))
    external_set = set(closure.get("external_callees", ()))
    reasons: list[str] = []
    for meta in all_metas:
        for entry in meta.get("trait_impls", ()):
            tm = entry["trait_method_def_path"]
            imp = entry["impl_path"]
            if (
                tm in referenced
                and imp != tm
                and imp not in inline_set
                and imp not in external_set
            ):
                msg = (
                    f"[{meta['body']['def_path']}] TraitImplEntry for `{tm}` redirects `lookupCallee` to `{imp}` "
                    "which is neither an inline callee nor an external callee in CalleeClosure"
                )
                if msg not in reasons:
                    reasons.append(msg)
    return reasons


def _check_companion_bindings(
    ob_scan: dict[str, Any],
    owner_def_path: str,
    mir_by_stem: dict[str, dict[str, Any]],
    ob_label: str,
) -> None:
    """`[adv ep2-B3]` Every `__anodized_fn_requires_*` / `__anodized_fn_ensures_*` companion
    that `defaultPre`/`defaultPost`(`For`) or an `externalSpecCallContract` evaluates must be the
    captured companion OF THAT subject / external target (`ContractRole.requires "<defPath>"`
    / `ContractRole.ensures "<defPath>"`). Otherwise `defaultPre` could evaluate some other
    function's (e.g. always-false) `requires` companion, making every claim vacuous while each
    clause still has the generated `MirBoolPredicateHolds Mir.<companion>.body args` shape.
    """
    for comp_suf, kind, expected_owner, context in ob_scan.get("companion_bindings", ()):
        comp_meta = mir_by_stem.get(comp_suf.replace(".", "/"))
        owner = owner_def_path if expected_owner is None else expected_owner
        if comp_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{context} in {ob_label} evaluates companion `Mir.{comp_suf}.body`, but `Mir/{comp_suf.replace('.', '/')}.lean` is missing",
            )
        if comp_meta["role"] != (kind, owner):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"{context} in {ob_label} evaluates companion `Mir.{comp_suf}.body` whose role is "
                f"`{comp_meta['role']}` instead of `ContractRole.{kind} \"{owner}\"`",
            )


def _audit_single_item_receipt(
    rel_stem: str,
    mir_path: Path,
    mir_meta: dict[str, Any],
    receipt_path: Path,
    mir_by_stem: dict[str, dict[str, Any]],
    receipt_files: dict[str, Path],
    obligations_root: Path | None,
    verify_root: Path | None,
    specs_root: Path | None,
    proofs_root: Path | None,
    gen_assumptions_root: Path | None,
    reg: dict[str, dict[str, str]],
) -> dict[str, Any]:
    """Independently re-audit one `FaultCensus/<Item>.json` receipt (`[adv ep2-B1]` / `[adv ep2-A1]`)."""
    receipt = _parse_fault_census_receipt_json(receipt_path)
    actual_sha = digest(mir_path)
    if receipt["mir_module_sha256"] != actual_sha:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt SHA-256 mismatch for {rel_stem}: receipt={receipt['mir_module_sha256']}, Mir={actual_sha}",
        )
    subject_body = mir_meta["body"]
    if receipt["def_path"] != subject_body["def_path"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt def_path `{receipt['def_path']}` does not match Mir `{subject_body['def_path']}` in {receipt_path}",
        )
    if mir_meta["role"][0] != "subject":
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt {receipt_path} audits Mir module `{rel_stem}` whose role is `{mir_meta['role'][0]}` instead of `subject`",
        )
    actual_census = census_mir_fault_sites(subject_body)
    if receipt["census_sites"] != actual_census:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt census_sites in {receipt_path} is stale or tampered relative to independent census_lean_mir_module ({len(receipt['census_sites'])} vs {len(actual_census)} sites)",
        )
    emitted = emit_mir_obligation_fault_sites(subject_body)
    if receipt["discharged_sites"] != emitted:
        missing = [str(s) for s in emitted if s not in set(receipt["discharged_sites"])]
        extra = [str(s) for s in receipt["discharged_sites"] if s not in set(emitted)]
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt discharged_sites in {receipt_path} does not match the independent obligation emitter "
            f"(omitted={missing[:8]}, unbacked={extra[:8]}, receipt={len(receipt['discharged_sites'])} vs emitted={len(emitted)} sites)",
        )
    if (
        not receipt["is_verified"]
        or receipt["reconciliation_verdict"] != "VERIFIED"
        or receipt["reasons"]
    ):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt {receipt_path} is not VERIFIED (verdict={receipt['reconciliation_verdict']!r}, is_verified={receipt['is_verified']}, reasons={receipt['reasons']})",
        )

    single_verdict = reconcile_obligation_coverage(actual_census, emitted, reg)
    if not single_verdict["is_verified"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"obligation coverage reconciliation failed for {receipt['def_path']} ({receipt_path}): {'; '.join(single_verdict['reasons'])}",
        )

    suffix = rel_stem.replace("/", ".")
    closure = receipt["callee_closure"]

    # 1. `inline_callees` must be exactly the `defaultCallees` installed into
    #    `s.memory.callees` by `Obligations/<Item>.lean` (both directions), and
    #    every claim in `Obligations/<Item>.lean` must bind `Mir.<Item>.body` + `defaultCallees`.
    if obligations_root is None:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing Obligations directory for FaultCensus receipt {receipt_path}",
        )
    ob_path = obligations_root / f"{rel_stem}.lean"
    ob_text = _read_regular_text(ob_path, f"Obligations module for `{rel_stem}`")
    ob_scan = _scan_obligations_module(
        ob_text,
        suffix,
        str(ob_path),
        expected_def_path=subject_body["def_path"],
        expected_mir_sha256=actual_sha,
    )
    inline_metas: list[dict[str, Any]] = []
    for suf in ob_scan["default_callee_suffixes"]:
        callee_meta = mir_by_stem.get(suf.replace(".", "/"))
        if callee_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Obligations module {ob_path} lists `Mir.{suf}.body` in `defaultCallees`, but `Mir/{suf.replace('.', '/')}.lean` is missing",
            )
        inline_metas.append(callee_meta)
    expected_inline = [m["body"]["def_path"] for m in inline_metas]
    if len(set(expected_inline)) != len(expected_inline):
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"duplicate `defaultCallees` entries in {ob_path}: {expected_inline}",
        )
    if len(set(closure["inline_callees"])) != len(closure["inline_callees"]) or set(
        closure["inline_callees"]
    ) != set(expected_inline):
        missing_inline = sorted(set(expected_inline) - set(closure["inline_callees"]))
        extra_inline = sorted(set(closure["inline_callees"]) - set(expected_inline))
        if missing_inline:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Obligations module {ob_path} links inline callee(s) {missing_inline} via `defaultCallees`, which are missing from FaultCensus `callee_closure.inline_callees`",
            )
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus `callee_closure.inline_callees` in {receipt_path} declares {extra_inline or closure['inline_callees']} that `Obligations/{rel_stem}.lean` `defaultCallees` never installs",
        )

    # Validate sidecar MIR modules of any `externalSpecCallContract` in `Obligations/<Item>.lean`.
    for ext in ob_scan["external_spec_contracts"]:
        sidecar_stem = ext["sidecar_mir_suffix"].replace(".", "/")
        sidecar_meta = mir_by_stem.get(sidecar_stem)
        if sidecar_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Obligations module {ob_path} binds `externalSpecCallContract` `{ext['def_ident']}` to missing `Mir/{sidecar_stem}.lean`",
            )
        if sidecar_meta["role"] != ("externalSpec", ext["target_def_path"]):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"sidecar `Mir.{ext['sidecar_mir_suffix']}` for `externalSpecCallContract \"{ext['target_def_path']}\"` has role `{sidecar_meta['role']}` instead of `ContractRole.externalSpec \"{ext['target_def_path']}\"`",
            )

    _check_companion_bindings(ob_scan, subject_body["def_path"], mir_by_stem, str(ob_path))

    # `[adv ep2-A2]`: Validate every imported `Mir.<Suffix>` and `defaultSpecCallees` entry
    # in `Obligations/<Item>.lean` exists in `mir_by_stem` and reconciles cleanly.
    for aux_mir_suf in [*ob_scan["imported_mir_suffixes"], *ob_scan["default_spec_callee_suffixes"]]:
        aux_mir_stem = aux_mir_suf.replace(".", "/")
        aux_mir_meta = mir_by_stem.get(aux_mir_stem)
        if aux_mir_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Obligations module {ob_path} references `Mir.{aux_mir_suf}`, but `Mir/{aux_mir_stem}.lean` is missing",
            )
        aux_body = aux_mir_meta["body"]
        aux_verdict = reconcile_obligation_coverage(
            census_mir_fault_sites(aux_body),
            emit_mir_obligation_fault_sites(aux_body),
            reg,
        )
        if not aux_verdict["is_verified"]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"imported `Mir.{aux_mir_suf}` in {ob_path} failed obligation coverage reconciliation: {'; '.join(aux_verdict['reasons'])}",
            )

    # 2. Verify `Verify/<Item>.lean` surface, active claim binding in `Obligations/<Item>.lean`,
    #    and transitive `Specs.*` / `Proof.*` / `Assumptions.*` import cone.
    if verify_root is None:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing Verify directory for FaultCensus receipt {receipt_path}",
        )
    v_path = verify_root / f"{rel_stem}.lean"
    v_text = _read_regular_text(v_path, f"Verify module for `{rel_stem}`")
    surface = _scan_verify_module_surface(v_text, suffix, str(v_path))
    active_claim = surface["claim"]
    if active_claim not in ob_scan["declared_claims"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"`Verify/{rel_stem}.lean` proves `Obligations.{suffix}.{active_claim}`, which is not defined in {ob_path}",
        )
    if active_claim in _POLY_CLAIM_TO_FOR:
        _, claim_for_name = _POLY_CLAIM_TO_FOR[active_claim]
        if (
            claim_for_name not in ob_scan["declared_claims"]
            or "polyCertificate" not in ob_scan["declared_helpers"]
            or "artifactIdentity" not in ob_scan["declared_canonical_defs"]
        ):
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`Verify/{rel_stem}.lean` proves `{active_claim}`, but `{claim_for_name}` or `polyCertificate` is missing in {ob_path}",
            )

    specs_scan: dict[str, Any] | None = None
    specs_queue: list[str] = []
    cone_mir_suffixes: list[str] = list(surface["imported_mir_suffixes"])
    if surface["imports_specs"]:
        if specs_root is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`Verify.{suffix}` imports `Specs.{suffix}`, but no `anneal/proofs/Specs` directory exists",
            )
        specs_path = specs_root / f"{rel_stem}.lean"
        specs_text = _read_regular_text(specs_path, f"Specs module for `{rel_stem}`")
        specs_scan = _scan_specs_module(specs_text, suffix, str(specs_path))
        for did in specs_scan["declared_spec_def_ids"]:
            if did != subject_body["def_path"]:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Specs.{suffix} ({specs_path}) declares an `*ItemSpec` instance for `{did}` instead of subject `{subject_body['def_path']}`",
                )
        specs_queue.extend(specs_scan["imported_specs_suffixes"])
        cone_mir_suffixes.extend(specs_scan["imported_mir_suffixes"])
    elif specs_root is not None:
        specs_path = specs_root / f"{rel_stem}.lean"
        if specs_path.exists() or specs_path.is_symlink():
            specs_text = _read_regular_text(specs_path, f"Specs module for `{rel_stem}`")
            specs_scan = _scan_specs_module(specs_text, suffix, str(specs_path))
            for did in specs_scan["declared_spec_def_ids"]:
                if did != subject_body["def_path"]:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"Specs.{suffix} ({specs_path}) declares an `*ItemSpec` instance for `{did}` instead of subject `{subject_body['def_path']}`",
                    )
            cone_mir_suffixes.extend(specs_scan["imported_mir_suffixes"])

    # Walk transitive `Proof.*` / `Assumptions.*` / sibling `Specs.*` import cone.
    proof_queue = list(surface["imported_proof_suffixes"])
    assump_queue = list(surface["imported_assumptions_suffixes"])
    visited_proof: set[str] = set()
    visited_assump: set[str] = set()
    visited_sib_specs: set[str] = set()
    while proof_queue or assump_queue or specs_queue:
        while proof_queue:
            psuf = proof_queue.pop(0)
            if psuf in visited_proof:
                continue
            visited_proof.add(psuf)
            if proofs_root is None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`Verify.{suffix}` imports `Proof.{psuf}`, but no `anneal/proofs/Proof` directory exists",
                )
            ppath = proofs_root / "Proof" / f"{psuf.replace('.', '/')}.lean"
            ptext = _read_regular_text(ppath, f"Proof.{psuf}")
            aux = _validate_auxiliary_module_no_spec_override(
                ptext, f"Proof.{psuf}", suffix, surface["imports_specs"]
            )
            specs_queue.extend(aux["imported_sibling_specs"])
            proof_queue.extend(aux["imported_proof_suffixes"])
            assump_queue.extend(aux["imported_assumptions_suffixes"])
            cone_mir_suffixes.extend(aux["imported_mir_suffixes"])
        while assump_queue:
            asuf = assump_queue.pop(0)
            if asuf in visited_assump:
                continue
            visited_assump.add(asuf)
            rel_a = f"{asuf.replace('.', '/')}.lean"
            cand_paths: list[Path] = []
            if proofs_root is not None:
                ap = proofs_root / "Assumptions" / rel_a
                if ap.exists() or ap.is_symlink():
                    cand_paths.append(ap)
            if gen_assumptions_root is not None:
                gp = gen_assumptions_root / rel_a
                if gp.exists() or gp.is_symlink():
                    cand_paths.append(gp)
            if not cand_paths:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`Verify.{suffix}` imports missing `Assumptions.{asuf}`",
                )
            for cpath in cand_paths:
                atext = _read_regular_text(cpath, f"Assumptions.{asuf}")
                aux = _validate_auxiliary_module_no_spec_override(
                    atext, f"Assumptions.{asuf}", suffix, surface["imports_specs"]
                )
                specs_queue.extend(aux["imported_sibling_specs"])
                proof_queue.extend(aux["imported_proof_suffixes"])
                assump_queue.extend(aux["imported_assumptions_suffixes"])
                cone_mir_suffixes.extend(aux["imported_mir_suffixes"])
        while specs_queue:
            sib_suf = specs_queue.pop(0)
            if sib_suf == suffix:
                if not surface["imports_specs"]:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"import cone of `Verify.{suffix}` transitively imports `Specs.{suffix}`, which is not imported by `Verify.{suffix}`",
                    )
                continue
            if sib_suf in visited_sib_specs:
                continue
            visited_sib_specs.add(sib_suf)
            if specs_root is None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"import cone of `Verify.{suffix}` imports missing `Specs.{sib_suf}`",
                )
            spath = specs_root / f"{sib_suf.replace('.', '/')}.lean"
            stext = _read_regular_text(spath, f"Specs.{sib_suf}")
            sib_scan = _scan_specs_module(stext, sib_suf, f"sibling Specs.{sib_suf}")
            if subject_body["def_path"] in sib_scan["declared_spec_def_ids"]:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"imported sibling `Specs.{sib_suf}` declares an `*ItemSpec` override for subject `{subject_body['def_path']}`",
                )
            specs_queue.extend(sib_scan["imported_specs_suffixes"])
            cone_mir_suffixes.extend(sib_scan["imported_mir_suffixes"])

    seen_cone_mir: set[str] = set()
    for cone_mir_suf in cone_mir_suffixes:
        if cone_mir_suf in seen_cone_mir:
            continue
        seen_cone_mir.add(cone_mir_suf)
        cone_mir_stem = cone_mir_suf.replace(".", "/")
        cone_mir_meta = mir_by_stem.get(cone_mir_stem)
        if cone_mir_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"import cone of `Verify.{suffix}` imports `Mir.{cone_mir_suf}`, but `Mir/{cone_mir_stem}.lean` is missing or unregistered",
            )
        cone_body = cone_mir_meta["body"]
        cone_verdict = reconcile_obligation_coverage(
            census_mir_fault_sites(cone_body),
            emit_mir_obligation_fault_sites(cone_body),
            reg,
        )
        if not cone_verdict["is_verified"]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"imported `Mir.{cone_mir_suf}` in import cone of `Verify.{suffix}` failed obligation coverage reconciliation: {'; '.join(cone_verdict['reasons'])}",
            )

    if closure["allow_unresolved_indirect_calls"] and not surface["assumed"]:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus receipt {receipt_path} sets `allow_unresolved_indirect_calls`, but `Verify/{rel_stem}.lean` proves `{surface['claim']}` without assuming the subject's own body",
        )
    if closure["external_callees"] and not surface["assumed"]:
        if not surface["modular"]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"FaultCensus receipt {receipt_path} declares external callees {closure['external_callees']}, but `Verify/{rel_stem}.lean` proves non-modular `{surface['claim']}`",
            )
        ext_by_ident = {
            e["def_ident"]: e["target_def_path"] for e in ob_scan["external_spec_contracts"]
        }
        justified: set[str] = set()
        sibling_deps: list[tuple[str, str]] = []
        if (
            surface["imports_specs"]
            and specs_scan is not None
            and specs_scan["has_modular_spec_instance"]
        ):
            if specs_scan["delegates_to_default_modular_spec_env"]:
                if ob_scan["default_modular_spec_count"] != 1:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`Specs.{suffix}` delegates to `defaultModularSpec.envAssumed`, which is missing in {ob_path}",
                    )
                justified.update(ext_by_ident.values())
                for csuf in ob_scan["referenced_callee_contracts"]:
                    sibling_deps.append((csuf, "defaultCallContract"))
            for csuf, kind in specs_scan["sibling_modular_contracts"]:
                if (csuf, kind) not in sibling_deps:
                    sibling_deps.append((csuf, kind))
            for ext_id in specs_scan["referenced_subject_external_contract_idents"]:
                resolved_id = (
                    ob_scan["default_external_contract_alias"]
                    if ext_id == "defaultExternalCallContract"
                    else ext_id
                )
                target_dp = ext_by_ident.get(resolved_id or "")
                if target_dp is None:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"`Specs.{suffix}` `ModularItemSpec.envAssumed` references unknown external contract `{ext_id}.holdsOn`",
                    )
                justified.add(target_dp)
        else:
            if ob_scan["default_modular_spec_count"] != 1:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`Verify/{rel_stem}.lean` proves `{surface['claim']}` without `defaultModularSpec` in {ob_path}",
                )
            justified.update(ext_by_ident.values())
            for csuf in ob_scan["referenced_callee_contracts"]:
                sibling_deps.append((csuf, "defaultCallContract"))

        for sib, kind in sibling_deps:
            sib_stem = sib.replace(".", "/")
            sib_meta = mir_by_stem.get(sib_stem)
            if sib_meta is None:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`{rel_stem}` references sibling `Obligations.{sib}`, but `Mir/{sib_stem}.lean` is missing",
                )
            if sib_stem not in receipt_files:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"modular caller `{rel_stem}` assumes sibling `Obligations.{sib}`, which has no verified `FaultCensus/{sib_stem}.json` receipt",
                )
            sib_ob_path = obligations_root / f"{sib_stem}.lean"
            sib_ob_text = _read_regular_text(
                sib_ob_path, f"sibling Obligations module `Obligations.{sib}`"
            )
            sib_ob = _scan_obligations_module(
                sib_ob_text,
                sib,
                str(sib_ob_path),
                expected_def_path=sib_meta["body"]["def_path"],
            )
            sib_v_path = verify_root / f"{sib_stem}.lean"
            sib_v_text = _read_regular_text(
                sib_v_path, f"sibling Verify module `Verify.{sib}`"
            )
            sib_surface = _scan_verify_module_surface(sib_v_text, sib, str(sib_v_path))
            _check_companion_bindings(
                sib_ob, sib_meta["body"]["def_path"], mir_by_stem, str(sib_ob_path)
            )
            if kind == "defaultCallContract":
                if sib_ob["default_call_contract_def_path"] != sib_meta["body"]["def_path"]:
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"sibling `Obligations.{sib}` is missing canonical `defaultCallContract` for `{sib_meta['body']['def_path']}`",
                    )
                sib_specs_overrides = False
                if sib_surface["imports_specs"] and specs_root is not None:
                    sib_sp_path = specs_root / f"{sib_stem}.lean"
                    sib_sp_text = _read_regular_text(sib_sp_path, f"Specs.{sib}")
                    sib_sp = _scan_specs_module(sib_sp_text, sib, str(sib_sp_path))
                    expected_cls = (
                        "ItemSpec" if sib_surface["claim"] == "claim" else "TotalItemSpec"
                    )
                    sib_specs_overrides = expected_cls in sib_sp["declared_spec_classes"]
                if (
                    sib_surface["claim"] not in ("claim", "totalClaim")
                    or sib_ob["has_legacy_spec_override"]
                    or sib_specs_overrides
                ):
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"modular caller `{rel_stem}` assumes `Obligations.{sib}.defaultCallContract`, which is incompatible with `Verify.{sib}` surface `{sib_surface['claim']}`",
                    )
            else:
                if sib_surface["claim"] != "ubExceptionClaim":
                    raise Failure(
                        1,
                        FAULT_COVERAGE_PHASE,
                        f"modular caller `{rel_stem}` assumes `Obligations.{sib}.ubExceptionClaim.callContract`, which is incompatible with `Verify.{sib}` surface `{sib_surface['claim']}`",
                    )
            justified.add(sib_meta["body"]["def_path"])

        unjustified = sorted(set(closure["external_callees"]) - justified)
        if unjustified:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"FaultCensus receipt {receipt_path} declares external callee(s) {unjustified} that are backed by neither an `externalSpecCallContract` target nor an imported sibling `Obligations.<Callee>`",
            )

    # 3. Reconcile every inline callee body (and `equivClaim` reference `specBody`)
    #    with independently emitted obligations.
    batch_items: list[dict[str, Any]] = [
        {
            "def_path": subject_body["def_path"],
            "body": subject_body,
            "discharged": emitted,
        }
    ]
    callee_metas: list[dict[str, Any]] = []
    seen_dps = {subject_body["def_path"]}
    for c_meta in inline_metas:
        c_dp = c_meta["body"]["def_path"]
        if c_dp in seen_dps:
            continue
        seen_dps.add(c_dp)
        callee_metas.append(c_meta)
        batch_items.append(
            {
                "def_path": c_dp,
                "body": c_meta["body"],
                "discharged": emit_mir_obligation_fault_sites(c_meta["body"]),
            }
        )

    batch_verdict = reconcile_multi_item_coverage(batch_items, closure, reg)
    trait_reasons = _check_trait_impl_closure(mir_meta, callee_metas, closure)
    all_reasons = [*batch_verdict["reasons"], *trait_reasons]

    if surface["equiv"]:
        ref_suffix: str | None = None
        if (
            surface["imports_specs"]
            and specs_scan is not None
            and specs_scan["has_equiv_spec_instance"]
        ):
            ref_suffix = specs_scan["equiv_spec_body_suffix"]
            if (
                ref_suffix is not None
                and ref_suffix != suffix
                and ref_suffix not in specs_scan["imported_mir_suffixes"]
            ):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`Specs.{suffix}` binds `StatefulEquivItemSpec` to `Mir.{ref_suffix}.body` without `import Mir.{ref_suffix}`",
                )
        else:
            ref_suffix = ob_scan["rust_equiv_spec_body_suffix"]
            if (
                ref_suffix is not None
                and ref_suffix != suffix
                and ref_suffix not in ob_scan["imported_mir_suffixes"]
            ):
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"`Obligations.{suffix}` binds `rustEquivSpec` to `Mir.{ref_suffix}.body` without `import Mir.{ref_suffix}`",
                )
        if not ref_suffix:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"`Verify.{suffix}` proves `equivClaim`, but neither `Specs.{suffix}` nor `Obligations.{suffix}` declares a `StatefulEquivItemSpec` reference body",
            )
        ref_meta = mir_by_stem.get(ref_suffix.replace(".", "/"))
        if ref_meta is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing reference MIR module `Mir/{ref_suffix.replace('.', '/')}.lean` for `equivClaim` of `{rel_stem}`",
            )
        ref_body = ref_meta["body"]
        spec_batch_items: list[dict[str, Any]] = [
            {
                "def_path": ref_body["def_path"],
                "body": ref_body,
                "discharged": emit_mir_obligation_fault_sites(ref_body),
            }
        ]
        seen_spec_dps = {ref_body["def_path"]}
        for c_meta in callee_metas:
            c_dp = c_meta["body"]["def_path"]
            if c_dp in seen_spec_dps:
                continue
            seen_spec_dps.add(c_dp)
            spec_batch_items.append(
                {
                    "def_path": c_dp,
                    "body": c_meta["body"],
                    "discharged": emit_mir_obligation_fault_sites(c_meta["body"]),
                }
            )
        spec_verdict = reconcile_multi_item_coverage(spec_batch_items, closure, reg)
        spec_trait_reasons = _check_trait_impl_closure(ref_meta, callee_metas, closure)
        if not spec_verdict["is_verified"] or spec_trait_reasons:
            all_reasons.extend(spec_verdict["reasons"])
            all_reasons.extend(spec_trait_reasons)

    if not batch_verdict["is_verified"] or all_reasons:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"multi-item fault-coverage reconciliation failed for {receipt['def_path']}: {'; '.join(all_reasons)}",
        )
    return receipt


def _collect_regular_files_by_suffix(
    root_dir: Path, suffix: str
) -> dict[str, Path]:
    if root_dir.is_symlink() or not root_dir.is_dir():
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"expected regular directory: {root_dir}",
        )
    out: dict[str, Path] = {}
    for directory, dirs, files in os.walk(root_dir, followlinks=False):
        dirs.sort()
        for dname in dirs:
            dpath = Path(directory) / dname
            if dpath.is_symlink():
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"symlinked directory not allowed: {dpath}",
                )
        for fname in sorted(files):
            if not fname.endswith(suffix):
                continue
            fpath = Path(directory) / fname
            regular(fpath, FAULT_COVERAGE_PHASE)
            rel = fpath.relative_to(root_dir).as_posix()
            stem = rel[: -len(suffix)]
            out[stem] = fpath
    return out


def _should_audit_manifest_fault_coverage(
    root: Path,
    lean_audit_targets: list[tuple[str, Path]],
    *,
    require_fault_coverage: bool = False,
) -> bool:
    if require_fault_coverage:
        return True
    if (root / "FaultCensus").exists() or (
        root / ".anneal/generated/FaultCensus"
    ).exists():
        return True
    for _mir_rel, mir_path in lean_audit_targets:
        try:
            txt = mir_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if "CapturedMir" in txt or "def body" in txt:
            return True
    return False


def _audit_manifest_targets_fault_coverage(
    manifest: dict[str, Any],
    root: Path,
    lean_audit_targets: list[tuple[str, Path]],
    *,
    registry: object = None,
    require_receipts: bool = False,
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=True)
    mir_by_stem: dict[str, dict[str, Any]] = {}
    mir_path_by_stem: dict[str, Path] = {}
    generated_root: Path | None = None

    for target_entry, (mir_rel, mir_path) in zip(
        manifest["targets"], lean_audit_targets
    ):
        try:
            mir_text = mir_path.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeDecodeError) as err:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"cannot read {mir_rel}: {err}"
            ) from err
        try:
            meta = parse_lean_mir_module_metadata_strict(mir_text)
        except CensusScanError as err:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Mir target {mir_rel} failed strict fault-site census scan: {err}",
            ) from err
        if meta["body"]["def_path"] != target_entry["def_id"]:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"CaptureManifest target def_id `{target_entry['def_id']}` does not match Mir defPath `{meta['body']['def_path']}` in {mir_rel}",
            )
        norm_rel = mir_rel.removeprefix("./")
        if norm_rel.startswith(".anneal/generated/Mir/") and norm_rel.endswith(".lean"):
            stem = norm_rel[len(".anneal/generated/Mir/") : -len(".lean")]
            generated_root = root / ".anneal/generated"
        elif norm_rel.startswith("Mir/") and norm_rel.endswith(".lean"):
            stem = norm_rel[len("Mir/") : -len(".lean")]
            if generated_root is None:
                generated_root = root
        else:
            stem = norm_rel[: -len(".lean")]
            if generated_root is None:
                generated_root = root
        if stem in mir_by_stem:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"duplicate Mir module stem `{stem}` in CaptureManifest.json",
            )
        _check_mir_module_namespace_binding(mir_text, stem, mir_rel)
        mir_by_stem[stem] = meta
        mir_path_by_stem[stem] = mir_path

    fc_root: Path | None = None
    if generated_root is not None and (generated_root / "FaultCensus").exists():
        fc_root = generated_root / "FaultCensus"
    elif (root / ".anneal/generated/FaultCensus").exists():
        fc_root = root / ".anneal/generated/FaultCensus"
    elif (root / "FaultCensus").exists():
        fc_root = root / "FaultCensus"

    if fc_root is None:
        if require_receipts:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing FaultCensus directory for CaptureManifest under {root}",
            )
        return {
            "mirTargetsAudited": len(mir_by_stem),
            "receiptsAudited": 0,
        }

    receipt_files = _collect_regular_files_by_suffix(fc_root, ".json")
    for r_stem, r_path in receipt_files.items():
        if r_stem not in mir_by_stem:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"orphan FaultCensus receipt `{r_stem}.json` has no matching Mir target in CaptureManifest.json",
            )
        _parse_fault_census_receipt_json(r_path)

    ob_root = (
        generated_root / "Obligations"
        if generated_root is not None
        and (generated_root / "Obligations").is_dir()
        and not (generated_root / "Obligations").is_symlink()
        else None
    )
    verify_root = (
        generated_root / "Verify"
        if generated_root is not None
        and (generated_root / "Verify").is_dir()
        and not (generated_root / "Verify").is_symlink()
        else None
    )
    if receipt_files or require_receipts:
        if verify_root is None:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing Verify directory next to FaultCensus receipts under {root}",
            )
        verify_files = _collect_regular_files_by_suffix(verify_root, ".lean")
        for stem in sorted(verify_files):
            if stem not in mir_by_stem:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"Verify module `{stem}` has no matching Mir target in CaptureManifest.json",
                )
            if stem not in receipt_files:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"subject Verify module `{stem}` is missing FaultCensus receipt `{fc_root / (stem + '.json')}`",
                )
        for stem in sorted(receipt_files):
            if stem not in verify_files:
                raise Failure(
                    1,
                    FAULT_COVERAGE_PHASE,
                    f"FaultCensus receipt `{stem}.json` has no matching `Verify/{stem}.lean` module",
                )

    if require_receipts and not receipt_files:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"FaultCensus directory {fc_root} contains no `.json` receipts",
        )
    proofs_root = (
        root / "anneal/proofs"
        if generated_root == root / ".anneal/generated"
        and (root / "anneal/proofs").is_dir()
        else None
    )
    specs_root = (
        proofs_root / "Specs"
        if proofs_root is not None and (proofs_root / "Specs").is_dir()
        else None
    )
    gen_assumptions_root = (
        generated_root / "Assumptions"
        if generated_root is not None
        and (generated_root / "Assumptions").is_dir()
        and not (generated_root / "Assumptions").is_symlink()
        else None
    )
    for stem, r_path in sorted(receipt_files.items()):
        _audit_single_item_receipt(
            stem,
            mir_path_by_stem[stem],
            mir_by_stem[stem],
            r_path,
            mir_by_stem,
            receipt_files,
            ob_root,
            verify_root,
            specs_root,
            proofs_root,
            gen_assumptions_root,
            reg,
        )

    return {
        "mirTargetsAudited": len(mir_by_stem),
        "receiptsAudited": len(receipt_files),
    }


def _resolve_manifest_workspace_root(manifest_path: Path) -> Path:
    parent = manifest_path.parent
    if (
        parent.name == ".anneal"
        and not (parent / ".anneal").exists()
        and (
            (parent / "generated").exists()
            or (parent.parent / "src").exists()
            or (parent.parent / "Cargo.toml").exists()
        )
    ):
        return parent.parent
    return parent


def audit_fault_coverage(
    target_path: Path, *, registry: object = None
) -> dict[str, Any]:
    reg = validate_property_registry(registry, require_all_verified=True)
    if target_path.is_symlink():
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"expected regular file or directory, not symlink: {target_path}",
        )
    if not target_path.exists():
        raise Failure(
            2,
            FAULT_COVERAGE_PHASE,
            f"audit target does not exist: {target_path}",
        )
    resolved = target_path.resolve()
    if resolved.is_file():
        manifest_root = _resolve_manifest_workspace_root(resolved)
        manifest = verify_capture_manifest(
            resolved,
            manifest_root,
            registry=reg,
            require_fault_coverage=True,
        )
        return {
            "mode": "manifest",
            "targets": len(manifest["targets"]),
        }
    if not resolved.is_dir():
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"unsupported audit target: {target_path}",
        )

    # Check if `resolved` is a manifest directory with `CaptureManifest.json`
    manifest_candidates = [
        resolved / "CaptureManifest.json",
        resolved / ".anneal/CaptureManifest.json",
    ]
    for m_cand in manifest_candidates:
        if m_cand.is_file() or m_cand.is_symlink():
            verify_capture_manifest(
                m_cand,
                resolved,
                registry=reg,
                require_fault_coverage=True,
            )

    if (resolved / ".anneal/generated").exists() or (
        resolved / ".anneal/generated"
    ).is_symlink():
        generated_dir = resolved / ".anneal/generated"
    elif (resolved / "Mir").exists() or (resolved / "FaultCensus").exists():
        generated_dir = resolved
    else:
        if any(m.is_file() for m in manifest_candidates):
            return {
                "mode": "manifest",
                "mirFilesAudited": len(
                    json.loads(
                        next(m for m in manifest_candidates if m.is_file()).read_text()
                    )["targets"]
                ),
            }
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"no `.anneal/generated/`, `Mir/`, `FaultCensus/`, or `CaptureManifest.json` found under {target_path}",
        )

    if generated_dir.is_symlink() or not generated_dir.is_dir():
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"expected regular generated directory: {generated_dir}",
        )

    mir_root = generated_dir / "Mir"
    fc_root = generated_dir / "FaultCensus"
    if not mir_root.exists():
        raise Failure(
            1, FAULT_COVERAGE_PHASE, f"missing Mir directory: {mir_root}"
        )
    if not fc_root.exists():
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"missing FaultCensus directory: {fc_root}",
        )

    mir_files = _collect_regular_files_by_suffix(mir_root, ".lean")
    if not mir_files:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"no `Mir/<Item>.lean` files found under {mir_root}",
        )
    receipt_files = _collect_regular_files_by_suffix(fc_root, ".json")
    if not receipt_files:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"no `FaultCensus/<Item>.json` receipts found under {fc_root}",
        )

    mir_by_stem: dict[str, dict[str, Any]] = {}
    for stem, mir_path in mir_files.items():
        try:
            mir_text = mir_path.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeDecodeError) as err:
            raise Failure(
                1, FAULT_COVERAGE_PHASE, f"cannot read {mir_path}: {err}"
            ) from err
        try:
            meta = parse_lean_mir_module_metadata_strict(mir_text)
        except CensusScanError as err:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Mir module {mir_path} failed strict fault-site census scan: {err}",
            ) from err
        _check_mir_module_namespace_binding(mir_text, stem, str(mir_path))
        mir_by_stem[stem] = meta

    for r_stem, r_path in receipt_files.items():
        if r_stem not in mir_by_stem:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"orphan FaultCensus receipt `{r_path}` has no matching `Mir/{r_stem}.lean`",
            )
        _parse_fault_census_receipt_json(r_path)

    verify_root = generated_dir / "Verify"
    ob_root = generated_dir / "Obligations"
    for label, required_dir in (("Verify", verify_root), ("Obligations", ob_root)):
        if required_dir.is_symlink() or not required_dir.is_dir():
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing {label} directory: {required_dir}",
            )
    verify_files = _collect_regular_files_by_suffix(verify_root, ".lean")
    _collect_regular_files_by_suffix(ob_root, ".lean")
    if not verify_files:
        raise Failure(
            1,
            FAULT_COVERAGE_PHASE,
            f"no `Verify/<Item>.lean` modules found under {verify_root}",
        )
    for stem in sorted(verify_files):
        if stem not in mir_by_stem:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"Verify module `{stem}` has no matching `Mir/{stem}.lean`",
            )
        if stem not in receipt_files:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"missing FaultCensus receipt `{fc_root / (stem + '.json')}` for subject item `{stem}`",
            )
    for stem in sorted(receipt_files):
        if stem not in verify_files:
            raise Failure(
                1,
                FAULT_COVERAGE_PHASE,
                f"FaultCensus receipt `{stem}.json` has no matching `Verify/{stem}.lean` module",
            )

    proofs_root = (
        resolved / "anneal/proofs"
        if generated_dir == resolved / ".anneal/generated"
        and (resolved / "anneal/proofs").is_dir()
        else None
    )
    specs_root = (
        proofs_root / "Specs"
        if proofs_root is not None and (proofs_root / "Specs").is_dir()
        else None
    )
    gen_assumptions_root = (
        generated_dir / "Assumptions"
        if (generated_dir / "Assumptions").is_dir()
        and not (generated_dir / "Assumptions").is_symlink()
        else None
    )
    total_sites = 0
    for stem, r_path in sorted(receipt_files.items()):
        rec = _audit_single_item_receipt(
            stem,
            mir_files[stem],
            mir_by_stem[stem],
            r_path,
            mir_by_stem,
            receipt_files,
            ob_root,
            verify_root,
            specs_root,
            proofs_root,
            gen_assumptions_root,
            reg,
        )
        total_sites += len(rec["census_sites"])

    return {
        "mode": "workspace",
        "mirFilesAudited": len(mir_files),
        "receiptsAudited": len(receipt_files),
        "totalCensusSites": total_sites,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="absolute path to an already installed pinned Lean executable")
    parser.add_argument("--self-test", action="store_true", help="run the bounded regression fixtures")
    parser.add_argument("--fast", action="store_true", help="enable content-addressed incremental caching outside the checkout")
    parser.add_argument("--cache-dir", type=Path, help="directory outside the checkout for --fast incremental cache")
    parser.add_argument("--audit-vacuity", action="store_true",
                        help="only run the pure-Python waiver-pin and annotated-claim vacuity audit (no Lean)")
    parser.add_argument("--audit-fault-coverage", type=Path, metavar="PATH",
                        help="audit MIR fault-site census and obligation coverage for a workspace or CaptureManifest.json (no Lean)")
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
    if args.audit_fault_coverage is not None:
        try:
            if base_snapshot is not None:
                verify_base_snapshot(checkout, base_snapshot, tuple(args.expected_tcb_drift))
            gate_summary = audit_checkout_fault_coverage_gate(checkout, require_source_pins=True)
            target_summary = audit_fault_coverage(args.audit_fault_coverage)
        except Failure as error:
            print(f"Trusted check failed ({error.phase}): {error}", file=sys.stderr)
            return error.code
        except OSError as error:
            print(f"Trusted check failed ({FAULT_COVERAGE_PHASE}): {error}", file=sys.stderr)
            return 2
        print(f"PASS: fault-site coverage audit; {json.dumps({**gate_summary, **target_summary}, sort_keys=True)}")
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
