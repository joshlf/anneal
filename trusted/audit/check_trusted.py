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

# Each entry is (module_name, relative_path, direct_imports, role)
# where role is "theory", "examples", "claim", or "test".
DOWNSTREAM_TARGETS = [
    ("Anneal.Refinement", "theory/Anneal/Refinement.lean", ["Trusted"], "theory"),
    ("Anneal.Effect", "theory/Anneal/Effect.lean", ["Trusted"], "theory"),
    ("Anneal.ITree", "theory/Anneal/ITree.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect"], "theory"),
    ("Anneal.Pass", "theory/Anneal/Pass.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree"], "theory"),
    ("Anneal.EffectWP", "theory/Anneal/EffectWP.lean", ["Trusted", "Anneal.Effect"], "theory"),
    ("Anneal.ITreeWP", "theory/Anneal/ITreeWP.lean", ["Std.Do", "Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.EffectWP"], "theory"),
    ("Anneal.Scalars", "theory/Anneal/Scalars.lean", [], "theory"),
    ("Anneal.Memory", "theory/Anneal/Memory.lean", ["Trusted"], "theory"),
    ("Anneal.BitValidity", "theory/Anneal/BitValidity.lean", ["Trusted", "Anneal.Scalars"], "theory"),
    ("Anneal.UnsafeObligations", "theory/Anneal/UnsafeObligations.lean", ["Trusted", "Anneal.Memory"], "theory"),
    ("Anneal.SepLogic", "theory/Anneal/SepLogic.lean", ["Trusted", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Memory", "Anneal.UnsafeObligations"], "theory"),
    ("Anneal.Rustc.V2026_06_01.Lower", "theory/Anneal/Rustc/V2026_06_01/Lower.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.SepLogic"], "theory"),
    ("Anneal.Rustc.V2026_06_01.SymbolicEval", "theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Scalars", "Anneal.Memory", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower"], "theory"),
    ("Anneal.Rustc.V2026_06_01.SymReflect", "theory/Anneal/Rustc/V2026_06_01/SymReflect.lean", ["Trusted", "Anneal.ITreeWP", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval"], "theory"),
    ("Anneal.FunctionalTranslation", "theory/Anneal/FunctionalTranslation.lean", ["Trusted", "Anneal.Refinement", "Anneal.ITree", "Anneal.ITreeWP", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower"], "theory"),
    ("Anneal", "theory/Anneal.lean", ["Trusted", "Anneal.Refinement", "Anneal.Effect", "Anneal.ITree", "Anneal.Pass", "Anneal.EffectWP", "Anneal.ITreeWP", "Anneal.Scalars", "Anneal.Memory", "Anneal.BitValidity", "Anneal.UnsafeObligations", "Anneal.SepLogic", "Anneal.Rustc.V2026_06_01.Lower", "Anneal.Rustc.V2026_06_01.SymbolicEval", "Anneal.Rustc.V2026_06_01.SymReflect", "Anneal.FunctionalTranslation"], "theory"),
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
    for entry in manifest["rust_sources"]:
        if (not isinstance(entry, list) or len(entry) != 2
                or not all(isinstance(x, str) and x for x in entry)
                or not re.fullmatch(r"[0-9a-f]{64}", entry[1])):
            raise Failure(1, phase, "invalid rust_sources entry in CaptureManifest.json")
        src_path = (root / entry[0]).resolve()
        regular(src_path, phase)
        if digest(src_path) != entry[1]:
            raise Failure(1, phase, f"Rust source digest mismatch for {entry[0]}")
    if not isinstance(manifest["targets"], list) or not manifest["targets"]:
        raise Failure(1, phase, "CaptureManifest.json must record at least one verification target")
    seen_defs = set()
    for target in manifest["targets"]:
        if (not isinstance(target, dict)
                or set(target) != {"def_id", "mir_module_path", "mir_module_sha256"}
                or not all(isinstance(target[k], str) and target[k] for k in target)
                or not re.fullmatch(r"[0-9a-f]{64}", target["mir_module_sha256"])):
            raise Failure(1, phase, "invalid target entry in CaptureManifest.json")
        if target["def_id"] in seen_defs:
            raise Failure(1, phase, f"duplicate target def_id {target['def_id']}")
        seen_defs.add(target["def_id"])
        mir_path = (root / target["mir_module_path"]).resolve()
        regular(mir_path, phase)
        if digest(mir_path) != target["mir_module_sha256"]:
            raise Failure(1, phase, f"Mir module digest mismatch for {target['mir_module_path']}")
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
    ):
        self.checkout = checkout.resolve()
        self.source = self.checkout / "trusted/lean"
        self.lean = (lean or Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean").absolute()
        self.fast = bool(fast)
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
                                               stdout=out, stderr=err, timeout=60, check=False)
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
            raise Failure(2, label, "direct Lean child exceeded 60 seconds; no retry")
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
                timeout=60,
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
                timeout=60,
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
            if digest(dest) != hashes[full]:
                raise Failure(2, "downstream-input", f"source changed while copying {path}")
            copies[module] = dest
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
        return self.inspect(
            "downstream-audit",
            trusted=list(self.modules),
            theory=[m for m, _, _, r in targets if r == "theory"],
            examples=[m for m, _, _, r in targets if r == "examples"],
            claimModules=[m for m, _, _, r in targets if r == "claim"],
            testModules=[m for m, _, _, r in targets if r == "test"],
        )

    def run(self, *, check_downstream: bool = False) -> dict:
        cargo_hashes = check_cargo_boundary(self.checkout) if (self.checkout / "Cargo.toml").exists() else {}
        self.tool_admission()
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
        (self.stage / "report.json").write_text(json.dumps(report, indent=2))
        self.budget()
        return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="absolute path to an already installed pinned Lean executable")
    parser.add_argument("--self-test", action="store_true", help="run the bounded regression fixtures")
    parser.add_argument("--fast", action="store_true", help="enable content-addressed incremental caching outside the checkout")
    parser.add_argument("--cache-dir", type=Path, help="directory outside the checkout for --fast incremental cache")
    args = parser.parse_args()
    checkout = Path(__file__).resolve().parent.parent.parent
    if args.lean is not None and not args.lean.is_absolute():
        parser.error("--lean must be absolute")
    if args.self_test:
        sys.path.insert(0, str(checkout / "tests/trusted-boundary"))
        from test_boundary import self_test
        return self_test(checkout, args.lean)
    try:
        checker = Checker(checkout, args.lean, fast=args.fast, cache_dir=args.cache_dir)
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
    print(f"PASS: {report['guarantee']}\n{len(checker.modules)} Trusted modules; "
          f"{report['kernelDeclarations']} Trusted kernel declarations; "
          f"{downstream.get('replayedDeclarations', 0)} total replayed declarations; "
          f"{downstream.get('claimTheoremsChecked', 0)} claim theorem statements origin-checked; "
          f"axioms={report['axioms']}\nSource {report['sourceSha256']}; tools/policy {report['toolsSha256']}\n"
          f"{report['toolchain']}")
    if report["kernelDeclarations"] == 0:
        print("0 Trusted declarations; no semantics")
    shutil.rmtree(checker.stage)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
