#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Incremental, Merkle-cached, cgroup-governed Lean 4 DAG builder for Lake-free trees."""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time
from typing import Any

WORKBENCH_LEAN_DIR = pathlib.Path(__file__).resolve().parents[1] / "lean"

ANNEAL_SUBROOTS: tuple[tuple[str, str], ...] = (
    ("Trusted.Correspondence", "trusted/correspondence"),
    ("Trusted", "trusted/lean"),
    ("Anneal.MirCorrespondence", "correspondence"),
    ("Anneal", "theory"),
    ("Miri", "vendor/lean-miri"),
    ("TrustedBoundary", "trusted/audit"),
)

IMPORT_RE = re.compile(
    r"(?m)^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)"
)
MODULE_HDR_RE = re.compile(r"\A\s*module\b")


def strip_comments_and_strings(text: str) -> str:
    """Replaces Lean comments and string literals with whitespace."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_string = False
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def find_lean_wrapper(disable_wrapper: bool) -> list[str]:
    if disable_wrapper:
        return []
    for candidate in (
        os.environ.get("ANNEAL_LEAN_RUN"),
        str(pathlib.Path.home() / ".local" / "bin" / "anneal-lean-run"),
        shutil.which("anneal-lean-run"),
    ):
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return [candidate, "--mode", "file", "--"]
    return []


def resolve_lean_toolchain(explicit_lean_bin: str | None) -> tuple[pathlib.Path, pathlib.Path]:
    """Returns `(lean_bin, sysroot_prefix)` pinned to the workbench toolchain by default."""
    lean_bin: pathlib.Path | None = None
    if explicit_lean_bin:
        lean_bin = pathlib.Path(explicit_lean_bin).resolve()
    elif (WORKBENCH_LEAN_DIR / "lean-toolchain").is_file() and shutil.which("lake"):
        proc = subprocess.run(
            ["lake", "env", "which", "lean"],
            cwd=str(WORKBENCH_LEAN_DIR),
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            lean_bin = pathlib.Path(proc.stdout.strip()).resolve()
    if lean_bin is None:
        which_lean = shutil.which("lean")
        if not which_lean:
            raise RuntimeError("Could not locate `lean` executable on PATH.")
        lean_bin = pathlib.Path(which_lean).resolve()

    pref = subprocess.run(
        [str(lean_bin), "--print-prefix"],
        capture_output=True,
        text=True,
        check=True,
    )
    return lean_bin, pathlib.Path(pref.stdout.strip()).resolve()


def parse_root_specs(
    anneal_dir: pathlib.Path | None,
    raw_roots: list[str],
) -> list[tuple[str, pathlib.Path]]:
    """Returns `(optional_module_prefix, root_dir)` ordered most-specific prefix first."""
    specs: list[tuple[str, pathlib.Path]] = []
    if anneal_dir is not None:
        base = anneal_dir.resolve()
        for prefix, rel in ANNEAL_SUBROOTS:
            cand = base / rel
            if cand.is_dir():
                specs.append((prefix, cand.resolve()))
    for raw in raw_roots:
        if "=" in raw:
            pfx, p_str = raw.split("=", 1)
            specs.append((pfx.strip(), pathlib.Path(p_str).resolve()))
        else:
            specs.append(("", pathlib.Path(raw).resolve()))
    # Longest non-empty module prefix wins; bare roots (`""`) serve as fallback.
    specs.sort(key=lambda item: (item[0] == "", -len(item[0])))
    return specs


def find_module_source(
    mod: str,
    roots: list[tuple[str, pathlib.Path]],
) -> tuple[pathlib.Path, pathlib.Path] | None:
    """Resolves `mod` to `(src_file, src_root)` across configured source roots."""
    rel_lean = pathlib.Path(*mod.split(".")).with_suffix(".lean")
    for prefix, root_dir in roots:
        if prefix:
            matches_prefix = (
                mod == prefix
                or mod.startswith(prefix + ".")
                or (prefix == "Anneal.MirCorrespondence" and mod.startswith(prefix))
            )
            if not matches_prefix:
                continue
        cand = root_dir / rel_lean
        if cand.is_file():
            return cand.resolve(), root_dir
    return None


def resolve_target_to_module(
    target: str,
    roots: list[tuple[str, pathlib.Path]],
) -> tuple[str, pathlib.Path, pathlib.Path]:
    """Maps a CLI target (module name or `.lean` file path) to `(mod, src_file, src_root)`."""
    as_path = pathlib.Path(target)
    if target.endswith(".lean") or as_path.is_file():
        fp = as_path.resolve()
        if not fp.is_file():
            raise FileNotFoundError(f"Lean source file not found: {target}")
        for _, root_dir in roots:
            if fp.is_relative_to(root_dir):
                rel = fp.relative_to(root_dir).with_suffix("")
                return ".".join(rel.parts), fp, root_dir
        return fp.stem, fp, fp.parent

    found = find_module_source(target, roots)
    if found is None:
        raise FileNotFoundError(
            f"Could not resolve module `{target}` under configured roots: "
            f"{[str(r) for _, r in roots]}"
        )
    return target, found[0], found[1]


def build_dag(
    *,
    targets: list[str],
    roots: list[tuple[str, pathlib.Path]],
    out_dir: pathlib.Path,
    extra_lean_paths: list[pathlib.Path],
    lean_bin: pathlib.Path,
    sysroot: pathlib.Path,
    jobs: int = 4,
    memory_mb: int = 4096,
    strict_warnings: bool = False,
    disable_wrapper: bool = False,
    quiet: bool = False,
) -> dict[str, Any]:
    t0 = time.monotonic()
    out_resolved = out_dir.resolve()
    out_resolved.mkdir(parents=True, exist_ok=True)
    cache_file = out_resolved / ".dag_cache.json"
    try:
        prev_cache: dict[str, str] = (
            json.loads(cache_file.read_text(encoding="utf-8")) if cache_file.is_file() else {}
        )
    except json.JSONDecodeError:
        prev_cache = {}

    srcs: dict[str, tuple[pathlib.Path, pathlib.Path]] = {}
    deps: dict[str, list[str]] = {}
    is_module_map: dict[str, bool] = {}
    src_sha_map: dict[str, str] = {}

    stack: list[str] = []
    for raw_t in targets:
        mod, fp, rdir = resolve_target_to_module(raw_t, roots)
        srcs[mod] = (fp, rdir)
        stack.append(mod)

    while stack:
        mod = stack.pop()
        if mod in deps:
            continue
        fp, _ = srcs[mod]
        raw_bytes = fp.read_bytes()
        src_sha_map[mod] = hashlib.sha256(raw_bytes).hexdigest()
        masked = strip_comments_and_strings(raw_bytes.decode("utf-8", errors="replace"))
        is_module_map[mod] = bool(MODULE_HDR_RE.search(masked))
        mod_deps: list[str] = []
        for imp in IMPORT_RE.findall(masked):
            if imp == mod:
                continue
            if imp not in srcs:
                resolved = find_module_source(imp, roots)
                if resolved is None:
                    continue
                srcs[imp] = resolved
            if imp not in mod_deps:
                mod_deps.append(imp)
            if imp not in deps:
                stack.append(imp)
        deps[mod] = mod_deps

    flags = ["-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false", f"-M{memory_mb}"]
    if strict_warnings:
        flags.extend(["-DautoImplicit=false", "-DwarningAsError=true"])

    merkle: dict[str, str] = {}
    visiting: set[str] = set()

    def compute_key(m: str) -> str:
        if m in merkle:
            return merkle[m]
        if m in visiting:
            raise RuntimeError(f"Import cycle detected involving `{m}`")
        visiting.add(m)
        h = hashlib.sha256()
        h.update(b"workbench-lean-dag-v1\0")
        h.update(str(lean_bin).encode("utf-8") + b"\0")
        h.update(" ".join(flags).encode("utf-8") + b"\0")
        h.update(src_sha_map[m].encode("utf-8") + b"\0")
        for d in sorted(deps[m]):
            h.update(f"{d}:{compute_key(d)}\0".encode("utf-8"))
        visiting.remove(m)
        digest = h.hexdigest()
        merkle[m] = digest
        return digest

    for mod in sorted(deps):
        compute_key(mod)

    def artifacts_exist(m: str) -> bool:
        stem = out_resolved / pathlib.Path(*m.split("."))
        exts = (".olean", ".olean.server", ".olean.private") if is_module_map[m] else (".olean",)
        return all(stem.with_suffix(ext).is_file() for ext in exts)

    cached_mods = {
        m for m in deps if prev_cache.get(m) == merkle[m] and artifacts_exist(m)
    }
    done_mods = set(cached_mods)
    pending = set(deps.keys()) - done_mods
    built_mods: list[str] = []
    failed_mods: dict[str, str] = {}

    lean_path_entries = [
        str(out_resolved),
        *(str(p.resolve()) for p in extra_lean_paths),
        str(sysroot / "lib" / "lean"),
    ]
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(lean_path_entries)
    wrapper = find_lean_wrapper(disable_wrapper)

    def compile_one(m: str) -> subprocess.CompletedProcess[str]:
        src_fp, src_root = srcs[m]
        out_olean = out_resolved / pathlib.Path(*m.split(".")).with_suffix(".olean")
        out_olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            *wrapper,
            str(lean_bin),
            *flags,
            "-R",
            str(src_root),
            "-o",
            str(out_olean),
            str(src_fp),
        ]
        return subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)

    in_flight: dict[Future[subprocess.CompletedProcess[str]], str] = {}
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        while pending or in_flight:
            blocked = {m for m in pending if any(d in failed_mods for d in deps[m])}
            for b in sorted(blocked):
                pending.remove(b)
                failed_mods[b] = "blocked by failed dependency"

            ready = sorted(
                m for m in pending
                if all(d in done_mods for d in deps[m])
            )
            for m in ready:
                if len(in_flight) >= max(1, jobs):
                    break
                pending.remove(m)
                in_flight[pool.submit(compile_one, m)] = m

            if not in_flight:
                if pending:
                    raise RuntimeError(f"Unresolvable DAG state across: {sorted(pending)}")
                break

            finished, _ = wait(in_flight.keys(), return_when=FIRST_COMPLETED)
            for fut in finished:
                m = in_flight.pop(fut)
                proc = fut.result()
                if proc.returncode == 0:
                    done_mods.add(m)
                    built_mods.append(m)
                    prev_cache[m] = merkle[m]
                    cache_file.write_text(json.dumps(prev_cache, indent=2) + "\n", encoding="utf-8")
                    if not quiet:
                        print(f"[OK]   {m}", flush=True)
                else:
                    msg = (proc.stdout + "\n" + proc.stderr).strip()
                    failed_mods[m] = msg
                    if not quiet:
                        print(f"[FAIL] {m}\n{msg}", file=sys.stderr, flush=True)

    return {
        "clean": len(failed_mods) == 0,
        "out_dir": str(out_resolved),
        "total_modules": len(deps),
        "built": built_mods,
        "cached": sorted(cached_mods),
        "failed": failed_mods,
        "elapsed_sec": round(time.monotonic() - t0, 3),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+",
                        help="Target module names (e.g. `Anneal.NatBitwise`) or `.lean` file paths.")
    parser.add_argument("--anneal-dir", default=None,
                        help="Anneal root directory (`trusted/lean`, `theory`, `correspondence`, etc.).")
    parser.add_argument("--root", action="append", default=[], dest="roots",
                        help="Source root directory (`PATH` or `Prefix=PATH`, repeatable).")
    parser.add_argument("--out-dir", required=True,
                        help="Output directory for compiled `.olean` artifacts and `.dag_cache.json`.")
    parser.add_argument("--lean-path", action="append", default=[], dest="lean_paths",
                        help="Extra prebuilt `.olean` directory to append to `LEAN_PATH` (repeatable).")
    parser.add_argument("--lean-bin", default=None,
                        help="Optional path to `lean` binary (defaults to workbench toolchain).")
    parser.add_argument("--jobs", type=int, default=max(1, min(os.cpu_count() or 1, 4)),
                        help="Max concurrent `lean` compile jobs (default: min(cpu, 4)).")
    parser.add_argument("--memory-mb", type=int, default=4096,
                        help="Per-process `-M` memory cap in MiB passed to `lean` (default: 4096).")
    parser.add_argument("--strict-warnings", action="store_true",
                        help="Pass `-DautoImplicit=false -DwarningAsError=true` to `lean`.")
    parser.add_argument("--no-wrapper", action="store_true",
                        help="Invoke `lean` without `anneal-lean-run`.")
    parser.add_argument("--json", action="store_true", help="Emit JSON summary.")
    args = parser.parse_args(argv)

    anneal_dir = pathlib.Path(args.anneal_dir) if args.anneal_dir else None
    roots = parse_root_specs(anneal_dir, args.roots)
    if not roots:
        parser.error("Provide `--anneal-dir <dir>` and/or at least one `--root <dir>`.")

    lean_bin, sysroot = resolve_lean_toolchain(args.lean_bin)
    report = build_dag(
        targets=args.targets,
        roots=roots,
        out_dir=pathlib.Path(args.out_dir),
        extra_lean_paths=[pathlib.Path(p) for p in args.lean_paths],
        lean_bin=lean_bin,
        sysroot=sysroot,
        jobs=args.jobs,
        memory_mb=args.memory_mb,
        strict_warnings=args.strict_warnings,
        disable_wrapper=args.no_wrapper,
        quiet=args.json,
    )
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(
            f"DAG build {'succeeded' if report['clean'] else 'FAILED'} in {report['elapsed_sec']}s: "
            f"{len(report['built'])} built, {len(report['cached'])} cached, "
            f"{len(report['failed'])} failed (out: {report['out_dir']})."
        )
    return 0 if report["clean"] else 1


if __name__ == "__main__":
    sys.exit(main())
