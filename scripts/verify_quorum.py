#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Canonical multi-kernel Lean 4 NDJSON v3.1.0 quorum verifier with tamper and Nat.land guards."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

DEFAULT_PERMITTED_AXIOMS: tuple[str, ...] = (
    "propext",
    "Classical.choice",
    "Quot.sound",
)
DECL_KEYS: tuple[str, ...] = (
    "axiom",
    "def",
    "thm",
    "inductive",
    "ctor",
    "rec",
    "quot",
    "opaque",
)


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


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


def resolve_elan_home() -> pathlib.Path:
    env_home = os.environ.get("ELAN_HOME")
    if env_home:
        return pathlib.Path(env_home).expanduser().resolve()
    return (pathlib.Path.home() / ".elan").resolve()


def resolve_tc_435(explicit: str | None = None) -> pathlib.Path:
    candidates = [
        explicit,
        os.environ.get("TC_435"),
        str(resolve_elan_home() / "toolchains" / "leanprover--lean4---v4.35.0"),
    ]
    for cand in candidates:
        if cand:
            p = pathlib.Path(cand).expanduser().resolve()
            if (p / "bin" / "leanexport").is_file():
                return p
    raise FileNotFoundError(
        "Could not locate Lean v4.35.0 toolchain with `bin/leanexport`; "
        "set `TC_435` or pass `--tc-435`."
    )


def resolve_tc_434(explicit: str | None = None) -> pathlib.Path | None:
    candidates = [
        explicit,
        os.environ.get("TC_434"),
        str(resolve_elan_home() / "toolchains" / "leanprover--lean4---v4.34.1"),
    ]
    for cand in candidates:
        if cand:
            p = pathlib.Path(cand).expanduser().resolve()
            if (p / "bin" / "lean").is_file():
                return p
    return None


def resolve_optional_bin(
    explicit: str | None,
    env_keys: tuple[str, ...],
    names: tuple[str, ...],
) -> pathlib.Path | None:
    if explicit:
        p = pathlib.Path(explicit).expanduser().resolve()
        if not (p.is_file() and os.access(p, os.X_OK)):
            raise FileNotFoundError(f"Configured kernel binary is missing or not executable: {p}")
        return p
    for key in env_keys:
        val = os.environ.get(key)
        if val:
            p = pathlib.Path(val).expanduser().resolve()
            if p.is_file() and os.access(p, os.X_OK):
                return p
    local_bin = pathlib.Path.home() / ".local" / "bin"
    for name in names:
        cand = local_bin / name
        if cand.is_file() and os.access(cand, os.X_OK):
            return cand.resolve()
        hit = shutil.which(name)
        if hit:
            return pathlib.Path(hit).resolve()
    return None


def run_timed(cmd: list[str], env: dict[str, str] | None = None) -> dict[str, Any]:
    t0 = time.monotonic()
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    ms = round((time.monotonic() - t0) * 1000.0, 2)
    return {
        "rc": proc.returncode,
        "ms": ms,
        "stdout": proc.stdout.strip()[:300],
        "stderr": proc.stderr.strip()[:300],
    }


def inspect_ndjson_text(ndjson_text: str) -> dict[str, Any]:
    lines = [ln for ln in ndjson_text.splitlines() if ln.strip()]
    names: dict[int, str] = {0: ""}
    axioms: list[str] = []
    decl_names: list[str] = []
    decls = 0
    for line in lines:
        obj = json.loads(line)
        if "in" in obj and isinstance(obj["in"], int):
            nid = obj["in"]
            if "str" in obj:
                pre = names.get(obj["str"]["pre"], "")
                seg = obj["str"]["str"]
                names[nid] = f"{pre}.{seg}" if pre else seg
            elif "num" in obj:
                pre = names.get(obj["num"]["pre"], "")
                seg = str(obj["num"]["i"])
                names[nid] = f"{pre}.{seg}" if pre else seg
        for key in DECL_KEYS:
            if key in obj:
                decls += 1
                payload = obj[key]
                raw_id = payload.get("name") if isinstance(payload, dict) else None
                resolved = names.get(raw_id, str(raw_id)) if isinstance(raw_id, int) else str(raw_id)
                decl_names.append(resolved)
                if key == "axiom":
                    axioms.append(resolved)
    has_nat_land = any(
        nm == "Nat.land" or nm.startswith("Nat.land.")
        for nm in (*decl_names, *names.values())
    )
    return {
        "lines": len(lines),
        "bytes": len(ndjson_text.encode("utf-8")),
        "declarations": decls,
        "decl_names": decl_names,
        "axioms": sorted(set(axioms)),
        "has_nat_land": has_nat_land,
    }


def inject_forged_axiom(ndjson_text: str, axiom_name: str = "forgedBackdoorAx") -> str:
    lines = [ln for ln in ndjson_text.splitlines() if ln.strip()]
    parsed = [json.loads(ln) for ln in lines]
    max_in = max((o["in"] for o in parsed if isinstance(o.get("in"), int)), default=0)
    max_ie = max((o["ie"] for o in parsed if isinstance(o.get("ie"), int)), default=-1)
    prop_ie = next(
        (o["ie"] for o in parsed if isinstance(o.get("ie"), int) and o.get("sort") == 0),
        None,
    )
    extra: list[str] = []
    if prop_ie is None:
        prop_ie = max_ie + 1
        extra.append(json.dumps({"ie": prop_ie, "sort": 0}, separators=(",", ":")))
    forged_id = max_in + 1
    extra.append(
        json.dumps({"in": forged_id, "str": {"pre": 0, "str": axiom_name}}, separators=(",", ":"))
    )
    extra.append(
        json.dumps(
            {
                "axiom": {
                    "name": forged_id,
                    "levelParams": [],
                    "type": prop_ie,
                    "isUnsafe": False,
                }
            },
            separators=(",", ":"),
        )
    )
    return "\n".join([*lines, *extra]) + "\n"


def compile_lean_file(
    lean_bin: pathlib.Path,
    src_file: pathlib.Path,
    root_dir: pathlib.Path,
    out_dir: pathlib.Path,
    extra_lean_paths: list[str],
    wrapper: list[str],
) -> dict[str, Any]:
    rel = src_file.resolve().relative_to(root_dir.resolve()).with_suffix(".olean")
    olean_path = out_dir / rel
    olean_path.parent.mkdir(parents=True, exist_ok=True)
    sysroot_lib = str(lean_bin.parent.parent / "lib" / "lean")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(out_dir), *extra_lean_paths, sysroot_lib])
    cmd = [
        *wrapper,
        str(lean_bin),
        "-R",
        str(root_dir.resolve()),
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        "-DwarningAsError=true",
        "-o",
        str(olean_path),
        str(src_file.resolve()),
    ]
    res = run_timed(cmd, env=env)
    res["file"] = str(src_file)
    return res


def format_nat_land_error(module_name: str) -> str:
    return (
        f"Export cone for `{module_name}` contains `Nat.land`, which expands NDJSON "
        "exports to ~730 KB and fails external quorum kernels (`con-ron` / `con-leche` "
        "rc=2: unsupported Nat.div/mod environment at `def Nat.land`). Use "
        "`Anneal.NatBitwise` (https://github.com/google/zerocopy/pull/4444, "
        "`Quot.sound`-free bitwise lemmas and `nat_land_two_pow_sub_one_eq_mod`) or "
        "pure `Init.Prelude` `Nat.div`/`Nat.mod` specifications instead (or pass "
        "`--allow-nat-land` to bypass this guard)."
    )


def run_quorum(
    *,
    lean_file: pathlib.Path | None,
    dep_files: list[pathlib.Path],
    root_dir: pathlib.Path | None,
    module_name: str | None,
    export_roots: list[str],
    extra_lean_paths: list[str],
    neg_files: list[pathlib.Path],
    permitted_axioms: list[str],
    mutant_ndjsons: list[pathlib.Path] | None = None,
    tc_435_arg: str | None = None,
    tc_434_arg: str | None = None,
    anneal_kc_arg: str | None = None,
    palladium_arg: str | None = None,
    jobs: int = 2,
    skip_v434: bool = False,
    allow_nat_land: bool = False,
    skip_tamper_check: bool = False,
    disable_wrapper: bool = False,
) -> tuple[int, dict[str, Any]]:
    if not export_roots:
        return 2, {
            "passed": False,
            "stage": "export_roots",
            "error": (
                "Refusing whole-module `leanexport` without `-- <root>`: pass at least one "
                "`--export-root <DeclName>` (omitting `-- <root>` pulls `Init` `sorryAx` and "
                "bloats NDJSON exports to 3.8-6.5 MB)."
            ),
        }

    if lean_file is None and not module_name:
        return 2, {
            "passed": False,
            "stage": "arguments",
            "error": "Provide `--file <Main.lean>` or `--module <ModuleName>` with `--lean-path`.",
        }

    tc_435 = resolve_tc_435(tc_435_arg)
    lean_435 = tc_435 / "bin" / "lean"
    leanexport_bin = tc_435 / "bin" / "leanexport"
    nanoda_bin = tc_435 / "bin" / "nanoda_bin"
    con_ron_bin = tc_435 / "bin" / "con-ron"
    con_leche_bin = tc_435 / "bin" / "con-leche"
    lean4lean_bin = tc_435 / "bin" / "lean4lean"
    anneal_kc_bin = resolve_optional_bin(
        anneal_kc_arg, ("ANNEAL_KC", "ANNEAL_KC_BIN"), ("anneal-kc",)
    )
    palladium_bin = resolve_optional_bin(
        palladium_arg, ("PALLADIUM", "PALLADIUM_BIN"), ("palladium-v1", "palladium")
    )

    wrapper = find_lean_wrapper(disable_wrapper)
    src = lean_file.resolve() if lean_file else None
    resolved_root = (
        root_dir.resolve()
        if root_dir
        else (src.parent if src is not None else pathlib.Path.cwd())
    )
    mod = (
        module_name
        if module_name
        else ".".join(src.relative_to(resolved_root).with_suffix("").parts)  # type: ignore[union-attr]
    )

    with tempfile.TemporaryDirectory(prefix="workbench-quorum-") as tmp:
        tmp_path = pathlib.Path(tmp)
        olean_435 = tmp_path / "olean435"
        olean_435.mkdir()

        v434_steps: list[dict[str, Any]] = []
        tc_434 = None if (skip_v434 or extra_lean_paths) else resolve_tc_434(tc_434_arg)
        if src is not None and tc_434 is not None:
            olean_434 = tmp_path / "olean434"
            olean_434.mkdir()
            for f in [*dep_files, src]:
                step = compile_lean_file(
                    tc_434 / "bin" / "lean", f, resolved_root, olean_434, [], wrapper
                )
                v434_steps.append(step)
                if step["rc"] != 0:
                    return 1, {
                        "passed": False,
                        "stage": "compile_v434",
                        "module": mod,
                        "failed_step": step,
                    }

        v435_steps: list[dict[str, Any]] = []
        if src is not None:
            for f in [*dep_files, src]:
                step = compile_lean_file(
                    lean_435, f, resolved_root, olean_435, extra_lean_paths, wrapper
                )
                v435_steps.append(step)
                if step["rc"] != 0:
                    return 1, {
                        "passed": False,
                        "stage": "compile_v435",
                        "module": mod,
                        "failed_step": step,
                    }

        sys_lib_435 = str(tc_435 / "lib" / "lean")
        lean_search = [*([] if src is None else [str(olean_435)]), *extra_lean_paths, sys_lib_435]
        exp_env = os.environ.copy()
        exp_env["LEAN_PATH"] = os.pathsep.join(lean_search)
        exp_env["LD_LIBRARY_PATH"] = os.pathsep.join(
            [sys_lib_435, *([exp_env["LD_LIBRARY_PATH"]] if exp_env.get("LD_LIBRARY_PATH") else [])]
        )

        export_cmd = [str(leanexport_bin), mod, "--", *export_roots]
        t0 = time.monotonic()
        ex_proc = subprocess.run(
            export_cmd, env=exp_env, capture_output=True, text=True, check=False
        )
        export_ms = round((time.monotonic() - t0) * 1000.0, 2)
        if ex_proc.returncode != 0:
            return 1, {
                "passed": False,
                "stage": "leanexport",
                "module": mod,
                "rc": ex_proc.returncode,
                "stderr": ex_proc.stderr.strip()[:500],
            }

        nd_path = tmp_path / f"{mod.replace('.', '_')}.ndjson"
        nd_path.write_text(ex_proc.stdout, encoding="utf-8")
        nd_info = inspect_ndjson_text(ex_proc.stdout)
        nd_info["sha256"] = sha256_file(nd_path)
        nd_info["export_ms"] = export_ms

        decl_set = set(nd_info["decl_names"])
        missing_roots = [r for r in export_roots if r not in decl_set]
        if missing_roots:
            return 2, {
                "passed": False,
                "stage": "missing_export_roots",
                "module": mod,
                "missing_roots": missing_roots,
                "ndjson": {k: v for k, v in nd_info.items() if k != "decl_names"},
            }

        disallowed_ax = [a for a in nd_info["axioms"] if a not in permitted_axioms]
        if disallowed_ax:
            return 2, {
                "passed": False,
                "stage": "disallowed_axioms",
                "module": mod,
                "disallowed_axioms": disallowed_ax,
                "axioms": nd_info["axioms"],
            }

        if nd_info["has_nat_land"] and not allow_nat_land:
            return 2, {
                "passed": False,
                "stage": "nat_land_guard",
                "module": mod,
                "error": format_nat_land_error(mod),
                "ndjson": {k: v for k, v in nd_info.items() if k != "decl_names"},
            }

        nanoda_cfg = tmp_path / "nanoda_cfg.json"
        nanoda_cfg.write_text(
            json.dumps(
                {
                    "use_stdin": False,
                    "export_file_path": str(nd_path),
                    "permitted_axioms": permitted_axioms,
                    "unpermitted_axiom_hard_error": True,
                    "num_threads": jobs,
                    "nat_extension": True,
                    "string_extension": True,
                }
            ),
            encoding="utf-8",
        )

        kernels: dict[str, dict[str, Any]] = {
            "nanoda_bin": run_timed([str(nanoda_bin), str(nanoda_cfg)], env=exp_env),
        }
        if con_ron_bin.is_file():
            kernels["con-ron"] = run_timed(
                [str(con_ron_bin), "--verified", f"--jobs={jobs}", str(nd_path)], env=exp_env
            )
        if con_leche_bin.is_file():
            kernels["con-leche"] = run_timed(
                [str(con_leche_bin), "--verified", f"--jobs={jobs}", str(nd_path)], env=exp_env
            )
        if lean4lean_bin.is_file():
            kernels["lean4lean"] = run_timed(
                [str(lean4lean_bin), "--import", str(nd_path)], env=exp_env
            )
        if anneal_kc_bin is not None:
            kc_flags = ["--anneal-policy"] if "Quot.sound" not in nd_info["axioms"] else []
            kernels["anneal-kc"] = run_timed(
                [str(anneal_kc_bin), *kc_flags, str(nd_path)], env=exp_env
            )
        if palladium_bin is not None:
            pal_flags = ["--strict-axioms"] if "Quot.sound" not in nd_info["axioms"] else []
            kernels["palladium"] = run_timed(
                [str(palladium_bin), *pal_flags, "-j", str(jobs), str(nd_path)], env=exp_env
            )

        failed_kernels = [k for k, r in kernels.items() if r["rc"] != 0]
        if failed_kernels:
            return 1, {
                "passed": False,
                "stage": "external_kernels",
                "module": mod,
                "failed_kernels": failed_kernels,
                "kernels": kernels,
                "ndjson": {k: v for k, v in nd_info.items() if k != "decl_names"},
            }

        tamper_results: dict[str, dict[str, Any]] = {}
        if not skip_tamper_check:
            tamper_nd = tmp_path / "tampered_forged_axiom.ndjson"
            tamper_nd.write_text(inject_forged_axiom(ex_proc.stdout), encoding="utf-8")
            tamper_cfg = tmp_path / "nanoda_tamper.json"
            tamper_cfg.write_text(
                json.dumps(
                    {
                        "use_stdin": False,
                        "export_file_path": str(tamper_nd),
                        "permitted_axioms": permitted_axioms,
                        "unpermitted_axiom_hard_error": True,
                        "num_threads": jobs,
                        "nat_extension": True,
                        "string_extension": True,
                    }
                ),
                encoding="utf-8",
            )
            tamper_results["nanoda_bin"] = run_timed(
                [str(nanoda_bin), str(tamper_cfg)], env=exp_env
            )
            if anneal_kc_bin is not None:
                tamper_results["anneal-kc"] = run_timed(
                    [str(anneal_kc_bin), "--anneal-policy", str(tamper_nd)], env=exp_env
                )
            if palladium_bin is not None:
                tamper_results["palladium"] = run_timed(
                    [str(palladium_bin), "--strict-axioms", "-j", str(jobs), str(tamper_nd)],
                    env=exp_env,
                )
            accepted_tamper = [k for k, r in tamper_results.items() if r["rc"] == 0]
            if accepted_tamper:
                return 1, {
                    "passed": False,
                    "stage": "tamper_canary",
                    "module": mod,
                    "accepted_unexpectedly": accepted_tamper,
                    "tamper_results": tamper_results,
                }

        neg_results: list[dict[str, Any]] = []
        for nf in neg_files:
            nf_res = nf.resolve()
            neg_out = tmp_path / f"neg_{nf_res.stem}"
            neg_out.mkdir(exist_ok=True)
            step = compile_lean_file(
                lean_435,
                nf_res,
                nf_res.parent,
                neg_out,
                [*([] if src is None else [str(olean_435)]), *extra_lean_paths],
                wrapper,
            )
            rejected = step["rc"] != 0
            neg_results.append(
                {
                    "file": nf_res.name,
                    "rc": step["rc"],
                    "ms": step["ms"],
                    "rejected_as_expected": rejected,
                    "stderr": step["stderr"],
                }
            )
            if not rejected:
                return 1, {
                    "passed": False,
                    "stage": "negative_mutation",
                    "module": mod,
                    "accepted_unexpectedly": str(nf_res),
                    "negative_mutations": neg_results,
                }

        mutant_ndjson_results: list[dict[str, Any]] = []
        for mf in mutant_ndjsons or []:
            mf_res = mf.resolve()
            mut_cfg = tmp_path / f"nanoda_mut_{mf_res.stem}.json"
            mut_cfg.write_text(
                json.dumps(
                    {
                        "use_stdin": False,
                        "export_file_path": str(mf_res),
                        "permitted_axioms": permitted_axioms,
                        "unpermitted_axiom_hard_error": True,
                        "num_threads": jobs,
                        "nat_extension": True,
                        "string_extension": True,
                    }
                ),
                encoding="utf-8",
            )
            mut_kernels: dict[str, dict[str, Any]] = {
                "nanoda_bin": run_timed([str(nanoda_bin), str(mut_cfg)], env=exp_env),
            }
            if con_ron_bin.is_file():
                mut_kernels["con-ron"] = run_timed(
                    [str(con_ron_bin), "--verified", f"--jobs={jobs}", str(mf_res)], env=exp_env
                )
            if anneal_kc_bin is not None:
                mut_kernels["anneal-kc"] = run_timed(
                    [str(anneal_kc_bin), "--anneal-policy", str(mf_res)], env=exp_env
                )
            if palladium_bin is not None:
                mut_kernels["palladium"] = run_timed(
                    [str(palladium_bin), "--strict-axioms", "-j", str(jobs), str(mf_res)],
                    env=exp_env,
                )
            accepted_mut = [k for k, r in mut_kernels.items() if r["rc"] == 0]
            mutant_ndjson_results.append(
                {
                    "file": mf_res.name,
                    "kernels": mut_kernels,
                    "rejected_by_all": len(accepted_mut) == 0,
                }
            )
            if accepted_mut:
                return 1, {
                    "passed": False,
                    "stage": "mutant_ndjson_rejection",
                    "module": mod,
                    "mutant_file": str(mf_res),
                    "accepted_unexpectedly": accepted_mut,
                    "mutant_ndjsons": mutant_ndjson_results,
                }

        nd_summary = {k: v for k, v in nd_info.items() if k != "decl_names"}
        return 0, {
            "passed": True,
            "module": mod,
            "export_roots": export_roots,
            "v434_compile_steps": v434_steps,
            "v435_compile_steps": v435_steps,
            "ndjson": nd_summary,
            "kernels": kernels,
            "tamper_forged_axiom": tamper_results,
            "negative_mutations": neg_results,
            "mutant_ndjsons": mutant_ndjson_results,
        }


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--file", help="Main `.lean` source file to compile and verify.")
    ap.add_argument(
        "--dep-file",
        action="append",
        default=[],
        help="Ordered dependency `.lean` file to compile before `--file` (repeatable).",
    )
    ap.add_argument("--root-dir", help="Module root directory (default: parent of `--file`).")
    ap.add_argument("--module", help="Explicit Lean module name (or prebuilt `.olean` module).")
    ap.add_argument(
        "--export-root",
        action="append",
        default=[],
        help="Required declaration root passed after `--` to `leanexport` (repeatable).",
    )
    ap.add_argument(
        "--lean-path",
        action="append",
        default=[],
        help="Additional `LEAN_PATH` directory for prebuilt `.olean` dependencies (repeatable).",
    )
    ap.add_argument(
        "--neg-file",
        action="append",
        default=[],
        help="Negative mutation `.lean` canary that must fail compilation (`rc != 0`).",
    )
    ap.add_argument(
        "--require-mutant-reject",
        action="append",
        default=[],
        dest="mutant_ndjsons",
        help="Mutated or corrupted NDJSON export that every external kernel must reject (`rc != 0`).",
    )
    ap.add_argument(
        "--permitted-axiom",
        action="append",
        default=[],
        help="Permitted axiom name (repeatable; defaults to propext, Classical.choice, Quot.sound).",
    )
    ap.add_argument("--tc-435", help="Explicit Lean v4.35.0 toolchain root (default: `$TC_435`).")
    ap.add_argument("--tc-434", help="Explicit Lean v4.34.1 toolchain root (default: `$TC_434`).")
    ap.add_argument("--anneal-kc", help="Optional path to `anneal-kc` binary (or `$ANNEAL_KC`).")
    ap.add_argument("--palladium", help="Optional path to `palladium` binary (or `$PALLADIUM`).")
    ap.add_argument("--jobs", type=int, default=2, help="Worker threads per external kernel.")
    ap.add_argument("--skip-v434", action="store_true", help="Skip Lean v4.34.1 dual compile.")
    ap.add_argument(
        "--allow-nat-land",
        action="store_true",
        help="Bypass the fail-fast `Nat.land` export-cone guard.",
    )
    ap.add_argument(
        "--skip-tamper-check",
        action="store_true",
        help="Skip automatic `forgedBackdoorAx` tampered-NDJSON rejection check.",
    )
    ap.add_argument(
        "--no-wrapper",
        action="store_true",
        help="Invoke `lean` directly without `anneal-lean-run`.",
    )
    ap.add_argument(
        "--out-json",
        "--receipt-out",
        dest="out_json",
        help="Write full JSON receipt to this file path.",
    )
    ap.add_argument("--json", action="store_true", help="Print full JSON receipt to stdout.")
    return ap


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    axioms = list(args.permitted_axiom) if args.permitted_axiom else list(DEFAULT_PERMITTED_AXIOMS)
    rc, report = run_quorum(
        lean_file=pathlib.Path(args.file) if args.file else None,
        dep_files=[pathlib.Path(p) for p in args.dep_file],
        root_dir=pathlib.Path(args.root_dir) if args.root_dir else None,
        module_name=args.module,
        export_roots=list(args.export_root),
        extra_lean_paths=list(args.lean_path),
        neg_files=[pathlib.Path(p) for p in args.neg_file],
        permitted_axioms=axioms,
        mutant_ndjsons=[pathlib.Path(p) for p in args.mutant_ndjsons],
        tc_435_arg=args.tc_435,
        tc_434_arg=args.tc_434,
        anneal_kc_arg=args.anneal_kc,
        palladium_arg=args.palladium,
        jobs=args.jobs,
        skip_v434=args.skip_v434,
        allow_nat_land=args.allow_nat_land,
        skip_tamper_check=args.skip_tamper_check,
        disable_wrapper=args.no_wrapper,
    )
    if args.out_json:
        out_p = pathlib.Path(args.out_json)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(report, indent=2))
    elif report.get("passed"):
        k_summary = ", ".join(f"{k}={v['ms']}ms" for k, v in report["kernels"].items())
        nd = report["ndjson"]
        print(
            f"[PASS] {report['module']}: decls={nd['declarations']} "
            f"bytes={nd['bytes']} axioms={nd['axioms']} kernels=({k_summary}) "
            f"tamper_rejected={list(report['tamper_forged_axiom'].keys())}"
        )
    else:
        err = report.get("error") or json.dumps(report, indent=2)
        print(f"[FAIL:{report.get('stage', 'quorum')}] {err}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
