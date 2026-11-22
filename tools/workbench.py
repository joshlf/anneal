#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Self-validating catalog generator and integrity checker for the `workbench` branch."""

from __future__ import annotations

import argparse
import ast
import json
import os
import pathlib
import py_compile
import re
import shutil
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_lean_hygiene  # noqa: E402
import preflight_syntax_check  # noqa: E402
import proof_health_scan  # noqa: E402

FORBIDDEN_PUBLIC_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("internal_hostname", re.compile(r"googlers" + r"\.com|corp\.google" + r"\.com")),
    ("internal_home_path", re.compile(r"/usr/local/" + r"google/")),
    ("internal_x20_path", re.compile(r"/" + r"x20/|/google/data/" + r"rw/")),
    ("todo_marker", re.compile(r"\b" + "TO" + "DO" + r"\b")),
)

DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|@\[[^\]]+\]\s*)*"
    r"(inductive|structure|class|def|abbrev|theorem|instance)\s+([A-Za-z_][A-Za-z0-9_.']*)",
    re.MULTILINE,
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)", re.MULTILINE)
DOC_BLOCK_RE = re.compile(r"/-\!\s*(.*?)\s*-/", re.DOTALL)
FLAG_RE = re.compile(r'add_argument\(\s*"(--[a-z0-9-]+)"')


def find_build_wrapper(disable_wrapper: bool) -> list[str]:
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


def extract_lean_summary(src: str) -> str:
    m = DOC_BLOCK_RE.search(src)
    if not m:
        return ""
    lines = [ln.strip() for ln in m.group(1).splitlines() if ln.strip()]
    body_lines = [ln for ln in lines if not ln.startswith("#")]
    if not body_lines:
        return lines[0].lstrip("#").strip() if lines else ""
    para: list[str] = []
    for ln in body_lines:
        if ln.startswith(("-", "1.", "2.", "*")):
            break
        para.append(ln)
    text = " ".join(para) if para else body_lines[0]
    return re.sub(r"\s+", " ", text).strip()


def module_name_for_path(lean_root: pathlib.Path, file_path: pathlib.Path) -> str:
    rel = file_path.relative_to(lean_root).with_suffix("")
    return ".".join(rel.parts)


def badge_for_module(mod_name: str) -> str:
    if mod_name == "Workbench.Pass1" or mod_name.startswith("Workbench.Pass1."):
        return "pass1_portable"
    return "lab_meta"


def build_catalog_dict() -> dict[str, Any]:
    lean_root = ROOT / "lean"
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()

    lean_files = sorted(
        p for p in (lean_root / "Workbench").rglob("*.lean")
        if p.is_file() and not p.is_symlink()
    )
    modules_out: list[dict[str, Any]] = []
    for lf in lean_files:
        raw = lf.read_text(encoding="utf-8")
        masked = proof_health_scan.strip_comments_and_strings(raw)
        mod_name = module_name_for_path(lean_root, lf)
        imports = IMPORT_RE.findall(masked)
        decls = [
            {"kind": m.group(1), "name": m.group(2)}
            for m in DECL_RE.finditer(masked)
        ]
        modules_out.append({
            "module": mod_name,
            "path": str(lf.relative_to(ROOT)),
            "badge": badge_for_module(mod_name),
            "summary": extract_lean_summary(raw),
            "line_count": len(raw.splitlines()),
            "imports": imports,
            "declaration_count": len(decls),
            "declarations": decls,
        })

    script_files = sorted(
        p for p in (ROOT / "scripts").glob("*.py")
        if p.is_file() and not p.is_symlink()
    )
    scripts_out: list[dict[str, Any]] = []
    for sf in script_files:
        raw = sf.read_text(encoding="utf-8")
        tree = ast.parse(raw, filename=str(sf))
        doc = (ast.get_docstring(tree) or "").strip()
        flags = sorted(set(FLAG_RE.findall(raw)))
        scripts_out.append({
            "name": sf.stem,
            "path": str(sf.relative_to(ROOT)),
            "badge": "host_script",
            "summary": doc,
            "cli_flags": flags,
        })

    return {
        "schema": "anneal-workbench/1",
        "toolchain": toolchain,
        "badges": {
            "pass1_portable": (
                "Pure `prelude` + 51 locked `Init.*` modules, 26 allowed theory tactics, "
                "zero `._unsafe_rec`, and standard axioms only; directly copyable into "
                "`anneal/theory/` or `anneal/correspondence/`."
            ),
            "lab_meta": (
                "Exploration, `#eval` counterexample/vacuity probing, and `Lean.Expr` / "
                "kernel replay profiling modules importing `Init`, `Std`, or `Lean`."
            ),
            "host_script": (
                "Standalone Python 3.10+ stdlib CLI diagnostics and certificate generators."
            ),
        },
        "modules": modules_out,
        "scripts": scripts_out,
    }


def render_catalog_json() -> str:
    return json.dumps(build_catalog_dict(), indent=2, ensure_ascii=False) + "\n"


def check_filesystem_and_headers() -> list[str]:
    errors: list[str] = []
    for dirpath, dirnames, filenames in os.walk(ROOT, followlinks=False):
        dp = pathlib.Path(dirpath)
        rel_dir = dp.relative_to(ROOT)
        if rel_dir.parts and rel_dir.parts[0] == ".git":
            dirnames[:] = []
            continue
        # Do not descend into ignored build caches, but reject symlinks anywhere
        pruned: list[str] = []
        for d in sorted(dirnames):
            child = dp / d
            if child.is_symlink():
                errors.append(f"Symlink directory forbidden: {child.relative_to(ROOT)}")
                continue
            if d in {".git", ".lake", "__pycache__"}:
                continue
            pruned.append(d)
        dirnames[:] = pruned

        for fn in sorted(filenames):
            fp = dp / fn
            rel = fp.relative_to(ROOT)
            if fp.is_symlink():
                errors.append(f"Symlink file forbidden: {rel}")
                continue
            if fp.suffix in {".olean", ".ilean", ".pyc"}:
                errors.append(f"Build/cache artifact outside ignored dir: {rel}")
                continue

            if fp.suffix in {".lean", ".py", ".md"}:
                txt = fp.read_text(encoding="utf-8")
                head = "\n".join(txt.splitlines()[:10])
                if "Copyright 2026 The Fuchsia Authors" not in head:
                    errors.append(f"Missing Fuchsia 2026 license header: {rel}")
                for label, pat in FORBIDDEN_PUBLIC_PATTERNS:
                    m = pat.search(txt)
                    if m:
                        errors.append(
                            f"Forbidden `{label}` match `{m.group(0)}` in {rel}"
                        )

            if (rel.parts[0] in {"scripts", "tools"} and fp.suffix == ".py"):
                if not os.access(fp, os.X_OK):
                    errors.append(f"Script must be executable (chmod +x): {rel}")

    return errors


def run_check(disable_wrapper: bool = False, skip_lean_build: bool = False) -> int:
    errors = check_filesystem_and_headers()

    # 1. Static Pass-1 check on `lean/Workbench/Pass1*`
    p1_targets = [
        str(ROOT / "lean" / "Workbench" / "Pass1.lean"),
        str(ROOT / "lean" / "Workbench" / "Pass1"),
    ]
    p1_files = proof_health_scan.collect_lean_files(p1_targets)
    for lf in p1_files:
        findings = proof_health_scan.scan_file(
            lf, force_pass1=True, allow_import_prefixes=("Workbench.Pass1.",)
        )
        for f in findings:
            errors.append(
                f"Pass-1 scan [{f['severity']}] {pathlib.Path(f['file']).relative_to(ROOT)}"
                f":{f['line']}:{f['column']} {f['code']}: {f['message']}"
            )

    # 2. Python syntax + CLI `--help` smoke tests
    for py_file in sorted([*(ROOT / "scripts").glob("*.py"), ROOT / "tools" / "workbench.py"]):
        try:
            py_compile.compile(str(py_file), doraise=True)
        except py_compile.PyCompileError as exc:
            errors.append(f"py_compile failed on {py_file.relative_to(ROOT)}: {exc}")
            continue
        proc = subprocess.run(
            [sys.executable, "-B", str(py_file), "--help"],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            errors.append(f"`--help` failed on {py_file.relative_to(ROOT)}: {proc.stderr}")

    # 3. Unit tests
    ut = subprocess.run(
        [sys.executable, "-B", "-m", "unittest", "discover", "-s", str(ROOT / "tests"), "-p", "test_*.py"],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if ut.returncode != 0:
        errors.append(f"Unit tests failed:\n{ut.stdout}\n{ut.stderr}")

    # 4. Lake build + CST syntax preflight + compiled Environment hygiene audit
    if not skip_lean_build:
        cst_report = preflight_syntax_check.run_syntax_preflight(
            files=p1_files,
            role="theory",
            lake_dir=ROOT / "lean",
            disable_wrapper=disable_wrapper,
        )
        if not cst_report["clean"]:
            for fr in cst_report["files"]:
                for v in fr["violations"]:
                    errors.append(
                        f"Pass-1 CST preflight {pathlib.Path(fr['file']).relative_to(ROOT)}"
                        f":{v['line']}:{v['column']}: {v['message']}"
                    )

        wrapper = find_build_wrapper(disable_wrapper)
        build_proc = subprocess.run(
            [*wrapper, "lake", "build"],
            cwd=str(ROOT / "lean"),
            capture_output=True,
            text=True,
            check=False,
        )
        if build_proc.returncode != 0:
            errors.append(
                f"`lake build` failed (exit {build_proc.returncode}):\n"
                f"{build_proc.stdout}\n{build_proc.stderr}"
            )
        else:
            p1_audit = audit_lean_hygiene.run_environment_audit(
                lake_dir=ROOT / "lean",
                modules=["Workbench.Pass1"],
                namespaces=["Workbench.Pass1"],
                disable_wrapper=disable_wrapper,
            )
            if not p1_audit["clean"]:
                errors.append(f"`Workbench.Pass1` environment hygiene failed: {json.dumps(p1_audit)}")

            lab_audit = audit_lean_hygiene.run_environment_audit(
                lake_dir=ROOT / "lean",
                modules=["Workbench.Lab"],
                namespaces=["Workbench.Lab"],
                disable_wrapper=disable_wrapper,
            )
            if lab_audit["sorry_decls"] or lab_audit["disallowed_axiom_decls"]:
                errors.append(f"`Workbench.Lab` axiom/sorry check failed: {json.dumps(lab_audit)}")

    # 5. CATALOG.json freshness check
    cat_path = ROOT / "CATALOG.json"
    expected_cat = render_catalog_json()
    if not cat_path.is_file():
        errors.append("Missing `CATALOG.json` (run `python3 tools/workbench.py catalog`).")
    elif cat_path.read_text(encoding="utf-8") != expected_cat:
        errors.append("`CATALOG.json` is out of date (run `python3 tools/workbench.py catalog`).")

    if errors:
        for err in errors:
            print(f"[FAIL] {err}", file=sys.stderr)
        return 1

    print("Workbench check passed: all hygiene, Pass-1, Lake, unit-test, and catalog gates green.")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_cat = sub.add_parser("catalog", help="Regenerate `CATALOG.json`.")
    p_cat.add_argument("--stdout", action="store_true", help="Print catalog JSON to stdout instead of writing.")

    p_chk = sub.add_parser("check", help="Validate repository hygiene, Lean build, tests, and catalog.")
    p_chk.add_argument("--no-wrapper", action="store_true", help="Invoke `lake` without `anneal-lean-run`.")
    p_chk.add_argument("--skip-lean-build", action="store_true", help="Skip `lake build` (fast static check).")

    args = parser.parse_args(argv)
    if args.cmd == "catalog":
        rendered = render_catalog_json()
        if args.stdout:
            sys.stdout.write(rendered)
        else:
            (ROOT / "CATALOG.json").write_text(rendered, encoding="utf-8")
            print(f"Wrote {ROOT / 'CATALOG.json'}.")
        return 0

    return run_check(
        disable_wrapper=args.no_wrapper,
        skip_lean_build=args.skip_lean_build,
    )


if __name__ == "__main__":
    sys.exit(main())
