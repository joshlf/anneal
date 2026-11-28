#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Stages a <100 KB standalone 1-package `reference-corpus/1` tree and runs `reference.py check`."""

from __future__ import annotations

import argparse
import datetime
import io
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tarfile
from typing import Any

CORPUS_INFRA_FILES: tuple[str, ...] = (
    ".gitignore",
    "AGENTS.md",
    "CORPUS.json",
    "CORPUS.md",
    "FORMAT.md",
    "README.md",
    "SHARED-RESOURCES.json",
    "tools/reference.py",
    "tests/test_reference.py",
)
REQUIRED_TEMPLATE_FILES: tuple[str, ...] = (
    "AGENTS.md",
    "CORPUS.json",
    "FORMAT.md",
    "README.md",
    "tools/reference.py",
    "tests/test_reference.py",
)
SLUG_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")


def _git_has_ref_file(repo: pathlib.Path, ref: str, rel_path: str) -> bool:
    proc = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", f"{ref}:{rel_path}"],
        capture_output=True,
        check=False,
    )
    return proc.returncode == 0


def resolve_corpus_repo_and_ref(
    explicit_repo: str | None,
    explicit_ref: str | None,
) -> tuple[pathlib.Path, str]:
    refs_to_try = (
        [explicit_ref]
        if explicit_ref
        else ["origin/reference", "refs/heads/reference", "reference"]
    )
    repo_candidates: list[pathlib.Path] = []
    if explicit_repo:
        repo_candidates.append(pathlib.Path(explicit_repo).expanduser().resolve())
    env_repo = os.environ.get("REFERENCE_CORPUS_REPO")
    if env_repo:
        repo_candidates.append(pathlib.Path(env_repo).expanduser().resolve())
    top_proc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if top_proc.returncode == 0 and top_proc.stdout.strip():
        repo_candidates.append(pathlib.Path(top_proc.stdout.strip()).resolve())
    default_zc = pathlib.Path.home() / "workspace" / "zerocopy"
    if default_zc.is_dir():
        repo_candidates.append(default_zc.resolve())

    for repo in repo_candidates:
        if not repo.is_dir():
            continue
        for ref in refs_to_try:
            if _git_has_ref_file(repo, ref, "CORPUS.json") and _git_has_ref_file(
                repo, ref, "tools/reference.py"
            ):
                return repo, ref

    raise FileNotFoundError(
        "Could not locate a git repository with `reference` corpus infrastructure; "
        "pass `--corpus-repo <git_dir>` or `--template-dir <corpus_dir>`."
    )


def materialize_from_git(repo: pathlib.Path, ref: str, out_dir: pathlib.Path) -> list[str]:
    existing = [p for p in CORPUS_INFRA_FILES if _git_has_ref_file(repo, ref, p)]
    proc = subprocess.run(
        ["git", "-C", str(repo), "archive", "--format=tar", ref, "--", *existing],
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        stderr = proc.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"`git archive` failed on {repo} ({ref}): {stderr}")

    staged: list[str] = []
    with tarfile.open(fileobj=io.BytesIO(proc.stdout), mode="r:") as tf:
        for member in tf.getmembers():
            if not member.isfile():
                continue
            rel = pathlib.Path(member.name)
            if rel.is_absolute() or ".." in rel.parts:
                raise ValueError(f"Unsafe archive path: {member.name}")
            dest = out_dir / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            extracted = tf.extractfile(member)
            if extracted is None:
                continue
            dest.write_bytes(extracted.read())
            os.chmod(dest, 0o755 if rel.as_posix() == "tools/reference.py" else 0o644)
            staged.append(rel.as_posix())
    return sorted(staged)


def materialize_from_template_dir(template_dir: pathlib.Path, out_dir: pathlib.Path) -> list[str]:
    src_root = template_dir.resolve()
    for req in REQUIRED_TEMPLATE_FILES:
        if not (src_root / req).is_file():
            raise FileNotFoundError(f"Template directory missing required file `{req}`: {src_root}")
    staged: list[str] = []
    for rel_str in CORPUS_INFRA_FILES:
        src = src_root / rel_str
        if not src.is_file():
            continue
        dest = out_dir / rel_str
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(src.read_bytes())
        os.chmod(dest, 0o755 if rel_str == "tools/reference.py" else 0o644)
        staged.append(rel_str)
    return sorted(staged)


def copy_tree_no_symlinks(src_dir: pathlib.Path, dst_dir: pathlib.Path) -> None:
    for root, dirnames, filenames in os.walk(src_dir, followlinks=False):
        rp = pathlib.Path(root)
        rel_root = rp.relative_to(src_dir)
        dirnames[:] = [d for d in sorted(dirnames) if d != "__pycache__"]
        for d in dirnames:
            if (rp / d).is_symlink():
                raise ValueError(f"Symlink directory forbidden in report package: {rp / d}")
        target_root = dst_dir / rel_root
        target_root.mkdir(parents=True, exist_ok=True)
        for fn in sorted(filenames):
            if fn.endswith(".pyc"):
                continue
            sp = rp / fn
            if sp.is_symlink():
                raise ValueError(f"Symlink file forbidden in report package: {sp}")
            shutil.copy2(sp, target_root / fn)


def render_starter_report_md(title: str) -> str:
    return (
        f"# {title}\n\n"
        "## Summary\n\n"
        "Pending synthesis of primary-source and empirical findings.\n\n"
        "## Applicability\n\n"
        "Applies to the pinned repository and toolchain revisions recorded in `REPORT.json`.\n\n"
        "## Findings\n\n"
        "Initial staged package awaiting report body population.\n\n"
        "## Boundaries\n\n"
        "Scoped strictly to the subjects declared in `REPORT.json`.\n\n"
        "## Evidence\n\n"
        "Evidence artifacts and reproducible probes live under `support/` when applicable.\n\n"
        "## Revalidation\n\n"
        "Run `python3 -B tools/reference.py catalog && python3 -B tools/reference.py check`.\n"
    )


def measure_tree(root: pathlib.Path) -> tuple[int, int]:
    total_bytes = 0
    file_count = 0
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = [d for d in dirnames if d != "__pycache__"]
        dp = pathlib.Path(dirpath)
        for fn in filenames:
            fp = dp / fn
            if fp.is_file() and not fp.is_symlink():
                file_count += 1
                total_bytes += fp.stat().st_size
    return file_count, total_bytes


def stage_package(
    *,
    out_dir: pathlib.Path,
    slug: str | None,
    corpus_repo: str | None = None,
    corpus_ref: str | None = None,
    template_dir: str | None = None,
    from_report_dir: str | None = None,
    title: str | None = None,
    topics: list[str] | None = None,
    subject_name: str = "Anneal workspace",
    subject_repo: str = "google/zerocopy",
    subject_rev: str | None = None,
    observed_at: str | None = None,
    with_support: bool = False,
    max_bytes: int = 102400,
    run_unit_tests: bool = False,
) -> tuple[int, dict[str, Any]]:
    dest = out_dir.expanduser().resolve()
    if from_report_dir and not slug:
        slug = pathlib.Path(from_report_dir).resolve().name
    if slug is not None and not SLUG_RE.fullmatch(slug):
        return 2, {
            "passed": False,
            "error": (
                f"Invalid report slug `{slug}`: must be lowercase ASCII words "
                "separated by single hyphens."
            ),
        }

    dest.mkdir(parents=True, exist_ok=True)
    source_desc: str
    resolved_repo: pathlib.Path | None = None
    if template_dir:
        staged_infra = materialize_from_template_dir(pathlib.Path(template_dir), dest)
        source_desc = f"template:{pathlib.Path(template_dir).resolve()}"
    else:
        resolved_repo, resolved_ref = resolve_corpus_repo_and_ref(corpus_repo, corpus_ref)
        staged_infra = materialize_from_git(resolved_repo, resolved_ref, dest)
        source_desc = f"git:{resolved_repo}@{resolved_ref}"

    reports_root = dest / "reports"
    reports_root.mkdir(exist_ok=True)

    if slug:
        pkg_dir = reports_root / slug
        if from_report_dir:
            src_rep = pathlib.Path(from_report_dir).expanduser().resolve()
            if not (src_rep / "REPORT.json").is_file() or not (src_rep / "REPORT.md").is_file():
                return 2, {
                    "passed": False,
                    "error": f"`--from-report-dir` must contain `REPORT.json` and `REPORT.md`: {src_rep}",
                }
            copy_tree_no_symlinks(src_rep, pkg_dir)
        else:
            pkg_dir.mkdir(parents=True, exist_ok=True)
            if with_support:
                (pkg_dir / "support").mkdir(exist_ok=True)
            policy_data = json.loads((dest / "CORPUS.json").read_text(encoding="utf-8"))
            allowed_ns = sorted(policy_data.get("topic_namespaces", []))
            default_ns = "anneal" if "anneal" in allowed_ns else allowed_ns[0]
            chosen_topics = list(topics) if topics else [f"{default_ns}/architecture"]
            rev = subject_rev
            if not rev and resolved_repo is not None:
                head_p = subprocess.run(
                    ["git", "-C", str(resolved_repo), "rev-parse", "HEAD"],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                if head_p.returncode == 0 and head_p.stdout.strip():
                    rev = head_p.stdout.strip()
            rev = rev or ("0" * 40)
            obs = observed_at or datetime.date.today().isoformat()
            rep_json = pkg_dir / "REPORT.json"
            if not rep_json.exists():
                rep_json.write_text(
                    json.dumps(
                        {
                            "topics": chosen_topics,
                            "subjects": [
                                {
                                    "name": subject_name,
                                    "identity": {
                                        "repository": subject_repo,
                                        "revision": rev,
                                    },
                                }
                            ],
                            "observed_at": obs,
                        },
                        indent=2,
                    )
                    + "\n",
                    encoding="utf-8",
                )
            rep_md = pkg_dir / "REPORT.md"
            if not rep_md.exists():
                human_title = title or slug.replace("-", " ").title()
                rep_md.write_text(render_starter_report_md(human_title), encoding="utf-8")

    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    ref_script = str(dest / "tools" / "reference.py")

    cat_proc = subprocess.run(
        [sys.executable, "-B", ref_script, "catalog"],
        cwd=str(dest),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    chk_proc = subprocess.run(
        [sys.executable, "-B", ref_script, "check"],
        cwd=str(dest),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )

    ut_rc = 0
    ut_err = ""
    if run_unit_tests and chk_proc.returncode == 0:
        ut_proc = subprocess.run(
            [sys.executable, "-B", "-m", "unittest", "discover", "-s", "tests", "-p", "test_*.py"],
            cwd=str(dest),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        ut_rc = ut_proc.returncode
        ut_err = ut_proc.stderr.strip()[-400:]

    file_count, total_bytes = measure_tree(dest)
    enforce_budget = max_bytes > 0 and not from_report_dir
    under_budget = (total_bytes <= max_bytes) if enforce_budget else True
    passed = (
        cat_proc.returncode == 0
        and chk_proc.returncode == 0
        and ut_rc == 0
        and under_budget
    )
    report: dict[str, Any] = {
        "passed": passed,
        "out_dir": str(dest),
        "slug": slug,
        "source": source_desc,
        "infra_files_staged": len(staged_infra),
        "file_count": file_count,
        "total_bytes": total_bytes,
        "total_kib": round(total_bytes / 1024.0, 2),
        "max_bytes": max_bytes if enforce_budget else None,
        "under_size_budget": under_budget,
        "catalog_rc": cat_proc.returncode,
        "check_rc": chk_proc.returncode,
        "check_stdout": chk_proc.stdout.strip(),
        "check_stderr": (cat_proc.stderr + "\n" + chk_proc.stderr).strip()[:500],
    }
    if run_unit_tests:
        report["unit_tests_rc"] = ut_rc
        if ut_rc != 0:
            report["unit_tests_stderr"] = ut_err
    return (0 if passed else 1), report


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", required=True, help="Target directory for the staged 1-package tree.")
    ap.add_argument("--slug", help="Report package slug under `reports/<slug>/` (kebab-case).")
    ap.add_argument(
        "--corpus-repo",
        "--repo",
        dest="corpus_repo",
        help="Git checkout containing the `reference` branch (default: auto-detected).",
    )
    ap.add_argument(
        "--corpus-ref",
        "--ref",
        dest="corpus_ref",
        help="Git ref for corpus infrastructure files (default: `origin/reference`).",
    )
    ap.add_argument(
        "--template-dir",
        help="Copy corpus infrastructure files from an existing `reference-corpus/1` directory.",
    )
    ap.add_argument(
        "--from-report-dir",
        help="Populate `reports/<slug>/` from an existing report directory.",
    )
    ap.add_argument("--title", help="Starter `REPORT.md` H1 title when scaffolding a new report.")
    ap.add_argument(
        "--topic",
        action="append",
        default=[],
        help="Starter `REPORT.json` topic label `<namespace>/<topic>` (repeatable).",
    )
    ap.add_argument(
        "--subject-name",
        default="Anneal workspace",
        help="Starter `REPORT.json` subject name.",
    )
    ap.add_argument(
        "--subject-repo",
        default="google/zerocopy",
        help="Starter `REPORT.json` subject repository identity.",
    )
    ap.add_argument("--subject-rev", help="Starter `REPORT.json` subject revision SHA.")
    ap.add_argument("--observed-at", help="Starter `REPORT.json` date (`YYYY-MM-DD`).")
    ap.add_argument(
        "--with-support",
        action="store_true",
        help="Create `reports/<slug>/support/` directory.",
    )
    ap.add_argument(
        "--max-bytes",
        type=int,
        default=102400,
        help="Maximum staged byte budget for scaffolded packages (default: 102400 = 100 KiB).",
    )
    ap.add_argument(
        "--run-unit-tests",
        action="store_true",
        help="Also run `tests/test_reference.py` inside the staged tree.",
    )
    ap.add_argument("--json", action="store_true", help="Emit JSON summary to stdout.")
    return ap


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    rc, report = stage_package(
        out_dir=pathlib.Path(args.out_dir),
        slug=args.slug,
        corpus_repo=args.corpus_repo,
        corpus_ref=args.corpus_ref,
        template_dir=args.template_dir,
        from_report_dir=args.from_report_dir,
        title=args.title,
        topics=list(args.topic) if args.topic else None,
        subject_name=args.subject_name,
        subject_repo=args.subject_repo,
        subject_rev=args.subject_rev,
        observed_at=args.observed_at,
        with_support=args.with_support,
        max_bytes=args.max_bytes,
        run_unit_tests=args.run_unit_tests,
    )
    if args.json:
        print(json.dumps(report, indent=2))
    elif report.get("passed"):
        print(
            f"[PASS] Staged `{report['slug'] or 'empty'}` at {report['out_dir']} "
            f"({report['total_kib']} KiB across {report['file_count']} files; "
            f"{report['check_stdout']})"
        )
    else:
        err = report.get("error") or report.get("check_stderr") or json.dumps(report)
        print(f"[FAIL] {err}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
