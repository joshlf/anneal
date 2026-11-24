# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_todo.sh`."""

import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parent / "check_todo.sh"
MARKER = "T" + "ODO"
DISABLE = f"{MARKER}-check-disable"
ENABLE = f"{MARKER}-check-enable"

_RG_SHIM_SOURCE = r'''
import fnmatch
import os
from pathlib import Path
import re
import sys


def glob_matches(rel_posix: str, pat: str) -> bool:
    pat = pat.lstrip("/")
    candidates = [rel_posix, os.path.basename(rel_posix)]
    if pat.startswith("**/"):
        sub = pat[3:]
        for c in candidates:
            if fnmatch.fnmatch(c, sub) or fnmatch.fnmatch(rel_posix, pat):
                return True
        parts = Path(rel_posix).parts
        if sub.endswith("/**"):
            target = sub[:-3]
            if target in parts:
                return True
    return any(fnmatch.fnmatch(c, pat) for c in candidates)


def excluded_by_globs(rel_posix: str, globs: list[str]) -> bool:
    excluded = False
    for g in globs:
        if g.startswith("!"):
            if glob_matches(rel_posix, g[1:]):
                excluded = True
        else:
            if glob_matches(rel_posix, g):
                excluded = False
    return excluded


def search_bytes(data: bytes, pattern: re.Pattern[str], prefix: str | None) -> int:
    if b"\x00" in data:
        return 0
    count = 0
    text = data.decode("utf-8", errors="surrogateescape")
    for idx, line in enumerate(text.splitlines(), 1):
        if pattern.search(line):
            if prefix is not None:
                sys.stdout.write(f"{prefix}:{idx}:{line}\n")
            else:
                sys.stdout.write(f"{idx}:{line}\n")
            count += 1
    return count


def main() -> int:
    args = sys.argv[1:]
    with_filename = False
    line_number = False
    word_regexp = False
    globs: list[str] = []
    positional: list[str] = []
    i = 0
    end_of_opts = False
    while i < len(args):
        arg = args[i]
        if end_of_opts:
            positional.append(arg)
            i += 1
            continue
        if arg == "--":
            end_of_opts = True
            i += 1
            continue
        if arg == "--version":
            sys.stdout.write("ripgrep 14.0.0 (python fallback)\n")
            return 0
        if arg == "--no-heading":
            i += 1
            continue
        if arg == "--glob":
            if i + 1 >= len(args):
                sys.stderr.write("rg: --glob requires a value\n")
                return 2
            globs.append(args[i + 1])
            i += 2
            continue
        if arg.startswith("--glob="):
            globs.append(arg.split("=", 1)[1])
            i += 1
            continue
        if arg.startswith("-") and len(arg) > 1 and not arg.startswith("--"):
            for ch in arg[1:]:
                if ch == "n":
                    line_number = True
                elif ch == "w":
                    word_regexp = True
                elif ch == "H":
                    with_filename = True
                else:
                    sys.stderr.write(f"rg: unsupported option -{ch}\n")
                    return 2
            i += 1
            continue
        if arg.startswith("--"):
            sys.stderr.write(f"rg: unsupported option {arg}\n")
            return 2
        positional.append(arg)
        i += 1

    if not positional:
        sys.stderr.write("rg: missing pattern\n")
        return 2
    raw_pat = positional[0]
    paths = positional[1:]
    if word_regexp:
        raw_pat = rf"\b(?:{raw_pat})\b"
    try:
        regex = re.compile(raw_pat)
    except re.error as err:
        sys.stderr.write(f"rg: invalid regex: {err}\n")
        return 2

    if not paths:
        data = sys.stdin.buffer.read()
        matched = search_bytes(data, regex, None if line_number or not with_filename else "(stdin)")
        return 0 if matched > 0 else 1

    total_matches = 0
    had_error = False
    show_file = with_filename or len(paths) > 1 or any(os.path.isdir(p) for p in paths)
    for target in paths:
        p = Path(target)
        if not p.exists():
            sys.stderr.write(f"rg: {target}: No such file or directory (os error 2)\n")
            had_error = True
            continue
        if p.is_file():
            rel_posix = p.as_posix()
            if excluded_by_globs(rel_posix, globs):
                continue
            try:
                data = p.read_bytes()
            except OSError as err:
                sys.stderr.write(f"rg: {target}: {err}\n")
                had_error = True
                continue
            total_matches += search_bytes(data, regex, target if show_file else None)
            continue
        if p.is_dir():
            for dirpath, dirnames, filenames in os.walk(target):
                dirnames[:] = sorted(
                    d for d in dirnames
                    if not d.startswith(".")
                    and not excluded_by_globs(Path(dirpath, d, "x").as_posix(), globs)
                )
                for fname in sorted(filenames):
                    if fname.startswith("."):
                        continue
                    fpath = Path(dirpath) / fname
                    fstr = str(fpath)
                    if excluded_by_globs(fpath.as_posix(), globs):
                        continue
                    try:
                        data = fpath.read_bytes()
                    except OSError as err:
                        sys.stderr.write(f"rg: {fstr}: {err}\n")
                        had_error = True
                        continue
                    total_matches += search_bytes(data, regex, fstr if show_file else None)
            continue
        sys.stderr.write(f"rg: {target}: unsupported path type\n")
        had_error = True

    if had_error:
        return 2
    return 0 if total_matches > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
'''


def run_git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            *args,
        ],
        cwd=repo,
        capture_output=True,
        text=True,
        check=True,
    )


class CheckTodoTests(unittest.TestCase):
    def make_repo(self, tmp: str) -> tuple[Path, Path, Path]:
        """Create a minimal Git repo with `anneal/ci/check_todo.sh`."""
        root = Path(tmp) / "repo"
        anneal = root / "anneal"
        ci_dir = anneal / "ci"
        ci_dir.mkdir(parents=True)

        script_copy = ci_dir / "check_todo.sh"
        shutil.copyfile(SCRIPT, script_copy)
        script_copy.chmod(script_copy.stat().st_mode | stat.S_IXUSR)

        (root / "README.md").write_text("root readme\n", encoding="utf-8")
        (anneal / "README.md").write_text("anneal readme\n", encoding="utf-8")

        run_git(root, "init", "-q", "-b", "main")
        run_git(root, "config", "user.name", "Test")
        run_git(root, "config", "user.email", "test@example.com")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "Initial commit")
        return root, anneal, script_copy

    def run_check(
        self, script: Path, *args: str, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        if shutil.which("rg") is not None:
            return subprocess.run(
                [str(script), *args],
                cwd=cwd,
                input="",
                capture_output=True,
                text=True,
                check=False,
            )
        with tempfile.TemporaryDirectory(prefix="anneal-rg-shim-") as shim_dir:
            rg_shim = Path(shim_dir) / "rg"
            rg_shim.write_text(
                f"#!{sys.executable}\n{_RG_SHIM_SOURCE.lstrip()}",
                encoding="utf-8",
            )
            rg_shim.chmod(0o755)
            env = os.environ.copy()
            env["PATH"] = f"{shim_dir}{os.pathsep}{env.get('PATH', '')}"
            return subprocess.run(
                [str(script), *args],
                cwd=cwd,
                env=env,
                input="",
                capture_output=True,
                text=True,
                check=False,
            )

    def test_clean_repo_passes(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-clean-") as tmp:
            _, anneal, script = self.make_repo(tmp)
            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_commit_message_cannot_use_disable_directive(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-msg-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            run_git(root, "checkout", "-qb", "feature")
            (anneal / "clean.txt").write_text("clean\n", encoding="utf-8")
            run_git(root, "add", "anneal/clean.txt")
            run_git(
                root,
                "commit",
                "-qm",
                f"Allow {DISABLE}\n\n{MARKER}: sneak past CI\n",
            )

            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("COMMIT_MESSAGE(", res.stderr)
            self.assertIn(f"{MARKER}: sneak past CI", res.stderr)

    def test_commit_message_with_only_disable_directive_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-dir-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            run_git(root, "checkout", "-qb", "feature")
            # Include a valid disabled marker in a source file too so the
            # source-file loop also runs and must preserve exit_code=1.
            (anneal / "doc.md").write_text(
                f"<!-- {DISABLE} -->\n{MARKER}(#123): tracked\n"
                f"<!-- {ENABLE} -->\n",
                encoding="utf-8",
            )
            run_git(root, "add", "anneal/doc.md")
            run_git(root, "commit", "-qm", f"Mention {DISABLE} in commit")

            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("COMMIT_MESSAGE(", res.stderr)
            self.assertIn(DISABLE, res.stderr)

    def test_nonexistent_and_empty_path_args_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-missing-") as tmp:
            _, anneal, script = self.make_repo(tmp)

            missing = self.run_check(script, "nonexistent.rs", cwd=anneal)
            self.assertNotEqual(missing.returncode, 0, missing.stdout)
            self.assertIn("nonexistent.rs", missing.stderr)

            empty = self.run_check(script, "", cwd=anneal)
            self.assertNotEqual(empty.returncode, 0, empty.stdout)
            self.assertIn("must not be empty", empty.stderr)

    def test_relative_path_arg_resolves_against_caller_pwd(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-pwd-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            # Put a bare marker in the parent root README while keeping
            # `anneal/README.md` clean so resolving relative to `anneal/`
            # instead of caller `$PWD` would miss the violation.
            (root / "README.md").write_text(
                f"{MARKER}: root marker\n", encoding="utf-8"
            )

            from_root_bad = self.run_check(script, "README.md", cwd=root)
            self.assertEqual(
                from_root_bad.returncode,
                1,
                from_root_bad.stdout + from_root_bad.stderr,
            )
            self.assertIn(f"{MARKER}: root marker", from_root_bad.stderr)

            from_root_good = self.run_check(
                script, "anneal/README.md", cwd=root
            )
            self.assertEqual(
                from_root_good.returncode,
                0,
                from_root_good.stdout + from_root_good.stderr,
            )

            from_ci_subdir = self.run_check(
                script, "../README.md", cwd=anneal / "ci"
            )
            self.assertEqual(
                from_ci_subdir.returncode,
                0,
                from_ci_subdir.stdout + from_ci_subdir.stderr,
            )

    def test_source_disable_enable_and_vendor_exclusion(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-src-") as tmp:
            _, anneal, script = self.make_repo(tmp)
            vendor_file = anneal / "vendor/dep/lib.rs"
            vendor_file.parent.mkdir(parents=True)
            vendor_file.write_text(
                f"// {MARKER}: upstream vendor note\n", encoding="utf-8"
            )

            # Wrapped marker with issue citation passes.
            exempt = anneal / "exempt.rs"
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked follow-up\n"
                f"// {ENABLE}\n",
                encoding="utf-8",
            )
            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            # A bare marker after re-enabling (even with `(#123):`) fails.
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked follow-up\n"
                f"// {ENABLE}\n// {MARKER}(#123): unexempt after enable\n",
                encoding="utf-8",
            )
            res_after = self.run_check(script, cwd=anneal)
            self.assertEqual(
                res_after.returncode, 1, res_after.stdout + res_after.stderr
            )
            self.assertIn("unexempt after enable", res_after.stderr)

    def test_git_grep_operational_error_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-outside-") as tmp:
            _, anneal, script = self.make_repo(tmp)
            outside = Path(tmp) / "outside.txt"
            outside.write_text("clean external file\n", encoding="utf-8")

            res = self.run_check(script, str(outside), cwd=anneal)
            self.assertNotEqual(res.returncode, 0, res.stdout)
            self.assertIn("outside repository", res.stderr)


if __name__ == "__main__":
    unittest.main()
