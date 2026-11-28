# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Repository hygiene checks for public distribution boundaries."""

from pathlib import Path
import os
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
# `check_pr_hygiene.py` runs isolated (`python3 -I`) and cannot import this
# module, so it owns the shared definitions and this test imports them. Both
# checks therefore enforce the same filenames, prefixes, and patterns.
import check_pr_hygiene as cph  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent

# Exclude vendored third-party corpora whose upstream prose is outside Anneal's
# authoring boundary.
_EXCLUDED_PREFIXES = (
    "minirust/vendor/",
    "theory/MiniRust/vendor/",
)

_BANNED_FILENAME_RE = cph.BANNED_FILENAME_RE
_BANNED_INTERNAL_PREFIXES = cph.BANNED_INTERNAL_PREFIXES
_BANNED_CONTENT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    cph.BANNED_CONTENT_PATTERNS
)


def _tracked_files() -> list[str]:
    # `cph.Git` strips ambient `GIT_*` variables and global config; `-z` avoids
    # Git's C-quoting of paths containing quotes or non-ASCII bytes.
    out = cph.Git(REPO_ROOT).run("ls-files", "-z")
    return [
        rel for rel in out.decode("utf-8", "surrogateescape").split("\0") if rel
    ]


def _tracked_blob(path: Path, rel: str = "") -> tuple[str, bool] | None:
    """Read a file, or a symlink's target, as `check_pr_hygiene.py` does.

    Bytes are decoded by `cph.decode_blob` without newline translation into
    `(text, binary)`; `None` means there is nothing to read.
    """
    try:
        if path.is_symlink():
            raw = os.fsencode(os.readlink(path))
            return cph.decode_blob(raw, rel or path.name, is_symlink=True)
        if path.is_file():
            return cph.decode_blob(path.read_bytes(), rel or path.name)
        return None
    except OSError:
        return None


def _hits(blob: tuple[str, bool] | None) -> list[tuple[int, str]]:
    if blob is None:
        return []
    text, binary = blob
    return cph.internal_reference_hits(text, binary=binary)


class RepoHygieneTests(unittest.TestCase):
    def test_shared_patterns_flag_internal_tokens(self) -> None:
        # Built from parts, like the patterns themselves. A short local
        # binding that spells the internal CLI is still a violation; the
        # descriptive spelling is not.
        cli = "cp" + "L"
        self.assertEqual(len(_BANNED_CONTENT_PATTERNS), 27)
        self.assertEqual(
            cph.internal_reference_hits(f"let (ty, {cli}, r) := x\n"),
            [(1, "internal-cli")],
        )
        self.assertEqual(
            cph.internal_reference_hits("let (ty, checkPtrL, r) := x\n"),
            [],
        )

    def test_symlink_and_cr_reading_matches_pr_hygiene(self) -> None:
        cli = "cp" + "L"
        mnt = "/x" + "20/missing"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cr_file = root / "cr.txt"
            cr_file.write_bytes(f"first\rsecond\n{cli}\n".encode())
            self.assertEqual(_hits(_tracked_blob(cr_file)),
                             [(2, "internal-cli")])
            broken = root / "dangling"
            os.symlink(mnt, broken)
            self.assertEqual(_tracked_blob(broken), (mnt, False))
            self.assertEqual(_hits(_tracked_blob(broken)),
                             [(1, "internal-mount")])
            # Binary blobs skip only the shortest patterns.
            binary = root / "bad.bin"
            binary.write_bytes(b"\x00\xff\xfe " + cli.encode() + b" "
                               + mnt.encode())
            self.assertTrue(_tracked_blob(binary)[1])
            self.assertEqual(_hits(_tracked_blob(binary)),
                             [(1, "internal-mount")])
            # A stray invalid byte in text does not hide a reference.
            latin1 = root / "latin1.txt"
            latin1.write_bytes(b"caf\xe9\n" + cli.encode() + b"\n")
            self.assertEqual(_hits(_tracked_blob(latin1)),
                             [(2, "internal-cli")])
            # Known source/prose paths are text even with NUL + 0xff.
            sneaky_md = root / "sneaky.md"
            sneaky_md.write_bytes(b"\x00\xff\n" + cli.encode() + b"\n")
            self.assertEqual(
                _hits(_tracked_blob(sneaky_md, "docs/sneaky.md")),
                [(2, "internal-cli")],
            )

    def test_tracked_files_ignores_ambient_git_dir(self) -> None:
        old = os.environ.get("GIT_DIR")
        os.environ["GIT_DIR"] = "/nonexistent-git-dir"
        try:
            tracked = _tracked_files()
        finally:
            if old is None:
                os.environ.pop("GIT_DIR", None)
            else:
                os.environ["GIT_DIR"] = old
        self.assertIn("ci/test_repo_hygiene.py", tracked)

    def test_no_ephemeral_batons_or_internal_skills(self) -> None:
        bad_paths = [
            rel
            for rel in _tracked_files()
            if cph.internal_path_message(rel, cph.STANDALONE) is not None
        ]
        self.assertEqual(
            bad_paths,
            [],
            f"Tracked files contain internal/ephemeral paths: {bad_paths}",
        )

    def test_no_internal_infrastructure_references(self) -> None:
        violations: list[str] = []
        for rel in _tracked_files():
            if rel.startswith(_EXCLUDED_PREFIXES):
                continue
            for line_no, label in _hits(_tracked_blob(REPO_ROOT / rel, rel)):
                violations.append(f"{rel}:{line_no} [{label}]")
        self.assertEqual(
            violations,
            [],
            "Internal infrastructure references found in tracked files:\n"
            + "\n".join(violations[:40]),
        )


if __name__ == "__main__":
    unittest.main()
