# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Repository hygiene checks for public distribution boundaries."""

import os
from pathlib import Path
import re
import subprocess
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
    # `-z` avoids Git's C-quoting of paths with quotes or non-ASCII bytes.
    out = subprocess.check_output(
        ["git", "-C", str(REPO_ROOT), "ls-files", "-z"],
    )
    return [
        rel for rel in out.decode("utf-8", "surrogateescape").split("\0") if rel
    ]


def _tracked_text(path: Path) -> str | None:
    """Read a file, or a symlink's target, as `check_pr_hygiene.py` does.

    Bytes are decoded by `cph.scannable_text` without newline translation;
    binary content yields `None`.
    """
    try:
        if path.is_symlink():
            raw = os.fsencode(os.readlink(path))
        elif path.is_file():
            raw = path.read_bytes()
        else:
            return None
    except OSError:
        return None
    return cph.scannable_text(raw)


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
            cr_text = _tracked_text(cr_file)
            self.assertIsNotNone(cr_text)
            self.assertEqual(
                cph.internal_reference_hits(cr_text or ""),
                [(2, "internal-cli")],
            )
            broken = root / "dangling"
            os.symlink(mnt, broken)
            link_text = _tracked_text(broken)
            self.assertEqual(link_text, mnt)
            self.assertEqual(
                cph.internal_reference_hits(link_text or ""),
                [(1, "internal-mount")],
            )
            binary = root / "bad.bin"
            binary.write_bytes(b"\x00\xff\xfe" + cli.encode())
            self.assertIsNone(_tracked_text(binary))
            # A stray invalid byte in text does not hide a reference.
            latin1 = root / "latin1.txt"
            latin1.write_bytes(b"caf\xe9\n" + cli.encode() + b"\n")
            self.assertEqual(
                cph.internal_reference_hits(_tracked_text(latin1) or ""),
                [(2, "internal-cli")],
            )

    def test_no_ephemeral_batons_or_internal_skills(self) -> None:
        bad_paths: list[str] = []
        for rel in _tracked_files():
            if _BANNED_FILENAME_RE.search(rel) or rel.startswith(
                _BANNED_INTERNAL_PREFIXES
            ):
                bad_paths.append(rel)
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
            text = _tracked_text(REPO_ROOT / rel)
            if text is None:
                continue
            for line_no, label in cph.internal_reference_hits(text):
                violations.append(f"{rel}:{line_no} [{label}]")
        self.assertEqual(
            violations,
            [],
            "Internal infrastructure references found in tracked files:\n"
            + "\n".join(violations[:40]),
        )


if __name__ == "__main__":
    unittest.main()
