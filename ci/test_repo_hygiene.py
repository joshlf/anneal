# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Repository hygiene checks for public distribution boundaries."""

from pathlib import Path
import re
import subprocess
import sys
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
    out = subprocess.check_output(
        ["git", "-C", str(REPO_ROOT), "ls-files"],
        text=True,
    )
    return [line for line in out.splitlines() if line]


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
            path = REPO_ROOT / rel
            if not path.is_file():
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
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
