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
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent

# Exclude vendored third-party corpora whose upstream prose is outside Anneal's
# authoring boundary.
_EXCLUDED_PREFIXES = (
    "minirust/vendor/",
    "theory/MiniRust/vendor/",
)

_BANNED_FILENAME_RE = re.compile(r"(^|/)(HANDOFF|PROGRESS|REPRODUCE[^/]*)\.md$")
_BANNED_INTERNAL_PREFIXES = (
    "skills/adversarial-rounds/",
    "skills/hierarchical-supervision/",
)

# Constructed from parts so this test module does not contain verbatim banned
# strings itself.
_BANNED_CONTENT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = tuple(
    (label, re.compile(pat, re.IGNORECASE))
    for label, pat in (
        ("internal-client", r"\b" + "jet" + r"ski\b"),
        ("internal-service", r"\b" + "rshell" + r"d\b"),
        ("internal-cli", r"\b" + "cp" + r"l\b"),
        ("internal-user-m", r"\b" + "mark" + r"dittmer\b"),
        ("internal-user-j", r"\b" + "jsw" + r"renn\b"),
        ("internal-mount", r"/x" + r"20\b"),
        ("internal-remote", r"/rem" + r"ote/"),
        ("internal-fuse", r"/mnt/" + r"fuse/"),
        ("internal-sync-bin", r"remote-" + r"sync\b"),
        ("internal-fsd", r"remote" + r"fsd\b"),
        ("internal-proto", r"storage_" + r"remote\b"),
        ("internal-envelope", r"MessageSet" + r"Payload\b"),
        ("internal-workstation", r"/usr/local/" + r"google\b"),
        ("internal-sidecar-uri", r"sidecar:" + r"//"),
        ("internal-repo", r"anneal-" + r"private\b"),
        ("internal-team-dir", r"teams/anneal-" + r"agent\b"),
        ("internal-placeholder", r"Projects/" + r"<"),
        ("internal-flag-remote", r"--remote-" + r"uri\b"),
        ("internal-flag-ff", r"--verify-bundle-" + r"ff\b"),
        ("internal-flag-chk", r"--check-unstable-" + r"ff\b"),
        ("internal-sym-sync", r"REMOTE_" + r"SYNC"),
        ("internal-launcher", r"run_capsule_" + r"diff_test"),
        ("internal-bucket-tf", r"team" + r"food\b"),
        ("internal-bucket-wtu", r"3p-" + r"wtu\b"),
        ("internal-infra-fsd", r"x20" + r"fsd\b"),
        ("internal-fleet-cfg", r"fleet_" + r"node\b"),
        ("internal-fleet-dir", r"fleet-" + r"management\b"),
    )
)


def _tracked_files() -> list[str]:
    out = subprocess.check_output(
        ["git", "-C", str(REPO_ROOT), "ls-files"],
        text=True,
    )
    return [line for line in out.splitlines() if line]


class RepoHygieneTests(unittest.TestCase):
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
            for line_no, line in enumerate(text.splitlines(), 1):
                for label, pattern in _BANNED_CONTENT_PATTERNS:
                    if pattern.search(line):
                        violations.append(f"{rel}:{line_no} [{label}]")
        self.assertEqual(
            violations,
            [],
            "Internal infrastructure references found in tracked files:\n"
            + "\n".join(violations[:40]),
        )


if __name__ == "__main__":
    unittest.main()
