# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_pr_hygiene.py`.

`RepoTestCase` fixtures use the monorepo layout, with Anneal under `anneal/`;
`StandaloneRepoTestCase` fixtures use the standalone layout, with Anneal at
the repository root.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_pr_hygiene as cph  # noqa: E402

SCRIPT = Path(__file__).resolve().parent / "check_pr_hygiene.py"
# Built at runtime so this file contains no literal review-round ID.
ROUND_ID = "G2" + "-R3"
SHA_RUST = "8144389c895da997dbdecaa635e41d6a50be6ffd"

HEADER_PY = """\
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
HEADER_RS = HEADER_PY.replace("# ", "// ").replace("#\n", "//\n")
HEADER_LEAN = HEADER_PY.replace("# ", "-- ").replace("#\n", "--\n")
HEADER_MD = """\
<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->
"""
CRR = (
    "<!-- code-review-rules:begin -->\n"
    "Rules text.\n"
    "<!-- code-review-rules:end -->\n"
)
TRAILER = "Agent-authored-by: AI agent acting on joshlf's behalf"
GOOD_MESSAGE = (
    "[ci] Add a helper\n\n"
    "Add a helper that does one thing well, so callers stop duplicating\n"
    "the logic.\n\n"
    f"{TRAILER}\n"
)
AUTHOR = "Test Author <test@example.com>"


def git(repo: Path, *args: str, env: dict[str, str] | None = None) -> str:
    full_env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_AUTHOR_NAME": "Test Author",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test Author",
        "GIT_COMMITTER_EMAIL": "test@example.com",
        "GIT_CONFIG_NOSYSTEM": "1",
        "HOME": str(repo.parent),
        **(env or {}),
    }
    return subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-c", "init.defaultBranch=main",
         *args],
        cwd=repo, env=full_env, capture_output=True, text=True, check=True,
    ).stdout


class RepoTestCase(unittest.TestCase):
    """Builds a scratch repository with a minimal Anneal tree on `main`."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="anneal-pr-hygiene-")
        self.repo = Path(self._tmp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.populate()
        self.commit("Initial commit")
        git(self.repo, "branch", "base")

    def populate(self) -> None:
        """Write the monorepo layout, with Anneal under `anneal/`."""
        self.write("AGENTS.md", "Root agent instructions.\n")
        self.write("anneal/AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write("anneal/.gemini/styleguide.md", "# Style\n\n" + CRR)
        self.write("anneal/docs/existing.md", HEADER_MD + "\n" + "x" * 100
                   + " y\n")
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 1\n")
        self.write("anneal/ci/legacy.sh", "echo 1\necho 2\necho 3\necho 4\n")
        self.write("anneal/README.md", "Short readme.\n")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str) -> None:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, message: str = GOOD_MESSAGE, env=None) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", message, env=env)
        return git(self.repo, "rev-parse", "HEAD").strip()

    def run_check(self, *args: str, base: str | None = "base",
                  env: dict[str, str] | None = None
                  ) -> tuple[int, dict[str, object]]:
        cmd = [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
               str(self.repo), "--json"]
        if base is not None:
            cmd += ["--base", base]
        res = subprocess.run(
            cmd + list(args), capture_output=True, text=True, check=False,
            env={**os.environ, **(env or {})},
        )
        return res.returncode, json.loads(res.stdout)

    def findings(self, *args: str, **kw) -> list[dict[str, object]]:
        return self.run_check(*args, **kw)[1]["findings"]

    def assert_finding(self, check: str, needle: str, *args: str,
                       **kw) -> dict[str, object]:
        found = self.findings(*args, **kw)
        for f in found:
            if f["check"] == check and needle in f["message"]:
                return f
        self.fail(f"no {check!r} finding containing {needle!r}: {found}")

    def assert_clean(self, *args: str, **kw) -> dict[str, object]:
        code, report = self.run_check(*args, **kw)
        self.assertEqual(report["findings"], [], report)
        self.assertEqual(code, 0)
        self.assertTrue(report["ok"])
        return report


class CleanChangeTests(RepoTestCase):
    def test_clean_change_passes_and_reports_tuple(self):
        self.write("anneal/ci/helper.py", HEADER_PY + "\n# Short comment.\n"
                   + "X = '" + "y" * 120 + "'\n")
        head = self.commit()
        report = self.assert_clean()
        self.assertEqual(report["schema"], "anneal-pr-hygiene/v1")
        self.assertEqual(report["head"], head)
        self.assertEqual(report["commits"], [head])
        self.assertEqual(report["merge_base"], report["target_base"])

    def test_tree_only_mode_runs_without_base(self):
        report = self.assert_clean(base=None)
        self.assertNotIn("commits", report)

    def test_bad_ref_fails_closed_with_exit_2(self):
        code, report = self.run_check(base="no-such-ref")
        self.assertEqual(code, 2)
        self.assertFalse(report["ok"])
        self.assertIn("error", report)

    def test_empty_flag_values_fail_closed(self):
        for flag in ("--pr-body-file", "--receipt-file", "--expected-author"):
            with self.subTest(flag=flag):
                code, report = self.run_check(flag, "")
                self.assertEqual(code, 2, report)
                self.assertIn("must not be empty", report["error"])

    def test_pr_inputs_require_base(self):
        body = self.repo.parent / "body.md"
        body.write_text("x\n")
        code, _ = self.run_check("--pr-body-file", str(body), base=None)
        self.assertEqual(code, 2)
        code, _ = self.run_check("--expected-author", AUTHOR, base=None)
        self.assertEqual(code, 2)

    def test_text_mode_exit_codes(self):
        self.write("anneal/ci/bad.py", "X = 1\n")
        self.commit()
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 1)
        self.assertIn("[header] anneal/ci/bad.py:1", res.stderr)


class CommitMessageTests(RepoTestCase):
    def touch(self) -> None:
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")

    def test_long_subject(self):
        self.touch()
        self.commit("[ci] " + "Word " * 15 + "\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "subject is")

    def test_github_squash_suffix_does_not_count(self):
        self.touch()
        subject = "[ci] " + "a" * 60
        self.commit(f"{subject} (#4321)\n\nBody.\n\n{TRAILER}\n")
        self.assert_clean()

    def test_subject_period_and_missing_blank_line(self):
        self.touch()
        self.commit(f"[ci] Add a thing.\nBody right away.\n\n{TRAILER}\n")
        self.assert_finding("commit-message", "ends with a period")
        self.assert_finding("commit-message", "one blank line")

    def test_wrappable_body_line(self):
        self.touch()
        self.commit("[ci] Add\n\n" + "word " * 16 + "end\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "wrap at 72")

    def test_unbreakable_url_code_fence_and_table_are_exempt(self):
        self.touch()
        url = "https://example.com/" + "a" * 70
        self.commit(
            "[ci] Add\n\n"
            f"{url}\n\n"
            "```\n" + "code " * 20 + "\n```\n\n"
            "    " + ("code " * 20).rstrip() + "\n\n"
            "| a | " + "b" * 80 + " |\n\n"
            "Fixes #123\n"
            "Signed-off-by: " + ("Long Name " * 6) + "<x@example.com>\n"
            f"{TRAILER}\n"
        )
        self.assert_clean()

    def test_gherrit_and_review_round_ids(self):
        self.touch()
        self.commit(f"[ci] Add\n\nAddress {ROUND_ID} feedback.\n\n"
                    f"gherrit-pr-id: Gabc\n{TRAILER}\n")
        self.assert_finding("commit-message", "gherrit-pr-id")
        self.assert_finding("commit-message", "review-round ID")

    def test_trailer_may_precede_other_trailers(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n"
                    "Signed-off-by: Test Author <test@example.com>\n")
        self.assert_clean()

    def test_trailer_examples_in_code_blocks_do_not_count(self):
        self.touch()
        self.commit(f"[ci] Add\n\nFor example:\n\n```\n{TRAILER}\n```\n\n"
                    f"{TRAILER}\n")
        self.assert_clean()

    def test_one_trailer_per_user(self):
        self.touch()
        other = TRAILER.replace("joshlf", "someone")
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n{other}\n")
        self.assert_clean()

    def test_trailer_outside_final_block(self):
        self.touch()
        self.commit(f"[ci] Add\n\n{TRAILER}\n\nMore prose after.\n")
        self.assert_finding("commit-message", "final trailer block")

    def test_duplicate_trailer(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n{TRAILER}\n")
        self.assert_finding("commit-message", "at most one")

    def test_tab_indented_body_is_measured_expanded(self):
        self.touch()
        self.commit("[ci] Add\n\n- item\n\t" + "word " * 13 + "end\n\n"
                    + TRAILER + "\n")
        self.assert_finding("commit-message", "wrap at 72")

    def test_malformed_trailer(self):
        self.touch()
        self.commit("[ci] Add\n\nBody.\n\n"
                    "Agent-Authored-By: Gemini on joshlf's behalf\n")
        self.assert_finding("commit-message", "malformed trailer")

    def test_qualified_trailer_is_accepted(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER} (content only)\n")
        self.assert_clean()

    def test_record_separators_and_quoted_paths_in_commits(self):
        self.write('anneal/docs/odd"name.md', HEADER_MD)
        self.commit("[ci] Add.\n\nBody with \x1e separator.\n")
        code, report = self.run_check()
        self.assertEqual(code, 1, report)
        self.assertTrue(any("ends with a period" in f["message"]
                            for f in report["findings"]))

    def test_bot_like_authors_are_checked_unless_skipped(self):
        self.write("anneal/Cargo.lock", "# lock\n")
        long_line = "Updates `x` from 3.23.2 to 3.24.1 " + "word " * 10
        self.commit(f"Bump x.\n\n{long_line}\n", env={
            "GIT_AUTHOR_NAME": "dependabot[bot]",
            "GIT_AUTHOR_EMAIL":
                "49699333+dependabot[bot]@users.noreply.github.com"})
        # Commit metadata is author-controlled, so a `[bot]` name alone
        # never skips the checks.
        self.assert_finding("commit-message", "ends with a period")
        code, report = self.run_check("--skip-commit-messages")
        self.assertEqual(code, 0, report)
        self.assertTrue(any("--skip-commit-messages" in w["message"]
                            for w in report["warnings"]))
        self.assert_finding("commit-message", "author is",
                            "--skip-commit-messages",
                            "--expected-author", AUTHOR)

    def test_commits_outside_anneal_are_skipped(self):
        self.write("zerocopy/src/lib.rs", "fn f() {}\n")
        self.commit("not our conventions at all, a very long subject line "
                    "that keeps going.")
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertIn("skipped", report["warnings"][0]["message"])

    def test_every_commit_in_range_is_checked(self):
        self.touch()
        self.commit()
        self.write("anneal/docs/note2.md", HEADER_MD + "\nB.\n")
        self.commit("[ci] Second commit.\n\nBody.\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "ends with a period")

    def test_expected_author(self):
        self.touch()
        self.commit()
        self.assert_clean("--expected-author", AUTHOR)
        f = self.assert_finding("commit-message", "author is",
                                "--expected-author", "J <j@example.com>")
        self.assertIn("Test Author", f["message"])


class DiffTests(RepoTestCase):
    def test_diff_check_trailing_whitespace(self):
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 2   \n")
        self.commit()
        self.assert_finding("diff-check", "trailing whitespace")

    def test_vendor_and_non_anneal_paths_are_out_of_scope(self):
        self.write("anneal/vendor/lean-miri/x.lean", "x   \n" + "-- " + "w " * 60
                   + "\n")
        self.write("zerocopy/src/lib.rs", "// " + "w " * 60 + "\n")
        self.commit()
        self.assert_clean()

    def test_anneal_integration_paths_are_in_scope(self):
        self.write(".github/workflows/anneal-extra.yml", "on: push\n")
        self.write("zerocopy/proofs/05_x/Spec.lean", HEADER_LEAN
                   + "\n-- " + "word " * 17 + "end\n")
        self.commit()
        found = {(f["check"], f["path"]) for f in self.findings()}
        self.assertIn(("header", ".github/workflows/anneal-extra.yml"), found)
        self.assertIn(("wrap", "zerocopy/proofs/05_x/Spec.lean"), found)

    def test_new_file_header(self):
        self.write("anneal/ci/new.py", "X = 1\n")
        self.commit()
        self.assert_finding("header", "does not open with the Fuchsia")

    def test_header_variants_and_exemptions(self):
        self.write("anneal/ci/a.py", "#!/usr/bin/env python3\n#\n" + HEADER_PY)
        self.write("anneal/src/b.rs", HEADER_RS)
        self.write("anneal/theory/C.lean", HEADER_LEAN)
        self.write("anneal/docs/d.md", HEADER_MD)
        self.write("anneal/skills/x/SKILL.md", "---\nname: x\n---\n")
        self.write("anneal/data.json", "{}\n")
        self.commit()
        self.assert_clean()

    def test_header_must_be_the_leading_comment(self):
        prose = "\n".join(ln[2:] for ln in HEADER_PY.splitlines())
        self.write("anneal/ci/late.py", 'X = 1\n"""\n' + prose + '\n"""\n')
        self.write("anneal/docs/late.md", "# Title\n\n" + HEADER_MD)
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "header"}
        self.assertEqual(paths, {"anneal/ci/late.py", "anneal/docs/late.md"})

    def test_header_comment_must_be_closed_and_contain_the_text(self):
        body = HEADER_MD.replace("<!-- Copyright", "Copyright")
        self.write("anneal/docs/a.md", "<!-- --> " + body)
        self.write("anneal/docs/b.md", HEADER_MD.replace(" -->", ""))
        self.write("anneal/docs/c.md", "#! title\n" + HEADER_MD)
        self.write("anneal/src/d.rs", "#![no_std]\n" + HEADER_RS)
        one_line = " ".join(body.replace(" -->", "").split())
        self.write("anneal/docs/e.md", "<!-- --> " + one_line + "\n")
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "header"}
        self.assertEqual(paths, {"anneal/docs/a.md", "anneal/docs/b.md",
                                 "anneal/docs/c.md", "anneal/src/d.rs",
                                 "anneal/docs/e.md"})

    def test_header_year_bound_ignores_commit_dates(self):
        self.write("anneal/ci/future.py", HEADER_PY.replace("2026", "2090"))
        self.commit(env={"GIT_COMMITTER_DATE": "2090-01-01T00:00:00Z",
                         "GIT_AUTHOR_DATE": "2090-01-01T00:00:00Z"})
        self.assert_finding("header", "plausible creation year")

    def test_header_year_must_be_plausible(self):
        self.write("anneal/ci/future.py", HEADER_PY.replace("2026", "2999"))
        self.commit()
        self.assert_finding("header", "plausible creation year")

    def test_renamed_file_is_not_new(self):
        # Neither file carries a header that would satisfy a new-file check.
        git(self.repo, "mv", "anneal/ci/legacy.sh", "anneal/ci/moved.sh")
        self.write("anneal/ci/moved.sh", "echo 1\necho 2\necho 3\necho 4\necho 5\n")
        self.commit()
        self.assert_clean()

    def test_moved_file_keeps_its_original_header(self):
        git(self.repo, "mv", "anneal/ci/existing.py", "anneal/ci/moved.py")
        self.commit()
        self.assert_clean()


class WrapTests(RepoTestCase):
    LONG = "word " * 17 + "end"

    def test_markdown_prose_over_80(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\n" + self.LONG
                   + "\n")
        self.commit()
        f = self.assert_finding("wrap", "wrap prose at 80")
        self.assertEqual(f["path"], "anneal/docs/existing.md")

    def test_markdown_exemptions(self):
        url = "https://example.com/" + "a" * 75
        self.write("anneal/docs/new.md", HEADER_MD + (
            "\n# A heading that is long " + "h" * 70 + "\n\n"
            "| a | b |\n|---|---|\n| " + "c " * 50 + "| d |\n\n"
            "a | b\n--- | ---\n" + "c " * 50 + "| d\n\n"
            "```\n" + "code " * 30 + "end\n```\n\n"
            f"See\n{url}\n\n"
            "- `" + "x" * 76 + "`\n\n"
            "$$a + b + " + "c + " * 30 + "$$\n\n"
            "[ref]: " + url + "\n\n"
            "<img src=\"" + url + "\">\n"
        ))
        self.commit()
        self.assert_clean()

    def test_front_matter_is_exempt(self):
        self.write("anneal/skills/s/SKILL.md",
                   "---\ndescription: " + "d " * 60 + "e\n---\n\nShort.\n")
        self.commit()
        self.assert_clean()

    def test_unchanged_long_line_is_not_flagged(self):
        self.write("anneal/docs/existing.md",
                   (self.repo / "anneal/docs/existing.md").read_text()
                   + "\nShort addition.\n")
        self.commit()
        self.assert_clean()

    def test_rust_comment_lean_comment_and_python_comment(self):
        self.write("anneal/src/a.rs", HEADER_RS + "\n/// " + self.LONG
                   + "\nfn f() { let s = \"" + "q" * 100 + "\"; }\n")
        self.write("anneal/theory/B.lean", HEADER_LEAN
                   + "\n/-- Doc.\n" + self.LONG + "\n-/\ndef x := 1\n")
        self.write("anneal/ci/c.py", HEADER_PY + "\n# " + self.LONG + "\n")
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "wrap"}
        self.assertEqual(paths, {"anneal/src/a.rs", "anneal/theory/B.lean",
                                 "anneal/ci/c.py"})

    def test_code_strings_directives_and_doc_fences_are_not_prose(self):
        self.write("anneal/src/a.rs", HEADER_RS + (
            "\n//@ fail(capture): \"" + "m " * 60 + "\"\n"
            "/// ```\n/// " + ("let x = 1; " * 10).rstrip() + "\n/// ```\nfn f() {}\n"
        ))
        self.write("anneal/ci/c.py", HEADER_PY + (
            '\nS = """\n# ' + self.LONG + '\n"""\n'
        ))
        self.write("anneal/x.nix", HEADER_PY + (
            "\n{ s = ''\n    # " + self.LONG + "\n  ''; }\n"
        ))
        self.commit()
        self.assert_clean()

    def test_package_readme_keeps_one_line_per_paragraph(self):
        self.write("anneal/README.md", self.LONG + " " + self.LONG + "\n")
        self.commit()
        self.assert_clean()

    def test_indented_license_header_is_verbatim_text(self):
        indented = "".join("        " + ln + "\n"
                           for ln in HEADER_PY.splitlines())
        self.write("anneal/ci/gen.sh", HEADER_PY
                   + "\ncat <<'EOF'\n" + indented + "EOF\n")
        self.commit()
        self.assert_clean()

    def test_split_code_span_is_a_warning_only(self):
        self.write("anneal/docs/new.md", HEADER_MD
                   + "\nThe `foo\nbar` span is split.\n")
        self.commit()
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertTrue(any("split across" in w["message"]
                            for w in report["warnings"]))

    def test_review_round_id_in_headings_and_tables(self):
        self.write("anneal/docs/new.md", HEADER_MD + (
            f"\n## Changes from {ROUND_ID}\n\n| a | {ROUND_ID} |\n|---|---|\n\n"
            f"```\n{ROUND_ID}\n```\n"))
        self.commit()
        found = [f["line"] for f in self.findings()
                 if f["check"] == "review-round-id"]
        self.assertEqual(found, [9, 11])

    def test_inline_triple_backtick_span_is_not_a_fence(self):
        self.write("anneal/docs/new.md", HEADER_MD + (
            f"\n```x``` is inline.\n\nSee {ROUND_ID}.\n"))
        self.commit()
        found = [f["line"] for f in self.findings()
                 if f["check"] == "review-round-id"]
        self.assertEqual(found, [11])

    def test_review_round_id_in_comment_but_not_string(self):
        self.write("anneal/ci/c.py", HEADER_PY
                   + f'\n# Fixes {ROUND_ID}.\nID = "{ROUND_ID}-01"\n')
        self.commit()
        found = [f for f in self.findings() if f["check"] == "review-round-id"]
        self.assertEqual([f["line"] for f in found], [9])


class WrapUnitTests(unittest.TestCase):
    def test_wrap_violation(self):
        self.assertFalse(cph.wrap_violation("a" * 80, 0, 80))
        self.assertTrue(cph.wrap_violation("a " * 41, 0, 80))
        # Overflowing unit starts the line.
        self.assertFalse(cph.wrap_violation("// " + "x" * 90, 3, 80))
        # Overflowing unit would not fit on a continuation line.
        self.assertFalse(cph.wrap_violation("see " + "x" * 81, 0, 80))
        # Code spans are unbreakable; this one fits on its own line.
        self.assertTrue(cph.wrap_violation("see `" + "x " * 38 + "`", 0, 80))

    def test_units_keep_code_spans_whole(self):
        text = "a `b c` d"
        self.assertEqual([text[s:e] for s, e in cph.units(text)],
                         ["a", "`b c`", "d"])
        self.assertEqual(cph.unmatched_backtick("x `y"), 1)
        self.assertIsNone(cph.unmatched_backtick("`` a ` b ``"))


class TrustedCitationTests(RepoTestCase):
    def write_trusted(self, body: str, path="anneal/trusted/lean/T.lean"):
        header = HEADER_RS if path.endswith(".rs") else HEADER_LEAN
        comment = "//" if path.endswith(".rs") else "--"
        self.write(path, header + "\n" + body.replace("-- ", comment + " "))
        self.commit()

    def test_unpinned_branch_link(self):
        self.write_trusted("-- https://github.com/rust-lang/rust/blob/master/"
                           "x.rs\n")
        self.assert_finding("trusted-citation", "full 40-hex")

    def test_rendered_reference_html(self):
        self.write_trusted("-- https://doc.rust-lang.org/reference/x.html\n")
        self.assert_finding("trusted-citation", "unpinned rendered docs")

    def test_unresolved_abbreviated_sha(self):
        self.write_trusted("-- See `rust-lang/rust` `8144389c` for this.\n")
        self.assert_finding("trusted-citation", "abbreviated upstream SHA")

    def test_pinned_and_resolved_citations_pass(self):
        self.write_trusted(
            f"-- `rust-lang/rust` `{SHA_RUST}`\n-- and rust-lang/rust@8144389c.\n"
            f"-- https://github.com/rust-lang/reference/blob/{SHA_RUST}/a.md\n",
            path="anneal/trusted/rustc-capture/src/x.rs",
        )
        self.assert_clean()

    def test_untrusted_paths_are_not_linted(self):
        self.write("anneal/theory/T.lean", HEADER_LEAN
                   + "\n-- https://doc.rust-lang.org/reference/x.html\n")
        self.commit()
        self.assert_clean()

    def test_new_trusted_file_without_sha_warns(self):
        self.write_trusted("def x := 1\n")
        code, report = self.run_check()
        self.assertEqual(code, 0)
        self.assertTrue(any(w["check"] == "trusted-citation"
                            for w in report["warnings"]))


class TreeCheckTests(RepoTestCase):
    def test_agents_budget(self):
        self.write("anneal/sub/AGENTS.md", "x" * 32000)
        self.commit()
        self.assert_finding("agents-budget", "shared instruction budget",
                            base=None)

    def test_agents_budget_reserve_env(self):
        self.write("anneal/sub/AGENTS.md", "x" * 31000)
        self.commit()
        self.assert_clean(base=None, env={"GLOBAL_AGENTS_BYTES": "0"})
        self.assert_finding("agents-budget", "budget", base=None,
                            env={"GLOBAL_AGENTS_BYTES": "1500"})
        self.assert_finding("agents-budget", "invalid", base=None,
                            env={"GLOBAL_AGENTS_BYTES": "1e3"})

    def test_agents_outside_anneal_are_not_counted(self):
        self.write("zerocopy/AGENTS.md", "x" * 32000)
        self.commit()
        self.assert_clean(base=None)

    def test_crr_mirror_drift(self):
        self.write("anneal/.gemini/styleguide.md",
                   "# Style\n\n" + CRR.replace("Rules", "Rulez"))
        self.commit()
        self.assert_finding("code-review-rules-parity", "byte-identical",
                            base=None)

    def test_crr_missing_marker(self):
        self.write("anneal/.gemini/styleguide.md", "# Style\n\nNo markers.\n")
        self.commit()
        self.assert_finding("code-review-rules-parity", "expected one",
                            base=None)


class PrBodyTests(RepoTestCase):
    MESSAGE = (
        "[ci] Add a helper\n\n"
        "Add a helper that does one thing well, so callers stop duplicating\n"
        "the logic.\n\n"
        "- First item wraps across\n  two lines.\n\n"
        "```\nkeep   this\n```\n\n"
        "Fixes #12\n"
        f"{TRAILER}\n"
    )
    EXPECTED = (
        "Add a helper that does one thing well, so callers stop duplicating "
        "the logic.\n\n"
        "- First item wraps across two lines.\n\n"
        "```\nkeep   this\n```\n\n"
        "Fixes #12\n\n"
        "*Authored by an AI agent acting on joshlf's behalf.*\n"
    )

    def setUp(self) -> None:
        super().setUp()
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")
        self.commit(self.MESSAGE)

    def body_file(self, text: str) -> str:
        path = self.repo.parent / "body.md"
        path.write_bytes(text.encode())
        return str(path)

    def test_emit_pr_body(self):
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--emit-pr-body"],
            capture_output=True, text=True, check=True,
        )
        self.assertEqual(res.stdout, self.EXPECTED)

    def test_matching_body_and_title_pass_with_crlf(self):
        self.assert_clean(
            "--pr-body-file", self.body_file(
                self.EXPECTED.replace("\n", "\r\n")),
            "--pr-title", "[ci] Add a helper")

    def test_mismatched_body(self):
        f = self.assert_finding(
            "pr-body", "first difference at line 1",
            "--pr-body-file", self.body_file("## Summary\n\nStuff.\n"))
        self.assertIn("## Summary", f["message"])

    def test_missing_disclosure(self):
        self.assert_finding(
            "pr-body", "end of body", "--pr-body-file",
            self.body_file(self.EXPECTED.rsplit("\n\n", 1)[0] + "\n"))

    def test_mismatched_title(self):
        self.assert_finding("pr-title", "differs", "--pr-title", "Other")

    def test_multi_commit_is_skipped_with_warning(self):
        self.write("anneal/docs/note2.md", HEADER_MD + "\nB.\n")
        self.commit()
        code, report = self.run_check("--pr-body-file", self.body_file("x"))
        self.assertEqual(code, 0, report)
        self.assertTrue(any(w["check"] == "pr-body"
                            for w in report["warnings"]))


class UnwrapUnitTests(unittest.TestCase):
    def test_qualifiers_and_blockquotes(self):
        body = ("> quoted line\n> continues\n\n"
                f"{TRAILER} (content only)\n")
        # A content-only trailer means the agent did not write the message,
        # so the description carries no notice.
        self.assertEqual(cph.commit_body_to_pr_body(body),
                         "> quoted line continues\n")
        body = f"Text.\n\n{TRAILER} (commit message only)\n"
        self.assertEqual(
            cph.commit_body_to_pr_body(body),
            "Text.\n\n*Authored by an AI agent acting on joshlf's behalf.*\n")

    def test_inline_triple_backtick_line_is_not_a_fence(self):
        body = (f"```x``` starts this line.\n\nWrapped\nprose.\n\n{TRAILER}\n")
        self.assertEqual(
            cph.commit_body_to_pr_body(body),
            "```x``` starts this line.\n\nWrapped prose.\n\n"
            "*Authored by an AI agent acting on joshlf's behalf.*\n")
        self.assertEqual(
            cph.commit_body_to_pr_body("Some prose\n```x``` continues.\n"),
            "Some prose ```x``` continues.\n")

    def test_hard_breaks_headings_and_empty(self):
        self.assertEqual(cph.commit_body_to_pr_body(""), "")
        body = "# Head\nline one  \nline two\nthree\n"
        self.assertEqual(cph.commit_body_to_pr_body(body),
                         "# Head\nline one  \nline two three\n")


class ReceiptTests(RepoTestCase):
    def setUp(self) -> None:
        super().setUp()
        self.write("anneal/trusted/lean/A.lean", HEADER_LEAN)
        self.write("anneal/trusted/lean/B.lean", HEADER_LEAN)
        self.write("anneal/ci/tool.py", HEADER_PY)
        self.write("anneal/docs/guide.md", HEADER_MD)
        self.commit()

    def receipt(self, text: str) -> str:
        path = self.repo.parent / "receipt.md"
        path.write_text(text, encoding="utf-8")
        return str(path)

    def footer(self) -> str:
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base", "--emit-receipt-footer"],
            capture_output=True, text=True, check=True,
        )
        return res.stdout

    def footer_data(self) -> dict[str, object]:
        m = cph.RECEIPT_FOOTER_RE.search(self.footer())
        return json.loads(m.group(1))

    def good(self, data: dict[str, object] | None = None) -> str:
        footer = (self.footer() if data is None else
                  f"<!-- anneal-receipt:v1 {json.dumps(data)} -->\n")
        return ("### Human review surface\n\n"
                "- `anneal/trusted/lean/{A,B}.lean`: new definitions.\n\n"
                + footer)

    def test_emitted_footer_binds_tuple_and_surface(self):
        data = self.footer_data()
        self.assertEqual(data["head"], git(self.repo, "rev-parse",
                                           "HEAD").strip())
        self.assertEqual(data["tree"], git(self.repo, "rev-parse",
                                           "HEAD^{tree}").strip())
        self.assertEqual(data["human_review_surface"], [
            "anneal/ci/tool.py", "anneal/trusted/lean/A.lean",
            "anneal/trusted/lean/B.lean"])
        self.assert_clean("--receipt-file", self.receipt(self.good()))

    def test_footer_count_json_and_keys(self):
        for text, needle in (
            ("### Human review surface\n\nnone\n", "0 `anneal-receipt:`"),
            (self.good() + self.footer(), "2 `anneal-receipt:`"),
            ("Human review surface\n<!-- anneal-receipt:v1 {nope} -->",
             "not valid JSON"),
        ):
            with self.subTest(needle=needle):
                self.assert_finding("receipt", needle,
                                    "--receipt-file", self.receipt(text))
        data = self.footer_data()
        data["extra"] = 1
        self.assert_finding("receipt", "exactly the keys",
                            "--receipt-file", self.receipt(self.good(data)))

    def test_extra_markers_duplicates_and_hidden_prose(self):
        good = self.good()
        for extra in ("<!-- anneal-receipt:v1 not-json -->\n",
                      "<!-- anneal-receipt:v1 [] -->\n",
                      "<!-- anneal-receipt:v2 {} -->\n"):
            with self.subTest(extra=extra):
                self.assert_finding("receipt", "2 `anneal-receipt:` marker",
                                    "--receipt-file",
                                    self.receipt(good + extra))
        # Mentioning the footer in prose is fine.
        self.assert_clean("--receipt-file", self.receipt(
            good + "The `anneal-receipt:v1` footer is generated.\n"))
        footer = self.footer()
        head = self.footer_data()["head"]
        dup = footer.replace('"target_base": ',
                             f'"target_base": "{head}", "target_base": ', 1)
        self.assert_finding("receipt", "duplicate key",
                            "--receipt-file", self.receipt(
                                "### Human review surface\n\n" + dup))
        hidden = "<!-- Human review surface -->\n" + footer
        self.assert_finding("receipt", "visible `Human review",
                            "--receipt-file", self.receipt(hidden))

    def test_footer_escapes_comment_close(self):
        footer = cph.receipt_footer("a" * 40, "a" * 40, "b" * 40, "c" * 40,
                                    ["anneal/ci/x-->y.py"])
        self.assertEqual(footer.count("-->"), 1)
        data = json.loads(cph.RECEIPT_FOOTER_RE.search(footer).group(1))
        self.assertEqual(data["human_review_surface"], ["anneal/ci/x-->y.py"])

    def test_shas_must_be_full_and_current(self):
        data = self.footer_data()
        data["head"] = data["head"][:12]
        self.assert_finding("receipt", "`head` must be a full 40-hex",
                            "--receipt-file", self.receipt(self.good(data)))
        data = self.footer_data()
        data["tree"] = "a" * 40
        self.assert_finding("receipt", "footer `tree` is `aaaaaaaaaaaa`",
                            "--receipt-file", self.receipt(self.good(data)))
        data = self.footer_data()
        data["target_base"], data["head"] = data["head"], data["target_base"]
        found = [f["message"] for f in self.findings(
            "--receipt-file", self.receipt(self.good(data)))]
        self.assertTrue(any("footer `head`" in m for m in found), found)
        self.assertTrue(any("footer `target_base`" in m for m in found), found)

    def test_surface_must_be_complete_and_real(self):
        data = self.footer_data()
        data["human_review_surface"].remove("anneal/ci/tool.py")
        f = self.assert_finding("receipt", "omits",
                                "--receipt-file", self.receipt(self.good(data)))
        self.assertIn("anneal/ci/tool.py", f["message"])
        data = self.footer_data()
        data["human_review_surface"] += ["anneal/ci/", "anneal/docs/other.md"]
        f = self.assert_finding("receipt", "does not change",
                                "--receipt-file", self.receipt(self.good(data)))
        self.assertIn("anneal/ci/", f["message"])
        # Listing a changed path outside the review surface is allowed.
        data = self.footer_data()
        data["human_review_surface"].append("anneal/docs/guide.md")
        self.assert_clean("--receipt-file", self.receipt(self.good(data)))
        data["human_review_surface"] = "anneal/ci/tool.py"
        self.assert_finding("receipt", "must be a list",
                            "--receipt-file", self.receipt(self.good(data)))

    def test_prose_block_is_still_required(self):
        text = self.good().replace("### Human review surface", "### Notes")
        self.assert_finding("receipt", "lacks a visible `Human review",
                            "--receipt-file", self.receipt(text))

    def test_emit_footer_requires_base(self):
        code, report = self.run_check("--emit-receipt-footer", base=None)
        self.assertEqual(code, 2, report)


class HardeningTests(RepoTestCase):
    """Inputs that once hid content from, or confused, the checks."""

    LONG = "word " * 17 + "end"

    def test_added_line_resembling_a_patch_header(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\n++ not a header\n"
                   + self.LONG + "\n")
        self.commit()
        f = self.assert_finding("wrap", "wrap prose at 80")
        self.assertEqual(f["line"], 10)

    def test_path_with_spaces_and_quotes(self):
        self.write("anneal/docs/my note.md", self.LONG + "\n")
        self.write('anneal/docs/odd"name.md', "x\n")
        self.write('anneal/docs/my "odd" note.md', "x\n")
        self.commit()
        found = self.findings()
        self.assertIn(("header", "anneal/docs/my note.md"),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("wrap", "anneal/docs/my note.md"),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("header", 'anneal/docs/odd"name.md'),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("header", 'anneal/docs/my "odd" note.md'),
                      {(f["check"], f["path"]) for f in found})

    def test_gitattributes_cannot_hide_content(self):
        self.write(".gitattributes", "*.py -diff\n* whitespace=-trailing-space\n")
        self.write("anneal/ci/new.py", "# " + self.LONG + "   \n")
        self.commit()
        checks = {f["check"] for f in self.findings()}
        self.assertTrue({"header", "wrap", "diff-check"} <= checks, checks)

    def test_binary_looking_content_is_still_checked(self):
        self.write("anneal/docs/nul.md", HEADER_MD + "\x00\n" + self.LONG
                   + "\n")
        self.commit()
        self.assert_finding("wrap", "wrap prose at 80")

    def test_ambient_git_config_and_env_are_ignored(self):
        cfg = self.repo.parent / "evil.gitconfig"
        cfg.write_text("[core]\n\twhitespace = -trailing-space\n"
                       "[diff]\n\trelative = true\n")
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 2   \n")
        self.commit()
        self.assert_finding("diff-check", "trailing whitespace", env={
            "GIT_CONFIG_GLOBAL": str(cfg), "HOME": str(self.repo.parent),
            "GIT_DIR": "/nonexistent",
        })

    def test_deletions_do_not_widen_diff_check(self):
        git(self.repo, "rm", "-q", "anneal/docs/existing.md")
        self.write("anneal/vendor/lean-miri/x.lean", "x   \n")
        self.commit()
        self.assert_clean()

    def test_empty_new_file_needs_header(self):
        self.write("anneal/ci/empty.py", "")
        self.commit()
        self.assert_finding("header", "does not open with")

    def test_python_triple_quotes_in_strings_and_docstrings(self):
        self.write("anneal/ci/q.py", HEADER_PY + (
            "\nQ = ('\"\"\"', \"'''\")\n# " + self.LONG + "\n"
            'def f():\n    """Doc.\n\n    # ' + self.LONG + '\n    """\n'
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_form_feed_does_not_shift_lines(self):
        self.write("anneal/ci/ff.py", HEADER_PY + '\nSEP = "\x0c"\n# '
                   + self.LONG + "\n")
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_markdown_indented_code_block_spans_lines(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\nText:\n\n    "
                   + self.LONG + "\n    " + self.LONG + "\n\nAfter.\n")
        self.commit()
        self.assert_clean()

    def test_rust_string_literals_are_not_comments(self):
        self.write("anneal/src/s.rs", HEADER_RS + (
            '\nconst A: &str = r#"\n// ' + self.LONG + '\n"#;\n'
            'const B: &str = "\n// ' + self.LONG + '\n";\n'
            "fn f<'a>(x: &'a str) -> char { '\"' }\n// " + self.LONG + "\n"
            'const C: &str = r"C:\\";\n// ' + self.LONG + '\n'
            'const D: &CStr = cr#"a"b"#;\n'
            "// " + self.LONG + "\n"
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [16, 18, 20])

    def test_lean_char_literal_does_not_open_a_string(self):
        self.write("anneal/theory/C.lean", HEADER_LEAN + (
            "\ndef c := '\"' /- Start of a block comment\n" + self.LONG
            + "\n-/\n"
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_pinned_link_with_fragment_or_punctuation(self):
        url = f"https://github.com/rust-lang/rust/commit/{SHA_RUST}"
        self.write("anneal/trusted/lean/T.lean", HEADER_LEAN
                   + f"\n-- See {url}.\n-- And {url}#diff-abc, too.\n")
        self.commit()
        self.assert_clean()

    def test_crr_markers_on_one_line(self):
        one = "<!-- code-review-rules:begin --><!-- code-review-rules:end -->\n"
        self.write("anneal/AGENTS.md", HEADER_MD + one)
        self.write("anneal/.gemini/styleguide.md", one)
        self.commit()
        self.assert_finding("code-review-rules-parity", "expected one",
                            base=None)


class ReviewSurfaceTests(RepoTestCase):
    def surface(self) -> list[str]:
        return self.run_check()[1]["human_review_surface"]

    def test_renames_and_deletions_count_their_sources(self):
        self.write("anneal/trusted/lean/A.lean", HEADER_LEAN)
        self.write("anneal/trusted/lean/D.lean", HEADER_LEAN + "-- d\n")
        self.commit()
        git(self.repo, "branch", "-f", "base", "HEAD")
        git(self.repo, "mv", "anneal/trusted/lean/A.lean",
            "anneal/docs/A.lean")
        git(self.repo, "rm", "-q", "anneal/trusted/lean/D.lean")
        self.commit()
        self.assertEqual(self.surface(), ["anneal/trusted/lean/A.lean",
                                          "anneal/trusted/lean/D.lean"])

    def test_trust_tier_edits_anywhere(self):
        self.write("anneal/theory/T.lean", HEADER_LEAN
                   + "-- anneal-trust-tier: vetted\n")
        self.write("zerocopy/proofs/01_x/Proof.lean", HEADER_LEAN
                   + "-- anneal-trust-tier: vetted\n")
        self.write("anneal/theory/U.lean", HEADER_LEAN)
        self.commit()
        self.assertEqual(self.surface(), ["anneal/theory/T.lean",
                                          "zerocopy/proofs/01_x/Proof.lean"])
        git(self.repo, "branch", "-f", "base", "HEAD")
        self.write("anneal/theory/T.lean", HEADER_LEAN)
        self.write("anneal/theory/U.lean", HEADER_LEAN + "-- plain\n")
        self.commit()
        self.assertEqual(self.surface(), ["anneal/theory/T.lean"])
        git(self.repo, "branch", "-f", "base", "HEAD")
        git(self.repo, "rm", "-q", "zerocopy/proofs/01_x/Proof.lean")
        self.commit()
        self.assertEqual(self.surface(), ["zerocopy/proofs/01_x/Proof.lean"])

    def test_proof_unit_specs_and_requests(self):
        self.write("zerocopy/proofs/05_x/Spec.lean", HEADER_LEAN)
        self.write("zerocopy/proofs/05_x/request.json", "{}\n")
        self.write("zerocopy/proofs/05_x/Proof.lean", HEADER_LEAN)
        self.commit()
        self.assertEqual(self.surface(), ["zerocopy/proofs/05_x/Spec.lean",
                                          "zerocopy/proofs/05_x/request.json"])

    def test_review_surface_categories(self):
        for path in (".gemini/styleguide.md", "anneal/.claude/x.json",
                     "zerocopy/.vscode/settings.json", "anneal/AGENTS.md",
                     "anneal/sub/AGENTS.override.md", "anneal/vendor/x.lean",
                     "anneal/trusted/lean/lake-manifest.json",
                     ".github/workflows/anneal.yml", "skills/x/SKILL.md",
                     "anneal/docs/trust-model.md", "rust-toolchain.toml",
                     "zerocopy/proofs/01_x/Spec.lean",
                     "zerocopy/proofs/01_x/request.json",
                     "zerocopy/proofs/01_x/SpecHelpers.lean",
                     "ci/checks.toml", ".cargo", "anneal/.cargo",
                     ".gitmodules", "anneal/.gitmodules",
                     "anneal/theory/bundle-manifest.json"):
            self.assertTrue(cph.is_hrs_path(path), path)
        for path in ("anneal/docs/guide.md", "anneal/theory/T.lean",
                     "zerocopy/src/lib.rs", "zerocopy/proofs/01_x/Proof.lean"):
            self.assertFalse(cph.is_hrs_path(path), path)
        self.assertTrue(cph.is_hrs_path("zerocopy/proofs/01_x/Proof.lean",
                                        trust_tier_changed=True))
        for path in (".claude", "anneal/.gemini", ".vscode"):
            self.assertTrue(cph.is_hrs_path(path), path)

    def test_single_hyphen_lines_are_not_trust_tier_directives(self):
        self.write("anneal/theory/V.lean", HEADER_LEAN
                   + "/-\n- anneal-trust-tier: prose\n-/\n")
        self.commit()
        git(self.repo, "branch", "-f", "base", "HEAD")
        self.write("anneal/theory/V.lean", HEADER_LEAN + "/-\n-/\n")
        self.commit()
        self.assertEqual(self.surface(), [])


class MonorepoLayoutTests(RepoTestCase):
    """Layout detection and scope in the monorepo layout."""

    def test_layout_is_detected(self):
        self.assertEqual(self.assert_clean(base=None)["layout"], "monorepo")
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")
        self.commit()
        self.assertEqual(self.assert_clean()["layout"], "monorepo")

    def test_root_paths_outside_anneal_are_out_of_scope(self):
        # The monorepo's own `trusted/` and `ci/` are not Anneal's.
        self.write("trusted/lean/T.lean",
                   "-- https://doc.rust-lang.org/reference/x.html   \n")
        self.write("ci/new.py", "# " + "word " * 17 + "end\n")
        self.commit("not our conventions at all.")
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertIn("touches no Anneal paths",
                      report["warnings"][0]["message"])

    def test_head_cannot_remove_the_layout_marker(self):
        git(self.repo, "rm", "-q", "anneal/AGENTS.md")
        self.commit()
        found = self.findings()
        self.assertIn("layout", {f["check"] for f in found}, found)
        self.assert_finding("layout", "`anneal/AGENTS.md` removed")
        f = self.assert_finding("code-review-rules-parity", "file is missing")
        self.assertEqual(f["path"], "anneal/AGENTS.md")


class StandaloneRepoTestCase(RepoTestCase):
    """Builds a scratch repository with Anneal at the repository root."""

    def populate(self) -> None:
        self.write("AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write(".gemini/styleguide.md", "# Style\n\n" + CRR)
        self.write("docs/existing.md", HEADER_MD + "\n" + "x" * 100 + " y\n")
        self.write("ci/existing.py", HEADER_PY + "\nVALUE = 1\n")
        self.write("ci/legacy.sh", "echo 1\necho 2\necho 3\necho 4\n")
        self.write("README.md", "Short readme.\n")


class StandaloneLayoutTests(StandaloneRepoTestCase):
    LONG = "word " * 17 + "end"

    def test_layout_is_detected(self):
        self.assertEqual(self.assert_clean(base=None)["layout"], "standalone")
        self.write("ci/helper.py", HEADER_PY + "\n# Short comment.\n")
        head = self.commit()
        report = self.assert_clean()
        self.assertEqual(report["layout"], "standalone")
        self.assertEqual(report["commits"], [head])

    def test_root_paths_are_in_scope(self):
        self.write("ci/new.py", "X = 1\n")
        self.write(".github/workflows/ci.yml", "on: push\n")
        self.write("theory/B.lean", HEADER_LEAN + "\n-- " + self.LONG + "\n")
        self.write("crates/x/src/lib.rs", HEADER_RS + "\n/// " + self.LONG
                   + "\nfn f() {}\n")
        self.write("docs/existing.md", HEADER_MD + "\n" + self.LONG + "\n")
        self.commit()
        found = {(f["check"], f["path"]) for f in self.findings()}
        self.assertEqual(found, {
            ("header", "ci/new.py"),
            ("header", ".github/workflows/ci.yml"),
            ("wrap", "theory/B.lean"),
            ("wrap", "crates/x/src/lib.rs"),
            ("wrap", "docs/existing.md"),
        })

    def test_diff_check_on_root_paths(self):
        self.write("ci/existing.py", HEADER_PY + "\nVALUE = 2   \n")
        self.commit()
        f = self.assert_finding("diff-check", "trailing whitespace")
        self.assertEqual((f["path"], f["line"]), ("ci/existing.py", 9))

    def test_vendored_corpora_are_out_of_scope(self):
        for prefix in ("vendor/", "anneal/vendor/", "lean-miri/vendor/",
                       "minirust/vendor/", "theory/MiniRust/vendor/"):
            self.write(prefix + "up/x.lean",
                       "x   \n-- " + "w " * 60 + "\n")
            self.write(prefix + "up/new.py", "# " + self.LONG + "\n")
        self.commit()
        self.assert_clean()

    def test_every_root_commit_is_checked(self):
        self.write("scripts/tool.sh", HEADER_PY + "\necho 1\n")
        self.commit("[ci] Add a tool.\n\nBody.\n\n" + TRAILER + "\n")
        code, report = self.run_check()
        self.assertEqual(code, 1, report)
        self.assertTrue(any("ends with a period" in f["message"]
                            for f in report["findings"]), report)
        self.assertFalse(any("touches no Anneal paths" in w["message"]
                             for w in report["warnings"]), report)

    def test_trusted_citations_at_root(self):
        self.write("trusted/lean/T.lean", HEADER_LEAN
                   + "\n-- https://github.com/rust-lang/rust/blob/master/x.rs\n")
        self.write("trusted/rustc-capture/src/x.rs", HEADER_RS
                   + "\n// https://doc.rust-lang.org/reference/x.html\n")
        # Outside the standalone trusted roots, links are not linted.
        self.write("theory/T.lean", HEADER_LEAN
                   + "\n-- https://doc.rust-lang.org/reference/x.html\n")
        self.write("anneal/trusted/lean/U.lean", HEADER_LEAN
                   + "\n-- https://doc.rust-lang.org/reference/x.html\n")
        self.commit()
        found = {(f["path"], f["message"].split(";")[0])
                 for f in self.findings() if f["check"] == "trusted-citation"}
        self.assertEqual(found, {
            ("trusted/lean/T.lean", "`rust-lang/rust` link pins `master`"),
            ("trusted/rustc-capture/src/x.rs",
             "`doc.rust-lang.org` serves unpinned rendered docs"),
        })

    def test_pinned_root_trusted_citations_pass(self):
        self.write("trusted/lean/T.lean", HEADER_LEAN
                   + f"\n-- `rust-lang/rust` `{SHA_RUST}`\n"
                   "-- and rust-lang/rust@8144389c.\n")
        self.commit()
        self.assert_clean()

    def test_new_root_trusted_file_without_sha_warns(self):
        self.write("trusted/lean/T.lean", HEADER_LEAN + "\ndef x := 1\n")
        self.commit()
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertIn(("trusted-citation", "trusted/lean/T.lean"),
                      {(w["check"], w["path"]) for w in report["warnings"]})

    def test_root_package_readme_is_exempt(self):
        self.write("README.md", self.LONG + " " + self.LONG + "\n")
        self.commit()
        self.assert_clean()

    def test_agents_budget_counts_root_and_nested_files(self):
        self.write("sub/AGENTS.md", "x" * 32000)
        self.commit()
        f = self.assert_finding("agents-budget", "shared instruction budget",
                                base=None)
        self.assertTrue(f["message"].startswith("AGENTS.md + sub/AGENTS.md"),
                        f)

    def test_tool_rule_bundles_are_not_counted(self):
        self.write("tools/lsp/rules/AGENTS.md", "x" * 32000)
        self.commit()
        self.assert_clean(base=None)
        self.write("tools/lsp/rules/AGENTS.override.md", "x" * 32000)
        self.commit()
        self.assert_finding("agents-budget", "AGENTS.override.md", base=None)

    def test_crr_drift_at_root(self):
        self.write(".gemini/styleguide.md",
                   "# Style\n\n" + CRR.replace("Rules", "Rulez"))
        self.commit()
        f = self.assert_finding("code-review-rules-parity",
                                "differs from `AGENTS.md`", base=None)
        self.assertEqual(f["path"], ".gemini/styleguide.md")

    def test_crr_missing_root_styleguide(self):
        git(self.repo, "rm", "-q", ".gemini/styleguide.md")
        self.commit()
        f = self.assert_finding("code-review-rules-parity", "file is missing",
                                base=None)
        self.assertEqual(f["path"], ".gemini/styleguide.md")

    def test_review_surface_and_receipt_use_root_paths(self):
        self.write("trusted/lean/A.lean", HEADER_LEAN)
        self.write("ci/tool.py", HEADER_PY)
        self.write("docs/trust-model.md", HEADER_MD)
        self.write("theory/bundle-manifest.json", "{}\n")
        self.write("docs/guide.md", HEADER_MD)
        self.write("theory/T.lean", HEADER_LEAN)
        self.commit()
        hrs = ["ci/tool.py", "docs/trust-model.md",
               "theory/bundle-manifest.json", "trusted/lean/A.lean"]
        self.assertEqual(self.run_check()[1]["human_review_surface"], hrs)
        footer = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base", "--emit-receipt-footer"],
            capture_output=True, text=True, check=True,
        ).stdout
        data = json.loads(cph.RECEIPT_FOOTER_RE.search(footer).group(1))
        self.assertEqual(data["human_review_surface"], hrs)
        receipt = self.repo.parent / "receipt.md"
        receipt.write_text("### Human review surface\n\n- `trusted/`.\n\n"
                           + footer, encoding="utf-8")
        self.assert_clean("--receipt-file", str(receipt))

    def test_head_cannot_switch_the_layout(self):
        # Adding the monorepo marker must not move the checks to `anneal/`.
        self.write("anneal/AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write("anneal/.gemini/styleguide.md", HEADER_MD + "\n" + CRR)
        self.write("ci/new.py", "X = 1\n")
        self.commit()
        code, report = self.run_check()
        self.assertEqual(code, 1, report)
        self.assertEqual(report["layout"], "standalone")
        found = {(f["check"], f["path"]) for f in report["findings"]}
        self.assertEqual(found, {("layout", None), ("header", "ci/new.py")})
        self.assert_finding("layout", "`anneal/AGENTS.md` added")
        # Without a trusted base, the head's own layout applies.
        self.assertEqual(self.assert_clean(base=None)["layout"], "monorepo")

    def test_symlink_marker_does_not_switch_layout(self):
        # A symlink at `anneal/AGENTS.md` has Git type `blob` (mode `120000`)
        # and must not be mistaken for a regular monorepo marker file.
        marker = self.repo / "anneal" / "AGENTS.md"
        marker.parent.mkdir(parents=True, exist_ok=True)
        os.symlink("../AGENTS.md", marker)
        self.commit()
        report = self.assert_clean(base=None)
        self.assertEqual(report["layout"], "standalone")
        _, report_diff = self.run_check()
        self.assertEqual(report_diff["layout"], "standalone")
        self.assertNotIn("layout", {f["check"] for f in report_diff["findings"]})

    def test_standalone_vendor_is_hrs_but_out_of_lint_scope(self):
        # Vendored corpora skip mechanical lint (headers, wrapping) while
        # still appearing on the Human review surface.
        self.write("lean-miri/vendor/Miri/X.lean",
                   "x   \n-- " + "w " * 60 + "\n")
        self.commit()
        report = self.assert_clean()
        self.assertEqual(report["human_review_surface"],
                         ["lean-miri/vendor/Miri/X.lean"])

    def test_rename_into_scope_and_trusted_checked(self):
        # Renaming a vendored file into Anneal scope must fail header, wrap,
        # and review-round-id checks on its existing lines, and renaming a
        # file with an unpinned upstream link into `trusted/lean/` must fail
        # citations.
        self.write(
            "lean-miri/vendor/Miri/Raw.lean",
            "-- " + " ".join(["word"] * 20) + "\n-- See G2-R1.\ndef raw := 1\n",
        )
        self.write("theory/Link.lean",
                   HEADER_LEAN + "\n-- https://doc.rust-lang.org/std/\n")
        base_with_files = self.commit("Seed vendor and theory files")
        (self.repo / "theory").mkdir(parents=True, exist_ok=True)
        (self.repo / "trusted" / "lean").mkdir(parents=True, exist_ok=True)
        git(self.repo, "mv", "lean-miri/vendor/Miri/Raw.lean",
            "theory/Raw.lean")
        git(self.repo, "mv", "theory/Link.lean", "trusted/lean/Link.lean")
        self.commit("Move files into scope and trusted")
        code, report = self.run_check(base=base_with_files)
        self.assertEqual(code, 1, report)
        found = {(f["check"], f["path"]) for f in report["findings"]}
        self.assertEqual(found, {
            ("header", "theory/Raw.lean"),
            ("wrap", "theory/Raw.lean"),
            ("review-round-id", "theory/Raw.lean"),
            ("trusted-citation", "trusted/lean/Link.lean"),
        })

    def test_explicit_layout_overrides_detection(self):
        self.assertEqual(self.assert_clean("--layout", "standalone",
                                           base=None)["layout"], "standalone")
        f = self.assert_finding("code-review-rules-parity", "file is missing",
                                "--layout", "monorepo", base=None)
        self.assertEqual(f["path"], "anneal/AGENTS.md")
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--layout", "other"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 2, res.stderr)


class LayoutUnitTests(unittest.TestCase):
    def test_scope(self):
        mono, solo = cph.MONOREPO, cph.STANDALONE
        for path in ("anneal/ci/x.py", ".github/workflows/anneal.yml",
                     "zerocopy/proofs/01_x/Spec.lean"):
            self.assertTrue(cph.in_anneal_scope(path, mono), path)
        for path in ("ci/x.py", "trusted/lean/T.lean", "anneal/vendor/x"):
            self.assertFalse(cph.in_anneal_scope(path, mono), path)
        for path in ("ci/x.py", "trusted/lean/T.lean", "AGENTS.md",
                     ".github/workflows/ci.yml", "crates/a/src/lib.rs"):
            self.assertTrue(cph.in_anneal_scope(path, solo), path)
        for path in ("vendor/x", "anneal/vendor/x", "lean-miri/vendor/x",
                     "minirust/vendor/x", "theory/MiniRust/vendor/x"):
            self.assertFalse(cph.in_anneal_scope(path, solo), path)

    def test_layout_relative_paths(self):
        self.assertEqual(cph.MONOREPO.crr_files,
                         ("anneal/AGENTS.md", "anneal/.gemini/styleguide.md"))
        self.assertEqual(cph.STANDALONE.crr_files,
                         ("AGENTS.md", ".gemini/styleguide.md"))
        self.assertEqual(cph.STANDALONE.trusted_citation_prefixes,
                         ("trusted/lean/", "trusted/rustc-capture/"))
        self.assertFalse(cph.needs_header("README.md", cph.STANDALONE))
        self.assertTrue(cph.needs_header("README.md", cph.MONOREPO))
        self.assertFalse(cph.needs_header("anneal/README.md", cph.MONOREPO))

    def test_agents_budget_membership(self):
        solo, mono = cph.STANDALONE, cph.MONOREPO
        self.assertTrue(solo.agents_file_counts("AGENTS.md"))
        self.assertTrue(solo.agents_file_counts("a/b/AGENTS.override.md"))
        self.assertFalse(solo.agents_file_counts("tools/x/rules/AGENTS.md"))
        self.assertFalse(solo.agents_file_counts("vendor/x/AGENTS.md"))
        self.assertFalse(solo.agents_file_counts(
            "lean-miri/vendor/x/AGENTS.md"))
        self.assertFalse(solo.agents_file_counts("README.md"))
        self.assertTrue(mono.agents_file_counts("AGENTS.md"))
        self.assertTrue(mono.agents_file_counts("anneal/sub/AGENTS.md"))
        self.assertFalse(mono.agents_file_counts("zerocopy/AGENTS.md"))
        self.assertFalse(mono.agents_file_counts(
            "anneal/vendor/x/AGENTS.md"))
        self.assertFalse(mono.agents_file_counts(
            "anneal/tools/x/rules/AGENTS.md"))

    def test_standalone_review_surface(self):
        solo = cph.STANDALONE
        for path in ("trusted/lean/A.lean", "ci/x.py", ".github/x.yml",
                     "skills/x/SKILL.md", "vendor/x", "anneal/vendor/x",
                     "lean-miri/vendor/x", "minirust/vendor/x",
                     "theory/MiniRust/vendor/x", "Cargo.lock",
                     "docs/codex-review.md", "PRINCIPLES.md", "AGENTS.md",
                     ".gemini/styleguide.md", "lakefile.toml",
                     "lean-toolchain", "theory/bundle-manifest.json"):
            self.assertTrue(cph.is_hrs_path(path, layout=solo), path)
        for path in ("docs/guide.md", "theory/T.lean", "crates/a/src/lib.rs",
                     "zerocopy/proofs/01_x/Spec.lean",
                     "anneal/trusted/lean/A.lean"):
            self.assertFalse(cph.is_hrs_path(path, layout=solo), path)
        self.assertTrue(cph.is_hrs_path("theory/T.lean", True, solo))


class InternalHygieneMixin:
    """`internal-path` and `internal-reference` checks in one layout.

    Banned tokens are built from parts so that this file contains none.
    """

    ROOT = ""
    LAYOUT = "standalone"
    CLI = "cp" + "L"
    CLIENT = "JET" + "SKI"
    MOUNT = "/x" + "20/teams"
    USER = "mark" + "dittmer"
    WORKSTATION = "/usr/local/" + "google"

    def internal(self, *args: str, **kw) -> set[tuple]:
        """Internal findings as `(check, path, line, label)` tuples."""
        out = set()
        for f in self.findings(*args, **kw):
            if f["check"] == "internal-reference":
                label = f["message"].split("(", 1)[1].split(")", 1)[0]
                out.add((f["check"], f["path"], f["line"], label))
            elif f["check"] == "internal-path":
                out.add((f["check"], f["path"], f["line"], None))
        return out

    def ref(self, rel: str, line: int, label: str) -> tuple:
        return ("internal-reference", self.ROOT + rel, line, label)

    def seed(self, files: dict[str, str]) -> None:
        """Commit `files` (relative to `ROOT`) into the `base` branch."""
        for rel, text in files.items():
            self.write(self.ROOT + rel, text)
        self.commit("Seed")
        git(self.repo, "branch", "-f", "base")

    def test_layout_matches_fixture(self):
        self.assertEqual(self.assert_clean(base=None)["layout"], self.LAYOUT)

    def test_clean_identifiers_and_prose_pass(self):
        self.write(self.ROOT + "theory/Clean.lean", HEADER_LEAN
                   + "def checkPtrL := 1\n-- The coupling of checkPtrR.\n")
        self.write(self.ROOT + "docs/clean.txt",
                   "Normal prose: cplx, xcpl, cp-l, x20, remote, fleet.\n")
        self.commit()
        self.assertEqual(self.internal(), set())
        self.assertEqual(self.internal(base=None), set())

    def test_lean_token_in_new_and_modified_files(self):
        self.write(self.ROOT + "theory/Bad.lean", HEADER_LEAN
                   + f"def x := 1\n    let (checkPtrTy, {self.CLI}, y) := t\n")
        self.write(self.ROOT + "ci/existing.py", HEADER_PY
                   + f"\nVALUE = 1\n# uses {self.CLIENT}\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("theory/Bad.lean", 9, "internal-cli"),
            self.ref("ci/existing.py", 10, "internal-client"),
        })

    def test_every_extension_is_scanned_case_insensitively(self):
        self.write(self.ROOT + "docs/notes.txt", f"see {self.MOUNT}\n")
        self.write(self.ROOT + "data/cfg.json",
                   '{"p": "' + self.WORKSTATION.upper() + '/x"}\n')
        self.write(self.ROOT + "scripts/tool",
                   f"#!/bin/sh\necho {self.CLIENT.lower()}\n")
        self.write(self.ROOT + "crates/a/src/lib.rs",
                   HEADER_RS + f"// {self.USER.title()}\n")
        self.commit()
        expected = {
            self.ref("docs/notes.txt", 1, "internal-mount"),
            self.ref("data/cfg.json", 1, "internal-workstation"),
            self.ref("scripts/tool", 2, "internal-client"),
            self.ref("crates/a/src/lib.rs", 8, "internal-user-m"),
        }
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_one_finding_per_label_and_line(self):
        self.write(self.ROOT + "docs/two.txt",
                   f"{self.CLI} {self.MOUNT} {self.CLI}\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("docs/two.txt", 1, "internal-cli"),
            self.ref("docs/two.txt", 1, "internal-mount"),
        })
        lines = [f for f in self.findings()
                 if f["check"] == "internal-reference"]
        self.assertEqual(len(lines), 2, lines)

    def test_banned_paths(self):
        banned = ["HANDOFF.md", "docs/PROGRESS.md", "REPRODUCE-1.md",
                  "skills/adversarial-rounds/SKILL.md",
                  "skills/hierarchical-supervision/tool.py"]
        allowed = ["docs/MY-HANDOFF.md", "HANDOFF.md.txt", "handoff.md",
                   "skills/adversarial-roundsx/SKILL.md", "docs/skills/"
                   "adversarial-rounds/SKILL.md"]
        for rel in banned + allowed:
            self.write(self.ROOT + rel, "Clean text.\n")
        self.commit()
        expected = {("internal-path", self.ROOT + rel, None, None)
                    for rel in banned}
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_renamed_and_deleted_baton_paths(self):
        self.seed({"docs/notes.md": HEADER_MD})
        git(self.repo, "mv", self.ROOT + "docs/notes.md",
            self.ROOT + "docs/HANDOFF.md")
        self.commit()
        self.assertEqual(self.internal(), {
            ("internal-path", self.ROOT + "docs/HANDOFF.md", None, None)})
        self.seed({})
        git(self.repo, "rm", "-q", self.ROOT + "docs/HANDOFF.md")
        self.commit()
        self.assertEqual(self.internal(), set())

    def test_vendored_corpora_are_excluded(self):
        for prefix in cph.LAYOUTS[self.LAYOUT].excluded:
            self.write(prefix + "up/x.txt", f"{self.CLI} {self.MOUNT}\n")
        self.commit()
        self.assertEqual(self.internal(), set())
        self.assertEqual(self.internal(base=None), set())

    def test_rename_into_scope_scans_every_line(self):
        vendor = cph.LAYOUTS[self.LAYOUT].excluded[0]
        self.write(vendor + "up/Raw.lean",
                   f"def raw := 1\n-- {self.CLI}\n")
        self.commit("Seed")
        git(self.repo, "branch", "-f", "base")
        (self.repo / self.ROOT / "theory").mkdir(parents=True, exist_ok=True)
        git(self.repo, "mv", vendor + "up/Raw.lean",
            self.ROOT + "theory/Raw.lean")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("theory/Raw.lean", 2, "internal-cli")})

    def test_untouched_lines_do_not_fail_a_change(self):
        # Shared filler keeps the edited file recognizably renamed below.
        filler = "".join(f"filler line {i}\n" for i in range(20))
        old = f"old {self.MOUNT}\n"
        self.seed({"docs/legacy.txt": "line one\n" + old + filler})
        self.write(self.ROOT + "docs/legacy.txt", "line 1\n" + old + filler)
        self.commit()
        self.assertEqual(self.internal(), set())
        # A rename within scope adds no lines either.
        git(self.repo, "mv", self.ROOT + "docs/legacy.txt",
            self.ROOT + "docs/moved.txt")
        self.commit()
        self.assertEqual(self.internal(), set())
        self.write(self.ROOT + "docs/moved.txt",
                   "line 1\n" + old + filler + f"new {self.CLI}\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("docs/moved.txt", 23, "internal-cli")})
        # Tree mode still reports the pre-existing reference.
        self.assertEqual(self.internal(base=None), {
            self.ref("docs/moved.txt", 2, "internal-mount"),
            self.ref("docs/moved.txt", 23, "internal-cli"),
        })

    def test_removing_references_is_clean(self):
        self.seed({"docs/a.txt": f"keep\n{self.CLI}\n",
                   "docs/b.txt": f"{self.MOUNT}\n"})
        self.write(self.ROOT + "docs/a.txt", "keep\n")
        git(self.repo, "rm", "-q", self.ROOT + "docs/b.txt")
        self.commit()
        self.assertEqual(self.internal(), set())

    def test_binary_blobs_skip_only_short_patterns(self):
        # A NUL byte early in the blob makes it binary, as Git decides. Short
        # literals match random bytes too often to check there, but longer
        # ones are still caught, so a NUL cannot hide a whole file.
        path = self.repo / self.ROOT / "assets" / "blob.bin"
        path.parent.mkdir(parents=True, exist_ok=True)
        png = b"\x89PNG\r\n\x1a\n\xff\xfe " + self.CLI.encode() + b" \x00"
        path.write_bytes(png + b"\n\x80\n")
        self.commit()
        for base in ("base", None):
            code, report = self.run_check(base=base)
            self.assertEqual(code, 0, report)
            self.assertEqual(report["findings"], [], report)
        path.write_bytes(png + b" " + self.MOUNT.encode() + b"\n\x80\n")
        self.commit()
        expected = {self.ref("assets/blob.bin", 3, "internal-mount")}
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_valid_utf8_with_nul_bytes_is_scanned(self):
        path = self.repo / self.ROOT / "assets" / "data.bin"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"\x00\x01\n" + self.MOUNT.encode() + b"\x00\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("assets/data.bin", 2, "internal-mount")})

    def test_symlink_target_is_scanned(self):
        link = self.repo / self.ROOT / "docs" / "link"
        link.parent.mkdir(parents=True, exist_ok=True)
        os.symlink(self.MOUNT + "/x", link)
        self.commit()
        expected = {self.ref("docs/link", 1, "internal-mount")}
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_commit_messages_are_not_scanned(self):
        self.write(self.ROOT + "docs/clean.txt", "Clean.\n")
        self.commit(f"[ci] Add a note\n\nThanks to {self.USER} and "
                    f"{self.CLI}.\n\n{TRAILER}\n")
        self.assert_clean()

    def test_binary_to_text_transition_scans_all_lines(self):
        # At `base`, both blobs are skipped as binary. Making either text
        # (even by deleting a line with zero added lines, or by editing an
        # unrelated line) brings its pre-existing lines into text scope for
        # `test_repo_hygiene.py`, so diff mode must catch them.
        del_path = self.repo / self.ROOT / "assets" / "del_bad.txt"
        edit_path = self.repo / self.ROOT / "assets" / "edit_head.txt"
        del_path.parent.mkdir(parents=True, exist_ok=True)
        del_path.write_bytes(b"\x00\xff\n" + self.MOUNT.encode() + b"\n")
        edit_path.write_bytes(b"\x00\xff\n" + self.CLI.encode() + b"\n")
        self.commit("Seed binary blobs")
        git(self.repo, "branch", "-f", "base")
        del_path.write_bytes(self.MOUNT.encode() + b"\n")
        edit_path.write_bytes(b"clean header\n" + self.CLI.encode() + b"\n")
        self.commit()
        expected = {
            self.ref("assets/del_bad.txt", 1, "internal-mount"),
            self.ref("assets/edit_head.txt", 2, "internal-cli"),
        }
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_non_utf8_text_is_scanned(self):
        # A stray invalid byte must not hide a text file's references.
        legacy = self.repo / self.ROOT / "docs" / "legacy.txt"
        legacy.parent.mkdir(parents=True, exist_ok=True)
        legacy.write_bytes(b"old \xff " + self.CLI.encode() + b"\nline two\n")
        self.commit("Seed")
        git(self.repo, "branch", "-f", "base")
        # Pre-existing lines of a text file stay out of a diff-mode change.
        legacy.write_bytes(b"old \xff " + self.CLI.encode() + b"\nline 2\n")
        latin1 = self.repo / self.ROOT / "docs" / "latin1.txt"
        latin1.write_bytes(b"caf\xe9\n" + self.MOUNT.encode() + b"\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("docs/latin1.txt", 2, "internal-mount")})
        self.assertEqual(self.internal(base=None), {
            self.ref("docs/latin1.txt", 2, "internal-mount"),
            self.ref("docs/legacy.txt", 1, "internal-cli"),
        })
        # Appending an invalid byte cannot hide a newly added reference.
        legacy.write_bytes(b"old \xff " + self.CLI.encode() + b"\nline 2\n"
                           + self.MOUNT.encode() + b" \x80\n")
        self.commit()
        self.assertIn(self.ref("docs/legacy.txt", 3, "internal-mount"),
                      self.internal())

    def test_submodule_entries_and_typechange(self):
        sub_sha = git(self.repo, "rev-parse", "HEAD").strip()
        clean_sub = self.ROOT + "third_party/sub"
        git(self.repo, "update-index", "--add", "--cacheinfo",
            f"160000,{sub_sha},{clean_sub}")
        git(self.repo, "commit", "-q", "-m", GOOD_MESSAGE)
        self.assert_clean()
        self.assert_clean(base=None)

        # A gitlink at a banned path reports `internal-path` (exit 1) rather
        # than crashing with `GitError` (exit 2) when `cat-file blob` runs.
        git(self.repo, "branch", "-f", "base")
        baton_sub = self.ROOT + "HANDOFF.md"
        skill_sub = self.ROOT + "skills/adversarial-rounds/sub"
        git(self.repo, "update-index", "--add", "--cacheinfo",
            f"160000,{sub_sha},{baton_sub}")
        git(self.repo, "update-index", "--add", "--cacheinfo",
            f"160000,{sub_sha},{skill_sub}")
        git(self.repo, "commit", "-q", "-m", GOOD_MESSAGE)
        expected_paths = {
            ("internal-path", baton_sub, None, None),
            ("internal-path", skill_sub, None, None),
        }
        code, _ = self.run_check()
        self.assertEqual(code, 1)
        self.assertEqual(self.internal(), expected_paths)
        self.assertEqual(self.internal(base=None), expected_paths)

        # Replacing a submodule (`160000`) with a regular file (`100644`)
        # scans the new blob's lines.
        git(self.repo, "rm", "-q", "--cached", baton_sub, skill_sub)
        git(self.repo, "commit", "-q", "-m", GOOD_MESSAGE)
        git(self.repo, "branch", "-f", "base")
        git(self.repo, "rm", "-q", "--cached", clean_sub)
        self.write(clean_sub, f"now a blob with {self.CLI}\n")
        self.commit()
        self.assertEqual(self.internal(), {
            self.ref("third_party/sub", 1, "internal-cli")})

    def test_source_prose_and_symlinks_ignore_nul_plus_invalid_utf8(self):
        # Combining NUL and invalid UTF-8 in source, prose, config, or symlink
        # entries must not classify them as binary to hide banned references.
        md = self.repo / self.ROOT / "docs" / "sneaky.md"
        lean = self.repo / self.ROOT / "theory" / "Sneaky.lean"
        cfg = self.repo / self.ROOT / "data" / "sneaky.json"
        md.parent.mkdir(parents=True, exist_ok=True)
        lean.parent.mkdir(parents=True, exist_ok=True)
        cfg.parent.mkdir(parents=True, exist_ok=True)
        md.write_bytes(HEADER_MD.encode() + b"\x00\xff\n"
                       + self.MOUNT.encode() + b"\n")
        lean.write_bytes(HEADER_LEAN.encode() + b"-- \x00\xff\n"
                         + f"def x := {self.CLI}\n".encode())
        cfg.write_bytes(b'{"k": "\x00\xff ' + self.CLIENT.encode() + b'"}\n')

        # A crafted `120000` symlink blob containing NUL + 0xff is also text.
        sym_oid = subprocess.run(
            ["git", "-C", str(self.repo), "hash-object", "-w", "--stdin"],
            input=self.WORKSTATION.encode() + b"\x00\xff",
            capture_output=True, check=True,
        ).stdout.decode().strip()
        git(self.repo, "add", "-A")
        git(self.repo, "update-index", "--add", "--cacheinfo",
            f"120000,{sym_oid},{self.ROOT}docs/raw_link")
        git(self.repo, "commit", "-q", "-m", GOOD_MESSAGE)
        expected = {
            self.ref("docs/sneaky.md", 9, "internal-mount"),
            self.ref("theory/Sneaky.lean", 9, "internal-cli"),
            self.ref("data/sneaky.json", 1, "internal-client"),
            self.ref("docs/raw_link", 1, "internal-workstation"),
        }
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_rename_from_binary_to_text_extension_scans_all_lines(self):
        # At `base`, `.bin` with NUL + 0xff is skipped as binary; renaming it
        # untouched (`R100`) to `.md` brings it into text scope at `head`.
        raw_bin = self.repo / self.ROOT / "assets" / "payload.bin"
        raw_bin.parent.mkdir(parents=True, exist_ok=True)
        raw_bin.write_bytes(HEADER_MD.encode() + b"\x00\xff\n"
                            + self.CLI.encode() + b"\n")
        self.commit("Seed binary payload")
        git(self.repo, "branch", "-f", "base")
        (self.repo / self.ROOT / "docs").mkdir(parents=True, exist_ok=True)
        git(self.repo, "mv", self.ROOT + "assets/payload.bin",
            self.ROOT + "docs/payload.md")
        self.commit()
        expected = {self.ref("docs/payload.md", 9, "internal-cli")}
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)

    def test_banned_skill_entry_without_trailing_slash(self):
        # A symlink or gitlink placed directly at `skills/<banned>` has no
        # trailing slash in `ls-tree` / `ls-files`, and must still be flagged.
        sub_sha = git(self.repo, "rev-parse", "HEAD").strip()
        sym_dir = self.repo / self.ROOT / "skills"
        sym_dir.mkdir(parents=True, exist_ok=True)
        os.symlink("../docs", sym_dir / "adversarial-rounds")
        os.symlink("../docs", sym_dir / "adversarial-roundsx")
        git(self.repo, "add", "-A")
        git(self.repo, "update-index", "--add", "--cacheinfo",
            f"160000,{sub_sha},{self.ROOT}skills/hierarchical-supervision")
        git(self.repo, "commit", "-q", "-m", GOOD_MESSAGE)
        expected = {
            ("internal-path", self.ROOT + "skills/adversarial-rounds",
             None, None),
            ("internal-path", self.ROOT + "skills/hierarchical-supervision",
             None, None),
        }
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)


class MonorepoInternalHygieneTests(InternalHygieneMixin, RepoTestCase):
    ROOT = "anneal/"
    LAYOUT = "monorepo"

    def test_root_paths_outside_anneal_are_out_of_scope(self):
        self.write("ci/x.txt", f"{self.CLI}\n")
        self.write("HANDOFF.md", "x\n")
        self.write("skills/adversarial-rounds/SKILL.md", "x\n")
        self.commit("not Anneal")
        self.assertEqual(self.internal(), set())
        self.assertEqual(self.internal(base=None), set())

    def test_integration_paths_are_in_scope(self):
        self.write(".github/workflows/anneal.yml", f"# {self.CLI}\n")
        self.write("zerocopy/proofs/01_x/PROGRESS.md", "x\n")
        self.commit()
        expected = {
            ("internal-reference", ".github/workflows/anneal.yml", 1,
             "internal-cli"),
            ("internal-path", "zerocopy/proofs/01_x/PROGRESS.md", None, None),
        }
        self.assertEqual(self.internal(), expected)
        self.assertEqual(self.internal(base=None), expected)


class StandaloneInternalHygieneTests(InternalHygieneMixin,
                                     StandaloneRepoTestCase):
    ROOT = ""
    LAYOUT = "standalone"


class InternalUnitTests(unittest.TestCase):
    CLI = InternalHygieneMixin.CLI

    def naive(self, text: str) -> list[tuple[int, str]]:
        return [(n, label)
                for n, line in enumerate(text.split("\n"), 1)
                for label, pat in cph.BANNED_CONTENT_PATTERNS
                if pat.search(line)]

    def test_hits_report_lines_and_labels(self):
        text = f"a\n{self.CLI} x\r\nb\f{self.CLI}\n"
        self.assertEqual(cph.internal_reference_hits(text),
                         [(2, "internal-cli"), (3, "internal-cli")])
        self.assertEqual(cph.internal_reference_hits(text, set()), [])
        self.assertEqual(cph.internal_reference_hits(text, {1, 4}), [])
        self.assertEqual(cph.internal_reference_hits(text, {3}),
                         [(3, "internal-cli")])

    def test_literal_screen_agrees_with_the_patterns(self):
        samples = ["", "plain", "cplx xcpl", "\u0130\u0131\u017f\u212a"]
        for (label, pat), lit in zip(cph.BANNED_CONTENT_PATTERNS,
                                     cph._BANNED_LITERALS):
            for variant in (lit, lit.upper(), lit.title()):
                samples += [variant, f"x {variant} y", f"a\n{variant}\nb",
                            f"_{variant}_", f"\u2200 {variant}"]
            # Non-ASCII characters that IGNORECASE equates with ASCII.
            for src, dst in cph._FOLD_EXTRA:
                samples.append(lit.replace(dst, src))
        for text in samples:
            with self.subTest(text=text):
                self.assertEqual(cph.internal_reference_hits(text),
                                 self.naive(text))

    def test_literals_are_plain_text(self):
        for (label, pat), lit in zip(cph.BANNED_CONTENT_PATTERNS,
                                     cph._BANNED_LITERALS):
            with self.subTest(label=label):
                self.assertEqual(pat.flags & re.IGNORECASE, re.IGNORECASE)
                self.assertFalse(set(lit) & set(".^$*+?{}[]|()\\"), lit)
                self.assertTrue(pat.search(lit), lit)

    def test_fold_extra_covers_every_case_insensitive_code_point(self):
        chars = sorted(set("".join(cph._BANNED_LITERALS)))
        cls = re.compile("[" + "".join(re.escape(c) for c in chars) + "]",
                         re.IGNORECASE)
        for cp in range(0x80, 0x110000):
            if 0xD800 <= cp < 0xE000 or not cls.fullmatch(chr(cp)):
                continue
            folded = cph._fold(chr(cp))
            with self.subTest(cp=hex(cp)):
                self.assertEqual(len(folded), 1)
                self.assertTrue(
                    re.fullmatch(re.escape(folded), chr(cp), re.IGNORECASE))
                self.assertIn(folded, chars)

    def test_path_messages(self):
        mono, solo = cph.MONOREPO, cph.STANDALONE
        for path, layout in (("HANDOFF.md", solo), ("a/PROGRESS.md", solo),
                             ("REPRODUCE.md", solo),
                             ("anneal/HANDOFF.md", mono),
                             ("skills/adversarial-rounds", solo),
                             ("skills/adversarial-rounds/x", solo),
                             ("anneal/skills/hierarchical-supervision", mono),
                             ("anneal/skills/hierarchical-supervision/x",
                              mono)):
            self.assertIsNotNone(cph.internal_path_message(path, layout), path)
        for path, layout in (("HANDOFF.mdx", solo), ("xHANDOFF.md", solo),
                             ("skills/adversarial-roundsx", solo),
                             ("skills/adversarial-rounds/x", mono),
                             ("anneal/skills/adversarial-rounds/x", solo),
                             ("skills/other/x", solo)):
            self.assertIsNone(cph.internal_path_message(path, layout), path)

    def test_decode_blob(self):
        dec = cph.decode_blob
        self.assertEqual(dec(b"ok\n"), ("ok\n", False))
        # Valid UTF-8 is text even with NUL bytes.
        self.assertEqual(dec(b"\x00ok"), ("\x00ok", False))
        self.assertEqual(dec(b"\x00\xff"), ("\x00\ufffd", True))
        self.assertEqual(dec(b"\x00\xff", "assets/blob.bin"),
                         ("\x00\ufffd", True))
        # Symlinks and source, prose, or config paths are never binary.
        for path in ("docs/note.MD", "AGENTS.md", "lakefile.toml",
                     "data/x.json"):
            self.assertEqual(dec(b"\x00\xff", path), ("\x00\ufffd", False))
        self.assertEqual(dec(b"\x00\xff", is_symlink=True),
                         ("\x00\ufffd", False))
        self.assertEqual(dec(b"a\xff\nb"), ("a\ufffd\nb", False))
        # Git only sniffs the first 8000 bytes for NUL.
        late = b"x" * 8000 + b"\x00\xff"
        self.assertFalse(dec(late)[1])
        self.assertTrue(dec(late[1:])[1])
        # A truncated sequence before a line feed keeps the line count.
        text, _ = dec(b"a\xe2\x82\nb\n")
        self.assertEqual(text.split("\n"), ["a\ufffd", "b", ""])

    def test_binary_scan_skips_only_short_literals(self):
        short = [label for (label, _), lit in zip(cph.BANNED_CONTENT_PATTERNS,
                                                  cph._BANNED_LITERALS)
                 if len(lit) < cph._BINARY_MIN_LITERAL]
        self.assertEqual(short, ["internal-cli"])
        for (label, _), lit in zip(cph.BANNED_CONTENT_PATTERNS,
                                   cph._BANNED_LITERALS):
            text = f"\x00 {lit} \ufffd\n"
            hits = cph.internal_reference_hits(text, binary=True)
            with self.subTest(label=label):
                self.assertEqual(hits, [] if label in short else [(1, label)])

    def test_every_banned_pattern_matches_and_respects_boundaries(self):
        for (label, pat), lit in zip(cph.BANNED_CONTENT_PATTERNS,
                                     cph._BANNED_LITERALS):
            with self.subTest(label=label):
                hits = cph.internal_reference_hits(f"prefix {lit} suffix\n")
                self.assertIn((1, label), hits)
                if pat.pattern.startswith(r"\b"):
                    self.assertNotIn(
                        (1, label),
                        cph.internal_reference_hits(f"a{lit} suffix\n"))
                if pat.pattern.endswith(r"\b"):
                    self.assertNotIn(
                        (1, label),
                        cph.internal_reference_hits(f"prefix {lit}z\n"))

    def test_git_blobs_rejects_malformed_batch_output(self):
        oid = "a" * 40

        class FakeGit(cph.Git):
            def __init__(self, payload: bytes):
                self.payload = payload

            def run(self, *args: str, ok_codes: tuple[int, ...] = (0,),
                    stdin: bytes | None = None) -> bytes:
                return self.payload

        self.assertEqual(FakeGit(b"").blobs([]), {})
        self.assertEqual(FakeGit(f"{oid} blob 2\nhi\n".encode()).blobs([oid]),
                         {oid: b"hi"})
        bad_payloads = (
            b"truncated-without-eol",
            f"{oid} commit 2\nhi\n".encode(),
            f"{oid} blob \u00b2\nhi\n".encode(),
            f"{oid} blob 2\nhiX".encode(),
            f"{oid} blob 2\nhi\nextra".encode(),
        )
        for payload in bad_payloads:
            with self.subTest(payload=payload):
                with self.assertRaises(cph.GitError):
                    FakeGit(payload).blobs([oid])


class RepoHygieneParityTests(unittest.TestCase):
    """`ci/test_repo_hygiene.py` enforces the same definitions as this script.

    The digest pins the pattern set, so that changing it is a deliberate,
    reviewed edit to this test as well.
    """

    LABELS = (
        "internal-client", "internal-service", "internal-cli",
        "internal-user-m", "internal-user-j", "internal-mount",
        "internal-remote", "internal-fuse", "internal-sync-bin",
        "internal-fsd", "internal-proto", "internal-envelope",
        "internal-workstation", "internal-sidecar-uri", "internal-repo",
        "internal-team-dir", "internal-placeholder", "internal-flag-remote",
        "internal-flag-ff", "internal-flag-chk", "internal-sym-sync",
        "internal-launcher", "internal-bucket-tf", "internal-bucket-wtu",
        "internal-infra-fsd", "internal-fleet-cfg", "internal-fleet-dir",
    )
    DIGEST = (
        "53f8907db177f95a8a8dcf2fcf40dbc53575db2ee5dcbbdf9fe2f90fb1b5e933"
    )

    def test_shared_definitions(self):
        import test_repo_hygiene as trh
        self.assertIs(trh._BANNED_CONTENT_PATTERNS,
                      cph.BANNED_CONTENT_PATTERNS)
        self.assertIs(trh._BANNED_FILENAME_RE, cph.BANNED_FILENAME_RE)
        self.assertIs(trh._BANNED_INTERNAL_PREFIXES,
                      cph.BANNED_INTERNAL_PREFIXES)
        self.assertLessEqual(set(trh._EXCLUDED_PREFIXES),
                             set(cph.STANDALONE.excluded))

    def test_pinned_definitions(self):
        pats = cph.BANNED_CONTENT_PATTERNS
        self.assertEqual(tuple(label for label, _ in pats), self.LABELS)
        self.assertEqual(len(pats), 27)
        self.assertEqual(cph.BANNED_FILENAME_RE.pattern,
                         r"(^|/)(HANDOFF|PROGRESS|REPRODUCE[^/]*)\.md$")
        self.assertEqual(cph.BANNED_FILENAME_RE.flags, re.UNICODE)
        self.assertEqual(cph.BANNED_INTERNAL_PREFIXES, (
            "skills/adversarial-rounds/", "skills/hierarchical-supervision/"))
        blob = "\n".join(f"{label}\t{pat.pattern}\t{pat.flags}"
                         for label, pat in pats)
        self.assertEqual(hashlib.sha256(blob.encode()).hexdigest(),
                         self.DIGEST)


class RepositoryTreeTests(unittest.TestCase):
    def test_checked_in_tree_passes_tree_checks(self):
        here = Path(__file__).resolve().parent
        res = subprocess.run(
            ["git", "-C", str(here), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=False,
        )
        if res.returncode != 0:
            self.skipTest("not running from a Git checkout")
        repo = Path(res.stdout.strip()).resolve()
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo", str(repo),
             "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        # The detected layout matches where this file lives.
        rel = SCRIPT.relative_to(repo).as_posix()
        expected = "monorepo" if rel.startswith("anneal/") else "standalone"
        self.assertEqual(json.loads(res.stdout)["layout"], expected)


if __name__ == "__main__":
    unittest.main()
