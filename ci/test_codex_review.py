# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise policy boundaries and publication using in-memory GitHub data."""

import copy
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

from codex_review import (
    BOT_ID, BOT_LOGIN, CONTEXT, GitHub, Result, combine_results,
    reconcile, review_result,
)


HEAD = "a" * 40
OTHER_HEAD = "b" * 40
BASE = "c" * 40


def summary(head=HEAD, **changes):
    # The wire shape comes from actual managed-review summaries, including the
    # independent security verdict that must not substitute for Code Review.
    review = {"commit_sha": head, "status": "completed",
              "has_any_findings": False, "has_unresolved_findings": False}
    review.update(changes)
    return {
        "id": 10,
        "user": {"id": BOT_ID, "login": BOT_LOGIN, "type": "Bot"},
        "body": "<!-- codex-pull-request-review-summary -->\n"
                "<!-- codex-review-state:v1 " + json.dumps({
                    "code_review": review,
                    "security_review": {"status": "completed",
                                        "has_any_findings": False},
                }) + " -->\nCodex Review Summary: Completed",
    }


def pull(number=1, head=HEAD, base="main"):
    return {"number": number, "head": {"sha": head},
            "base": {"ref": base, "sha": BASE}, "draft": False}


class PolicyTests(unittest.TestCase):
    def test_clean_exact_head_needs_no_formal_review_or_reaction(self):
        self.assertEqual(review_result(HEAD, [summary()]).state, "success")

    def test_missing_deleted_or_wrong_head_summary_waits(self):
        for comments in [[], [summary(OTHER_HEAD)]]:
            with self.subTest(comments=comments):
                self.assertEqual(review_result(HEAD, comments).state, "pending")

    def test_only_the_exact_bot_identity_is_authoritative(self):
        for key, value in [("id", BOT_ID + 1), ("login", "codex[bot]"),
                           ("type", "User")]:
            comment = summary()
            comment["user"][key] = value
            with self.subTest(key=key):
                self.assertEqual(review_result(HEAD, [comment]).state, "pending")

    def test_running_and_failed_review_states_do_not_pass(self):
        for status in ["running", "queued", "failed", None, True]:
            with self.subTest(status=status):
                self.assertNotEqual(review_result(
                    HEAD, [summary(status=status)]).state, "success")

    def test_completed_is_not_a_verdict_and_resolution_is_not_a_clean_review(self):
        for key in ["has_any_findings", "has_unresolved_findings"]:
            for value in [True, None, 0, "false", [], {}]:
                with self.subTest(key=key, value=value):
                    self.assertEqual(review_result(
                        HEAD, [summary(**{key: value})]).state, "failure")
            comment = summary()
            payload = json.loads(comment["body"].split("v1 ")[1].split(" -->")[0])
            del payload["code_review"][key]
            comment["body"] = ("<!-- codex-pull-request-review-summary -->\n"
                               "<!-- codex-review-state:v1 "
                               + json.dumps(payload) + " -->")
            self.assertEqual(review_result(HEAD, [comment]).state, "failure")

    def test_no_fallback_to_an_older_clean_summary(self):
        older = summary()
        newer = summary(status="running")
        newer["id"] += 1
        # Updated timestamps and input ordering do not change creation order.
        older["updated_at"] = "2099-01-01T00:00:00Z"
        for comments in [[older, newer], [newer, older]]:
            self.assertEqual(review_result(HEAD, comments).state, "pending")
        newer["body"] = "<!-- codex-pull-request-review-summary:v2 -->"
        self.assertEqual(review_result(HEAD, [older, newer]).state, "failure")

    def test_unsupported_ambiguous_and_malformed_state_blocks(self):
        clean = summary()["body"]
        variants = [
            clean.replace("state:v1", "state:v2"),
            clean.replace('"code_review": {', '"code_review": null, "extra": {'),
            clean.replace('"status": "completed"', '"status": "completed", "status": "running"'),
            clean.replace('"has_any_findings": false', '"has_any_findings": true, "has_any_findings": false'),
            clean + clean,
            clean + "<!-- codex-review-state:v2 {} -->",
            clean.replace(" -->\nCodex", "\nCodex"),
            "<!-- codex-pull-request-review-summary -->\n<!-- codex-review-state:v1 [] -->",
        ]
        for body in variants:
            comment = summary()
            comment["body"] = body
            with self.subTest(body=body):
                self.assertEqual(review_result(HEAD, [comment]).state, "failure")

    def test_security_receipt_and_emoji_do_not_fill_in_code_review(self):
        comment = summary()
        comment["body"] = comment["body"].replace('"code_review":', '"other":')
        self.assertEqual(review_result(HEAD, [comment]).state, "failure")
        for body in ["👍", "No major issues found", "<!-- codex-review-receipt:v1 -->"]:
            comment["body"] = body
            self.assertEqual(review_result(HEAD, [comment]).state, "pending")

    def test_shared_head_requires_each_pr_even_with_a_different_base_or_draft(self):
        pulls = [pull(1), pull(2, base="stack-parent")]
        pulls[1]["draft"] = True
        results = {1: review_result(HEAD, [summary()]),
                   2: review_result(HEAD, [])}
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "pending")
        results[2] = Result("failure", "Findings")
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "failure")
        results[2] = review_result(HEAD, [summary()])
        self.assertEqual(combine_results(pulls, results)[HEAD].state, "success")

    def test_findings_are_reported_even_if_another_pr_is_still_waiting(self):
        results = {1: Result("pending", "Waiting"),
                   2: Result("failure", "Findings")}
        combined = combine_results([pull(1), pull(2)], results)
        self.assertEqual(combined[HEAD], Result("failure", "PR #2: Findings"))

    def test_unrelated_commits_have_independent_verdicts(self):
        results = {1: Result("success", "Clean"), 2: Result("failure", "Findings")}
        combined = combine_results([pull(1), pull(2, OTHER_HEAD)], results)
        self.assertEqual(combined[HEAD].state, "success")
        self.assertEqual(combined[OTHER_HEAD].state, "failure")


class FakeGitHub:
    def __init__(self, initial, comments, final=None):
        self.snapshots = [initial, initial if final is None else final]
        self.bodies = comments
        self.writes = []

    def pulls(self):
        return copy.deepcopy(self.snapshots.pop(0))

    def comments(self, number):
        body = self.bodies[number]
        if isinstance(body, Exception):
            raise body
        return body

    def publish(self, head, result):
        self.writes.append((head, result))


class ReconciliationTests(unittest.TestCase):
    def run_gate(self, github, publish=False):
        with patch("sys.stdout", new=io.StringIO()):
            return reconcile(github, publish)

    def test_dry_run_reads_live_inputs_without_writes(self):
        github = FakeGitHub([pull()], {1: [summary()]})
        self.assertEqual(self.run_gate(github)[HEAD].state, "success")
        self.assertEqual(github.writes, [])

    def test_event_coalescing_does_not_omit_unrelated_prs(self):
        github = FakeGitHub([pull(1), pull(2, OTHER_HEAD)],
                            {1: [summary()], 2: []})
        self.run_gate(github, True)
        self.assertEqual({head: result.state for head, result in github.writes},
                         {HEAD: "success", OTHER_HEAD: "pending"})

    def test_push_open_close_and_retarget_during_reads_cannot_publish_success(self):
        initial = [pull()]
        changed_base = pull()
        changed_base["base"]["sha"] = OTHER_HEAD
        for final in [[], [pull(1, OTHER_HEAD)], [pull(1), pull(2)],
                      [pull(base="another-branch")], [changed_base]]:
            github = FakeGitHub(initial, {1: [summary()]}, final)
            with self.subTest(final=final), self.assertRaises(RuntimeError):
                self.run_gate(github, True)
            self.assertEqual(github.writes, [(
                HEAD, Result("pending", "PR #1: PR snapshot changed or is unavailable"))])

    def test_api_failure_blocks_that_commit_and_preserves_other_evaluations(self):
        github = FakeGitHub([pull(1), pull(2, OTHER_HEAD)],
                            {1: OSError("API unavailable"), 2: [summary(OTHER_HEAD)]})
        with self.assertRaisesRegex(RuntimeError, "API unavailable"):
            self.run_gate(github, True)
        self.assertEqual({head: result.state for head, result in github.writes},
                         {HEAD: "failure", OTHER_HEAD: "success"})

    def test_new_head_can_never_receive_an_old_heads_success(self):
        github = FakeGitHub([pull(head=OTHER_HEAD)], {1: [summary()]})
        self.run_gate(github, True)
        self.assertEqual([(head, result.state) for head, result in github.writes],
                         [(OTHER_HEAD, "pending")])


class TransportTests(unittest.TestCase):
    def test_rollout_ruleset_requires_the_publishers_context_from_actions(self):
        root = Path(__file__).resolve().parent.parent
        ruleset = json.loads((root / ".github/codex-review-ruleset.json").read_text())
        self.assertEqual(ruleset["conditions"]["ref_name"]["include"],
                         ["refs/heads/main"])
        required = ruleset["rules"][0]["parameters"]["required_status_checks"]
        self.assertEqual(required, [{"context": CONTEXT, "integration_id": 15368}])
        self.assertEqual(ruleset["bypass_actors"], [])

    def test_pagination_continues_past_a_full_page(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", side_effect=[list(range(100)), [100]]) as request:
            self.assertEqual(list(github.pages("pulls?state=open")), list(range(101)))
        self.assertEqual(request.call_args_list[1].args,
                         ("pulls?state=open&per_page=100&page=2",))

    def test_malformed_page_is_not_an_empty_result(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", return_value={"message": "Error"}):
            with self.assertRaises(ValueError):
                github.pulls()

    def test_status_is_written_to_the_evaluated_sha_and_repeated_results_are_noops(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch.object(github, "request", side_effect=[[], {}]) as request:
            github.publish(HEAD, Result("success", "Clean"))
        path, desired = request.call_args.args
        self.assertEqual(path, f"statuses/{HEAD}")
        self.assertEqual(desired["context"], CONTEXT)
        existing = dict(desired, creator={"login": "github-actions[bot]"})
        with patch.object(github, "request", return_value=[existing]) as request:
            github.publish(HEAD, Result("success", "Clean"))
            self.assertEqual(request.call_count, 1)
        # A previous success must not suppress publication when the summary is
        # removed or a new review is running on the same commit.
        with patch.object(github, "request", side_effect=[[existing], {}]) as request:
            github.publish(HEAD, Result("pending", "Waiting"))
            self.assertEqual(request.call_args.args[1]["state"], "pending")
        existing["creator"]["login"] = "another-writer"
        with patch.object(github, "request", side_effect=[[existing], {}]) as request:
            github.publish(HEAD, Result("success", "Clean"))
            self.assertEqual(request.call_count, 2)

    def test_repository_text_cannot_change_the_api_host_or_path(self):
        for repository in ["../anneal", "joshlf/anneal/../x", "https://evil.invalid/x"]:
            with self.subTest(repository=repository), self.assertRaises(ValueError):
                GitHub(repository, "not-a-real-token")

    def test_transport_encodes_data_without_executing_or_logging_it(self):
        github = GitHub("joshlf/anneal", "not-a-real-token")
        with patch("codex_review.urlopen") as open_url:
            open_url.return_value.__enter__.return_value = io.BytesIO(b"{}")
            github.request(f"statuses/{HEAD}", {"description": "$(exit 99)"})
        request = open_url.call_args.args[0]
        self.assertEqual(request.full_url,
                         f"https://api.github.com/repos/joshlf/anneal/statuses/{HEAD}")
        self.assertEqual(json.loads(request.data), {"description": "$(exit 99)"})
        with patch("codex_review.urlopen", side_effect=HTTPError(
                request.full_url, 403, "Forbidden", {}, None)):
            with self.assertRaisesRegex(RuntimeError, "POST.*HTTP 403") as error:
                github.request(f"statuses/{HEAD}", {})
        self.assertNotIn("not-a-real-token", str(error.exception))


if __name__ == "__main__":
    unittest.main()
