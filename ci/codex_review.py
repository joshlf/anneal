# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Translate managed Codex review summaries into a required commit status.

The GitHub workflow supplies serialization and a trusted checkout. This module
uses only the standard library and never executes PR code or comment contents.
Without --publish it reads the same live inputs and prints proposed statuses,
so maintainers can diagnose the gate without changing a merge requirement.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
import json
import os
import re
import sys
from urllib.error import HTTPError
from urllib.request import Request, urlopen


CONTEXT = "Codex review"
# Pin the account ID as well as its display name. A copied marker or a similarly
# named account must not acquire authority to approve a revision.
BOT_ID = 199175422
BOT_LOGIN = "chatgpt-codex-connector[bot]"
SUMMARY = "<!-- codex-pull-request-review-summary"
STATE = "<!-- codex-review-state:"


@dataclass(frozen=True)
class Result:
    """A native commit-status state and the reason shown beside it."""

    state: str
    reason: str


def unique_object(pairs):
    """Reject ambiguous JSON rather than accepting the last duplicate key."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def review_result(head, comments):
    """Read the latest authentic summary; never fall back to an older success.

    The hidden v1 state is an observed integration format, not a documented
    OpenAI API contract. Recognize summary and state prefixes broadly enough to
    notice a replacement version, then require exactly the version understood
    here. A format change should stop merging and call for an adapter update.
    """
    summaries = []
    for comment in comments:
        user = comment.get("user") or {}
        if (user.get("id") == BOT_ID and user.get("login") == BOT_LOGIN
                and user.get("type") == "Bot"
                and SUMMARY in (comment.get("body") or "")):
            summaries.append(comment)
    if not summaries:
        return Result("pending", "Waiting for a Codex Review Summary")
    # Comment IDs order creation. An edit to an older summary must not make it
    # supersede a newer, possibly incomplete review summary.
    body = max(summaries, key=lambda comment: comment["id"])["body"]
    markers = re.findall(r"<!-- codex-review-state:.*?-->", body, re.DOTALL)
    if (body.count(SUMMARY) != 1
            or "<!-- codex-pull-request-review-summary -->" not in body
            or body.count(STATE) != 1 or len(markers) != 1):
        return Result("failure", "Unrecognized or ambiguous Codex summary")
    match = re.fullmatch(r"<!-- codex-review-state:v1 (.*?) -->", markers[0],
                         re.DOTALL)
    if match is None:
        return Result("failure", "Unsupported Codex review-state version")
    try:
        payload = json.loads(match[1], object_pairs_hook=unique_object)
        review = payload["code_review"]
        if not isinstance(review, dict):
            raise ValueError("Code Review state is not an object")
    except (ValueError, TypeError, KeyError):
        return Result("failure", "Malformed Codex Code Review state")

    # Security Review has an independent verdict. A clean security result,
    # emoji, or prose receipt cannot fill in a missing Code Review verdict.
    if review.get("commit_sha") != head:
        return Result("pending", "Codex has not reviewed this head commit")
    if review.get("status") != "completed":
        return Result("pending", "Waiting for a completed Codex Code Review")
    # Identity checks distinguish JSON false from null, zero, and empty strings.
    # Resolving threads by hand is insufficient: has_any_findings must also be
    # false, so Codex must publish a clean result for this revision.
    if (review.get("has_any_findings") is not False
            or review.get("has_unresolved_findings") is not False):
        return Result("failure", "Codex findings remain or the verdict is unknown")
    return Result("success", "Codex completed Code Review with no findings")


def pull_snapshot(pulls):
    """Keep the PR identities that affect a commit's shared status."""
    return sorted((pull["number"], pull["head"]["sha"], pull["base"]["ref"],
                   pull["base"]["sha"]) for pull in pulls)


def combine_results(pulls, results):
    """Require each open PR sharing a commit to have its own clean result.

    A status belongs to a commit, not to a PR. Publishing independent answers
    under the same context lets the last PR overwrite the others. Group all
    open PRs, including drafts and stacks targeting other branches, so a clean
    review of one diff cannot supply a missing review of another diff.
    """
    groups = defaultdict(list)
    for pull in pulls:
        groups[pull["head"]["sha"]].append(pull["number"])
    combined = {}
    for head, numbers in groups.items():
        # Findings take precedence over waiting, and neither can become green
        # just because a different PR on the same commit is already clean.
        blockers = [n for n in numbers if results[n].state != "success"]
        if blockers:
            blocked = next((n for n in blockers
                            if results[n].state == "failure"), blockers[0])
            result = results[blocked]
            combined[head] = Result(result.state, f"PR #{blocked}: {result.reason}")
        else:
            combined[head] = Result(
                "success", f"Clean Codex Code Review for all {len(numbers)} PR(s)")
    return combined


class GitHub:
    """The effect boundary: fixed-host API reads and commit-status writes."""

    def __init__(self, repository, token):
        if (not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repository)
                or repository.split("/")[-1] in {".", ".."}):
            raise ValueError("Expected an owner/repository name")
        self.repository = repository
        self.root = f"https://api.github.com/repos/{repository}/"
        self.token = token

    def request(self, path, data=None):
        request = Request(self.root + path,
                          data=None if data is None else json.dumps(data).encode(),
                          headers={"Authorization": f"Bearer {self.token}",
                                   "Accept": "application/vnd.github+json",
                                   "Content-Type": "application/json",
                                   "X-GitHub-Api-Version": "2022-11-28"})
        try:
            with urlopen(request, timeout=30) as response:
                return json.load(response)
        except HTTPError as error:
            # Do not log request headers or retry an ambiguous status write.
            # A manual recheck recomputes the result instead of replaying it.
            raise RuntimeError(
                f"GitHub {request.get_method()} {path}: HTTP {error.code}") from None

    def pages(self, path):
        separator = "&" if "?" in path else "?"
        page = 1
        while True:
            batch = self.request(f"{path}{separator}per_page=100&page={page}")
            if not isinstance(batch, list):
                raise ValueError("Expected a paginated GitHub array")
            yield from batch
            if len(batch) < 100:
                return
            page += 1

    def pulls(self):
        return list(self.pages("pulls?state=open&sort=created&direction=asc"))

    def comments(self, number):
        return list(self.pages(f"issues/{number}/comments"))

    def publish(self, head, result):
        # Use the SHA evaluated, never a branch name that could have advanced.
        # The Actions job's own check belongs to its default-branch checkout;
        # this explicit status is what branch protection requires on the PR.
        desired = {
            "context": CONTEXT, "state": result.state,
            "description": result.reason[:140],
            "target_url": f"https://github.com/{self.repository}/actions/workflows/codex-review.yml",
        }
        # GitHub limits the number of statuses per commit and context. An
        # unrelated PR's event must not consume another entry for an unchanged
        # verdict. The API returns statuses newest first; stop at this context.
        current = next((status for status in self.pages(f"commits/{head}/statuses")
                        if status["context"].casefold() == CONTEXT.casefold()), {})
        if (current.get("creator", {}).get("login") == "github-actions[bot]"
                and all(current.get(key) == value
                        for key, value in desired.items())):
            return
        self.request(f"statuses/{head}", desired)


def reconcile(github, publish=False):
    """Recompute every open PR, because serialized event runs can be coalesced.

    GitHub may replace a pending concurrency-group run with a newer one. Since
    every run reads all open PRs, the retained run also covers the discarded
    event. No database, event history, or polling runner is needed.
    """
    pulls = github.pulls()
    results = {}
    read_errors = []
    for pull in pulls:
        number = pull["number"]
        try:
            results[number] = review_result(
                pull["head"]["sha"], github.comments(number))
        except (RuntimeError, ValueError, OSError) as error:
            # A failed read replaces old success with a blocking verdict where
            # the status API remains available. Other PRs are still evaluated.
            results[number] = Result("failure", "Cannot read Codex summary")
            read_errors.append(f"PR #{number}: {error}")
    # A push, retarget, newly opened PR, or closure can change grouping while
    # comments are read. Leave statuses pending and let the queued event (or a
    # manual recheck) read a new snapshot rather than publish a mixed snapshot.
    try:
        if pull_snapshot(pulls) != pull_snapshot(github.pulls()):
            raise RuntimeError("Open PRs changed during evaluation")
    except (RuntimeError, ValueError, OSError) as error:
        results = {pull["number"]: Result("pending", "PR snapshot changed or is unavailable")
                   for pull in pulls}
        read_errors.append(str(error))
    combined = combine_results(pulls, results)
    for head, result in sorted(combined.items()):
        print(f"{head}: {result.state}: {result.reason}")
        if publish:
            github.publish(head, result)
    if read_errors:
        raise RuntimeError("; ".join(read_errors))
    return combined


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY"))
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    token = os.environ.get("GH_TOKEN")
    if not args.repository or not token:
        parser.error("Supply --repository and GH_TOKEN (read-only is enough without --publish)")
    reconcile(GitHub(args.repository, token), args.publish)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError) as error:
        sys.exit(str(error))
