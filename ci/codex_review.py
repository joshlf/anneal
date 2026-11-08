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
The default mode reads live inputs and prints proposed statuses. Explicit
--publish and --record-deletion modes perform the workflow's two write effects.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
import json
import io
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
# Deletions remove evidence from the comments API. Record each deletion as an
# immutable, uniquely named commit status on Anneal's initial commit. This
# stable anchor survives branch moves without needing a database, a new ref,
# contents-write permission, or a stored copy of the deleted prose.
STATE_ANCHOR = "8950b5afa6444859c21fb4d100e21dd283afb6d6"
DELETION_CONTEXT = "Codex summary deletion/"


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


def authentic_summary(comment):
    """Authenticate the comment author, independently of the event sender."""
    user = comment.get("user") or {}
    return (user.get("id") == BOT_ID and user.get("login") == BOT_LOGIN
            and user.get("type") == "Bot"
            and SUMMARY in (comment.get("body") or ""))


def summary_snapshot(comments):
    """Track edits and deletions as well as replacement summary comments."""
    return sorted((c["id"], c.get("updated_at"), c["body"])
                  for c in comments if authentic_summary(c))


def review_result(head, comments, deleted_through=0):
    """Read the latest authentic summary; never fall back to an older success.

    The hidden v1 state is an observed integration format, not a documented
    OpenAI API contract. Recognize summary and state prefixes broadly enough to
    notice a replacement version, then require exactly the version understood
    here. A format change should stop merging and call for an adapter update.
    """
    summaries = [c for c in comments if authentic_summary(c)]
    if not summaries:
        return Result("pending", "Waiting for a Codex Review Summary")
    # Comment IDs order creation. An edit to an older summary must not make it
    # supersede a newer, possibly incomplete review summary.
    latest = max(summaries, key=lambda comment: comment["id"])
    if latest["id"] <= deleted_through:
        return Result("pending", "A newer summary was deleted; request a new summary")
    body = latest["body"]
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
        return self.request_url(self.root + path, data)

    def request_url(self, url, data=None):
        request = Request(url,
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
                f"GitHub {request.get_method()}: HTTP {error.code}") from None

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

    def deleted_summaries(self):
        deleted = {}
        for status in self.pages(f"commits/{STATE_ANCHOR}/statuses"):
            match = re.fullmatch(r"Codex summary deletion/([1-9][0-9]*)/([1-9][0-9]*)",
                                 status["context"])
            if (match and status["state"] == "success"
                    and status.get("creator", {}).get("login") == "github-actions[bot]"):
                number, comment = map(int, match.groups())
                deleted[number] = max(deleted.get(number, 0), comment)
        return deleted

    def record_deletion(self, event):
        """Record deletion events before they enter a coalescing job queue.

        A user may delete a bot comment, so authenticate the deleted comment's
        author, not the user who performed the deletion. Each event has a unique
        context: concurrent recorders cannot overwrite another deletion.
        """
        comment = event.get("comment") or {}
        issue = event.get("issue") or {}
        if (event.get("action") != "deleted" or not issue.get("pull_request")
                or not authentic_summary(comment)):
            return
        number, comment_id = issue["number"], comment["id"]
        self.publish_status(STATE_ANCHOR, {
            "context": f"{DELETION_CONTEXT}{number}/{comment_id}",
            "state": "success", "description": "Deleted Codex summary; older results cannot approve",
            "target_url": f"https://github.com/{self.repository}/pull/{number}",
        })

    def queue_groups(self):
        """Read the main queue's generated heads and their required PR prefix.

        GitHub's MergeQueueEntry exposes the generated headCommit for an entry,
        its queue position, and its pullRequest. A group may incorporate earlier
        entries, so require the entire prefix through that position, including
        entries which do not yet have a generated commit. Never infer membership
        from a branch name or assume squash commits retain PR ancestry.
        """
        owner, name = self.repository.split("/")
        query = """query($owner: String!, $name: String!, $after: String) {
          repository(owner: $owner, name: $name) {
            mergeQueue(branch: "main") { entries(first: 100, after: $after) {
              nodes { position headCommit { oid }
                pullRequest { number headRefOid } }
              pageInfo { hasNextPage endCursor }
            } }
          }
        }"""
        entries, after = [], None
        while True:
            response = self.request_url("https://api.github.com/graphql", {
                "query": query, "variables": {"owner": owner, "name": name, "after": after},
            })
            if response.get("errors"):
                raise RuntimeError("GitHub could not read merge queue membership")
            queue = response["data"]["repository"]["mergeQueue"]
            if queue is None:
                return {}
            page = queue["entries"]
            entries.extend(page["nodes"])
            if not page["pageInfo"]["hasNextPage"]:
                break
            after = page["pageInfo"]["endCursor"]
        prefix, groups = {}, {}
        for entry in sorted(entries, key=lambda entry: entry["position"]):
            pull = entry["pullRequest"]
            prefix[pull["number"]] = pull["headRefOid"]
            if entry["headCommit"] is not None:
                head = entry["headCommit"]["oid"]
                groups.setdefault(head, {}).update(prefix)
        return groups

    def publish(self, head, result):
        # Use the SHA evaluated, never a branch name that could have advanced.
        # The Actions job's own check belongs to its default-branch checkout;
        # this explicit status is what branch protection requires on the PR.
        desired = {
            "context": CONTEXT, "state": result.state,
            "description": result.reason[:140],
            "target_url": f"https://github.com/{self.repository}/actions/workflows/codex-review.yml",
        }
        self.publish_status(head, desired)

    def publish_status(self, head, desired):
        # GitHub limits the number of statuses per commit and context. An
        # unrelated PR's event must not consume another entry for an unchanged
        # verdict. The API returns statuses newest first; stop at this context.
        current = next((status for status in self.pages(f"commits/{head}/statuses")
                        if status["context"].casefold() == desired["context"].casefold()), {})
        if (current.get("creator", {}).get("login") == "github-actions[bot]"
                and all(current.get(key) == value
                        for key, value in desired.items())):
            return
        self.request(f"statuses/{head}", desired)


def reconcile(github, publish=False, requested_group=None):
    """Recompute every open PR, because serialized event runs can be coalesced.

    GitHub may replace a pending concurrency-group run with a newer one. Since
    every run reads all open PRs, the retained run also covers the discarded
    event. Deletion tombstones are recorded separately before coalescing, since
    the comments API alone cannot recover a deleted summary's existence.
    """
    pulls = github.pulls()
    deleted = github.deleted_summaries()
    queues = github.queue_groups()
    comments = {}
    results = {}
    read_errors = []
    for pull in pulls:
        number = pull["number"]
        try:
            comments[number] = github.comments(number)
            results[number] = review_result(
                pull["head"]["sha"], comments[number], deleted.get(number, 0))
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
        if deleted != github.deleted_summaries() or queues != github.queue_groups():
            raise RuntimeError("Deletion records or merge queue changed during evaluation")
        for number, original in comments.items():
            # PR metadata does not change when Codex edits its summary. Include
            # that evidence in the final read, rather than revalidating only the
            # commit graph and accidentally accepting a superseded verdict.
            if summary_snapshot(original) != summary_snapshot(github.comments(number)):
                results[number] = Result("pending", "Codex summary changed; recheck required")
    except (RuntimeError, ValueError, OSError) as error:
        results = {pull["number"]: Result("pending", "PR snapshot changed or is unavailable")
                   for pull in pulls}
        read_errors.append(str(error))
    pr_verdicts = combine_results(pulls, results)
    combined = dict(pr_verdicts)
    by_number = {pull["number"]: pull for pull in pulls}
    for head, members in queues.items():
        queue_results = []
        for number, expected_head in members.items():
            pull = by_number.get(number)
            if pull is None or pull["head"]["sha"] != expected_head:
                queue_results.append(Result("pending", "Merge queue PR head changed"))
            else:
                queue_results.append(pr_verdicts[expected_head])
        # Use shared-head verdicts so queueing one PR cannot bypass a blocked
        # duplicate. An empty or unknown queue membership never passes.
        blockers = [r for r in queue_results if r.state != "success"]
        if not queue_results:
            combined[head] = Result("pending", "Unknown merge queue membership")
        elif blockers:
            combined[head] = next((r for r in blockers if r.state == "failure"),
                                  blockers[0])
        else:
            combined[head] = Result("success", "Clean Codex reviews for the merge queue group")
    if requested_group and requested_group not in queues:
        combined[requested_group] = Result("pending", "Merge queue membership is not available; recheck")
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
    effects = parser.add_mutually_exclusive_group()
    effects.add_argument("--publish", action="store_true")
    effects.add_argument("--record-deletion", action="store_true")
    args = parser.parse_args()
    token = os.environ.get("GH_TOKEN")
    if not args.repository or not token:
        parser.error("Supply --repository and GH_TOKEN (read-only is enough without --publish)")
    github = GitHub(args.repository, token)
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    with open(event_path, encoding="utf-8") if event_path else io.StringIO("{}") as source:
        event = json.load(source)
    if args.record_deletion:
        github.record_deletion(event)
    else:
        group = (event.get("merge_group") or {}).get("head_sha")
        reconcile(github, args.publish, group)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError) as error:
        sys.exit(str(error))
