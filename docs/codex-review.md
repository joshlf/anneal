<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Require a clean Codex Code Review

The [review gate](../.github/workflows/codex-review.yml) translates the managed
Codex reviewer's summary into a commit status named **Codex review**. It passes
only when the latest authentic summary says Code Review completed for the full
current head SHA and both findings flags are explicitly `false`.

This means no *reported* findings. It does not certify that the code has no
bugs.
Security Review, human approval, conversation resolution, and build/test checks
remain separate requirements. A reaction, a prose receipt, or a manually
resolved thread cannot substitute for the structured clean verdict.

## Enable enforcement after merging the workflow

The workflow must exist on `main` before comment events can run it. It always
checks out `main`, including when dispatched from another ref. Merge the
workflow before enabling the requirement, so the introducing PR does not wait
for an evaluator that has not been deployed.

1. In Codex's repository review settings, enable automatic Code Review for the
  intended PR authors and configure reviews after pushes. An initial review does
  not approve later commits. If an automatic review does not run, request one
  with `@codex review` on the PR.
2. Run the gate manually and inspect its results:

   ```sh
   gh workflow run codex-review.yml --repo joshlf/anneal --ref main
   gh run list --repo joshlf/anneal --workflow codex-review.yml
   ```

3. After confirming it publishes **Codex review** on open PR heads, create the
  dedicated ruleset once, from the repository checkout:

   ```sh
   gh api --method POST repos/joshlf/anneal/rulesets \
     --input .github/codex-review-ruleset.json
   ```

The [ruleset](../.github/codex-review-ruleset.json) requires this status from
the GitHub Actions app (integration ID `15368`), requires an up-to-date branch,
and has no bypass actors. It adds to existing protections; it does not replace
their CI checks or review requirements. Inspect existing rulesets before
applying it again; update the existing rule by ID rather than creating
duplicates.

Changing a file in Git does not change GitHub's live ruleset. Check the live
settings after edits to the status name, required source, or enforcement policy.
No additional secret is needed: the evaluator uses `GITHUB_TOKEN` with PR-read
and status-write permission.

## What the evaluator trusts

The adapter accepts summaries only from account ID `199175422`, with login
`chatgpt-codex-connector[bot]` and account type `Bot`. It requires the
`codex-pull-request-review-summary` marker and exactly one
`codex-review-state:v1` JSON payload. The newest summary by comment creation ID
supersedes older ones; editing an older comment does not make it newer.
Duplicate JSON keys, unknown versions, malformed state, and unknown findings
verdicts block merging.

Deletion events first record the deleted comment ID in a uniquely named status
on Anneal's initial commit, `8950b5afa6444859c21fb4d100e21dd283afb6d6`. These
small, independent records survive branch moves and concurrent deletions without
storing comment text or needing another credential. A summary at or below the
largest deleted ID for its PR cannot approve it. A new summary with a larger ID
can. If Codex keeps updating an older surviving summary, remove that obsolete
summary and request a new review so Codex creates a fresh summary comment.

The deletion-recording job has no concurrency group. Only evaluator jobs are
serialized and coalesced, after their own deletion record succeeds. Do not move
concurrency to workflow scope: dropping a pending deletion event could erase the
only evidence that an older success was superseded. If a recording job fails,
rerun that failed workflow run, which retains the deletion event payload; a new
manual dispatch alone cannot reconstruct deleted data. Deletions before this
workflow was deployed cannot be reconstructed either.

The hidden state format is observed integration behavior, not a documented
stable OpenAI API. If it changes, inspect the bot's raw comment and update the
adapter and tests deliberately. Do not recover by accepting a matching phrase
or emoji.
The verdict is bound to the head SHA; the format does not attest to a base SHA.
Request a fresh review after retargeting a PR or changing the comparison base.
The gate cannot independently prove that the reviewer used that new base.

Because GitHub statuses belong to commits, every open PR sharing a head SHA must
have its own clean summary before that SHA passes. This includes drafts and PRs
targeting stack branches. Closing a duplicate PR removes its contribution on the
next evaluation. The evaluator reads all open PRs on every retained run; pending
GitHub concurrency runs can be coalesced without losing another PR's event.

The workflow receives PR and comment events, merge-group events, `main` pushes,
and manual dispatch.
It executes only the adapter from `main`, never a PR checkout or comment text.
PR code runs in the separate read-only CI job that tests the adapter. No action
cache is restored, checkout credentials are not persisted, and status
credentials are supplied only to the recorder and evaluator commands.

For merge queues, the evaluator reads GitHub's main-branch queue entries and
requires the whole queue prefix through each generated head to have clean PR
reviews. It publishes **Codex review** on those generated SHAs as well as on PR
heads. Queue positions and generated heads come from the GraphQL API, not from
branch-name parsing or commit ancestry, which squash merges need not preserve.
This carries the member PR verdicts to the queue; it does not claim Codex
reviewed the generated composite commit. Build and boundary checks still test
that commit.
Unknown queue membership remains pending and requires a recheck. Queue behavior
is covered by simulated API tests; Anneal has no live merge queue configured for
an end-to-end deployment check.

## Diagnose a blocked PR

Inspect **Codex review**, not just the green check for the evaluator workflow:
the workflow can successfully publish a blocking or waiting verdict. The status
links to the evaluator's workflow page, whose logs explain each evaluated SHA.

- A pending result means the summary is absent, stale, incomplete, or the PR
  snapshot changed while it was read. Finish or request the matching review,
  then recheck.
- A failed result means findings remain, the verdict is inconclusive, the
  format is unsupported, or the comment API could not be read. Fix the reported
  cause and recheck. An API failure also fails the evaluator workflow.
- A shared-head result names a blocking PR. Inspect that PR even if the PR you
  are viewing has its own clean review.

For local diagnosis, the following command reads live data without publishing:

```sh
GH_TOKEN="$(gh auth token)" python3 -I -B ci/codex_review.py \
  --repository joshlf/anneal
```

Use manual workflow dispatch to publish a recheck. Do not run local `--publish`
alongside the serialized workflow: a second writer would defeat serialization,
and its personal-token statuses would not have the required Actions source.
Unchanged statuses are not republished, preserving GitHub's per-context limit.

The evaluator reads the summaries again and checks deletion records, queue
membership, PR membership, head, and base before publishing. It uses the SHA it
evaluated, never a mutable branch name. GitHub API reads and
status writes are not one transaction. New events take time to run; a full API
outage can prevent both reading and revoking a previous result. Manual rechecks
recover missed events. The gate does not defend against administrators changing
rules or trusted repository writers changing the workflow or forging statuses.

## Test locally

```sh
python3 -B -m unittest discover -s ci -p 'test_codex_review.py' -v
```

The tests use fake API data and cover authority, freshness, strict verdicts,
format changes, duplicate keys, shared commits, pagination, API failures,
concurrent summary/PR changes, durable deletion records, merge queues, and
status publication. They do not invoke Codex or change GitHub settings.

See [Codex review setup](https://learn.chatgpt.com/docs/third-party/github),
[GitHub commit statuses](https://docs.github.com/en/rest/commits/statuses),
[merge queue entries](https://docs.github.com/en/graphql/reference/pulls#mergequeueentry), and
[required-check troubleshooting](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks)
for the hosting mechanisms.
