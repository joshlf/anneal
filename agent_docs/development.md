# Development guide

Read [`README.md`](../README.md) and [`trusted/README.md`](../trusted/README.md)
before adding or modifying code. Anneal separates the human-audited trusted
computing base (`trusted/`) from untrusted proof libraries (`theory/`),
untrusted CLI orchestration (`crates/`), worked examples (`examples/`), and test
suites (`tests/`).

## Keep `trusted/` minimal and self-contained

Before placing a definition in `trusted/`, apply the failure-mode test in
[`trusted/README.md`](../trusted/README.md):

- If a bug in the code would simply cause a proof in `theory/` or `Proof/<Item>.lean`
  to fail kernel typechecking (or fail `trusted/audit/`), the code belongs
  **outside** `trusted/` (in `theory/` or `crates/`).
- Only primitive semantic and theorem definitions required to state
  `VerificationResult` (`trusted/lean/`), the `.olean` environment and manifest
  auditor (`trusted/audit/`), and the mechanical `rustc_driver` capture
  serializer (`trusted/rustc-capture/`) belong inside `trusted/`.

Never add a helper to `theory/` that is referenced in the **type (statement)**
of `VerificationResult` or `Mir.<Item>.claim`: `trusted/audit/` enforces that
theorem statements (`ci.type`) depend only on `trusted/lean/`, the pinned
foundation lock, and read-only item data, while `theory/` (`Anneal.*`) may be
referenced only inside proof terms (`ci.value?`).

## Preserve the meaning of claims

When working on semantics, transformations, or specifications, identify the
admitted programs and states, outcomes, observations (`π_c`, `π_v`), choice
quantifiers (`Choice.demonic` vs. `Choice.angelic`), assumptions (`TCBEntry`),
and direction of refinement (`GuardedRefines` in
[#100](https://github.com/joshlf/anneal/issues/100)).

Keep structural admission (`WellFormedCapture`), all-prefix UB freedom
(`MirNoUB`, `BinNoUB`), progress (`TotalStep`, `InhabitedDemonic`), termination,
resource bounds, and constant-time leakage distinct. Do not hide an unsupported
construct or bad execution prefix by narrowing a safe function's baseline domain
or turning UB into divergence.

## Validate the change

Choose checks that test the behavior or claim affected, and report their scope
and actual results:

- For documentation changes, verify relative links, file paths, and that prose
  claims match the architecture and evidence. The tutor chapters quote only
  commands, reports, errors, and files produced by
  [`docs/tutor/workflow/tutor.toml`](../docs/tutor/workflow/README.md); after
  changing `cargo-anneal` or the tutorial, run
  `python3 docs/tutor/workflow/tutor_workflow.py render` and review the diff
  rather than editing generated blocks by hand.
- For Lean and boundary changes, run the `trusted/audit/` containment,
  statement-origin, axiom, and kernel-replay gates, along with positive and
  negative control fixtures in `tests/`. A syntax error in a negative test does
  not demonstrate semantic rejection.

## Maintain the GHerrit stack

Use [GHerrit](https://github.com/joshlf/gherrit) for this repository's stacked PR
workflow. Inspect the current stack and branch-management state before changing
history. In a new checkout or worktree, ensure hooks are installed (`gherrit install`)
and use a managed working branch (`gherrit manage --private` configures a stack
whose local branch name is not published).

Each commit's `gherrit-pr-id` trailer identifies its PR across rebases and
amendments. Preserve the IDs of existing commits. Give a new logical change its
own commit and let the `commit-msg` hook create its ID. Keep the authorship
disclosure trailer (`Agent-authored-by: AI agent acting on joshlf's behalf`)
required by [the writing policy](writing.md) in the trailer block.

When publication is authorized, `git push` synchronizes the managed stack.
GHerrit creates or updates one PR per commit, chains each PR to its predecessor,
and regenerates PR descriptions from commit messages. After pushing, inspect the
resulting PR description to ensure the required prose authorship disclosure
(`*Authored by an AI agent acting on joshlf's behalf.*`) is present at the top
of the PR body while preserving GHerrit's metadata comments.
