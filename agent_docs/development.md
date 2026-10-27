# Development guide

Read [`README.md`](../README.md) and [`trusted/README.md`](../trusted/README.md)
before adding or modifying code. Anneal separates the human-audited trusted
computing base (`trusted/`, which contains all primitive semantic definitions
and all effectful code) from pure, effect-free Lean proof libraries (`theory/`),
worked examples (`examples/`), and test suites (`tests/`).

## Keep `trusted/` minimal and self-contained

Before placing code in `trusted/` or `theory/`, apply the two boundary rules in
[`trusted/README.md`](../trusted/README.md):

- **Pure, derived Lean definitions and proofs belong in `theory/`:** If a bug in
  a pure Lean definition or proof would simply cause a proof in `theory/` or
  `Proof.lean` to fail kernel typechecking (or fail `trusted/audit/`), the code
  belongs **outside** `trusted/` (in `theory/`, `examples/`, or `tests/`).
- **Primitive semantic commitments and all effectful code belong in `trusted/`:**
  Only primitive Lean definitions required to state `Trusted.CrateTheorem` and
  `VerificationResult` (`trusted/lean/`), the `.olean` kernel-environment
  inspector (`trusted/audit/`), the CLI orchestrator and boundary/manifest audit
  runner (`trusted/cargo-anneal/`), and the mechanical `rustc` capture
  serializer (`trusted/rustc-capture/`) belong inside `trusted/`. No Rust crates
  or effectful Lean code may exist outside `trusted/`.

Never add a helper to `theory/` that is referenced in the **type (statement)**
of `Trusted.CrateTheorem` or `Mir.crate`: `trusted/cargo-anneal` and
`trusted/audit/TrustedBoundary.lean` enforce that theorem statements (`ci.type`)
depend only on `trusted/lean/`, the pinned foundation lock, and read-only item
data (`Mir.lean`), while `theory/` (`Anneal.*`) may be referenced only inside
proof terms (`ci.value?`).

## Preserve the meaning of claims

When working on semantics, transformations, or specifications, identify the
admitted programs and states, outcomes, observations (`π_c`, `π_v`), choice
quantifiers (`ChoiceKind.demonic` vs. `ChoiceKind.angelic`), assumptions
(`TCBItem`), and direction of refinement (`≤`, `Partial`, `Compiles`, and
`Abstracts` in [#100](https://github.com/joshlf/anneal/issues/100)).

Keep structural admission, all-prefix well-formedness (`Language.WellFormed` and
`Language.WellFormedOn`), progress (`TotalStep`, `InhabitedDemonic`),
termination, resource bounds, and constant-time leakage distinct. Do not hide an
unsupported construct or bad execution prefix by narrowing a safe function's
baseline `.defined` domain or turning UB into divergence.

## Validate the change

Choose checks that test the behavior or claim affected, and report their scope
and actual results:

- For documentation changes, verify relative links, file paths, and that prose
  claims match the architecture and evidence.
- For Lean, Rust, and boundary changes, run
  `cargo run --locked -p cargo-anneal -- audit-repo`,
  `cargo run --locked -p cargo-anneal -- audit-self-test`, and
  `cargo test --workspace --locked`. A syntax error in a negative test does not
  demonstrate semantic rejection.

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
