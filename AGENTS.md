# Agent instructions for Anneal

Read this file before changing the repository. It is the entry point for agent
and contributor work throughout this tree; read any more specific instructions
in the directory you change as well.

## Understand the architecture and trust boundary
## Project principles

Before designing, modifying, or reviewing repository artifacts, read and
preserve [`PRINCIPLES.md`](PRINCIPLES.md), which defines Anneal's mission,
correctness promise, and decision-making principles.

## Standing rules

Apply these rules to all work in this repository:

- **File headers:** New source, script, workflow, and documentation files must
  begin with the repository's Fuchsia copyright and license header (matching
  [`PRINCIPLES.md`](PRINCIPLES.md) or [`ci/check_todo.sh`](ci/check_todo.sh)
  in the appropriate comment syntax for the file type) using the file's
  creation year. Preserve the original creation year when modifying an existing
  file. Files whose syntax requires leading metadata or forbids comments (such
  as JSON files or `SKILL.md` files with leading YAML frontmatter) are exempt.
<!-- TODO-check-disable -->
- **`TODO` markers:** Do not leave `TODO` markers in code, documentation, or
  commit messages unless you intend to block merging;
  [`./ci/check_todo.sh`](ci/check_todo.sh) rejects `TODO` across the working
  tree and all commits in `origin/main..HEAD`. Use `FIXME` for non-blocking
  follow-up work. Any temporary or exempted `TODO` must cite an issue using
  `TODO(#123):`.
<!-- TODO-check-enable -->
- **Prose and comment wrapping:** Wrap prose in code comments and Markdown
  files at 80 columns from the left margin when practical, including any
  comment prefix (`//`, `///`, `//!`, `--`, `/--`, `/-!`). Do not wrap Markdown
  tables, ASCII diagrams, long URLs, code blocks, or trailing inline comments
  when wrapping would impair readability. Indent wrapped bullet continuation
  lines by two spaces, and put a blank line between paragraphs and after section
  headings.
- **Pre-commit validation:** Run `./ci/check_todo.sh` (along with any build or
  test checks applicable to the changed files) before finishing a task or
  committing.

## Required skills

The [`skills/`](skills/README.md) directory contains the skills that govern work
in this repository. Whenever your task involves an activity in the table below,
open and read the full `SKILL.md` for every listed skill (plus any
`references/` files it routes you to) before performing that work. Do not infer
a skill's rules from its name or summary. Skills compose: when more than one
applies, follow all of them.

| Activity | Required skills |
| :--- | :--- |
| Writing, revising, or reviewing any technical prose (documentation, code comments, commit messages, PR descriptions, or issue bodies) | [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Adding, revising, or reviewing explanatory inline (`//`, `--`) or documentation (`///`, `//!`, `/--`, `/-!`) code comments | [`comment-guidelines`](skills/comment-guidelines/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Structuring commits, drafting or revising commit messages, rebasing or amending commits, or managing GHerrit branches and stacks | [`source-control`](skills/source-control/SKILL.md), [`commit-message`](skills/commit-message/SKILL.md), [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |
| Preparing or updating Git commits, pull request descriptions, or other externally visible prose | [`authorship-disclosure`](skills/authorship-disclosure/SKILL.md) |
| Designing, simplifying, or generalizing conceptual models, semantic interfaces, schemas, protocols, or instructions | [`model-refinement`](skills/model-refinement/SKILL.md) |
| Coordinating multi-agent conceptual model refinement across theories, software designs, schemas, protocols, or instructions | [`swarm-model-refinement`](skills/swarm-model-refinement/SKILL.md), [`model-refinement`](skills/model-refinement/SKILL.md) |
| Running $N$-round adversarial implementation, critique, and repair between two frontier models in shared git worktree(s) | [`adversarial-rounds`](skills/adversarial-rounds/SKILL.md) |
| Orchestrating multi-tier supervisor and leaf agent workflows across worktrees with quota-aware model pools and hardware-matched `lake`/`lean` bounds | [`hierarchical-supervision`](skills/hierarchical-supervision/SKILL.md), [`adversarial-rounds`](skills/adversarial-rounds/SKILL.md) |
| Leading or directing ambiguous engineering efforts, recovering requirements, developing or evaluating architecture, or recovering technical understanding after context loss | [`tech-lead`](skills/tech-lead/SKILL.md), [`reader-oriented-explanation`](skills/reader-oriented-explanation/SKILL.md), [`williams-style`](skills/williams-style/SKILL.md) |

## Architecture and trust boundary

Anneal verifies Rust programs (including unsafe code) by extracting typed
`Runtime(PostCleanup)` MIR and compiler facts via a thin `rustc_driver` wrapper
and checking per-item `VerificationResult` theorems inside the Lean 4 kernel.

Start with [`PRINCIPLES.md`](PRINCIPLES.md), [`DESIGN.md`](DESIGN.md), and
[README.md](README.md) for the normative project principles, design contract,
repository map, and links to the
architecture issues ([#1](https://github.com/joshlf/anneal/issues/1),
[#100](https://github.com/joshlf/anneal/issues/100),
[#99](https://github.com/joshlf/anneal/issues/99),
[#103](https://github.com/joshlf/anneal/issues/103),
[#88](https://github.com/joshlf/anneal/issues/88),
[#101](https://github.com/joshlf/anneal/issues/101), and
[#102](https://github.com/joshlf/anneal/issues/102)).

Before placing or modifying code, check whether it belongs inside
[`trusted/`](trusted/README.md) or outside it (`theory/`, `crates/`,
`examples/`, `tests/`):

- Only definitions required to state or gate `VerificationResult` (`trusted/lean/`),
  inspect compiled `.olean` environments and manifests (`trusted/audit/`), or
  serialize `rustc` MIR and attributes (`trusted/rustc-capture/`) belong in
  `trusted/`.
- All derived definitions, program transformations (`VerifierPass`, `ExactPass`),
  certificate checkers (`VerifiedChecker`), program logics (`WP`), tactics, and
  CLI orchestration belong outside `trusted/`.

## Required writing skills

Use the skills from `joshlf/skills` identified in
[the writing policy](agent_docs/writing.md). Read their full instructions before
writing or revising the corresponding material:

- All documentation, explanatory code comments, and commit messages must use
  `reader-oriented-explanation` for content and `williams-style` for style.
- Code comments must additionally use `comment_guidelines`.
- Git commits and separately published prose must additionally use
  `authorship_disclosure`.

The writing policy links to pinned sources and explains how these requirements
apply to commits and PR descriptions. A summary of a skill is not a substitute
for reading it.

## Rust correspondence in `trusted/`

Any code in [`trusted/`](trusted/README.md) that claims to model Rust semantics
or extract `rustc` compiler structures must follow
[the Rust correspondence comment policy](agent_docs/trusted-rust.md). Its
comments must explain the correspondence and both quote and cite the applicable
Rust documentation or compiler source at a pinned version.

## Development and validation

Read [the development guide](agent_docs/development.md) before making changes.
It explains how to preserve claim meanings, enforce the `trusted/` containment
boundary, run validation checks, and maintain the GHerrit stack.

## Agentic proof construction workflow

When discharging per-item Lean 4 proof obligations for a Rust crate with
`cargo anneal`, follow [the agent proof construction workflow](docs/agent-proof-workflow.md),
[the agent harness setup guide](docs/agent-harness-setup.md), and
[the project owner guide](docs/project-owner-guide.md), and load the
[`anneal-prove` skill](skills/anneal-prove/SKILL.md) and
[`anneal-lsp` skill](skills/anneal-lsp/SKILL.md). In locked
verification sessions (`cargo anneal lock-specs` followed by
`cargo anneal agent-verify`), only `anneal/proofs/Proof/<Crate>/<Item>.lean` is
writable; specification overrides (`anneal/proofs/Specs/**`), assumption modules
(`anneal/proofs/Assumptions/**`), and generated assembly (`.anneal/**`) are
locked and audited.

## Commenting in `trusted/`

Because auditing `trusted/` alone must suffice to verify that Anneal upholds
[`PRINCIPLES.md`](PRINCIPLES.md), all code in `trusted/` will undergo careful
human review. Human understanding is therefore paramount in `trusted/`: comment
liberally using `comment-guidelines` (and its companion writing skills) so a
human auditor can verify the design rationale, invariants, assumptions, contracts,
and subtle semantic or implementation choices without reconstructing unstated context.
Include Lean comment markers (`--`, `/--`, `/-!`) alongside Rust comment markers
(`//`, `///`, `//!`).
