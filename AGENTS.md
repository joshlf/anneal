# Agent instructions for Anneal

Read this file before changing the repository. It is the entry point for agent
and contributor work throughout this tree; read any more specific instructions
in the directory you change as well.

## Understand the architecture and trust boundary

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
`cargo anneal`, follow [the agent proof construction workflow](docs/agent-proof-workflow.md)
and load the [`anneal-prove` skill](skills/anneal-prove/SKILL.md). In locked
verification sessions (`cargo anneal lock-specs` followed by
`cargo anneal agent-verify`), only `anneal/proofs/Proof/<Crate>/<Item>.lean` is
writable; specification overrides (`anneal/proofs/Specs/**`), assumption modules
(`anneal/proofs/Assumptions/**`), and generated assembly (`.anneal/**`) are
locked and audited.
