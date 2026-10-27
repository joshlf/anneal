# Agent instructions for Anneal

Read this file before changing the repository. It is the entry point for agent
and contributor work throughout this tree; read any more specific instructions
in the directory you change as well.

## Understand the architecture and trust boundary

Anneal verifies Rust programs (including unsafe code) by extracting typed
`Runtime(PostCleanup)` MIR and compiler facts via a thin `rustc` capture wrapper
and checking the crate's `Trusted.CrateTheorem` (`VerificationResult` over every
captured function's `Compiler.Verified` obligations) inside the Lean 4 kernel.

Start with [README.md](README.md) for the repository map and links to the
architecture issues ([#1](https://github.com/joshlf/anneal/issues/1),
[#100](https://github.com/joshlf/anneal/issues/100),
[#99](https://github.com/joshlf/anneal/issues/99),
[#103](https://github.com/joshlf/anneal/issues/103),
[#88](https://github.com/joshlf/anneal/issues/88),
[#101](https://github.com/joshlf/anneal/issues/101),
[#102](https://github.com/joshlf/anneal/issues/102), and
[#109](https://github.com/joshlf/anneal/issues/109)).

Before placing or modifying code, check whether it belongs inside
[`trusted/`](trusted/README.md) or outside it (`theory/`, `examples/`,
`tests/`):

- Only primitive semantic and theorem definitions required to state or gate
  `Trusted.CrateTheorem` and `VerificationResult` (`trusted/lean/`) and
  effectful components—the `.olean` kernel-environment inspector
  (`trusted/audit/`), the CLI orchestrator and boundary/manifest audit runner
  (`trusted/cargo-anneal/`), and the `rustc` MIR/attribute serializer
  (`trusted/rustc-capture/`)—belong in `trusted/`.
- All code outside `trusted/` (`theory/`, `examples/`, `tests/`) must be pure,
  effect-free Lean definitions and proofs checked by the Lean kernel: derived
  definitions, composition theorems (`verify_through_passes`), program
  transformations (`VerifierPass`, `ExactPass`), certificate checkers
  (`VerifiedChecker`), program logics (`WP`), and proof terms.

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
