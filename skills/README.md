<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Agent skills for Anneal

This directory contains the agent skills used when working on `joshlf/anneal`
or proving verification obligations with Anneal. See [`../AGENTS.md`](../AGENTS.md)
for standing repository rules and [`../docs/agent-harness-setup.md`](../docs/agent-harness-setup.md)
for configuring Claude Code, Gemini CLI, Antigravity, and Codex to load these skills.

## Provenance

Vendor only documents used to run a skill, including the references its
instructions load. For imported skills, the table records the original upstream
paths and revisions. Repository-owned skills are labeled in the Source column.
These historical identifiers do not imply that the corresponding commits are
available in the public distribution. Public releases select package versions
independently; a matching skill name does not establish byte correspondence.
The matching-public-bytes links identify only packages whose complete local
path/byte/mode inventory matches that public release. Other rows retain only
their historical import identifiers. Preserve local changes when updating.

`research-wheel` supports multi-wave inquiry and can run on its own.
`architectural-design` uses it for research that needs several adaptive rounds.
The [Anneal reference corpus guidance][reference-corpus] applies when working
with the separately distributed corpus.

[reference-corpus]: ../AGENTS.md#technical-reference-corpus

| Skill | Source | Upstream path & revision |
| :--- | :--- | :--- |
| [`anneal-prove`](anneal-prove/SKILL.md) | Repository-owned | Interactive and symbolic Lean 4 proof construction (`wpMirSym`, `runCfgSteps`, `SymReflect`, and kernel proof-scaling patterns) |
| [`anneal-lsp`](anneal-lsp/SKILL.md) | Repository-owned | Warm `lake serve` LSP MCP workflow (`lean_goal`, `lean_multi_attempt`, `anneal_audit_preview`) and two-regime threshold heuristic |
| [`anneal-doc-audit`](anneal-doc-audit/SKILL.md) | Repository-owned | CLI command, tutorial directive, and report output verification across `docs/` and `examples/` |
| [`architectural-design`](architectural-design/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`architectural-design/` at `fcd5ac02ddc0ad1002db890a7b94c355bb73226b`](https://github.com/joshlf/skills/tree/fcd5ac02ddc0ad1002db890a7b94c355bb73226b/architectural-design) |
| [`authorship-disclosure`](authorship-disclosure/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`authorship_disclosure/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/authorship_disclosure) |
| [`clear-writing`](clear-writing/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`clear-writing/` at `12c20182ac57213eebb3f6ade950911e7b563c2a`](https://github.com/joshlf/skills/tree/12c20182ac57213eebb3f6ade950911e7b563c2a/clear-writing) (see below) |
| [`comment-guidelines`](comment-guidelines/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `comment_guidelines/` at `b563468a8148df117283494915cee5b6561cc47f` (historical pin) |
| [`commit-message`](commit-message/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`commit-message/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/commit-message) |
| [`model-refinement`](model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`model-refinement/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/model-refinement) |
| [`reader-oriented-explanation`](reader-oriented-explanation/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`reader-oriented-explanation/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/reader-oriented-explanation) |
| [`research-wheel`](research-wheel/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`research-wheel/` at `95420245403de7d840c8469e2bb4dc747e4ab6cd`](https://github.com/joshlf/skills/tree/95420245403de7d840c8469e2bb4dc747e4ab6cd/research-wheel) |
| [`robust-code`](robust-code/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`robust-code/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/robust-code) (see below) |
| [`skill-authorship`](skill-authorship/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`skill-authorship/` at `6a63da89d7240b1083e56991ab3718fbe7862ae7`](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/skill-authorship) |
| [`swarm-model-refinement`](swarm-model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | [`swarm-model-refinement/` at `f0afc6cb1203fff09089112f31cc481df7f1de75`](https://github.com/joshlf/skills/tree/f0afc6cb1203fff09089112f31cc481df7f1de75/swarm-model-refinement) (see below) |
| [`tech-lead`](tech-lead/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `tech-lead/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d` (historical pin) (see below) |
| [`change-review`](change-review/SKILL.md) | Repository-owned | Local and hosted review workflow, risk sizing, pipelining, and receipts ([maintainer contract](../docs/review-policy-design.md)) |
| [`source-control`](source-control/SKILL.md) | Repository-owned | Adapted from [`google/zerocopy`'s Contributing Guide](https://github.com/google/zerocopy/discussions/1318); commits, worker quarantine, publication, and stacks |
| [`trust-review`](trust-review/SKILL.md) | Repository-owned | Derived from [`META_PRINCIPLES.md`](../META_PRINCIPLES.md), [`PRINCIPLES.md`](../PRINCIPLES.md), [`THREAT_MODEL.md`](../THREAT_MODEL.md), and [`docs/trust-model.md`](../docs/trust-model.md) |

The current public export omits `comment-guidelines` and `tech-lead` and no
longer resolves their recorded upstream revisions.

## Local modifications

Most vendored documents match their historical upstream import. Runtime-only
vendoring also omits `authorship_disclosure/MAINTAINER.md` from its original
import; the current `authorship-disclosure/` runtime matches the linked public
release. The following packages carry additional intentional local changes:

- The reference documents in `robust-code/` and `tech-lead/` carry the
  repository copyright and license header. Their upstream bodies remain
  unchanged.

- **`skills/clear-writing/`:** Links to the pinned upstream
  `references/SOURCES.md` bibliography.

- **`skills/swarm-model-refinement/`:** Omits the executable upstream
  `scripts/holdout-seal.py` helper. Cooperative same-UID `sealed-file` mode
  requires a separately supplied host helper. The skill uses
  `private-subagent` only if the host can resume a private worker, and records
  holdout mode `none` if neither mode is available. Discovery-only runs return
  to the caller after Phase 1. T3 handles repairable checks and bounded retries
  before T1 can stop the run.

- **`skills/robust-code/`:**
  - **Omitted file:** `references/agent-scaffolding.md`. (This reference file
    focuses on external agent evaluation harness design, multi-arm benchmarking
    methodology, and prompt contract templates. Anneal manages its agent
    workflows and evaluation harnesses through repository-owned files in
    `AGENTS.md` and dedicated supervisor skills, so this reference is not
    needed in-tree. The core scaffolding honesty and boundary principles
    remain in `SKILL.md`.)
  - **`SKILL.md` patch:** Removed the sentence referencing
    `agent-scaffolding.md` to prevent dead links.

Except for documented local modifications, keep vendored `joshlf/skills`
packages unmodified so they can be updated cleanly from upstream; place
Anneal-specific conventions in repository-owned files (`AGENTS.md`,
`skills/anneal-prove/`, `skills/anneal-lsp/`, `skills/anneal-doc-audit/`,
`skills/change-review/`, `skills/source-control/`, and `skills/trust-review/`).
