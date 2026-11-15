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

## Historical maintainer imports

Vendor only documents used to run a skill, including the references its
instructions load. The table records the historical maintainer imports and their original paths
and revisions. These identifiers do not imply that the corresponding commits
are available in the public distribution. Public releases select package versions
independently; a matching skill name does not establish byte correspondence.
The matching-public-bytes links identify only packages whose complete local
path/byte/mode inventory matches that public release. Other rows retain only
their historical import identifiers. Preserve local changes when updating.

| Skill | Source | Upstream path & revision |
| :--- | :--- | :--- |
| [`anneal-prove`](anneal-prove/SKILL.md) | Repository-owned | Interactive and symbolic Lean 4 proof construction (`wpMirSym`, `runCfgSteps`, `SymReflect`, and kernel proof-scaling patterns) |
| [`anneal-lsp`](anneal-lsp/SKILL.md) | Repository-owned | Warm `lake serve` LSP MCP workflow (`lean_goal`, `lean_multi_attempt`, `anneal_audit_preview`) and two-regime threshold heuristic |
| [`anneal-doc-audit`](anneal-doc-audit/SKILL.md) | Repository-owned | CLI command, tutorial directive, and report output verification across `docs/` and `examples/` |
| [`adversarial-rounds`](adversarial-rounds/SKILL.md) | Repository-owned | $N$-round adversarial implementation, critique, and repair between two randomly assigned frontier models (`Model X` and `Model Y`) over shared git worktree(s) |
| [`hierarchical-supervision`](hierarchical-supervision/SKILL.md) | Repository-owned | Quota- and hardware-aware multi-tier supervisor + leaf orchestration (`<SUPERVISOR_MODEL>`, `P0`/`P1`/`P2` reserve floors, handoff-only model switching, and `anneal-lean-run` resource bounds) |
| [`authorship-disclosure`](authorship-disclosure/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `authorship_disclosure/` at `b563468a8148df117283494915cee5b6561cc47f`  ([matching public bytes](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/authorship_disclosure)) |
| [`comment-guidelines`](comment-guidelines/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `comment_guidelines/` at `b563468a8148df117283494915cee5b6561cc47f` |
| [`commit-message`](commit-message/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `commit-message/` at `b563468a8148df117283494915cee5b6561cc47f` |
| [`model-refinement`](model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `model-refinement/` at `0073be02ea65150ad56ded426261245ec1a22848`  ([matching public bytes](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/model-refinement)) |
| [`reader-oriented-explanation`](reader-oriented-explanation/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `reader-oriented-explanation/` at `b563468a8148df117283494915cee5b6561cc47f`  ([matching public bytes](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/reader-oriented-explanation)) |
| [`robust-code`](robust-code/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `robust-code/` at `468f74547999ad6879905c91398b1a218b010791` (patched; see below) |
| [`skill-authorship`](skill-authorship/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `skill-authorship/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d`  ([matching public bytes](https://github.com/joshlf/skills/tree/6a63da89d7240b1083e56991ab3718fbe7862ae7/skill-authorship)) |
| [`swarm-model-refinement`](swarm-model-refinement/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `swarm-model-refinement/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d` |
| [`tech-lead`](tech-lead/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `tech-lead/` at `3bf3f345b2916f8417306ba197f779b0b4429c1d` |
| [`williams-style`](williams-style/SKILL.md) | [`joshlf/skills`](https://github.com/joshlf/skills) | `williams-style/` at `b563468a8148df117283494915cee5b6561cc47f` |
| [`architectural-design`](architectural-design/SKILL.md) | Repository-owned | End-to-end architectural design workflow for `joshlf/anneal` |
| [`source-control`](source-control/SKILL.md) | Repository-owned | Adapted from [`google/zerocopy`'s Contributing Guide](https://github.com/google/zerocopy/discussions/1318) |
| [`trust-review`](trust-review/SKILL.md) | Repository-owned | Derived from [`PRINCIPLES.md`](../PRINCIPLES.md) and [`docs/trust-model.md`](../docs/trust-model.md) |

## Local modifications

Most vendored documents match their historical upstream import. Runtime-only
vendoring also omits `authorship_disclosure/MAINTAINER.md` from its original
import; the current `authorship-disclosure/` runtime matches the linked public
release. The following packages carry additional intentional local changes:

- The reference documents in `robust-code/` and `tech-lead/` carry the
  repository copyright and license header. Their upstream bodies remain
  unchanged.

- **`skills/williams-style/`:** The copy omits the upstream
  `references/SOURCES.md` document and removes its optional link from
  `SKILL.md`.

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
`skills/adversarial-rounds/`, `skills/hierarchical-supervision/`,
`skills/anneal-prove/`, `skills/anneal-lsp/`, `skills/anneal-doc-audit/`,
`skills/architectural-design/`, `skills/source-control/`, and
`skills/trust-review/`).

*Updated by an AI agent acting on joshlf's behalf.*
