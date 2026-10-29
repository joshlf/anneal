# Writing policy

Write for a technically competent reader who did not participate in the work
session. Explain the supported result, the relationship that makes it useful,
and the conditions that limit it. Preserve uncertainty and independent
obligations when improving the prose.

## Required skills and sources

These skills come from `joshlf/skills` at revision
`e25301fa37318796355a7254a7d84b1c0f87bdaa`. The package paths below are the
upstream directory names; two differ from the names in their skill metadata.

| Package | Apply it to | Full instructions |
| --- | --- | --- |
| `reader-oriented-explanation` | Content in all documentation, code comments, and commit messages | [SKILL.md](https://github.com/joshlf/skills/blob/e25301fa37318796355a7254a7d84b1c0f87bdaa/reader-oriented-explanation/SKILL.md) |
| `williams-style` | Style in all documentation, code comments, and commit messages | [SKILL.md](https://github.com/joshlf/skills/blob/e25301fa37318796355a7254a7d84b1c0f87bdaa/williams-style/SKILL.md) |
| `comment_guidelines` | Explanatory implementation comments and caller-facing documentation comments | [SKILL.md](https://github.com/joshlf/skills/blob/e25301fa37318796355a7254a7d84b1c0f87bdaa/comment_guidelines/SKILL.md) |
| `authorship_disclosure` | Git commit authorship and disclosure; separately published prose such as PR descriptions | [SKILL.md](https://github.com/joshlf/skills/blob/e25301fa37318796355a7254a7d84b1c0f87bdaa/authorship_disclosure/SKILL.md) |

Use the host's supported skill-loading mechanism when the package is available.
Otherwise, obtain and read the linked instructions and any runtime references
they require at the pinned revision. Do not infer missing instructions from a
skill's name. Keep changes to the selected skill revision explicit so reviewers
can inspect a change in writing policy.

## Documentation and comments

Keep an explanation's claims within its evidence. Distinguish a checked theorem
from an observed execution, an audited source correspondence, an assumed
contract, and an open obligation. State the subject and scope needed to
interpret the result. A successful Lean check establishes the stated
proposition; it does not by itself establish that the proposition adequately
describes Rust.

For implementation comments, explain a non-obvious reason, invariant, or
assumption that the surrounding code does not supply. For caller-facing
comments, document the contract callers need without requiring them to inspect
the implementation. Apply the comment skill's sentence, paragraph, and 80-column
wrapping rules, including its exceptions. Avoid copying mutable implementation
details into prose that would become a second source of truth.

Comments for code in [`trusted/`](../trusted/README.md) that claims to model
Rust or serialize `rustc` internals must also follow
[the Rust correspondence comment policy](trusted-rust.md), including its
requirements for verbatim quotations and versioned citations.

## Commits and publication

Describe the final change relative to its parent. Give the history reader enough
context to understand why it exists, and keep validation claims tied to checks
actually performed on that change.

Use the user's established Git identity and select the disclosure trailer from
the authorship skill's content/message table. Recompute that disclosure when
amending or combining contributions, and preserve other contributors'
attribution. The commit's files and message form one disclosure unit; the skill
does not call for a repeated notice in each committed file.

PR descriptions are separately presented prose and follow the skill's prose
disclosure rule. GHerrit regenerates descriptions on synchronization. Inspect
the published description to ensure the required visible notice survives; a Git
trailer alone does not replace that prose notice. Preserve GHerrit's stack
metadata when repairing a disclosure.
