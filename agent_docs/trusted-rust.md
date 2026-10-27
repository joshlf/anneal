<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Rust correspondence comments in `trusted/`

Every declaration in [`trusted/lean/`](../trusted/lean/README.md) that claims to
model Rust—and every extraction path in
[`trusted/rustc-capture/`](../trusted/rustc-capture/README.md) that translates
`rustc` data structures—must have an adjacent documentation comment explaining
and justifying that correspondence. A purely mathematical helper in
`trusted/lean/` needs this evidence when its comment or contract attributes a
property to Rust.

The policy adapts zerocopy's
[safety comment requirements](https://github.com/google/zerocopy/blob/476ba6ae092a7b7def5752df4dde5cf88948f0d6/zerocopy/POLICIES.md#safety-comments)
and its
[guidance on applicable premises](https://github.com/google/zerocopy/blob/476ba6ae092a7b7def5752df4dde5cf88948f0d6/skills/unsafe-rust/SKILL.md#use-only-applicable-premises).
The comment provides a reviewable argument that the formalization or extractor
expresses the documented Rust rule within its stated scope. Kernel checking
alone does not establish that correspondence.

## Required content

Each correspondence comment must:

1. State the Rust or `rustc` property being modeled and identify the
   corresponding parts of the declaration. Specify its preconditions and
   relevant scope, including the Rust release, edition, target, MIR phase,
   configuration, or type restrictions on which the claim depends.
2. Quote verbatim every Rust documentation passage (or `rustc` compiler comment
   / definition in `trusted/rustc-capture/`) the argument relies on. Include the
   smallest sufficient passages, retaining their qualifications and exceptions.
   A paraphrase, topic label, or link to a clause ledger or another comment does
   not replace the local quotations.
3. Cite each quotation with a link to the specific section or source lines in
   the stable Rust Reference, `core`, `alloc`, `std` documentation, or pinned
   `rustc` commit. Name the exact release or commit and use an immutable
   versioned URL. Floating `stable`, `latest`, `main`, and unversioned links are
   insufficient evidence.
4. Explain how the quoted premises and any cited mathematical lemmas justify
   the correspondence. Preserve the direction and strength of each guarantee;
   do not turn a necessary condition into a sufficient one or a permitted
   behavior into a required one.
5. Distinguish documented guarantees from our modeling choices, supplied
   compiler facts, and additional assumptions. State what remains unsupported
   or unproved. This documentation requirement does not authorize project
   axioms or relax the [`trusted/` boundary policy](../trusted/README.md).

Use the selected semantic baseline consistently. Record a baseline change
explicitly and review the declarations that depend on it. A versioned citation
establishes the source being interpreted; it does not by itself extend a
guarantee to earlier or later releases. Broader claims need their own documented
compatibility argument.

## Sources and missing guarantees

Rust-attributed premises in `trusted/lean/` must come from the stable Reference
or standard-library documentation. Beta or nightly documentation, the
Rustonomicon, Unsafe Code Guidelines, RFCs, discussions, compiler behavior, and
tests can guide an investigation, but they do not substitute for those premises.

If the permitted documentation does not justify a required proposition, record
the precise gap and narrow the correspondence claim or parameterize the model
behind an explicit interface outside the normative core. Describe any extra
model assumption explicitly without presenting it as a documented Rust
guarantee.

## Review and maintenance

Open each cited version and check the quotation, its surrounding conditions,
and its applicability to the declaration. Review the argument as well as the
formal proof. When code, premises, or the semantic baseline changes, update the
comment and recheck the affected correspondence; changing a URL alone does not
establish that the new version supports the same claim.

These comments are a required authoring and review policy. Automated containment
checks in [`trusted/audit/`](../trusted/audit/README.md) do not validate
quotations or prove Rust correspondence.
