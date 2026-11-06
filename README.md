<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification framework for Rust under active development. See
[`PRINCIPLES.md`](PRINCIPLES.md) for the project principles and
[`THREAT_MODEL.md`](THREAT_MODEL.md) for the threat model.

## Correctness policy and `trusted/`

[`PRINCIPLES.md`](PRINCIPLES.md) promises that if the code in a verification
result's TCB audit log is correct, its assumptions are valid, and Anneal emits
no errors, then the verified code is correct. A **verification result** asserts
that:

1. its **TCB** satisfies its **trust policy**, and
2. if the trusted code in its **TCB** is correct, and its trusted assumptions
   are jointly valid, then its requested **claim** holds.

The `trusted/` directory isolates every first-party component of Anneal on
which those two assertions depend without checked evidence. The invariant of
`trusted/` is that **auditing `trusted/` and its explicit, pinned dependency
manifest is sufficient to verify that Anneal upholds
[`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md)**: an
auditor never needs to inspect first-party code outside `trusted/` to trust a
verification result. This must remain true in the face of adversarial
implementations in any other part of the repository.

To keep the human audit surface tractable and reliable, `trusted/` permits
battle-tested, widely-used external libraries for routine utilities (such as
command-line flag parsing, serialization, and trace logging). Using established
libraries for generic infrastructure is strongly preferred over hand-rolling
bespoke implementations inside `trusted/`, which inflates audit burden and
invites defect-prone reinvented wheels.

(Currently, `.github` is an exception to this rule, although we aim to tighten
that as well.)

## Design documentation

- [`PRINCIPLES.md`](PRINCIPLES.md): Anneal's mission, correctness promise, and
  decision-making priority order.
- [`THREAT_MODEL.md`](THREAT_MODEL.md): Threat model, why verification assumes
  an uncompromised execution environment (CI vs. local dev), and what
  repository-borne threats Anneal aims to defend against (including `build.rs`
  and procedural macros).
- [`docs/design.md`](docs/design.md): Overall system design, end-to-end
  verification workflow, library-centric verification, multi-modal
  specifications, and incremental adoption.
- [`docs/architecture.md`](docs/architecture.md): The three-stage MIR pipeline,
  repository layout, `rustc` extraction lifecycle, and multi-version toolchain
  strategy.
- [`docs/trust-model.md`](docs/trust-model.md): How Anneal's internal `trusted/`
  vs. `theory/` boundary and `trusted/audit/` implement and enforce
  [`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md).
