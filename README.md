<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification framework for Rust under active development. See
[`PRINCIPLES.md`](PRINCIPLES.md) for the current project principles.

## Correctness policy and `trusted/`

[`PRINCIPLES.md`](PRINCIPLES.md) promises that if the code in a verification
result's TCB audit log is correct, its assumptions are valid, and Anneal emits
no errors, then the verified code is correct. A **verification result** asserts
that:

1. its **TCB** satisfies its **trust policy**, and
2. if the trusted code in its **TCB** is correct, and its trusted assumptions
   are jointly valid, then its requested **claim** holds.

The `trusted/` directory isolates every part of Anneal on which those two
assertions depend without checked evidence. The invariant of `trusted/` is that
**auditing `trusted/` alone is sufficient to verify that Anneal upholds
[`PRINCIPLES.md`](PRINCIPLES.md)**: an auditor never needs to inspect code
outside `trusted/` to trust a verification result. This must remain true in the
face of adversarial implementations in any other part of the repository.

(Currently, `.github` is an exception to this rule, although we aim to tighten
that as well.)
