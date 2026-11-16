<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Experimental scalar verifier target

This document sets requirements for an experimental scalar verifier. It
describes the intended behavior of the capture adapter, model, proof checker
and first production example.

The verifier must connect typed compiler capture, an operational Lean model,
authored specifications and proofs, and exact theorem acceptance. Its first
production target is Starnix's endianness conversion in the original multi-file
`ebpf_core` compilation.

A selected-unit result must identify the named functions and cover their
admitted closure: every item or obligation needed to justify the selected
claim. Any trusted helper, waiver or transitive assumption must be explicit in
the reported scope and trust assumptions; admission must not silently waive an
obligation. The result must not claim to verify the enclosing crate.

Whole-crate verification must account for every function, method, trait
implementation and other relevant item in the configured crate, including
uncalled entry points. Every applicable obligation must be supported and proved.
In either mode, an unsupported or missing obligation within the claimed scope
must cause refusal. Both modes must require safety of every execution prefix;
divergence must not exempt an execution from safety.

The compiler, capture adapter, source model, Lean foundation and acceptance
runtime will remain experimental trusted components. Their correctness and an
intact verification environment are separate assumptions that this prototype
must document. Complete TCB audit-log presentation, hostile elaborator effects
and the final automated review-surface guarantee remain outside this prototype's
assurance target. Deferring presentation does not permit hidden assumptions.
Pure proof placeholders, extra axioms, incorrect roots and stale source bindings
must be rejected.

The operational target is pointer-free scalar MIR: booleans, integers,
fieldless enums, storage, moves, bitwise operations and control flow.
Unsupported selected constructs must cause refusal. Broader memory, calls,
destruction, concurrency and full Starnix migration require further semantics.
