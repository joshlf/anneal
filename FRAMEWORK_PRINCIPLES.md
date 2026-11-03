<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# The Verification Framework

[`PRINCIPLES.md`](PRINCIPLES.md) defines Anneal's promise to a developer
verifying a *program*: if Anneal's trusted computing base (TCB) is valid and
Anneal emits no errors, the program is correct. Because Anneal itself is built
by formal-verification experts who define its model of Rust and undefined
behavior, [`PRINCIPLES.md`](PRINCIPLES.md) can treat *"user error that
misconstrued developer-defined requirements"* as outside Anneal's core
guarantee.

For the underlying **verification framework**, the goal is broader: to enable a
software engineer who is **not** a formal-verification specialist to
**vibe-code any formal verification tool**—such as a static analyzer, type or
borrow checker, deductive verifier, model checker, bug-finder, bound inferrer,
compiler, optimizer, decompiler, equivalence checker, sandbox instrumenter, or
synthesizer—and rely on the framework itself to ensure that the resulting tool
is bug-free.

# Some things we believe

## A tool that satisfies its formal specification can still be buggy in practice

In traditional interactive theorem proving, proving that an implementation
satisfies its formal specification is treated as the finish line because a
formal-methods expert authored both. When a non-expert developer vibe-codes a
tool and either authors or accepts an agent-authored specification, that
assumption breaks down. An optimization-driven coding agent seeking a passing
build will naturally exploit any slack between **what the formal specification
mathematically states** and **what the developer intuitively believes the tool
guarantees in the real world**.

A tool can therefore be completely sound according to its formal specification
while still failing in practice:

- The specification may define a language dialect or property that differs from
  what the developer and the tool's users expect (as when CompCert's C
  semantics differed from ISO C, causing standard-compliant C programs to be
  miscompiled).
- The formal model may omit real-world behavior that matters to the user's
  goal (such as an instruction-set model that omits execution timing, allowing
  cryptographic code to be compiled with timing side channels).
- The specification or tool may be degenerate (for example, vacuously sound
  because its preconditions admit no programs, or trivially safe because the
  tool rejects every non-trivial input).
- The verified core may be connected to the real system through buggy or
  incomplete bindings (such as a static analyzer that resolves the wrong Cargo
  project and reports success on the wrong code, or a compiler that claims to
  produce verified binaries while actually emitting verified `.S` assembly into
  an unverified assembler and linker).

## Domain intuition is enough to judge what a tool should do

A software engineer who builds a compiler pass, static analyzer, or sandbox
already has a concrete engineering theory of what inputs the tool should
handle, what real-world environment those inputs execute in, and what a passing
run of the tool guarantees. Developers should not need formal-methods expertise
to tell whether a specification captures that theory; the framework must bridge
the gap between formal definitions and engineering intuition.

## If a gap with reality cannot be eliminated, it must be impossible to miss

Every formal model abstracts away some aspects of physical reality. A framework
cannot always eliminate every gap between a mathematical model and the real
world, nor can it always verify every external tool in a user's environment.
Where a gap with reality exists, however, the framework can guarantee that it
is impossible for the developer to accept the specification while remaining
unaware of that gap.

# The framework's promise

> ***If** the framework's trusted computing base is valid, a developer
> vibe-codes a formal verification tool and authors or accepts a specification
> of that tool (along with any disclosed assumptions), **and** the framework
> certifies the tool with no errors, **then** the tool's real-world behavior
> accords with the developer's intuition.*

This commitment means that if an agent produces a tool or specification whose
real-world behavior would violate the expectations of a domain engineer who
accepted that specification, *the framework will not certify it*. If the
framework emits no errors, then either:

1. There is a bug or invalid assumption in the framework's own trusted
   computing base, or
2. The deployed tool behaves in the real world as a domain engineer accepting
   that specification and its disclosed assumptions would reasonably expect.

# Corollaries of the promise

For a certified tool's real-world behavior to accord with a non-expert
developer's intuition, five independent conditions must hold across **the
developer's intuition**, **the formal specification**, **the real world**,
**the deployed tool**, and **the verification foundation**. If any one of these
conditions fails, a formally verified tool can still violate the developer's
expectations in practice.

## 1. The specification must mean what the developer thinks it means

A non-expert developer's acceptance of a specification carries weight only if
they can accurately understand what they are accepting using ordinary domain
and engineering intuition, without needing formal-methods expertise.

- **No misleading or opaque abstractions:** A specification must not rely on
  deceptive helper names (such as a predicate named `isConstantTime` or
  `isStandardsCompliant` whose definition checks something weaker), deeply
  nested definitions, or hidden special cases that obscure what is actually
  proved.
- **No formal-language traps:** A specification must not silently depend on
  formal-logic idioms whose behavior diverges from standard engineering meaning
  (such as saturating natural-number subtraction where `0 - 1 = 0`, division by
  zero returning `0`, Euclidean rather than truncating remainder on negative
  numbers, or implicit variable quantification turning a typo into a vacuous
  premise).
- **Claim-polarity and behavioral fidelity:** The form of the guarantee must
  match the kind of tool the developer believes they are building—for example,
  proving that *all* executions are safe (for a verifier) rather than *some*
  execution, proving that *every* reported failure is a genuine bug (for a
  bug-finder), preserving bidirectional witness completeness (for codecs and
  zero-knowledge circuits), enforcing target safety without breaking benign
  inputs (for sandboxes and sanitizers), preserving randomness and entropy (for
  cryptographic code) rather than treating a constant key as a valid refinement
  of random choice, and establishing genuine progress (for liveness).
- **No silent post-acceptance drift:** An agent must not be able to repair a
  failing proof by quietly weakening a specification after the developer has
  authored or accepted it.

## 2. Neither the specification nor the tool may be degenerate

A specification and tool must not achieve formal correctness by emptying either
the domain of inputs they apply to or the substance of what they guarantee.

- **No antecedent vacuity (winning by domain collapse):** A specification must
  not be satisfied vacuously because its preconditions, environmental
  assumptions, or target-language rules are contradictory or overly restrictive
  (admitting no valid programs or executions).
- **No consequent triviality (winning by claim collapse):** A specification
  must not assert a tautological postcondition, nor project away the program
  state or side effects that matter to the user's property (such as ignoring
  corrupted callee-saved registers, heap state, or erased secret-wiping
  writes). In a compound specification (for example, functional correctness
  *and* side-channel freedom), every individual requirement must be
  non-degenerate; one genuine clause must not mask a vacuous companion clause.
- **No degenerate or utility-destroying tools:** A certified tool must
  genuinely handle the general class of inputs the developer expects. It must
  not pass verification by rejecting all inputs, always returning
  "inconclusive," memorizing a finite set of test cases, inferring trivial
  bounds (such as `+∞`), acting as a no-op optimizer, or achieving "safety" by
  destroying the program's useful behavior (such as a compiler or sanitizer
  that rewrites valid code into an unconditional abort or infinite loop).

## 3. The specification must have no silent gap with reality

Formal verification proves properties against a *model* of a language,
instruction set, or execution environment. Wherever that formal model differs
from the real world in which the user's artifacts actually execute, that
difference must either be eliminated or made impossible for the developer to
miss.

- **No silent divergence from standards or hardware:** When a tool targets an
  existing language standard, runtime, protocol, or hardware architecture, its
  formal model must not silently deviate from the real system's semantics (as
  when CompCert's C semantics diverged from ISO C, or when IEEE-754
  floating-point arithmetic is modeled as idealized real numbers).
- **Unmistakable disclosure of unmodeled reality:** Every formal model
  abstracts away some aspects of physical reality—such as instruction timing
  and microarchitectural side channels, weak-memory concurrency, finite stack
  and heap bounds, asynchronous cancellation, fault injection, or re-entrant
  callbacks from unverified code in an open world. If a specification omits a
  real-world behavior or relies on an environmental assumption, **it must be
  impossible for the developer to accept the specification while remaining
  unaware of that gap**, especially when the property the developer cares about
  depends on the omitted behavior.

## 4. The verified core must be bound end-to-end to the real system

A sound, non-degenerate, reality-faithful theorem about an internal
mathematical function is insufficient if the tool as actually run in the user's
workflow does not match that mathematical function from end to end.

- **Exact input and scope binding:** The deployed tool must analyze the exact
  project, files, build configuration (such as `release` vs. `debug`), target
  parameters, and feature flags the user invokes it on. It must never report
  overall success because it resolved the wrong project or silently skipped
  unsupported functions or language constructs.
- **End-to-end output and downstream toolchain integrity:** When a tool emits
  or transforms an artifact, the formal guarantee must hold all the way to the
  final artifact the user deploys:
  - The bytes emitted by the tool must match the formal object governed by the
    proof (with no unverified or drifting pretty-printers).
  - If the tool stops at an intermediate representation (such as emitting `.S`
    assembly files or C source code) and relies on an unverified downstream
    assembler, linker, or optimizing compiler—or if a downstream optimizer
    could erase the property the tool just established (such as dead-store
    elimination removing secret-zeroizing writes or branch optimizations
    undoing constant-time masks)—that unverified downstream boundary is a gap
    with reality: it must be either eliminated or made impossible for the
    developer to overlook.
- **Honest verdicts and diagnostics:** The tool's externally observable output
  (exit code, summary, and failure traces) must accurately reflect what was
  established—strictly distinguishing unbounded proofs, horizon-bounded checks
  (such as loops unrolled to depth `k`), refutations backed by genuine
  counterexamples, and inconclusive or unsupported cases.

## 5. The tool cannot silently expand the trusted computing base

When a developer uses the framework, they choose to trust the framework's own
core, not the agent that vibe-coded their tool.

- **No self-validating or circular specifications:** A specification must not
  define correctness by delegating back to the tool's own implementation (for
  example, defining `is_valid(x)` as `tool(x) == true`).
- **No silent proof or runtime escapes:** An agent-authored tool or proof must
  not bypass verification through unfinished proofs, custom axioms, or
  unverified runtime code replacements; any unproven assumption must either be
  rejected outright or surfaced with the same unmistakable visibility as a gap
  with reality under Corollary 3.

# How we make decisions about the framework

1. **Assume optimization pressure against every boundary.** We evaluate
   candidate framework designs under the assumption that an automated coding
   agent will take the path of least resistance to achieve a passing check. Any
   unpoliced gap between the formal theorem and real-world behavior will
   eventually be exploited.
2. **Respect the developer's cognitive budget.** A non-expert developer cannot
   be expected to audit large formal semantics, read proof scripts, or spot
   subtle theorem-prover idioms. Whatever the developer must review to accept a
   specification must remain concise, concrete, and grounded in ordinary
   engineering concepts.
3. **Never lock out honest tools to block degenerate ones.** Requirements that
   rule out vacuous specifications or memorized lookup-table tools must not
   reject legitimate verification tools—such as conservative syntactic type or
   borrow checkers that intentionally reject safe programs they cannot prove.
4. **Support the full spectrum of formal verification tools.** We prefer
   foundational concepts that naturally express the guarantees of all formal
   verification tools—verifiers, bug-finders, bounded checkers, inferrers,
   compilers, lifters, equivalence checkers, sandboxes, and synthesizers—rather
   than forcing every tool into a single mold.
