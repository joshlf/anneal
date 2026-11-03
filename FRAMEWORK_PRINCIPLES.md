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
borrow checker, deductive verifier, model checker, bug-finder, bound or
invariant inferrer, compiler, optimizer, binary lifter, decompiler, equivalence
checker, open-world linker, sandbox instrumenter, repair tool, synthesizer, or
specification auditor—and rely on the framework itself to ensure that the
resulting tool is bug-free.

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

- The specification may define a language dialect, claim polarity, or property
  that differs from what the developer and the tool's users expect (as when
  CompCert's C semantics differed from ISO C, causing standard-compliant C
  programs to be miscompiled).
- The formal model may omit real-world behavior that matters to the user's
  goal (such as an instruction-set model that omits execution timing, allowing
  cryptographic code to be compiled with timing side channels).
- The specification or tool may be degenerate (for example, vacuously sound
  because its preconditions admit no programs, or trivially safe because the
  tool rejects every non-trivial input).
- The verified core may be connected to the real system through buggy or
  incomplete bindings (such as a static analyzer that resolves the wrong Cargo
  project or build profile and reports success on the wrong code, or a compiler
  that claims to produce verified binaries while actually emitting verified
  `.S` assembly into an unverified assembler and linker).

## Domain intuition is enough to judge what a tool should do

A software engineer who builds a compiler pass, static analyzer, bug-finder, or
sandbox already has a concrete engineering theory of what inputs the tool
should handle, what real-world environment those inputs execute in, and what a
run of the tool guarantees. Developers should not need formal-methods expertise
to tell whether a specification captures that theory; the framework must bridge
the gap between formal definitions and engineering intuition.

## If a gap with reality cannot be eliminated, it must be impossible to miss

Every formal model abstracts away some aspects of physical reality. A framework
cannot always eliminate every gap between a mathematical model and the real
world, nor can it always verify every external tool in a user's environment.
Where an unavoidable gap with reality exists, however, the framework can
guarantee that it is impossible for the developer to accept the specification
while remaining unaware of that gap—without allowing an agent to use disclosure
as an escape hatch for avoidable proof obligations or bury a fatal assumption
in boilerplate warnings.

# The framework's promise

> ***If** the framework's trusted computing base is valid, a developer
> vibe-codes a formal verification tool and authors or accepts a specification
> of that tool (along with any disclosed assumptions), **and** the framework
> certifies the tool with no errors, **then** for every input given to the
> tool, either the tool rejects or abstains on that input as expected, or the
> artifact or claim it certifies or produces upholds the guarantee the
> developer expects of it in the real world.*

Both branches of this commitment are essential:

- **Expected rejection or abstention:** The tool may decline to certify or
  transform an input—rejecting it or returning an inconclusive, unsupported, or
  "no bug found" status—only when that input genuinely falls outside the
  developer's intended acceptance envelope (because it violates the property or
  rules the tool checks, exhibits no bug in a bug-finding search, lies outside
  the tool's supported scope, or exceeds the honest limits of its analysis),
  and never by crashing, hanging, vacuously refusing valid inputs, or emitting
  a false claim or broken artifact alongside a refusal. Any diagnostic
  accompanying a rejection must accurately reflect the violated rule or
  analysis limit.
- **Real-world validity of produced artifacts and claims:** Whenever the tool
  certifies or produces an artifact or emits a substantive claim, that output
  must satisfy the developer's intuitive contract in the real target
  environment (within any explicitly disclosed assumptions). Any **artifact**
  the tool certifies, compiles, hardens, links, repairs, or synthesizes must
  behave as expected when built, shipped, and run (across all executions for a
  verified, hardened, repaired, linked, or synthesized artifact, and across all
  well-defined source executions for a compiled or optimized one). Any **claim,
  bound, abstract model, or counterexample** the tool emits (including a
  concrete failure trace accompanying a rejection or a synthesizer's
  unrealizability witness) must hold true of the input and its real-world
  executions in the target environment.

If an agent produces a tool or specification whose real-world behavior would
violate the expectations of a domain engineer who accepted that specification,
*the framework will not certify it*. If the framework emits no errors, then
either:

1. There is a bug or invalid assumption in the framework's own trusted
   computing base, or
2. Every invocation of the deployed tool upholds both branches of that promise
   in the real world as a domain engineer accepting that specification and its
   disclosed assumptions would reasonably expect.

# Corollaries of the promise

For a certified tool to uphold this promise for a non-expert developer, five
independent conditions must hold across **the developer's intuition**, **the
formal specification**, **the real world**, **the deployed tool**, and **the
verification foundation**. If any one of these conditions fails, a formally
verified tool or the artifacts and claims it produces can still violate the
developer's expectations in practice.

## 1. The specification must mean what the developer thinks it means

A non-expert developer's acceptance of a specification carries weight only if
they can accurately understand what they are accepting using ordinary domain
and engineering intuition, without needing formal-methods expertise.

- **No misleading or opaque abstractions:** A specification must not rely on
  deceptive helper names (such as a predicate named `isConstantTime` or
  `isStandardsCompliant` whose definition checks something weaker), deeply
  nested definitions, implicit conversions or overloaded definitions, or hidden
  special cases that obscure what is actually proved.
- **No formal-language traps:** A specification must not silently depend on
  formal-logic idioms whose behavior diverges from standard engineering meaning
  (such as saturating natural-number subtraction where `0 - 1 = 0`, division by
  zero or out-of-bounds indexing returning `0`, Euclidean rather than
  truncating remainder on negative numbers, unbounded mathematical integers
  where fixed-width wrapping or overflow is expected, or implicit variable
  quantification turning a typo into a vacuous premise).
- **Claim-polarity and precondition fidelity:** The form of the guarantee and
  its preconditions must match the kind of tool the developer believes they are
  building. A verifier, sandbox, sanitizer, or repair tool must establish or
  enforce safety across *all* executions rather than assuming away the bugs or
  undefined behavior it is meant to catch, contain, or repair (unlike a
  semantics-preserving compiler, which may assume well-defined source inputs);
  a bug-finder must prove that *every* reported failure trace is a genuine bug
  without equating an exhausted search with universal safety; a binary lifter
  or decompiler must capture every possible real-world execution of an input
  binary; and a codec or zero-knowledge circuit verifier must preserve
  bidirectional witness completeness alongside soundness. Likewise, the modeled
  execution regime must match the target property—preserving module invariants
  across all public entry points and unverified callbacks (for open-world
  libraries), relational equivalence or multi-trace hyperproperties (for
  equivalence and constant-time checkers), probability distributions and
  entropy rather than collapsing random choice to a constant (for cryptographic
  code), and genuine progress over complete runs rather than finite prefixes or
  infinite stuttering (for termination and liveness).
- **No silent post-acceptance drift:** An agent must not be able to repair a
  failing proof on a later turn by quietly weakening a specification or
  expanding its disclosed assumptions after the developer has authored or
  accepted them.

## 2. Neither the specification nor the tool may be degenerate

A specification and tool must not achieve formal correctness by emptying either
the domain of inputs they apply to or the substance of what they guarantee.

- **No antecedent vacuity (winning by domain collapse):** A specification must
  not be satisfied vacuously because its preconditions, initial-state
  constraints, environmental assumptions, or target-language rules are
  contradictory or overly restrictive (admitting no valid programs or
  executions, or narrowing them to a trivial subset of the intended input or
  execution space).
- **No consequent triviality (winning by claim collapse):** A specification
  must not assert a tautological postcondition, check a ghost output slot
  decoupled from real ABI registers, or project away the program state or side
  effects that matter to the user's property (such as ignoring corrupted
  callee-saved registers, heap state, or erased secret-wiping writes). In a
  compound specification (for example, functional correctness *and*
  side-channel freedom), every individual requirement must be independently
  non-degenerate; one genuine clause must not mask a vacuous companion clause.
- **No degenerate or utility-destroying tools:** A certified tool—as a complete
  deployed system, including any untrusted solver, search pass, optimization
  pass, or certificate finder paired with a verified checker—must genuinely
  handle the general class of inputs the developer expects. It must not pass
  verification through trivial refusal or domain restriction (rejecting all
  inputs, always returning "inconclusive," memorizing a finite set of test
  cases, or checking only syntactic identity `p1 == p2`) or through vacuous
  outputs (emitting a hardcoded program from a synthesizer, inferring trivial
  bounds such as `+∞` or unconstrained `Top` models that permit all behaviors,
  or acting as a no-op optimizer). Likewise, a compiler, sandbox, sanitizer, or
  repair tool must not achieve formal safety through utility-destroying rewrites
  that turn valid code or benign executions into an unconditional abort, panic,
  infinite loop, or trivial constant return.

## 3. The specification must have no silent gap with reality

Formal verification proves properties against a *model* of a language,
instruction set, or execution environment. Wherever that formal model differs
from the real world in which the user's artifacts actually execute, that
difference must either be eliminated or made impossible for the developer to
miss.

- **No silent divergence from standards or hardware:** When a tool targets an
  existing language standard, runtime, protocol, or hardware architecture, its
  formal model must match the real system's semantics (unlike CompCert's early
  C semantics where it diverged from ISO C, or a model that treats IEEE-754
  floating-point arithmetic as idealized real numbers) and be validated against
  real implementations so a common-mode bug shared by an agent-authored model
  and tool cannot pass. A tool that intentionally models a custom dialect or
  restricted subset must declare that scope unmistakably rather than claiming
  the standard.
- **Unmistakable, bounded disclosure of unmodeled reality:** Every formal model
  abstracts away some aspects of physical reality or external execution
  environments—such as instruction timing and microarchitectural side channels,
  weak-memory concurrency, finite stack and heap bounds, asynchronous
  cancellation, physical fault injection, or interactions with unverified
  external code. If a specification omits a real-world behavior or relies on an
  environmental assumption, **it must be impossible for the developer to accept
  the specification while remaining unaware of that gap**. Disclosed
  assumptions may record only genuine, unavoidable boundary conditions outside
  the guarantee the tool claims: an agent must never omit a behavior on which
  the target property depends, assume away the core bug classes the tool is
  meant to check, bypass an avoidable proof obligation, or bury a critical
  limitation in boilerplate caveats.

## 4. The verified core must be bound end-to-end to the real system

A sound, non-degenerate, reality-faithful theorem about an internal
mathematical function is insufficient if the tool as actually run in the user's
workflow does not match that mathematical function from end to end.

- **Exact input, configuration, and scope binding:** The deployed tool must
  ingest and faithfully decode the exact project, source files or binary
  artifacts, build configuration (such as `release` vs. `debug`, where overflow
  and assertion semantics differ), target parameters, and feature flags the
  user invokes it on. It must never report overall success after resolving the
  wrong project, reusing stale cached verdicts after source files,
  dependencies, macros, or build flags change, or silently skipping unsupported
  functions, instructions, or language constructs (including implicit
  destructors, closures, and macros).
- **End-to-end output and downstream toolchain integrity:** When a tool emits
  or transforms an artifact or model, the formal guarantee must hold all the
  way to the final output the user relies on:
  - The bytes or model emitted by the tool must match the formal object
    governed by the proof (with no unverified or drifting pretty-printers or
    serializers).
  - If the tool stops at an intermediate representation (such as emitting `.S`
    assembly files or C source code) and relies on an unverified downstream
    assembler, linker, or optimizing compiler—or if a downstream optimizer
    could erase the property the tool just established (such as dead-store
    elimination removing secret-zeroizing writes or branch optimizations
    undoing constant-time masks)—that unverified downstream boundary must be
    either eliminated or surfaced as an unmistakable disclosed assumption under
    Corollary 3.
- **Honest verdicts and diagnostics:** The tool's externally observable output
  (exit code, summary, and failure traces) must accurately reflect what was
  established—strictly distinguishing unbounded proofs, horizon-bounded checks
  (such as loops unrolled to depth `k`), refutations backed by genuine
  counterexamples, and inconclusive or unsupported cases. It must never claim
  unbounded safety when a check is horizon-bounded, and never return a passing
  verdict or exit code when checks were skipped or inconclusive.

## 5. The tool cannot silently expand the trusted computing base

When a developer uses the framework, they choose to trust the framework's own
core, not the agent that vibe-coded their tool.

- **No self-validating or circular specifications:** A specification must be
  defined independently of the tool's own implementation (never defining
  `is_valid(x)` as `tool(x) == true` or defining target semantics via the
  tool's own printer), which would fold the unverified tool into the trusted
  specification.
- **No silent proof or runtime escapes:** An agent-authored tool,
  specification, or proof must never bypass verification through unfinished
  proofs, custom axioms, unproven helper annotations or external solver results
  treated as axioms, hidden premises that assume the tool's own correctness,
  unverified compile-time evaluation, or unverified runtime code replacements
  (such as compiler override or foreign-function attributes that silently
  substitute unverified code for a verified definition at runtime). Any
  external boundary assumption must be surfaced through the bounded disclosure
  channel of Corollary 3.

# How we make decisions about the framework

1. **Assume optimization pressure against every boundary.** We evaluate
   candidate framework designs under the assumption that an automated coding
   agent will take the path of least resistance to achieve a passing check. Any
   unpoliced gap between the formal theorem and real-world behavior will
   eventually be exploited.
2. **Respect the developer's cognitive budget.** A non-expert developer cannot
   be expected to audit large formal semantics, read proof scripts, spot subtle
   theorem-prover idioms, or sift through pages of boilerplate disclaimers.
   Whatever the developer must review to accept a specification and its
   disclosed assumptions must remain concise, concrete, and grounded in
   ordinary engineering concepts.
3. **Never lock out honest tools to block degenerate ones.** Requirements that
   rule out vacuous specifications, broken certificate finders, or memorized
   lookup-table tools must test for genuine algorithmic generalization across
   the tool's intended input family—never requiring semantic completeness that
   would reject legitimate conservative tools, such as syntactic type or borrow
   checkers that intentionally reject safe programs they cannot prove.
4. **Support the full spectrum of formal verification tools.** We prefer
   foundational concepts that naturally express the guarantees of all formal
   verification tools—verifiers, bug-finders, bounded checkers, inferrers,
   compilers, lifters, equivalence checkers, linkers, sandboxes, repair tools,
   synthesizers, and specification auditors—rather than forcing every tool into
   a single mold.
