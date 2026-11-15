<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR Semantics and Reference Correspondence Strategy

Anneal verifies Rust programs by stating its top-level verification obligation
(`Trusted.CrateTheorem`) over an operational semantics for Rust's Mid-level
Intermediate Representation (MIR) inside the Lean 4 kernel. Because that MIR
semantics defines what it means for a program to be free of undefined behavior
(UB) and to satisfy a functional specification, any soundness bug in Anneal's
MIR semantics directly undermines Anneal's correctness promise.

This document describes the strategy for building Anneal's MIR semantics
incrementally while guarding against semantic bugs through a machine-checked
correspondence proof against an established reference model in continuous
integration (CI).

## 1. The core problem: verification ergonomics vs. semantic trust

A MIR operational semantics for Anneal must satisfy two competing requirements:

1. **Ergonomic symbolic reasoning in Lean 4:** Proving properties of real Rust
   functions requires a semantics structured for symbolic evaluation,
   compositional framing, and proof automation. As Anneal matures, this
   semantics ($M_{\text{anneal}}$) will be iteratively extended, refactored,
   and optimized for proof performance—often by AI coding agents.
2. **High confidence in Rust semantic fidelity:** Rust's operational semantics
   contains many subtle rules across integer and pointer arithmetic, niche and
   padding representations, place projections, borrow and aliasing state
   machines, drop elaboration, and unwinding. When contributors or AI agents
   implement or optimize $M_{\text{anneal}}$ under pressure to make verification
   proofs pass, both accidental oversights and optimization incentives push
   toward omitting inconvenient UB checks or oversimplifying corner cases.

Verifying user programs directly against an external reference interpreter or
specification (such as `lean-miri` or `MiniRust`) avoids writing a custom
semantics, but those models are structured as literal interpreters or reference
documents rather than compositional verification targets in Lean 4. Conversely,
writing $M_{\text{anneal}}$ from scratch and relying on human reviewers to
catch every missing UB check or behavioral divergence across tens of thousands
of lines of Lean definitions does not scale reliably.

Anneal resolves this tension by maintaining **both** models and connecting them
with a single, locked correspondence theorem in CI:

- **Anneal's MIR semantics ($M_{\text{anneal}}$):** Designed and iteratively
  evolved for verification ergonomics in Lean 4, and treated as potentially
  buggy during development.
- **A reference MIR model ($M_{\text{ref}}$):** An existing external
  formalization (`lean-miri`, `MiniRust`, or a combination of reference models)
  landed in the repository and audited once for fidelity to upstream.

## 2. The three-step development strategy

Rather than implementing a large portion of $M_{\text{anneal}}$ first and
attempting to retrofit correspondence proofs afterward, Anneal establishes the
reference model and the end-to-end correspondence theorem **first**, before
iteratively implementing MIR features.

### Step 1: Land the reference model ($M_{\text{ref}}$)

First, we land a reference MIR semantics ($M_{\text{ref}}$)—such as
`lean-miri`, `MiniRust`, or a combination—in the repository. Because
$M_{\text{ref}}$ is transcribed or adapted from an existing external
specification rather than invented alongside Anneal's proof tactics, human
reviewers can audit $M_{\text{ref}}$ once up front.

### Step 2: Define the core MIR representation and execution outcomes

Second, we define the core MIR representation and execution semantics for
$M_{\text{anneal}}$. In addition to normal progress and termination outcomes,
executions in $M_{\text{anneal}}$ distinguish at least two failure outcomes:

- **`undefined`:** The program executed a construct that $M_{\text{anneal}}$
  models and violated Rust's operational rules (exhibiting undefined behavior).
- **`unsupported`:** The program reached a construct, type, operation, or
  execution mode that $M_{\text{anneal}}$ does not model, or an execution that
  $M_{\text{anneal}}$ conservatively rejects because it enforces a simpler rule
  than full Rust.

For verification soundness, both `undefined` and `unsupported` act as failure
outcomes: a program verified by Anneal is not permitted to reach either outcome.
Splitting them into distinct outcomes serves developer experience and
engineering diagnostics:

- Reporting `undefined` tells the user that their program exhibits UB under the
  modeled semantics.
- Reporting `unsupported` tells the user (and Anneal developers) that the
  program may be valid Rust, but uses a feature that $M_{\text{anneal}}$ does
  not yet implement or falls outside a simplified rule that
  $M_{\text{anneal}}$ enforces.

### Step 3: Lock the correspondence theorem in CI and grow $M_{\text{anneal}}$

Third, we state and prove a single correspondence theorem in CI before
implementing the bulk of MIR:

> **Correspondence Theorem (Informal):** For every program $p$ and every input
> query $q$, if $p$ is well-formed on $q$ according to $M_{\text{anneal}}$
> (meaning that no execution of $p$ from $q$ reaches `undefined` or
> `unsupported`), then $p$ is also well-formed on $q$ according to
> $M_{\text{ref}}$, and every observable behavior that $M_{\text{ref}}$ permits
> for $p$ on $q$ is also a behavior of $p$ on $q$ in $M_{\text{anneal}}$.

Two features of this statement carry its soundness.

First, both models execute the same input. The theorem quantifies universally
over input queries $q$ (function arguments and initial caller-visible memory)
in a representation that both models share, and each model constructs its
initial state directly from $q$ (in Anneal's design, `initState` for
$M_{\text{anneal}}$ and `initRefState` for $M_{\text{ref}}$). If the models
represented inputs differently, the theorem would instead have to quantify over
a total, structure-preserving relation between the two input representations.
A conversion function or an unverified precondition on $q$ could otherwise
filter out or sanitize exactly the inputs that trigger UB, leaving every
remaining reference execution trivially safe.

Second, behavioral inclusion runs from $M_{\text{ref}}$ into
$M_{\text{anneal}}$. Writing $\mathsf{Behavior}(p, q)$ for the set of
observable behaviors (including divergence) that a model permits for $p$ on
$q$, sound specification transfer requires behavioral refinement:

$$
\mathsf{Behavior}_{\text{ref}}(p, q) \subseteq
\mathsf{Behavior}_{\text{anneal}}(p, q)
$$

This is the backward-simulation direction of the `Abstracts` relation that
Anneal's verified lowering uses ([`docs/architecture.md`](architecture.md)),
with $M_{\text{ref}}$ in the role of the concrete semantics and
$M_{\text{anneal}}$ in the role of its abstraction. A specification proved for
every behavior of $M_{\text{anneal}}$ then holds for every behavior that
$M_{\text{ref}}$ permits, while $M_{\text{anneal}}$ remains free to
over-approximate (for example, by admitting several outcomes for a
nondeterministic choice). When $M_{\text{anneal}}$ is deterministic and does
not over-approximate any outcome, the theorem can state the stronger
bidirectional equivalence, under which each model permits a behavior if and
only if the other does:

$$
\mathsf{Behavior}_{\text{anneal}}(p, q) = \mathsf{Behavior}_{\text{ref}}(p, q)
$$

The opposite inclusion alone,
$\mathsf{Behavior}_{\text{anneal}}(p, q) \subseteq
\mathsf{Behavior}_{\text{ref}}(p, q)$, would be unsound: if $M_{\text{ref}}$
admitted an extra nondeterministic outcome, a postcondition proved over every
behavior of $M_{\text{anneal}}$ would say nothing about that outcome.

Initially, $M_{\text{anneal}}$ can return `unsupported` for almost every MIR
construct. Because reaching `unsupported` falsifies the hypothesis that $p$ is
well-formed in $M_{\text{anneal}}$, the correspondence theorem is
straightforward to prove on the initial skeleton.

Once this theorem is locked in CI, incremental development proceeds by
replacing `unsupported` branches in $M_{\text{anneal}}$ with concrete execution
rules (returning normal progress or `undefined`) one MIR feature at a time:

1. **The theorem statement stays fixed:** Adding support for a new MIR feature
   changes the definition of $M_{\text{anneal}}$ and the proof of the
   correspondence theorem, without changing the theorem statement itself.
2. **CI polices soundness automatically:** Whenever a pull request changes a
   branch of $M_{\text{anneal}}$ from `unsupported` to an active execution
   rule, the Lean 4 kernel requires the pull request to prove that the new rule
   never succeeds on an execution where $M_{\text{ref}}$ faults, and never
   omits a behavior that $M_{\text{ref}}$ permits.

If implementing a new MIR feature in $M_{\text{anneal}}$ omits a UB check that
$M_{\text{ref}}$ enforces (for example, a division-by-zero, shift-overflow,
alignment, or aliasing guard) or miscomputes a result, so that
$M_{\text{anneal}}$ no longer permits the behavior that $M_{\text{ref}}$
permits, the correspondence proof fails to compile in CI.

The proof detects divergences between $M_{\text{anneal}}$ and
$M_{\text{ref}}$; it cannot detect an error that both share. If
$M_{\text{ref}}$ omits the same UB check or encodes the same mistaken rule, if
$M_{\text{ref}}$ was transcribed incorrectly, or if the trusted boundary
definitions that state the theorem are wrong, the two models can agree and the
proof still compiles. The upfront human TCB audit of $M_{\text{ref}}$ and of
those boundary definitions remains responsible for such shared errors.

## 3. Why order matters: avoiding the retrofit trap

Implementing a large semantics first and deferring correspondence proofs until
later fails in two ways:

1. **Compounding divergences:** Small differences in value representations,
   layout calculations, control-flow handling, and side-condition checks
   accumulate across thousands of lines of code before any mechanized check
   compares the two models.
2. **Pressure to weaken the theorem:** When an agent or contributor is asked to
   prove correspondence between two large, already-written models that disagree
   on edge cases, the path of least resistance is to weaken the theorem
   statement—for example, by gating the theorem behind an ad hoc syntactic
   fragment predicate, adding a hypothesis assuming that $M_{\text{ref}}$ does
   not fault, or proving isolated per-instruction lemmas rather than a single
   whole-program theorem.

Landing $M_{\text{ref}}$ and locking the single whole-program correspondence
theorem on a minimal skeleton inverts these incentives. Human reviewers inspect
the correspondence theorem statement, together with the boundary definitions
that give it meaning, once when the codebase is small. Every subsequent feature
addition must satisfy that unchanged theorem statement, and any later change
to the statement or to those boundary definitions requires the same human
review.

## 4. Subtleties and formal failure modes

A machine-checked theorem is only as strong as its statement and its boundary
definitions. Even with the Lean 4 kernel checking every proof, a correspondence
theorem can be "technically true" while failing to establish what a human
intuitively expects.

**Human comprehension of the correspondence theorem statement and every
definition in its transitive dependency cone is therefore paramount.** It must
be crystal clear to a human reviewer that the correspondence theorem means in
mathematical terms what they intend it to mean in intuitive terms. Non-obvious
subtleties, clever encodings, or indirect formulations in the theorem statement
or its transitive boundary definitions are unacceptable: any complexity needed
to relate the two models belongs in the untrusted proof, while every definition
that controls the meaning of the theorem must be maximally direct, self-evident
to a human auditing the file, and documented so that every boundary condition is
explicit rather than subtle.

In particular, the design of $M_{\text{anneal}}$, $M_{\text{ref}}$, and the
correspondence theorem must guard against the following failure modes from the
beginning and across all future additions.

### 4.1 One-way soundness asymmetry

The correspondence implication runs from $M_{\text{anneal}}$ to
$M_{\text{ref}}$ for every program $p$ and input query $q$:

$$
\mathsf{WellFormed}_{\text{anneal}}(p, q) \implies
\mathsf{WellFormed}_{\text{ref}}(p, q) \;\land\;
\mathsf{Behavior}_{\text{ref}}(p, q) \subseteq
\mathsf{Behavior}_{\text{anneal}}(p, q)
$$

This asymmetry is deliberate:

- **$M_{\text{anneal}}$ may never be more permissive than $M_{\text{ref}}$:**
  If $M_{\text{ref}}$ exhibits UB on an execution, $M_{\text{anneal}}$ must
  report either `undefined` or `unsupported`. A theorem that instead assumed
  $\mathsf{WellFormed}_{\text{ref}}(p, q)$ as a hypothesis would pass
  vacuously on every input where $M_{\text{anneal}}$ omitted a UB guard
  enforced by $M_{\text{ref}}$.
- **The implication tolerates a more restrictive $M_{\text{anneal}}$:**
  $M_{\text{anneal}}$ may reject an execution that $M_{\text{ref}}$ accepts,
  either because a construct is not yet implemented or because
  $M_{\text{anneal}}$ conservatively enforces a simpler rule than full Rust.
  Soundness is preserved in both cases, and in both cases $M_{\text{anneal}}$
  must report `unsupported`, not `undefined`. `undefined` is reserved for
  executions that actually exhibit UB; reporting it for a valid program would
  falsely tell the user that the program has UB. The bidirectional fault
  equivalence of Section 4.6 narrows this latitude further: it permits
  $M_{\text{anneal}}$ to report `unsupported` only where $M_{\text{ref}}$ also
  does.
- **Behaviors are included in the opposite direction:** Every behavior that
  $M_{\text{ref}}$ permits must also be a behavior of $M_{\text{anneal}}$,
  while $M_{\text{anneal}}$ may permit more (see Step 3).

### 4.2 Requiring $M_{\text{ref}}$ to model everything in $M_{\text{anneal}}$

No existing reference model covers 100% of `rustc` MIR (for example, arbitrary
compiler intrinsics or inline assembly). Consequently, $M_{\text{ref}}$ also
distinguishes between well-defined executions and unmodeled or faulting
executions.

$\mathsf{WellFormed}_{\text{ref}}(p, q)$ requires that $p$ is completely
supported and UB-free in $M_{\text{ref}}$ on $q$. That means
$M_{\text{anneal}}$ is not allowed to treat a construct as well-formed unless
$M_{\text{ref}}$ also models it and agrees it is well-formed. This strict
requirement keeps the theorem statement simple and prevents an escape hatch
where $M_{\text{anneal}}$ could implement a construct with no reference oracle
checking its soundness.

The requirement does not lapse as coverage grows. To support a construct (such
as an additional compiler intrinsic) beyond $M_{\text{ref}}$'s initial
coverage, we extend $M_{\text{ref}}$ itself, through its extension hooks or an
audited extension suitable for upstreaming, or we compose a second, explicit
reference model for that construct. Either way, the extension joins the
human-audited TCB, and the theorem statement does not change. We never exempt
a construct from correspondence while presenting it as correspondence-checked:
an exemption would leave bugs in $M_{\text{anneal}}$'s rules for that
construct unchecked while CI still passes. If a construct is ever deliberately
left without a reference, it must be surfaced as trusted, human-audited
semantics rather than as correspondence-checked semantics.

### 4.3 Program representation and translation ($\tau_{\text{prog}}$)

To compare how $M_{\text{anneal}}$ and $M_{\text{ref}}$ execute "the same
program," the theorem must either:

1. **Share the exact same MIR syntax type** between $M_{\text{anneal}}$ and
   $M_{\text{ref}}$, or
2. **Translate programs** via a trusted translation function
   $\tau_{\text{prog}}$.

If $\tau_{\text{prog}}$ is buggy, the correspondence theorem can become useless:

- **Partiality fail-open:** If $\tau_{\text{prog}}(p)$ is partial (returning
  `Option Prog_ref`) and the theorem is conditioned on
  $\tau_{\text{prog}}(p) = \mathsf{some}\;p_{\text{ref}}$, then returning `none`
  on difficult constructs makes the theorem hold vacuously. Any program that is
  $\mathsf{WellFormed}_{\text{anneal}}$ must be guaranteed to translate.
- **Collapsing or constant translation:** If $\tau_{\text{prog}}$ maps multiple
  programs to a trivial no-op program while a corresponding output map hides the
  difference, the theorem proves nothing about the original program.
- **Semantic laundering:** Even a one-to-one AST translation can silently
  rewrite an unsafe operation into a safe one (for example, translating an
  unchecked arithmetic operator in $M_{\text{anneal}}$ to a wrapping operator in
  $M_{\text{ref}}$, or synthesizing storage/cleanup instructions that were not
  present in the source MIR).

Round-trip invertibility, such as a decoder that recovers every source program
from its translation, rules out collapsing distinct programs onto a trivial
default. It does not by itself rule out semantic laundering. A translation that
permutes operators bijectively still round-trips: if the encoder maps `.add` to
the reference's `.addUnchecked` and `.addUnchecked` to `.add`, and the decoder
swaps them back, every program decodes exactly, yet the theorem now describes a
different reference program.

Anneal therefore keeps semantic content out of $\tau_{\text{prog}}$. In
Anneal's three-stage pipeline ([`docs/architecture.md`](architecture.md)),
$M_{\text{anneal}}$ is the Stage 2 captured MIR operational semantics in
`trusted/lean/` over which `Trusted.CrateTheorem` is stated, whereas Stage 3's
normalized `StableAst` and weakest-precondition calculi in `theory/` sit above
Stage 2 and are linked to $M_{\text{anneal}}$ by kernel-checked `Abstracts`
backward simulations inside `theory/`. Because $\tau_{\text{prog}}$ translates
between two unnormalized Stage 2 MIR representations, the two models share
operator constructors directly and mirror each statement and terminator
constructor one-to-one, which confines $\tau_{\text{prog}}$ to bookkeeping such
as type-table indexing without giving up Stage 3 normalization. Kernel-checked
constructor-preservation theorems lock each semantic constructor through the
translation, and end-to-end semantic canaries pin the meaning of the shared
constructors: for example, an unchecked addition that overflows must exhibit
UB, whereas a wrapping addition of the same operands must not. The remaining
translation is still kept minimal and audited as part of the TCB.

### 4.4 Behavior representation and projection ($\pi$)

Similarly, to state that $p$ "has the same behavior" in $M_{\text{anneal}}$ and
$M_{\text{ref}}$, the theorem must either:

1. **Use the exact same representation of observable program behavior** in both
   semantics, or
2. **Project or translate behaviors** through a trusted function $\pi$.

A flawed $\pi$ function can silently hollow out the theorem in several ways:

- **Outcome erasure:** If $\pi$ projects outcomes to `Unit`, a constant, or an
  echo of the input arguments, then any two terminating runs trivially "have the
  same behavior" regardless of the values they compute.
- **Bijective value permutations:** Requiring $\pi$ to be bijective rules out
  many-to-one erasure, but a bijection on values alone can still permute
  distinct concrete results (for example, mapping $v \mapsto v \oplus 1$ or
  swapping two output fields) if the two sides compensate inside their
  respective evaluators.
- **Omitting caller-visible state:** If $\pi$ compares only a scalar return
  slot while projecting away caller-visible memory or mutable reference targets,
  a function that corrupts caller memory while returning the expected integer
  passes the behavioral check.
- **Over-constraining internal machine state:** Conversely, requiring a strict
  bijection between full *internal* execution states ($S_{\text{anneal}}$ and
  $S_{\text{ref}}$) is too rigid when the two models use different internal
  representations for local storage, allocation identifiers, or uninitialized
  padding bytes.

The clean separation is to keep internal machine states private to the
simulation proof while making the **observable behavior representation**
(covering termination vs. unwinding vs. divergence, return values, and
caller-visible memory effects) shared directly—or related by a simple,
structure-preserving bijection accompanied by concrete input-output tests.

### 4.5 All-prefix safety, productivity, and nondeterminism

The theorem's definition of well-formedness and behavior must also account for
non-terminating and nondeterministic executions:

- **All-prefix safety (not return-only safety):** If well-formedness only
  inspects completed returns, a program that triggers UB on step 3 and enters an
  infinite loop on step 4 has no completed returns and would be judged
  vacuously well-formed. Both $\mathsf{WellFormed}_{\text{anneal}}$ and
  $\mathsf{WellFormed}_{\text{ref}}$ must require that *every reachable finite
  execution prefix* avoids `undefined` and `unsupported`.
- **No silent stuck states (productivity):** If $M_{\text{ref}}$ represents
  steps relationally and an unmodeled or invalid state simply has no outgoing
  transitions (rather than stepping to an explicit fault outcome), universal
  claims over all executions in $M_{\text{ref}}$ hold vacuously. Every
  non-terminal state in both models must step productively to either a successor
  state or an explicit failure outcome.
- **Demonic nondeterminism:** When $M_{\text{ref}}$ models nondeterministic
  choices (such as memory allocator addresses),
  $\mathsf{WellFormed}_{\text{anneal}}(p, q)$ must imply that *all* permitted
  executions in $M_{\text{ref}}$ are well-formed and that each of their
  behaviors is a behavior of $M_{\text{anneal}}$. If $M_{\text{anneal}}$ is
  deterministic, it cannot arbitrarily pick one lucky choice when the
  program's branch or safety depends on that choice; the correspondence
  theorem automatically forces $M_{\text{anneal}}$ to either return
  `unsupported` on operations that observe the nondeterminism or model the
  nondeterministic choice itself.

### 4.6 Guarding against antecedent collapse and outcome misclassification

Because both `undefined` and `unsupported` falsify
$\mathsf{WellFormed}_{\text{anneal}}(p, q)$, the correspondence theorem by
itself does not prevent two bugs in $M_{\text{anneal}}$:

1. **Antecedent collapse (vacuous `unsupported` or `undefined`):** If a pull
   request claims to add support for a MIR construct, but a bug in
   $M_{\text{anneal}}$ causes every execution of that construct to return
   `unsupported` (or `undefined`), the correspondence theorem still holds
   vacuously.
2. **`undefined` vs. `unsupported` swaps:** If $M_{\text{anneal}}$ returns
   `unsupported` on a program that actually triggers UB (masking a real bug as
   "unmodeled"), or returns `undefined` on a valid program that uses an
   unimplemented construct (falsely reporting UB on safe code), the
   correspondence theorem still holds because both outcomes falsify the
   antecedent.

To close this gap and ensure future additions cannot regress into vacuity or
misclassification, incremental additions to $M_{\text{anneal}}$ must be paired
with concrete canary tests in CI:

- **Positive execution canaries:** Concrete programs exercising each supported
  MIR construct and proving that $M_{\text{anneal}}$ evaluates them to the
  expected `ok` outcome (witnessing that $\mathsf{WellFormed}_{\text{anneal}}$
  is inhabited and non-vacuous for that feature).
- **Negative `undefined` canaries:** Concrete programs exercising each modeled
  UB condition and proving that $M_{\text{anneal}}$ evaluates them to
  `undefined` (not `ok` and not `unsupported`).
- **Negative `unsupported` canaries:** Concrete programs exercising unmodeled
  constructs and proving that $M_{\text{anneal}}$ evaluates them to
  `unsupported` (not `ok` and not `undefined`) until support for those
  constructs is intentionally added.

Canaries alone cannot cover a supported domain. For a construct parameterized
by operators, integer widths, signedness, or modes, one positive canary
witnesses a single execution: an implementation could special-case that
program and return `unsupported` for the rest of the claimed domain while the
correspondence theorem and every canary still pass. Anneal therefore pairs
concrete boundary-case canaries with a staged support gate in $M_{\text{ref}}$
and fault equivalence along corresponding executions.

Because an imported reference interpreter may already evaluate constructs that
$M_{\text{anneal}}$ has not yet enabled (or that $M_{\text{anneal}}$
conservatively rejects under Section 4.1), $M_{\text{ref}}$'s correspondence
wrapper applies an explicit, human-audited support gate that reports
`unsupported` outside the currently claimed support domain and delegates every
construct inside that domain to the reference interpreter. Along corresponding
executions (indexed by any shared nondeterministic choice trace $\sigma$), each
model must reach the same fault classification
$k \in \{\mathsf{undefined}, \mathsf{unsupported}\}$. When both models are
deterministic on the supported domain, this per-execution fault correspondence
reduces to bidirectional fault-reachability equivalence for every program $p$
and input query $q$:

$$
\mathsf{Reaches}_{\text{anneal}}(p, q, \mathsf{fault}\;k) \iff
\mathsf{Reaches}_{\text{ref}}(p, q, \mathsf{fault}\;k)
\quad \text{for } k \in \{\mathsf{undefined}, \mathsf{unsupported}\}
$$

When a model permits nondeterministic choices, comparing fault outcomes along
corresponding executions (rather than merely existential reachability over $p$
and $q$) ensures that $M_{\text{anneal}}$ cannot report `unsupported` on one
branch merely because a different nondeterministic branch of the same input
triggers `unsupported`, and cannot swap `undefined` and `unsupported` on any
execution.

Because fault equivalence quantifies over all inputs and corresponding
executions inside the gated reference domain, it forbids $M_{\text{anneal}}$
from returning `unsupported` (or `undefined`) on any execution where
$M_{\text{ref}}$ succeeds, and from reporting one failure outcome where
$M_{\text{ref}}$ reports the other. $M_{\text{ref}}$'s staged support gate
thereby serves as the single audited support predicate: $M_{\text{anneal}}$
reports `unsupported` if and only if $M_{\text{ref}}$'s gated semantics does, so
widening the supported domain means widening the coverage that $M_{\text{ref}}$
exposes to the theorem, under human review. The CI canaries then guard that
staged support predicate itself against collapse. For each parameterized
construct, they cover positive and boundary cases across its parameters (such as
each integer width and signedness, the extremes of each operand range, a zero
divisor, or a shift amount equal to the bit width), proving that concrete
executions reach `ok` or `undefined` (never `unsupported`) so that a staged gate
or implementation narrower than the claimed domain fails CI.
