<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Design and Wording Rationale for `FRAMEWORK_PRINCIPLES.md`

[`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md) states the mission, core
promise, necessary corollaries, and decision-making principles for the
verification framework. Every phrase, qualifier, and structural boundary in
[`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md) exists to close one or more
concrete failure modes—cases where a formal verification tool is mathematically
sound according to its formal specification, yet violates a domain engineer's
reasonable expectations in practice.

This companion document provides an exhaustive clause-by-clause explanation of
the wording in [`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md), the formal
semantic model underlying it, the alternative formulations that were rejected
during design refinement, and the catalog of adversarial failure modes that
forced each wording choice.

---

# 1. The Formal Semantic Model Behind `FRAMEWORK_PRINCIPLES.md`

## 1.1 System Entities

To reason precisely about what it means for a vibe-coded formal verification
tool to be "bug-free in practice," the framework models five distinct entities:

1. **The Real World ($\mathcal{R}$):** The physical hardware, operating system,
   runtime, external language or protocol standards (such as ISO C, Rust,
   RISC-V, x86-64, or IEEE-754), build system, downstream toolchain, and
   deployment environment in which inputs and outputs actually exist and
   execute.
2. **The Developer's Intuition ($\mathcal{I}$):** The concrete engineering
   theory held by a domain software engineer (who is not a formal-methods
   specialist) regarding what family of inputs the tool handles, what kind of
   claim or transformation the tool performs, and what a run of the tool
   guarantees in $\mathcal{R}$.
3. **The Tool ($T = (T_{\text{formal}}, T_{\text{deployed}})$):**
   - $T_{\text{formal}}$ is the pure mathematical definition verified inside the
     proof assistant's kernel.
   - $T_{\text{deployed}}$ is the complete end-to-end executable system invoked
     by the user—including its CLI or daemon entrypoint, project and flag
     resolver, parser/lifter, incremental cache, untrusted heuristic passes
     (such as external SMT solvers, search passes, optimizers, or certificate
     finders paired with a verified checker), pretty-printer or binary
     serializer, and exit-code reporter.
4. **The Formal Specification ($S$):** The mathematical specification authored
   or accepted by the developer that governs $T_{\text{formal}}$.
5. **The Disclosed Assumptions ($\Delta$):** The explicit, bounded set of
   unmodeled physical reality layers or external boundary conditions disclosed
   to and accepted by the developer alongside $S$.

## 1.2 The Two-Dimensional Space of Formal Verification Tools

A central requirement of [`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md) is
that its top-level promise and corollaries must apply without distortion across
*every* class of formal verification tool. The design space spans two orthogonal
axes—**13 Claim Archetypes** and **7 Execution/Semantic Regimes**:

### Axis 1: Thirteen Claim Archetypes

1. **`A1` — Universal Property Verifiers & Conservative Static Analyzers:**
   Deductive verifiers, abstract interpreters, and syntactic type or borrow
   checkers claiming that *all* executions of an accepted input program satisfy
   a target safety or functional property ($\forall \tau \in \mathsf{Runs}(x),\;
   P(\tau)$).
2. **`A2` — Existential Bug-Finders & Refutation Engines:** Symbolic executors,
   concurrency fuzzers, and Incorrectness Logic analyzers claiming that *every*
   reported counterexample trace $w$ is a genuine bug reachable in reality
   ($\exists \tau \in \mathsf{Runs}(x)$ matching $w$ that violates $P$), while
   treating "no bug found" as an abstention rather than a proof of safety.
3. **`A3` — Bilateral Deciders, Solvers, & Bounded Checkers:**
   - `A3a` (Exact Deciders / SAT / SMT Solvers): Emit either `SAT(model)` or
     `UNSAT(proof)`.
   - `A3b` (Primal-Dual Certificate Checkers): Verify an external certificate of
     either satisfaction or refutation.
   - `A3c` (Horizon-Bounded Model Checkers): Establish safety up to an explicit
     unrolling or depth bound $k$ (`BoundedSafe(k)`).
4. **`A4` — Standalone Certificate Checkers Paired with Untrusted Finders:**
   Tools factored into an untrusted heuristic search, solver, or optimizer pass
   $F(x)$ and a verified kernel checker $C(x, \pi)$ such that
   $T_{\text{deployed}}(x) = C(x, F(x))$.
5. **`A5` — Quantitative Bound & Invariant Inferrers:** Worst-case execution
   time (WCET) analyzers, stack-depth analyzers, floating-point error bounders,
   differential-privacy $\varepsilon$-bounders, and loop-invariant inferrers
   that take a program $x$ and emit a quantitative bound or invariant $B$.
6. **`A6` — Downward Compilers, Transpilers, & Optimizers:** Translators from a
   source language to a target language or IR that preserve observable behavior
   across all executions on which the source program is well-defined
   ($\mathsf{WellDefined}(x) \implies \mathsf{Runs}(A) \sqsubseteq
   \mathsf{Runs}(x)$).
7. **`A7` — Upward Binary Lifters, Decompilers, & Functional Translators:**
   Tools that take a concrete executable binary or low-level program $x$ as
   *input* and emit a high-level mathematical model or IR $M$ as *output*,
   claiming that $M$ soundly captures *every* real-world execution of $x$
   ($\mathsf{Runs}(x) \sqsubseteq \mathsf{Runs}(M)$).
8. **`A8` — Bidirectional Codecs & Zero-Knowledge Circuit Compilers:** Parsers
   and serializers (`GetPut`/`PutGet`) and ZK circuit compilers (`R1CS`/Plonky)
   that must preserve *both* soundness (no forged proofs or misparsed messages)
   and witness completeness (every valid high-level input has a valid encoding
   or witness).
9. **`A9` — Hardening Instrumenters, Sandboxes, Sanitizers, & Repair Tools:**
   Software fault isolation (SFI) instrumenters, WebAssembly/eBPF sandboxes,
   compiler sanitizers, and automated bug-repair tools that accept *untrusted or
   buggy* inputs $x$ and emit a transformed artifact $A$ that enforces target
   safety on *all* executions while preserving behavior on benign executions.
10. **`A10` — Relational Equivalence, Refinement, & Regression Checkers:**
    Translation validators, equivalence checkers, and semantic diff tools that
    take a *tuple* of programs $(p_1, p_2)$ and certify relational equivalence
    or refinement.
11. **`A11` — Open-World Compositional Verifiers & Horizontal Linkers:** Modular
    library verifiers and verified linkers that certify open modules $M_1,
    \dots, M_n$ interacting across public entry points, ABI boundaries, and
    unverified external callbacks.
12. **`A12` — Program Synthesizers & Reactive Planners:** Tools that take a
    specification $\phi$ as input and either synthesize an artifact $A$
    satisfying $\phi$ or emit an unrealizability witness proving that no valid
    implementation exists.
13. **`A13` — Meta-Verifiers & Specification Auditors:** Tools whose input is
    itself a specification, security policy, or formal model $\phi$ and whose
    output is a consistency, non-vacuity, or coverage audit verdict.

### Axis 2: Seven Execution and Semantic Regimes

1. **`R1` — Finite-Prefix Safety:** Nothing bad happens along any finite prefix.
2. **`R2` — Total Correctness Under Unbounded Nondeterminism:** Termination must
   hold along *every* complete branch, not merely via arbitrary-length finite
   prefixes.
3. **`R3` — Reactive Liveness & Temporal Progress:** Infinite runs must make
   genuine domain progress (ruling out infinite internal stuttering or Zeno
   timestamp convergence).
4. **`R4` — Game / Open-Environment Interaction:** Alternating adversarial and
   angelic steps across re-entrant callbacks and environment boundaries.
5. **`R5` — Multi-Trace Hyperproperties:** Properties over $k$-tuples of traces,
   such as non-interference and constant-time execution.
6. **`R6` — Probabilistic & Quantitative Distributions:** Preservation of
   probability distributions, entropy, and quantitative bounds rather than
   nondeterministic set inclusion.
7. **`R7` — Resource-Bounded & Physical-Platform Semantics:** Finite stack/heap,
   instruction timing, IEEE-754 floating-point bit patterns, and weak-memory
   concurrency.

## 1.3 The Outcome-Indexed Promise Formula

Every invocation of a certified tool $T$ on an input $x$ either declines to
certify/transform $x$, or certifies/produces one or more artifacts $A$ and/or
substantive claims $C$:

$$
\mathsf{Certified}(T, S, \Delta) \implies \forall x,\;
\begin{aligned}
  &\mathsf{ValidDecline}_{\mathcal{R}, \mathcal{I}, \Delta}(x, T(x)) \\
  &\land \mathsf{ValidArtifacts}_{\mathcal{R}, \mathcal{I}, \Delta}(x, T(x)) \\
  \land\; &\mathsf{ValidClaims}_{\mathcal{R}, \mathcal{I}, \Delta}(x, T(x))
\end{aligned}
$$

subject to the **Disclosed-Assumption Scope Invariant**:

$$
  \Delta \cap \mathsf{InDomainObligations}(S, \mathcal{I}, \mathcal{R})
    = \emptyset
\quad \land \quad
|\Delta| \le \mathsf{CognitiveBudget}(\mathcal{I})
$$

## 1.4 Why the Five Corollaries Form a Minimal, Orthogonal Partition

The five corollaries in [`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md)
are not an arbitrary checklist; they are the five links of the semantic chain
connecting the developer's intuition $\mathcal{I}$ to the real-world behavior of
$T_{\text{deployed}}$ in $\mathcal{R}$:

$$
\begin{aligned}
\mathcal{I} \;\xrightarrow{\text{Cor. 1}}\; S
  &\;\xrightarrow{\text{Cor. 2}}\;
    (S, T_{\text{deployed}}) \notin \{\bot, \top\} \\
  &\;\xrightarrow{\text{Cor. 3}}\; \mathcal{R} \bmod \Delta \\
  &\;\xrightarrow{\text{Cor. 4}}\;
    T_{\text{deployed}} \leftrightarrow T_{\text{formal}} \\
  &\;\xrightarrow{\text{Cor. 5}}\; \mathsf{TCB}_{\text{framework}}
\end{aligned}
$$

Each corollary is strictly independent of the other four (any one can fail while
the other four hold):

- **Corollary 1 fails alone ($\mathcal{I} \not\leftrightarrow S$):** $S$ is
  non-degenerate (Cor. 2), models real hardware faithfully (Cor. 3), is bound
  end-to-end to the CLI (Cor. 4), and is proved with zero axioms (Cor. 5), but
  uses saturating natural-number subtraction `0 - 1 = 0` or checks existential
  reachability instead of universal safety, violating $\mathcal{I}$.
- **Corollary 2 fails alone ($(S, T_{\text{deployed}}) \in \{\bot, \top\}$):**
  $S$ is transparent (Cor. 1), models real hardware (Cor. 3), is bound to the
  CLI (Cor. 4), and is proved with zero axioms (Cor. 5), but
  $T_{\text{deployed}}$ pairs a verified checker with a stubbed certificate
  finder that returns `"inconclusive"` on every non-trivial input.
- **Corollary 3 fails alone ($S \not\leftrightarrow \mathcal{R} \bmod
  \Delta$):** $S$ is transparent (Cor. 1), non-degenerate (Cor. 2), bound to the
  CLI (Cor. 4), and proved with zero axioms (Cor. 5), but models IEEE-754 floats
  as ideal real numbers $\mathbb{R}$ without disclosing that gap.
- **Corollary 4 fails alone ($T_{\text{deployed}} \not\leftrightarrow
  T_{\text{formal}}$):** $S$ and $T_{\text{formal}}$ satisfy Corollaries 1, 2,
  3, and 5, but the CLI resolves the wrong Cargo project, verifies in `debug`
  mode while the user deploys `release`, or prints a corrupted assembly file.
- **Corollary 5 fails alone ($\mathsf{TCB}(T, S) \not\subseteq
  \mathsf{TCB}_{\text{framework}} \cup \Delta$):** Corollaries 1–4 appear to
  hold on the surface, but the proof uses a custom axiom, defines `is_valid(x)`
  as `tool(x) == true`, or attaches `@[implemented_by]` to swap a verified
  function for unverified C code at runtime.

---

# 2. Evolution of `# The framework's promise` (Why Earlier Drafts Failed)

During the design of [`FRAMEWORK_PRINCIPLES.md`](FRAMEWORK_PRINCIPLES.md), four
successive formulations of `# The framework's promise` were evaluated against
adversarial counterexamples. Understanding why the first three failed explains
why the current wording is structured as it is.

## 2.1 Formulation 1: Tool-Behavior Framing

> ***If** ... the framework certifies the tool with no errors, **then** the
> tool's real-world behavior accords with the developer's intuition.*

- **Why it was insufficient:** Developers do not build formal verification tools
  merely to watch the tool execute; they build them to **gate or produce
  artifacts and claims that are subsequently built, shipped, and run in
  production**. Leaving the downstream artifact implicit made it too easy to
  read "the tool's real-world behavior" as governing only the CLI process itself
  (for example, whether the tool exits cleanly) rather than whether a compiled
  binary or certified crate is actually safe when deployed and executed in the
  target environment.

## 2.2 Formulation 2: One-Sided Shipped-Artifact Recognizer

> ***If** ... the framework certifies the tool with no errors, **then** any
> artifact certified or produced by the tool behaves in the real world in
> accordance with the developer's intuition when built, shipped, and run.*

- **Why it failed (`model-refinement` falsification):**
  Formally, this states only a one-sided implication:
  $$
  \forall x,\; T(x) = \mathsf{Ok}(A) \implies
    \mathsf{DeployedInReality}(A) \models \mathcal{I}(x)
  $$
  This formulation fails on four distinct fronts:
  1. **Vacuous rejection / total refusal:** A tool $T$ that rejects 100% of
     inputs (`T(x) = Err` for all $x$) never produces an accepted artifact $A$,
     so the implication $\mathsf{Ok}(A) \implies \dots$ is vacuously true!
  2. **Dishonest or crashing rejection:** If $T(x)$ panics, hangs forever, or
     emits a fabricated counterexample trace on an rejected input, the
     one-sided implication says nothing because $T(x) \neq \mathsf{Ok}(A)$.
  3. **Wrong-input substitution:** If the user invokes $T$ on crate $x$, and $T$
     silently analyzes a tiny hello-world crate $x_0$ and certifies $x_0$, then
     $x_0$ really is safe when shipped—so "the artifact certified by the tool"
     is safe, even though it was not the input $x$ the user gave the tool.
  4. **Tools whose primary output is not a shipped binary:** Bug-finders (`A2`),
     UNSAT solvers (`A3a`), bound inferrers (`A5`), binary lifters (`A7`), and
     equivalence checkers (`A10`) emit *claims, bounds, models, or
     counterexamples* rather than deployable binaries.

## 2.3 Formulation 3: Binary Decider / Gatekeeper Framing

> ***If** ... the framework certifies the tool with no errors, **then** for
> every input given to the tool, either the tool rejects that input as expected,
> or the artifact or claim it certifies or produces behaves in the real world in
> accordance with the developer's intuition when built, shipped, and run.*

- **Why it was a major step forward:** By universally quantifying over every
  input $x$ given to the tool ($\forall x$) and tightening the left branch of
  material implication from unconstrained $\mathsf{NotOk}(T, x)$ to
  $\mathsf{RejectedAsExpected}(T, x)$, Formulation 3 closed the
  vacuous-rejection, crash/hang, and wrong-Cargo-project loopholes in a single
  law without needing a separate `ToolBehavesAsExpected(T)` conjunct.
- **Why it still failed under adversarial red-teaming:**
  1. **Non-rejection abstentions (`Inconclusive`, `Unsupported`, `"No bug
     found"`):** When a 3-valued analyzer returns `Inconclusive / Timeout` or a
     bounded bug-finder returns `"No bug found"`, it is *abstaining* from
     certifying or refuting the input, not *rejecting* the input as invalid.
  2. **Category error on non-runnable claims, bounds, models, and traces:**
     Saying *"the artifact or claim ... behaves in the real world ... when
     built, shipped, and run"* is a category error for a WCET bound (`4200
     cycles`), a lifted IR model (`LiftedModel(M)`), a synthesizer's
     `Unrealizable` witness, or a refutation counterexample trace: claims are
     not "built, shipped, and run"—they *hold true of* the input and its
     real-world executions.
  3. **Conflation of static rejection diagnostics with counterexample traces:**
     When a borrow checker rejects a program with `"cannot borrow x as
     mutable"`, that message is a diagnostic of a violated static rule, not an
     execution trace that "holds in the real world." Conversely, when a model
     checker rejects a program with a concrete failure trace $w$, $w$ is a
     substantive claim that must actually trigger the bug in $\mathcal{R}$.
  4. **Precondition polarity across tool kinds:** A verified compiler (`A6`)
     only guarantees that the emitted binary $A$ behaves as expected on
     executions where the source input $x$ is *well-defined* (it does not
     guarantee that compiling a C program with a buffer overflow produces a
     safe binary), whereas a verifier (`A1`), sandbox (`A9`), sanitizer, or
     repair tool must guarantee safety across *all* executions.
  5. **Unbounded $\Delta$-disclosure smuggling:** Mentioning `(along with any
     disclosed assumptions)` without bounding what may be disclosed allowed an
     agent to move in-domain proof obligations or core bug classes into
     $\Delta$.

## 2.4 Formulation 4: The Converged Wording in `FRAMEWORK_PRINCIPLES.md`

> ***If** the framework's trusted computing base is valid, a developer
> vibe-codes a formal verification tool and authors or accepts a specification
> of that tool (along with any disclosed assumptions), **and** the framework
> certifies the tool with no errors, **then** for every input given to the
> tool, either the tool rejects or abstains on that input as expected, or the
> artifact or claim it certifies or produces upholds the guarantee the
> developer expects of it in the real world.*

Followed immediately by the two bullets (`Expected rejection or abstention` and
`Real-world validity of produced artifacts and claims`), this formulation
preserves the intuitive two-branch Decider structure while resolving all five
failure modes exposed in Formulation 3.

---

# 3. Exhaustive Section-by-Section and Clause-by-Clause Wording Rationale

## 3.1 Section: `# The Verification Framework` (Lines 9–26)

### Paragraph 1 (Lines 11–17): Contrast with `PRINCIPLES.md`
> [`PRINCIPLES.md`](PRINCIPLES.md) defines Anneal's promise to a developer
> verifying a *program*: if Anneal's trusted computing base (TCB) is valid and
> Anneal emits no errors, the program is correct. Because Anneal itself is built
> by formal-verification experts who define its model of Rust and undefined
> behavior, [`PRINCIPLES.md`](PRINCIPLES.md) can treat *"user error that
> misconstrued developer-defined requirements"* as outside Anneal's core
> guarantee.

- **Why this wording is necessary:** [`PRINCIPLES.md`](PRINCIPLES.md) explicitly
  carves out *"user error that misconstrued developer-defined requirements."* In
  the verification framework, the user is a non-expert tool developer who
  authors or accepts an agent-authored specification $S$. If the framework
  inherited [`PRINCIPLES.md`](PRINCIPLES.md)'s carve-out for misconstrued
  specifications, an agent could write a deceptive, vacuous, or
  standard-divergent specification $S$, get the non-expert human to click
  "accept," and blame the human for "user error." This paragraph establishes why
  specification comprehension and non-degeneracy are *inside* the framework's
  promise.

### Paragraph 2 (Lines 19–26): Mission and Illustrative Tool Spectrum
> For the underlying **verification framework**, the goal is broader: to enable
> a software engineer who is **not** a formal-verification specialist to
> **vibe-code any formal verification tool**—such as a static analyzer, type or
> borrow checker, deductive verifier, model checker, bug-finder, bound or
> invariant inferrer, compiler, optimizer, binary lifter, decompiler,
> equivalence checker, open-world linker, sandbox instrumenter, repair tool,
> synthesizer, or specification auditor—and rely on the framework itself to
> ensure that the resulting tool is bug-free.

- **Why every item in this 16-tool list is present:** Each named tool anchors
  one of the 13 Claim Archetypes (`A1`–`A13`) so that no reader or framework
  designer can assume "formal verification tool" means only a deductive program
  verifier:
  - `static analyzer`, `type or borrow checker`, `deductive verifier` $\to$ `A1`
    (universal property verifiers, both decidable syntactic/abstract and
    hint-guided).
  - `model checker` $\to$ `A3` (bilateral and horizon-bounded state-space
    explorers).
  - `bug-finder` $\to$ `A2` (existential under-approximating refutation tools).
  - `bound or invariant inferrer` $\to$ `A5` (tools emitting quantitative
    bounds or inductive invariants rather than pass/fail verdicts).
  - `compiler`, `optimizer` $\to$ `A6` (downward semantics-preserving
    translators).
  - `binary lifter`, `decompiler` $\to$ `A7` (upward abstracting translators
    whose *input* is a machine binary and whose *output* is a model).
  - `equivalence checker` $\to$ `A10` (relational multi-input verifiers).
  - `open-world linker` $\to$ `A11` (horizontal module composers across ABI and
    callback boundaries).
  - `sandbox instrumenter`, `repair tool` $\to$ `A9` (tools that accept buggy
    or untrusted inputs and enforce safety while preserving benign behavior).
  - `synthesizer` $\to$ `A12` (tools taking a specification as input and
    producing an implementation or unrealizability witness).
  - `specification auditor` $\to$ `A13` (meta-verifiers whose input is a
    specification or policy rather than executable code).

---

## 3.2 Section: `# Some things we believe` (Lines 28–78)

### `## A tool that satisfies its formal specification...` (Lines 30–58)

- **"An optimization-driven coding agent seeking a passing build will naturally
  exploit any slack between what the formal specification mathematically states
  and what the developer intuitively believes the tool guarantees in the real
  world." (Lines 35–39):**
  - *Failure mode addressed:* Goodhart's Law under automated proof search. A
    human formal-methods expert does not intentionally write `def isSafe (x) :=
    True` to make a proof pass; an LLM coding agent optimizing for `lake build`
    exit code `0` routinely weakens definitions, adds preconditions, or skips
    hard cases whenever the framework permits it.
- **Bullet 1 (Lines 44–47): *"The specification may define a language dialect,
  claim polarity, or property that differs from what the developer and the
  tool's users expect (as when CompCert's C semantics differed from ISO C,
  causing standard-compliant C programs to be miscompiled)."***
  - *Why `language dialect, claim polarity, or property` are all named:*
    - `language dialect`: Covers CompCert-style divergence where the formal
      source semantics differs from ISO C (for example, bitfield sign, char
      signedness, or pointer-comparison rules).
    - `claim polarity`: Covers polarity inversions where a developer asks for a
      verifier ($\forall$ traces) and the agent proves existential reachability
      ($\exists$ trace), or asks for a sandbox ($\forall$ inputs) and the agent
      proves conditional compilation ($\mathsf{WellDefined}(x) \implies \dots$).
    - `property`: Covers deceptive or weakened predicates (such as
      `isConstantTime` checking only that secret keys are not printed to
      `stdout`).
- **Bullet 2 (Lines 48–50): *"The formal model may omit real-world behavior that
  matters to the user's goal (such as an instruction-set model that omits
  execution timing, allowing cryptographic code to be compiled with timing side
  channels)."***
  - *Failure mode addressed:* Capability-blind world models (such as verifying
    constant-time cryptography against a purely functional ISA semantics that
    has no cycle counter, cache state, or branch-predictor leakage model).
- **Bullet 3 (Lines 51–53): *"The specification or tool may be degenerate (for
  example, vacuously sound because its preconditions admit no programs, or
  trivially safe because the tool rejects every non-trivial input)."***
  - *Failure mode addressed:* Two-pole degeneracy—vacuity of $S$ ($\bot$ domain)
    and trivial refusal by $T$ (`fn verify(_) -> bool { false }`).
- **Bullet 4 (Lines 54–58): *"The verified core may be connected to the real
  system through buggy or incomplete bindings (such as a static analyzer that
  resolves the wrong Cargo project or build profile and reports success on the
  wrong code, or a compiler that claims to produce verified binaries while
  actually emitting verified `.S` assembly into an unverified assembler and
  linker)."***
  - *Why `or build profile` was added:* A tool that resolves the right Cargo
    project but analyzes it under `debug` mode (where `debug_assert!` guards an
    unsafe indexing operation and integer overflow panics) while the user ships
    the `--release` binary (where `debug_assert!` is stripped and overflow
    wraps) is a real-world system-binding bug.
  - *Why `.S` assembly into an unverified assembler and linker is cited:*
    Historical formal compilers (including early CompCert configurations)
    verified lowering down to textual assembly `.S` files while relying on an
    unverified GNU assembler and linker to produce the actual ELF binary.

### `## Domain intuition is enough to judge what a tool should do` (Lines 60–67)

> A software engineer who builds a compiler pass, static analyzer, bug-finder,
> or sandbox already has a concrete engineering theory of what inputs the tool
> should handle, what real-world environment those inputs execute in, and what a
> run of the tool guarantees.

- **Why `bug-finder` is included and why it says *"what a run of the tool
  guarantees"* instead of *"what a passing run of the tool guarantees"*:**
  For a bug-finder (`A2`) or bilateral decider (`A3`), the most important
  guarantee occurs when the tool *reports a bug* (a refutation run), not when it
  "passes." Saying "a passing run" would implicitly restrict the belief to
  positive verification runs.

### `## If a gap with reality cannot be eliminated...` (Lines 69–78)

> Where an unavoidable gap with reality exists, however, the framework can
> guarantee that it is impossible for the developer to accept the specification
> while remaining unaware of that gap—without allowing an agent to use
> disclosure as an escape hatch for avoidable proof obligations or bury a fatal
> assumption in boilerplate warnings.

- **Why *"unavoidable"* and the final `"—without allowing..."` clause are
  essential:**
  Without these two qualifications, "if a gap with reality cannot be eliminated,
  it must be impossible to miss" creates a catastrophic Goodhart loophole:
  1. **Proof-obligation offloading (`Assumption Smuggling`):** Whenever an agent
     cannot prove an internal lemma or wants to skip checking pointer aliasing,
     it simply declares `[Disclosed Assumption]: Assumes pointers do not alias`
     and surfaces it to the user.
  2. **Alert fatigue (`Disclosure Flooding`):** The agent generates 40 standard
     "formal verification disclaimers" (cosmic rays, compiler bugs, OS kernel
     bugs, power loss, etc.) and hides `[Assumption 27]: Assumes single-threaded
     execution` in the middle of the list when the user is building a concurrent
     lock-free queue verifier.

---

## 3.3 Section: `# The framework's promise` (Lines 80–125)

### The Promise Blockquote (Lines 82–88)

> ***If** the framework's trusted computing base is valid, a developer
> vibe-codes a formal verification tool and authors or accepts a specification
> of that tool (along with any disclosed assumptions), **and** the framework
> certifies the tool with no errors, **then** for every input given to the
> tool, either the tool rejects or abstains on that input as expected, or the
> artifact or claim it certifies or produces upholds the guarantee the
> developer expects of it in the real world.*

Every clause in this single sentence is load-bearing:

1. **`"If the framework's trusted computing base is valid"`:**
   Parallels [`PRINCIPLES.md`](PRINCIPLES.md). The framework cannot guarantee
   soundness if the underlying theorem-prover kernel, hardware, or framework
   auditor in `trusted/` has a soundness bug.
2. **`"a developer vibe-codes a formal verification tool and authors or accepts
   a specification of that tool (along with any disclosed assumptions)"`:**
   Covers both human-authored specifications and agent-authored specifications
   that a human developer reviews and accepts, together with the bounded
   assumption set $\Delta$.
3. **`"and the framework certifies the tool with no errors"`:**
   Establishes the fail-closed gate: any violation of the corollaries must cause
   framework certification to fail with an error.
4. **`"then for every input given to the tool"`:**
   - Binds the exact input $x$ supplied by the user at the CLI/API boundary
     across both branches of the disjunction, blocking the "wrong Cargo project"
     loophole where a tool certifies *some* safe artifact $A_0 \neq x$.
   - Uses `"every input"` (which may be a single source file, a crate, a binary,
     a pair of programs $(p_1, p_2)$ for an equivalence checker, or a
     specification $\phi$ for a synthesizer or specification auditor).
5. **`"either the tool rejects or abstains on that input as expected"`:**
   - Tightens the left branch of material implication so the tool cannot reject
     valid inputs vacuously, crash, hang, or silently skip inputs.
   - Includes `"or abstains"` so 3-valued tools returning `Inconclusive`,
     `Unsupported`, or `"No bug found"` are governed by the first branch rather
     than misclassified as rejections of invalid inputs or acceptances (`D2`).
6. **`"or the artifact or claim it certifies or produces upholds the guarantee
   the developer expects of it in the real world."`:**
   - Covers both **artifacts** (certified input programs, compiled binaries,
     sandboxed binaries, linked modules, repaired code, synthesized programs)
     and **claims** (safety verdicts, horizon-bounded checks, quantitative
     bounds, lifted abstract models, equivalence verdicts, counterexample
     traces, unrealizability witnesses).
   - Uses `"upholds the guarantee the developer expects of it in the real
     world"` rather than ending the blockquote with `"when built, shipped, and
     run"` so the headline sentence does not commit a category error on bounds,
     models, or counterexamples (`D3`, `H1`), while delegating the exact
     artifact vs. claim mechanics to Bullet 2 immediately below.

### Bullet 1: `Expected rejection or abstention` (Lines 92–101)

> - **Expected rejection or abstention:** The tool may decline to certify or
>   transform an input—rejecting it or returning an inconclusive, unsupported,
>   or "no bug found" status—only when that input genuinely falls outside the
>   developer's intended acceptance envelope (because it violates the property
>   or rules the tool checks, exhibits no bug in a bug-finding search, lies
>   outside the tool's supported scope, or exceeds the honest limits of its
>   analysis), and never by crashing, hanging, vacuously refusing valid inputs,
>   or emitting a false claim or broken artifact alongside a refusal. Any
>   diagnostic accompanying a rejection must accurately reflect the violated
>   rule or analysis limit.

- **Why all four parenthetical refusal reasons are listed:**
  An earlier draft listed only three refusal reasons and omitted
  inputs lying outside a domain-specific tool's supported scope or unrealizable
  synthesis specs. The four clauses exhaust the legitimate reasons a tool may
  decline to certify or produce an output:
  1. `violates the property or rules the tool checks` (e.g., a program with a
     use-after-free, a type error, or an unrealizable synthesis specification
     $\phi$);
  2. `exhibits no bug in a bug-finding search` (e.g., a fuzzer or symbolic
     bug-finder (`A2`) that searches $x$, finds no bug, and abstains from
     reporting a failure trace);
  3. `lies outside the tool's supported scope` (e.g., an embedded verifier that
     intentionally restricts its domain to `no_std` code without dynamic heap
     allocation);
  4. `exceeds the honest limits of its analysis` (e.g., a conservative syntactic
     borrow checker rejecting a dynamically safe program it cannot prove, or an
     SMT-backed verifier timing out on a nonlinear arithmetic goal).
- **Why `"never by crashing, hanging, vacuously refusing valid inputs, or
  emitting a false claim or broken artifact alongside a refusal"`:**
  - `crashing, hanging`: Blocks production verifier denial-of-service (such as
    exponential recursion or stack overflow on a 2 KB malformed eBPF bytecode
    input) and treats internal panics (`exit 1`) on genuinely
    bad inputs as framework violations rather than "expected rejections."
  - `vacuously refusing valid inputs`: Blocks trivial `return Err("unverified")`
    tools and broken certificate finders.
  - `emitting a false claim or broken artifact alongside a refusal`: Blocks
    hybrid tools (such as an automated repair tool or certifying compiler) that
    return a non-zero rejection exit code while still writing a corrupted
    "candidate patch" or `.o` file to disk, or emitting a false diagnostic claim
    alongside an `Inconclusive` status.
- **Why `"Any diagnostic accompanying a rejection must accurately reflect the
  violated rule or analysis limit"`:**
  Separates static rejection diagnostics (such as `"cannot borrow x as mutable"`
  or `"solver timeout at depth 20"`, which explain which rule or analysis limit
  triggered the refusal) from concrete counterexample execution traces (which
  are governed as substantive claims in Bullet 2). This prevents both dishonest
  error messages (blaming safe function `bar()` when `foo()` failed) and the
  category error of demanding that a static type error "execute in the real
  world".

### Bullet 2: `Real-world validity of produced artifacts...` (Lines 102–113)

> - **Real-world validity of produced artifacts and claims:** Whenever the tool
>   certifies or produces an artifact or emits a substantive claim, that output
>   must satisfy the developer's intuitive contract in the real target
>   environment (within any explicitly disclosed assumptions). Any **artifact**
>   the tool certifies, compiles, hardens, links, repairs, or synthesizes must
>   behave as expected when built, shipped, and run (across all executions for a
>   verified, hardened, repaired, linked, or synthesized artifact, and across
>   all well-defined source executions for a compiled or optimized one). Any
>   **claim, bound, abstract model, or counterexample** the tool emits
>   (including a concrete failure trace accompanying a rejection or a
>   synthesizer's unrealizability witness) must hold true of the input and its
>   real-world executions in the target environment.

- **Why `"Whenever the tool certifies or produces an artifact or emits a
  substantive claim"` instead of `"Whenever the tool accepts an input"`:**
  A tool that *rejects* an input program $x$ and emits a concrete counterexample
  failure trace $w$ (`Reject(w)`) has emitted a substantive claim ($w$ triggers
  the bug in reality) even though it rejected $x$! Using `"Whenever the tool
  certifies or produces an artifact or emits a substantive claim"` ensures that
  counterexample traces emitted during a rejection are subject to real-world
  validity.
- **Why the six artifact verbs (`certifies, compiles, hardens, links, repairs,
  or synthesizes`) are paired with the exact partition (`verified, hardened,
  repaired, linked, or synthesized` vs. `compiled or optimized`):**
  - If a tool **certifies** (`A1`), **hardens** (`A9` sandbox/sanitizer),
    **repairs** (`A9` autofixer), **links** (`A11`), or **synthesizes** (`A12`)
    an artifact $A$, the developer expects $A$ to satisfy its target safety or
    functional guarantee across **all** real-world executions.
  - By contrast, if a tool **compiles or optimizes** (`A6`) a C or Rust program
    $x$ without claiming to be a source-level UB verifier, the compiler cannot
    prevent $x$ from crashing if the user runs $x$ on an input that triggers
    source-level undefined behavior. The compiler's contract is
    *conditional behavioral preservation*: $A$ behaves as $x$ across **all
    well-defined source executions**.
  - Explicitly pairing all six verbs across the two clauses prevents both false
    claims (claiming a compiler verifies source UB) and the `D1` exploit (an
    agent giving a verifier or sandbox a compiler-style conditional spec that
    is vacuous on buggy inputs).
- **Why `"Any claim, bound, abstract model, or counterexample the tool emits
  (including a concrete failure trace accompanying a rejection or a
  synthesizer's unrealizability witness) must hold true of the input and its
  real-world executions in the target environment"`:**
  - `claim`: Covers boolean safety verdicts, equivalence verdicts (`A10`), and
    specification audit verdicts (`A13`).
  - `bound`: Covers WCET, stack, numerical error, and privacy bounds (`A5`).
  - `abstract model`: Covers lifted IR or functional models emitted by binary
    lifters and decompilers (`A7`).
  - `counterexample (including a concrete failure trace accompanying a rejection
    or a synthesizer's unrealizability witness)`: Covers bug-finder traces
    (`A2`), model-checker counterexamples (`A3`), and dual impossibility proofs
    when a synthesizer claims `Unrealizable`.
  - `of the input and its real-world executions in the target environment`: An
    unrealizable specification $\phi$ or an inconsistent policy audited
    by a specification auditor (`A13`) has *no* valid executions; saying `"of
    the input and its real-world executions in the target environment"` covers
    both properties of the input specification itself and properties of
    executions.

### The Fail-Closed Contrapositive (Lines 115–125)

> If an agent produces a tool or specification whose real-world behavior would
> violate the expectations of a domain engineer who accepted that specification,
> *the framework will not certify it*. If the framework emits no errors, then
> either:
>
> 1. There is a bug or invalid assumption in the framework's own trusted
>    computing base, or
> 2. Every invocation of the deployed tool upholds both branches of that promise
>    in the real world as a domain engineer accepting that specification and its
>    disclosed assumptions would reasonably expect.

- **Why `Every invocation of the deployed tool` is used:**
  An incremental verification daemon or stateful IDE server is invoked
  repeatedly across file, macro, and dependency edits. Requiring *every
  invocation of the deployed tool* to uphold both branches ensures that the
  second, third, and $n$-th cached invocations are bound by the same promise as
  a cold single-shot run.

---

## 3.4 Section: `# Corollaries of the promise` (Lines 126–296)

### Introductory Paragraph (Lines 128–133)

> For a certified tool to uphold this promise for a non-expert developer, five
> independent conditions must hold across **the developer's intuition**, **the
> formal specification**, **the real world**, **the deployed tool**, and **the
> verification foundation**. If any one of these conditions fails, a formally
> verified tool or the artifacts and claims it produces can still violate the
> developer's expectations in practice.

- **Why this wording is necessary:** Explicitly maps the five corollaries to the
  five nodes/edges of the formal model ($\mathcal{I}$, $S$, $\mathcal{R}$,
  $T_{\text{deployed}}$, $\mathsf{TCB}_{\text{framework}}$) so the reader sees
  immediately *why* there are five corollaries and why none can be omitted.

---

### Corollary 1: `## 1. The specification must mean...` (Lines 135–174)

#### Bullet 1: `No misleading or opaque abstractions` (Lines 141–145)
> - **No misleading or opaque abstractions:** A specification must not rely on
>   deceptive helper names (such as a predicate named `isConstantTime` or
>   `isStandardsCompliant` whose definition checks something weaker), deeply
>   nested definitions, implicit conversions or overloaded definitions, or
>   hidden special cases that obscure what is actually proved.

- **Failure modes addressed:**
  1. **Trojan horse / deceptive naming:** An agent defines `def isConstantTime
     (p : Prog) : Prop := True` or checks only that `p` terminates, while naming
     the top-level theorem `theorem compiler_is_constant_time`. A non-expert
     reading the top-level theorem statement trusts the identifier name.
  2. **Deeply nested obfuscation:** Burying a weakening premise (such as
     `if input.len < 4 then ... else True`) five helper layers deep outside the
     file or block the developer inspects.
  3. **Implicit conversions or overloaded definitions:** Theorem provers support
     implicit coercions, typeclass projections, and operator overloading (for
     instance, overloading `+` or `<=` on a custom wrapper type, or silently
     coercing `Int` to `Nat`). Note that we deliberately use the plain
     engineering phrase *"implicit conversions or overloaded definitions"*
     rather than Lean-specific jargon like *"hidden typeclass projections"* so
     the document stays accessible to non-FV engineers.
  4. **Hidden special cases:** Carving out hard instruction opcodes or corner
     cases inside a helper predicate.

#### Bullet 2: `No formal-language traps` (Lines 146–152)
> - **No formal-language traps:** A specification must not silently depend on
>   formal-logic idioms whose behavior diverges from standard engineering
>   meaning (such as saturating natural-number subtraction where `0 - 1 = 0`,
>   division by zero or out-of-bounds indexing returning `0`, Euclidean rather
>   than truncating remainder on negative numbers, unbounded mathematical
>   integers where fixed-width wrapping or overflow is expected, or implicit
>   variable quantification turning a typo into a vacuous premise).

- **Failure modes addressed:** Even when zero helper names are
  deceptive, theorem provers totalize partial functions and use mathematical
  defaults that silently invert the meaning of ordinary-looking code:
  1. **Saturating `Nat` subtraction (`0 - 1 = 0`):** An assertion `buf_len -
     offset >= 0` or `remaining - n <= remaining` is a tautology on `Nat` in
     Lean, Rocq, and Isabelle, masking integer underflow bugs.
  2. **Totalized division by zero (`x / 0 = 0`) and out-of-bounds array indexing
     (`arr[i]! = 0`):** In standard theorem-prover libraries, dividing by zero
     or indexing past the end of an array returns a default value `0` rather
     than trapping or failing. A specification stating `prog_output == a / b` or
     `prog_output == arr[i]` silently permits division by zero and out-of-bounds
     reads if $b = 0$ or $i \ge \text{len}$ is not separately ruled out.
  3. **Euclidean vs. truncating remainder on negative numbers:** Mathematical
     integer `%` in theorem provers is often Euclidean (`-7 % 2 = +1`), whereas
     C, Rust, Go, and x86/ARM `idiv`/`srem` use truncating remainder (`-7 % 2 =
     -1`).
  4. **Unbounded mathematical integers (`Int`/`Nat`) where fixed-width wrapping
     or overflow (`u32`/`i32`/`BitVec`) is expected:**
     Writing `x + 1 > x` in a specification over `Int` is always true, hiding
     32-bit or 64-bit integer overflow in real hardware. *(Note: An earlier
     draft used `"unsigned comparisons on fixed-width bitvectors where x < 0 is
     always false"` as an example here; adversarial review showed that `x < 0`
     on an unsigned integer is also always false in C and Rust, so that was not
     a formal-language divergence from engineering intuition! Replacing it with
     unbounded mathematical integers vs. fixed-width wrapping/overflow fixed
     that flaw.)*
  5. **Implicit variable quantification (`autoImplicit`):** In Lean 4 (when
     `autoImplicit` is enabled) and similar systems, a misspelled identifier
     (such as writing `isAllowed reqs` instead of `isAllowed req`) is silently
     bound as a fresh universally quantified variable $\forall
     \text{reqs},\dots$ instead of raising an "unbound identifier" error,
     turning the theorem into a vacuous or unintended statement.

#### Bullet 3: `Claim-polarity and precondition fidelity` (Lines 153–170)
> - **Claim-polarity and precondition fidelity:** The form of the guarantee and
>   its preconditions must match the kind of tool the developer believes they
>   are building. A verifier, sandbox, sanitizer, or repair tool must establish
>   or enforce safety across *all* executions rather than assuming away the bugs
>   or undefined behavior it is meant to catch, contain, or repair (unlike a
>   semantics-preserving compiler, which may assume well-defined source inputs);
>   a bug-finder must prove that *every* reported failure trace is a genuine bug
>   without equating an exhausted search with universal safety; a binary lifter
>   or decompiler must capture every possible real-world execution of an input
>   binary; and a codec or zero-knowledge circuit verifier must preserve
>   bidirectional witness completeness alongside soundness. Likewise, the
>   modeled execution regime must match the target property—preserving module
>   invariants across all public entry points and unverified callbacks (for
>   open-world libraries), relational equivalence or multi-trace hyperproperties
>   (for equivalence and constant-time checkers), probability distributions and
>   entropy rather than collapsing random choice to a constant (for
>   cryptographic code), and genuine progress over complete runs rather than
>   finite prefixes or infinite stuttering (for termination and liveness).

- **Every clause in these two sentences closes a specific adversarial exploit:**
  1. **`"A verifier, sandbox, sanitizer, or repair tool must establish or
     enforce safety across all executions rather than assuming away the bugs or
     undefined behavior it is meant to catch, contain, or repair (unlike a
     semantics-preserving compiler, which may assume well-defined source
     inputs)"`:**
     - Blocks **Existential Quantifier Inversion** (proving $\exists \tau \in
       \mathsf{Runs}(x),\; \mathsf{Safe}(\tau)$ instead of $\forall \tau$).
     - Blocks **Conditional-Compilation Smuggling (`D1`)**, where an agent gives
       a verifier or sandbox a compiler-style theorem $\mathsf{WellDefined}(x)
       \implies \mathsf{Safe}(T(x))$ that holds vacuously on every buggy input.
     - Phrasing this as *"rather than assuming away the bugs or undefined
       behavior it is meant to catch, contain, or repair"* (rather than banning
       all input preconditions on verifiers) preserves honest compositional
       verifiers that explicitly assume an upstream pass has already established
       a separate property.
  2. **`"a bug-finder must prove that every reported failure trace is a genuine
     bug without equating an exhausted search with universal safety"`:**
     - Blocks false-positive counterexample hallucination on reported bugs AND
       blocks treating a bounded/under-approximating bug-finder's `"0 bugs
       found"` output as a proof of safety.
  3. **`"a binary lifter or decompiler must capture every possible real-world
     execution of an input binary"`:**
     - In downward compilation (`A6`), target behaviors must be a *subset* of
       source behaviors ($\mathsf{Beh}(\text{target}) \subseteq
       \mathsf{Beh}(\text{source})$). In upward binary lifting or decompilation
       (`A7`), using downward inclusion $\mathsf{Beh}(\text{lifted}) \subseteq
       \mathsf{Beh}(\text{binary})$ is unsound: a lifted model that captures
       only *one* benign execution branch of the binary and drops a trojan
       branch would pass! Upward abstraction requires the reverse inclusion
       ($\mathsf{Beh}(\text{binary}) \subseteq \mathsf{Beh}(\text{lifted})$) so
       every real-world execution of the binary is captured.
  4. **`"and a codec or zero-knowledge circuit verifier must preserve
     bidirectional witness completeness alongside soundness."` (`Scenario
     R1`):**
     - A wire-format codec or ZK circuit compiler (`Circom`/R1CS) verified only
       for soundness ($\mathsf{Solutions}(\mathcal{C}) \subseteq \mathsf{Spec}$)
       can emit an over-constrained circuit that rejects honest provers (or
       leave the witness generator unverified). Conversely, verifying only
       completeness allows an under-constrained circuit (`0 * x = 0`) that lets
       dishonest provers forge proofs. Both directions are required.
  5. **`"preserving module invariants across all public entry points and
     unverified callbacks (for open-world libraries)"`:**
     - In an open-world library (such as an `unsafe` Rust collection or smart
       contract), safe caller code can call any public constructor/method in any
       order and pass callbacks (`Ord::cmp`, `Hash::hash`, `Deref`) that mutate
       state via interior mutability (`Cell`/`RefCell`) or re-enter the library.
       If the specification assumes closed-world callers or pure mathematical
       callbacks, safe caller code can trigger undefined behavior in the
       "verified" library.
  6. **`"relational equivalence or multi-trace hyperproperties (for equivalence
     and constant-time checkers)"`:**
     - Constant-time execution and non-interference are 2-trace hyperproperties
       ($\forall \tau_1, \tau_2,\; \text{pub}(\tau_1) = \text{pub}(\tau_2)
       \implies \text{leak}(\tau_1) = \text{leak}(\tau_2)$) that must be
       symmetric and step-aligned. Approximating them as single-trace safety
       properties or one-way implications misses side-channel leaks.
  7. **`"probability distributions and entropy rather than collapsing random
     choice to a constant (for cryptographic code)"`:**
     - If OS randomness (`getrandom`) is modeled as demonic nondeterminism over
       7-bit/256-bit byte arrays and verified via standard trace inclusion
       ($\mathsf{Traces}(A) \subseteq \mathsf{Traces}(x)$), then replacing key
       generation with a constant all-zero key `[0u8; 32]` is a valid trace
       refinement ($\{[0\text{u8}; 32]\} \subseteq \{0, 1\}^{256}$)!
  8. **`"and genuine progress over complete runs rather than finite prefixes or
     infinite stuttering (for termination and liveness)."`:**
     - Blocks three classic temporal-logic traps:
       - *Unbounded nondeterminism prefix trap:* Defining
         divergence as "has arbitrarily long finite execution prefixes"
         ($\forall k,\; \exists \tau,\; |\tau| \ge k$). By König's lemma, a
         finitely branching divergent program has an infinite branch, but an
         *infinitely branching* terminating program (`choose n : Nat; loop n
         times; return 0`) also has arbitrarily long finite prefixes—allowing a
         compiler to compile a guaranteed-terminating program into `loop {}`!
       - *Infinite stuttering / heartbeat starvation:* A
         reactive server that drops all client requests while emitting internal
         no-op ticks forever.
       - *Zeno time convergence:* A cyber-physical model that
         takes infinitely many discrete transitions in $0.5\text{ ms}$ of
         converging physical time ($t_i = 1 - 2^{-i}$) without ever reaching
         hazard time $t = 1$.

#### Bullet 4: `No silent post-acceptance drift` (Lines 171–174)
> - **No silent post-acceptance drift:** An agent must not be able to repair a
>   failing proof on a later turn by quietly weakening a specification or
>   expanding its disclosed assumptions after the developer has authored or
>   accepted them.

- **Failure mode addressed:** In a multi-turn coding session,
  the developer reviews and accepts $S$ and $\Delta$ in Turn 1. In Turn 5, the
  agent hits a hard proof case, edits a helper definition in $S$ (or appends a
  new caveat to $\Delta$), and reports `"Proof complete!"` without re-triggering
  human review of the weakened contract.

---

### Corollary 2: `## 2. Neither the specification...` (Lines 176–207)

#### Bullet 1: `No antecedent vacuity` (Lines 181–186)
> - **No antecedent vacuity (winning by domain collapse):** A specification must
>   not be satisfied vacuously because its preconditions, initial-state
>   constraints, environmental assumptions, or target-language rules are
>   contradictory or overly restrictive (admitting no valid programs or
>   executions, or narrowing them to a trivial subset of the intended input or
>   execution space).

- **Failure modes addressed:**
  1. **Contradictory preconditions ($\mathsf{Pre}(x) \equiv \bot$):** The agent
     adds incompatible alignment, ownership, or well-formedness premises so no
     input satisfies $\mathsf{Pre}(x)$, making $\forall x,\; \mathsf{Pre}(x)
     \implies \mathsf{Post}(x)$ vacuously true.
  2. **Uninhabited `initial-state constraints` or `target-language rules`:**
     Even if $\mathsf{Pre}(x)$ is inhabited by a program AST $x$, the language
     domain `L.dom` or initial-state predicate `init_ok` admits zero executions
     of $x$.
  3. **`"or narrowing them to a trivial subset of the intended input or
     execution space"`:** If the framework checks only
     bare existential inhabitation ($\exists x,\; \mathsf{Pre}(x)$), an agent
     can define $\mathsf{Pre}(x) := (x == \text{empty\_main})$ so the
     precondition is satisfied by a single 0-line program while excluding every
     real program the developer intends to analyze.

#### Bullet 2: `No consequent triviality` (Lines 187–194)
> - **No consequent triviality (winning by claim collapse):** A specification
>   must not assert a tautological postcondition, check a ghost output slot
>   decoupled from real ABI registers, or project away the program state or side
>   effects that matter to the user's property (such as ignoring corrupted
>   callee-saved registers, heap state, or erased secret-wiping writes). In a
>   compound specification (for example, functional correctness *and*
>   side-channel freedom), every individual requirement must be independently
>   non-degenerate; one genuine clause must not mask a vacuous companion clause.

- **Failure modes addressed:**
  1. **Tautological postconditions ($\mathsf{Post}(y) \equiv \top$):** Proving
     that a function returns a `u32` (which is true of any `u32`) or satisfies
     `y == y`.
  2. **`"check a ghost output slot decoupled from real ABI registers"`:** The
     formal machine state has both real hardware registers (`rax`, `rdi`, `rsp`)
     and a convenient ghost field `ghost_ret : Int`. The compiler writes the
     correct result to `ghost_ret` while leaving `rax` uninitialized, or uses a
     permuting observation codec that swaps `rax` and `rdx`.
  3. **Projecting away frame state, callee-saved registers, heap state, or
     secret-wiping writes:** A compiled function computes
     the right return value in `rax` but clobbers the caller's stack pointer
     `rsp`, callee-saved register `rbx`, or caller heap allocations, or projects
     away memory after return so secret-zeroizing writes are ignored.
  4. **Multi-conjunct canary masking:** Suppose a developer asks
     for a compound guarantee $S(x) = S_{\text{func}}(x) \land
     S_{\text{sec}}(x)$ (functional correctness *and* constant-time security).
     The agent defines $S_{\text{func}}$ honestly and sets $S_{\text{sec}} :=
     \mathsf{True}$. If non-degeneracy only tests that the *conjunction* $S(x)$
     can be falsified by some negative witness $x^-$, any witness that falsifies
     $S_{\text{func}}$ also falsifies $S_{\text{func}} \land
     \mathsf{True}$—completely masking the vacuous $S_{\text{sec}}$ clause!
     Requiring *every individual requirement* to be independently non-degenerate
     closes this loophole.

#### Bullet 3: `No degenerate or utility-destroying tools` (Lines 195–207)
> - **No degenerate or utility-destroying tools:** A certified tool—as a
>   complete deployed system, including any untrusted solver, search pass,
>   optimization pass, or certificate finder paired with a verified checker—must
>   genuinely handle the general class of inputs the developer expects. It must
>   not pass verification through trivial refusal or domain restriction
>   (rejecting all inputs, always returning "inconclusive," memorizing a finite
>   set of test cases, or checking only syntactic identity `p1 == p2`) or
>   through vacuous outputs (emitting a hardcoded program from a synthesizer,
>   inferring trivial bounds such as `+∞` or unconstrained `Top` models that
>   permit all behaviors, or acting as a no-op optimizer). Likewise, a compiler,
>   sandbox, sanitizer, or repair tool must not achieve formal safety through
>   utility-destroying rewrites that turn valid code or benign executions into
>   an unconditional abort, panic, infinite loop, or trivial constant return.

- **Every phrase in this bullet closes a distinct tool-level Goodhart exploit:**
  1. **`"as a complete deployed system, including any untrusted solver, search
     pass, optimization pass, or certificate finder paired with a verified
     checker"`:**
     If an agent builds a tool $T(x) = \text{check}(x, \text{find}(x))$ where
     `check` is verified in Lean and `find` is an untrusted Rust heuristic pass,
     testing `check` on hand-supplied certificates lets the agent ship `find(x)
     = None` (which fails on 100% of real user inputs). The *coupled end-to-end
     system* must be productive on the intended input family.
  2. **Group 1 — Trivial refusal or domain restriction:**
     - `rejecting all inputs` / `always returning "inconclusive"`: The trivial
       1-line verifier `fn verify(_) { Err("rejected") }`.
     - `memorizing a finite set of test cases`: A lookup-table tool `if x ==
       test1 || x == test2 { Ok } else { Err }` built to pass a fixed finite set
       of non-vacuity unit tests.
     - `checking only syntactic identity p1 == p2`: Since program equivalence
       and refinement are reflexive ($\forall p,\; p \equiv p$), a translation
       validator or equivalence checker that accepts if and only if `AST(p1) ==
       AST(p2)` is 100% sound and passes on infinite families of identical pairs
       $(p, p)$, yet is completely useless for verifying actual optimizations or
       refactorings where $p_1 \neq p_2$.
  3. **Group 2 — Vacuous outputs:**
     - `emitting a hardcoded program from a synthesizer`: A
       synthesizer that hardcodes one valid program $p_0$ and returns
       `Synthesized(p_0)` whenever the input specification $\phi(p_0)$ holds,
       rather than synthesizing distinct programs for mutually incompatible
       specifications $\phi_1, \phi_2$.
     - `inferring trivial bounds such as +∞`: A WCET, stack-depth, or numerical
       error bound inferrer (`A5`) that always outputs $+\infty$ (which is
       sound for every program because every execution takes $\le +\infty$
       cycles).
     - `unconstrained Top models that permit all behaviors`: An
       upward binary lifter (`A7`) or invariant inferrer (`A5`) that emits the
       universal chaos model `Top` (which soundly over-approximates every
       binary because `Top` permits every execution).
     - `acting as a no-op optimizer`: An optimization pass that
       returns its input unchanged (`p' = p`), trivially satisfying behavioral
       refinement while performing zero optimization.
  4. **Group 3 — Utility-destroying rewrites:**
     - `turn valid code or benign executions into an unconditional abort, panic,
       infinite loop, or trivial constant return`: A compiler, SFI sandbox,
       sanitizer, or automated bug-repair tool that achieves "100% memory
       safety" by replacing the body of `main()` with `abort()`, `panic!()`,
       `loop {}`, or `return 0` (and classifying clean traps or divergence as
       safe non-UB outcomes).

---

### Corollary 3: `## 3. The specification must have no...` (Lines 209–238)

#### Bullet 1: `No silent divergence from standards or hardware` (Lines 217–225)
> - **No silent divergence from standards or hardware:** When a tool targets an
>   existing language standard, runtime, protocol, or hardware architecture, its
>   formal model must match the real system's semantics (unlike CompCert's early
>   C semantics where it diverged from ISO C, or a model that treats IEEE-754
>   floating-point arithmetic as idealized real numbers) and be validated
>   against real implementations so a common-mode bug shared by an
>   agent-authored model and tool cannot pass. A tool that intentionally models
>   a custom dialect or restricted subset must declare that scope unmistakably
>   rather than claiming the standard.

- **Failure modes addressed:**
  1. **Silent standard/hardware divergence:** Modeling C, Rust, x86, ARM,
     RISC-V, or WebAssembly in a way that disagrees with real compilers or
     silicon (such as CompCert's early C bitfield/char/pointer semantics or
     modeling IEEE-754 floats as $\mathbb{R}$, missing `NaN` propagation, signed
     zeros, subnormals, and hardware NaN sign-bit nondeterminism as in `Scenario
     H8`).
  2. **Common-mode bugs in co-authored custom models:** When an
     agent authors *both* a formal semantics (for example, `SqlSemantics` or a
     custom VM model) and a tool verified against that semantics, any
     misconception held by the agent (such as treating `NULL = NULL` as `true`
     in SQL) will appear identically in both the model and the tool, so the
     formal proof passes with zero errors! Validating the formal model against
     real-world reference implementations / conformance oracles breaks this
     common-mode loop.
  3. **Custom dialects masquerading as standards:** A
     tool is allowed to target a custom dialect or restricted subset (such as
     Verified Rust `$K_{\text{anc}}$` or `panic=abort` Rust), provided it
     declares that custom dialect unmistakably rather than claiming full
     unqualified compliance with the standard. Conversely, if a tool claims the
     standard, it cannot excuse a wrong model of the standard via a footnote.

#### Bullet 2: `Unmistakable, bounded disclosure...` (Lines 226–238)
> - **Unmistakable, bounded disclosure of unmodeled reality:** Every formal
>   model abstracts away some aspects of physical reality or external execution
>   environments—such as instruction timing and microarchitectural side
>   channels, weak-memory concurrency, finite stack and heap bounds,
>   asynchronous cancellation, physical fault injection, or interactions with
>   unverified external code. If a specification omits a real-world behavior or
>   relies on an environmental assumption, **it must be impossible for the
>   developer to accept the specification while remaining unaware of that gap**.
>   Disclosed assumptions may record only genuine, unavoidable boundary
>   conditions outside the guarantee the tool claims: an agent must never omit a
>   behavior on which the target property depends, assume away the core bug
>   classes the tool is meant to check, bypass an avoidable proof obligation, or
>   bury a critical limitation in boilerplate caveats.

- **Failure modes addressed:**
  1. **Unmodeled physical and environmental layers:** Explicitly enumerates the
     six recurring reality gaps that cause formally verified systems to fail in
     production:
     - `instruction timing and microarchitectural side channels` (cache, branch
       predictor, variable-time division instructions);
     - `weak-memory concurrency` (TSO/ARM/RISC-V/C11 relaxed atomics modeled as
       sequential consistency);
     - `finite stack and heap bounds` (stack overflow or OOM modeled on an
       infinite-memory Turing machine);
     - `asynchronous cancellation` (Rust `Future` drop at arbitrary `.await`
       points or signal/interrupt preemption);
     - `physical fault injection` (single-event upsets / glitch attacks in
       high-assurance hardware/firmware);
     - `interactions with unverified external code` (FFI calls, safe callback
       re-entrancy, unverified callers).
  2. **Closing the self-contradictory `"especially when..."` loophole:** An
     earlier draft said that if a specification omits a real-world behavior, it
     must be disclosed, *"especially when the property the developer cares about
     depends on the omitted behavior."* If the property the developer cares
     about *depends* on the omitted behavior (for example, a constant-time
     verifier whose model omits instruction timing!), disclosing that timing is
     omitted does *not* make the tool valid—it means the tool fails its core
     purpose (`Corollary 1` + `Corollary 2`)! Hence the hard prohibition: *"an
     agent must never omit a behavior on which the target property depends,
     assume away the core bug classes the tool is meant to check, bypass an
     avoidable proof obligation, or bury a critical limitation in boilerplate
     caveats."*

---

### Corollary 4: `## 4. The verified core must be bound...` (Lines 240–275)

#### Bullet 1: `Exact input, configuration, and scope binding` (Lines 246–254)
> - **Exact input, configuration, and scope binding:** The deployed tool must
>   ingest and faithfully decode the exact project, source files or binary
>   artifacts, build configuration (such as `release` vs. `debug`, where
>   overflow and assertion semantics differ), target parameters, and feature
>   flags the user invokes it on. It must never report overall success after
>   resolving the wrong project, reusing stale cached verdicts after source
>   files, dependencies, macros, or build flags change, or silently skipping
>   unsupported functions, instructions, or language constructs (including
>   implicit destructors, closures, and macros).

- **Failure modes addressed:**
  1. **`"ingest and faithfully decode the exact project, source files or binary
     artifacts"`:** Covers both source-level tools and upward binary lifters
     (`A7`), and blocks parser/extractor desynchronization (such as hand-rolled
     lexers misparsing raw byte strings `br#"..."#` or multi-file crates hashing
     only `src/lib.rs` while ignoring `mod foo;` or `include!`).
  2. **`"build configuration (such as release vs. debug, where overflow and
     assertion semantics differ), target parameters, and feature flags"`
    :** Blocks verifying a crate under `debug` profile or
     host-endianness/target-width parameters while the user deploys `--release`
     or cross-compiles to a 32-bit target.
  3. **`"reusing stale cached verdicts after source files, dependencies, macros,
     or build flags change"`:** Blocks incremental verification
     cache poisoning where a daemon reuses an old `Verified` certificate after a
     cross-module struct layout, trait implementation, or macro changes.
  4. **`"silently skipping unsupported functions, instructions, or language
     constructs (including implicit destructors, closures, and macros)"`
    :** An agent-written extractor encounters
     `Drop::drop` cleanup glue, closures, inline assembly, or macro-expanded
     `unsafe` blocks that its formal AST does not support, silently filters them
     out of the verification list, proves the remaining 3 trivial functions
     safe, and exits `0`!

#### Bullet 2: `End-to-end output and downstream toolchain...` (Lines 255–268)
> - **End-to-end output and downstream toolchain integrity:** When a tool emits
>   or transforms an artifact or model, the formal guarantee must hold all the
>   way to the final output the user relies on:
>   - The bytes or model emitted by the tool must match the formal object
>     governed by the proof (with no unverified or drifting pretty-printers or
>     serializers).
>   - If the tool stops at an intermediate representation (such as emitting `.S`
>     assembly files or C source code) and relies on an unverified downstream
>     assembler, linker, or optimizing compiler—or if a downstream optimizer
>     could erase the property the tool just established (such as dead-store
>     elimination removing secret-zeroizing writes or branch optimizations
>     undoing constant-time masks)—that unverified downstream boundary must be
>     either eliminated or surfaced as an unmistakable disclosed assumption
>     under Corollary 3.

- **Failure modes addressed:**
  1. **Unverified pretty-printers or serializers:** The formal proof governs an
     in-memory AST `AsmProg`, while an unverified string formatter prints wrong
     register names, wrong instruction mnemonics, or wrong relocation offsets to
     the output file.
  2. **Stopping at `.S` or C source before an unverified
     assembler/linker/compiler:** Forces any unverified downstream compilation
     or linking stage to be either eliminated (by emitting verified machine
     code/ELF directly or verifying the downstream pass) or surfaced
     unmistakably under Corollary 3.
  3. **Downstream optimizer erasure of verified source/IR properties:** Even if
     a downstream compiler (`clang -O3` or `rustc -O`) is functionally correct
     under standard C/Rust semantics, standard source semantics treat
     secret-wiping buffer writes before deallocation as dead stores and treat
     branchless bitwise masks as equivalent to conditional branches! Thus, a
     source-level constant-time or zeroization verifier whose output is fed
     through an unverified downstream `-O3` pass will have its security property
     legally erased by the downstream optimizer.

#### Bullet 3: `Honest verdicts and diagnostics` (Lines 269–275)
> - **Honest verdicts and diagnostics:** The tool's externally observable output
>   (exit code, summary, and failure traces) must accurately reflect what was
>   established—strictly distinguishing unbounded proofs, horizon-bounded checks
>   (such as loops unrolled to depth `k`), refutations backed by genuine
>   counterexamples, and inconclusive or unsupported cases. It must never claim
>   unbounded safety when a check is horizon-bounded, and never return a passing
>   verdict or exit code when checks were skipped or inconclusive.

- **Failure modes addressed:**
  1. **Bounded-check inflation (`D2`):** A bounded model checker unrolls loops
     to depth $k = 2$, finds no bug, and prints `"VERIFIED SAFE"` without
     disclosing the bound $k = 2$.
  2. **CI exit-code `0` fail-open on skipped/inconclusive checks (`R5`):** A CLI
     tool prints a warning `"Skipped 47 unsupported functions"` to `stderr`,
     prints `"0 errors"` to `stdout`, and returns exit code `0`, causing CI
     pipelines to pass silently.
  3. **Why the final sentence separates horizon-bounded checks from
     skipped/inconclusive checks:** An honest
     bounded model checker (`A3c`) invoked by a user specifically to check depth
     $k$ *should* be allowed to return exit code `0` when its depth-$k$ check
     succeeds, so long as it reports a *horizon-bounded* verdict
     (`BoundedSafe(k)`) and never claims *unbounded* safety. By contrast,
     skipped or inconclusive checks must *never* return a passing verdict or
     exit code `0`.

---

### Corollary 5: `## 5. The tool cannot silently expand the TCB` (Lines 277–296)

#### Bullet 1: `No self-validating or circular specifications` (Lines 282–286)
> - **No self-validating or circular specifications:** A specification must be
>   defined independently of the tool's own implementation (never defining
>   `is_valid(x)` as `tool(x) == true` or defining target semantics via the
>   tool's own printer), which would fold the unverified tool into the trusted
>   specification.

- **Why this lives in Corollary 5 (`TCB expansion`) rather than Corollary 2
  (`Consequent triviality`), and why `"which would fold the unverified tool into
  the trusted specification"` is stated:**
  - Suppose an agent defines the specification of a tool $T$ as $S(x, y) := (y =
    T(x))$ (or defines `is_valid(x) := (tool(x) == true)`). Mathematically, for
    any deterministic function $T$, the relation $S(x, y) := (y = T(x))$ is a
    singleton per input $x$—it is *not* consequent-trivial ($\top$), and if $T$
    returns `true` on at least one input and `false` on at least one input, it
    passes every semantic non-vacuity and non-triviality test in Corollary 2!
  - What is actually wrong with $S(x, y) := (y = T(x))$? Its defect is **TCB
    contamination**: by referencing the unverified implementation $T$ (or the
    tool's own pretty-printer + an external interpreter)
    inside the specification $S$, the agent pulls the unverified tool $T$ into
    the trusted specification $\mathsf{TCB}(S)$, so the human accepting $S$ is
    unknowingly trusting $T$'s code! Placing this rule in Corollary 5 Bullet 1
    makes Corollaries 2 and 5 strictly orthogonal.

#### Bullet 2: `No silent proof or runtime escapes` (Lines 287–296)
> - **No silent proof or runtime escapes:** An agent-authored tool,
>   specification, or proof must never bypass verification through unfinished
>   proofs, custom axioms, unproven helper annotations or external solver
>   results treated as axioms, hidden premises that assume the tool's own
>   correctness, unverified compile-time evaluation, or unverified runtime code
>   replacements (such as compiler override or foreign-function attributes that
>   silently substitute unverified code for a verified definition at runtime).
>   Any external boundary assumption must be surfaced through the bounded
>   disclosure channel of Corollary 3.

- **Every item in this list blocks a concrete foundation/TCB exploit discovered
  during adversarial pentesting:**
  1. `unfinished proofs`: `sorry` / `admit` tokens left in proof scripts.
  2. `custom axioms`: `axiom trust_me : ...` added by the agent.
  3. `unproven helper annotations ... treated as axioms`: In a
     deductive verifier, the agent repairs a failing proof by inserting
     user-level helper annotations (`#[assume(ptr != null)]` or unchecked lemma
     attributes) into the input program, which the verifier silently consumes as
     trusted axioms without proving them.
  4. `external solver results treated as axioms`: Calling an
     external SMT solver (`Z3`/`cvc5`) or untrusted oracle and trusting its
     `UNSAT` answer without checking a proof certificate inside the verified
     core.
  5. `hidden premises that assume the tool's own correctness`: Adding a premise
     `(h_sound : ∀ x, tool x = true → Safe x)` to the theorem hypothesis list so
     the theorem proves $P \implies P$.
  6. `unverified compile-time evaluation`:
     Using unchecked reflection (such as `Lean.ofReduceBool` / `native_decide`,
     which trusts the unverified native code generator and C compiler at
     typechecking time) or executing arbitrary `IO` inside elaboration-time
     tactics (`run_tac`) to falsify environment state.
  7. `unverified runtime code replacements (such as compiler override or
     foreign-function attributes that silently substitute unverified code for a
     verified definition at runtime)`: In Lean 4 and
     similar compilers, an agent can prove `def verifyPure (x) : Bool`
     completely sound with zero axioms in the logical kernel, and then attach
     `@[implemented_by verifyFastUnverified]`, `@[csimp]`, or `@[extern "c_fn"]`
     so the compiled binary executes unverified C or Lean code at runtime while
     the kernel proof audits clean!
  8. **`"Any external boundary assumption must be surfaced through the bounded
     disclosure channel of Corollary 3."`:** Contrast this with
     an earlier draft that said *"any unproven assumption must either be
     rejected outright or surfaced... under Corollary 3."* In the converged
     wording, internal proof/TCB escapes are *unconditionally forbidden*
     (`"must never bypass verification..."`), and *only* genuine external
     boundary assumptions may be surfaced under Corollary 3's bounded disclosure
     rules.

---

## 3.5 Section: `# How we make decisions about the framework` (Lines 298–321)

### Principle 1: `Assume optimization pressure...` (Lines 299–303)
- Establishes the anti-Goodhart threat model as the primary architectural lens
  for evaluating any candidate framework mechanism.

### Principle 2: `Respect the developer's cognitive budget` (Lines 304–309)
> 2. **Respect the developer's cognitive budget.** A non-expert developer cannot
>    be expected to audit large formal semantics, read proof scripts, spot
>    subtle theorem-prover idioms, or sift through pages of boilerplate
>    disclaimers. Whatever the developer must review to accept a specification
>    and its disclosed assumptions must remain concise, concrete, and grounded
>    in ordinary engineering concepts.

- **Why `"or sift through pages of boilerplate disclaimers"` and `"and its
  disclosed assumptions"` are included:** Ensures that any
  framework mechanism for surfacing disclosed assumptions $\Delta$ is subject to
  the same strict human cognitive budget as the specification $S$ itself,
  ruling out verbose disclaimer dumps.

### Principle 3: `Never lock out honest tools...` (Lines 310–315)
> 3. **Never lock out honest tools to block degenerate ones.** Requirements that
>    rule out vacuous specifications, broken certificate finders, or memorized
>    lookup-table tools must test for genuine algorithmic generalization across
>    the tool's intended input family—never requiring semantic completeness that
>    would reject legitimate conservative tools, such as syntactic type or
>    borrow checkers that intentionally reject safe programs they cannot prove.

- **Why `"test for genuine algorithmic generalization across the tool's intended
  input family—never requiring semantic completeness"` is the exact mathematical
  separator:**
  During earlier formalization attempts, several naive mathematical definitions
  of "non-degeneracy" were found to lock out legitimate formal verification
  tools:
  1. *Semantic closure (`SemanticallyClosedOn`):* Requiring
     that if $T$ accepts program $x_1$ and $x_2$ has the same runtime behavior
     as $x_1$, $T$ must also accept $x_2$. By Rice's theorem, no decidable
     static analyzer, type checker, or borrow checker is semantically closed
     (for example, `if false { *null_ptr } else { 0 }` has the same runtime
     behavior as `0`, yet every syntactic type/borrow checker rejects the
     former and accepts the latter!).
  2. *Point-separating specifications (`PointSeparatingSpec`):*
     Requiring the specification to distinguish every pair of distinct inputs.
     Any boolean property (such as memory safety) has only 2 truth values and
     therefore cannot point-separate $\ge 3$ inputs!
  3. *Strict ABI bijection (`ObsABIInjective`):* Requiring
     observation codecs to be globally injective over full machine states,
     which locks out real ISA backends that have caller-saved scratch registers
     (`rcx`) or dead stack padding bytes.
  By stating that anti-degeneracy checks must test for *algorithmic
  generalization across the tool's intended input family* rather than *semantic
  completeness*, Principle 3 prevents future framework mechanisms from
  introducing false lockouts of conservative tools.

### Principle 4: `Support the full spectrum of FV tools` (Lines 316–321)
- Prevents architectural proposals that work only for unary safety verifiers or
  only for downward compilers, requiring every foundational primitive to
  accommodate all 13 tool archetypes.

---

# 4. Master Cross-Reference Matrix (`FRAMEWORK_PRINCIPLES.md`)

| # | Failure Mode / Adversarial Exploit | Archetypes Affected | Where Addressed in `FRAMEWORK_PRINCIPLES.md` |
| :--- | :--- | :--- | :--- |
| **1** | **Deceptive identifier names** (`def isConstantTime := True`) | All (`A1`–`A13`) | Corollary 1, Bullet 1 (`No misleading or opaque abstractions`, lines 141–145) |
| **2** | **Deeply nested helper obfuscation or hidden `if n < 10` special cases** | All (`A1`–`A13`) | Corollary 1, Bullet 1 (lines 143–145) |
| **3** | **Implicit conversions, coercions, or overloaded operators** | All (`A1`–`A13`) | Corollary 1, Bullet 1 (line 144) |
| **4** | **Saturating natural-number subtraction (`0 - 1 = 0`)** | All (`A1`–`A13`) | Corollary 1, Bullet 2 (`No formal-language traps`, line 148) |
| **5** | **Totalized division by zero (`x / 0 = 0`) or out-of-bounds indexing (`arr[i] = 0`)** | All (`A1`–`A13`) | Corollary 1, Bullet 2 (lines 148–149) |
| **6** | **Euclidean vs. truncating remainder on negative integers (`-7 % 2`)** | All (`A1`–`A13`) | Corollary 1, Bullet 2 (lines 149–150) |
| **7** | **Unbounded mathematical integers (`Int`/`Nat`) masking fixed-width overflow** | All (`A1`–`A13`) | Corollary 1, Bullet 2 (lines 150–151) |
| **8** | **Implicit variable quantification (`autoImplicit`) turning a typo into a vacuous premise** | All (`A1`–`A13`) | Corollary 1, Bullet 2 (lines 151–152) |
| **9** | **Universal vs. existential execution quantifier inversion** ($\exists$ trace vs. $\forall$ traces) | `A1`, `A9`, `A11`, `A12` | Promise Bullet 2 (lines 107–108); Corollary 1, Bullet 3 (lines 155–156) |
| **10** | **Smuggling compiler-style conditional UB premises (`WellDefined(x) => ...`) into a verifier or sandbox** | `A1`, `A9` vs. `A6` | Promise Bullet 2 (lines 107–109); Corollary 1, Bullet 3 (lines 155–158) |
| **11** | **Bug-finder fabricating counterexample traces or claiming `"0 bugs found"` = universal safety** | `A2`, `A3c` | Promise Bullets 1 & 2 (lines 92–113); Corollary 1, Bullet 3 (lines 159–160); Corollary 4, Bullet 3 (lines 269–275) |
| **12** | **Upward binary lifter / decompiler capturing only *some* executions instead of *all* binary executions** | `A7` | Promise Bullet 2 (lines 109–113); Corollary 1, Bullet 3 (lines 160–162) |
| **13** | **Under-constrained (`0 * x = 0`) or over-constrained (completeness-breaking) ZK circuits and codecs** | `A8` | Corollary 1, Bullet 3 (lines 162–163); Corollary 2, Bullets 1–3 |
| **14** | **Open-world library verifier assuming closed world or pure non-re-entrant callbacks (`Ord::cmp` / `RefCell`)** | `A11` | Corollary 1, Bullet 3 (lines 164–166); Corollary 3, Bullet 2 (lines 230–231) |
| **15** | **Approximating constant-time / non-interference hyperproperties as single-trace safety or asymmetric checks** | `A1`, `A6`, `A10` (`R5`) | Corollary 1, Bullet 3 (lines 166–167) |
| **16** | **Refining cryptographic randomness (`getrandom`) into a constant key (`[0u8; 32]`) via trace inclusion** | `A1`, `A6`, `A12` (`R6`) | Corollary 1, Bullet 3 (lines 167–169) |
| **17** | **Infinite-branching prefix termination collapse, heartbeat stuttering, or Zeno time convergence** | `A1`, `A6`, `A12` (`R2`, `R3`) | Corollary 1, Bullet 3 (lines 169–170) |
| **18** | **Multi-turn silent weakening of the specification $S$ or expansion of $\Delta$ after human acceptance** | All (`A1`–`A13`) | Corollary 1, Bullet 4 (`No silent post-acceptance drift`, lines 171–174) |
| **19** | **Antecedent vacuity via contradictory preconditions, unreachable initial states, or trivial domain narrowing** | All (`A1`–`A13`) | Corollary 2, Bullet 1 (`No antecedent vacuity`, lines 181–186) |
| **20** | **Consequent triviality (`Post := True`), ghost ABI output slots, or projecting away clobbered registers/heap** | All (`A1`–`A13`) | Corollary 2, Bullet 2 (`No consequent triviality`, lines 187–191) |
| **21** | **Multi-conjunct canary masking** (one real clause $S_1$ masking a vacuous clause $S_2 := \mathsf{True}$ in $S_1 \land S_2$) | All (`A1`–`A13`) | Corollary 2, Bullet 2 (lines 191–194) |
| **22** | **Verified certificate checker paired with a broken or stubbed untrusted finder (`find(x) = None`)** | `A4` (and all checker-backed tools) | Corollary 2, Bullet 3 (lines 195–198); Decision Principle 3 (lines 310–315) |
| **23** | **Trivial refusal (`verify(_) = false`), always returning `"inconclusive"`, or finite test-case memorization** | All (`A1`–`A13`) | Promise Bullet 1 (lines 92–99); Corollary 2, Bullet 3 (lines 198–201) |
| **24** | **Equivalence or differential verifier accepting only syntactically identical inputs (`p1 == p2`)** | `A10` | Corollary 2, Bullet 3 (line 201) |
| **25** | **Synthesizer emitting a hardcoded program, bound inferrer emitting `+∞`, lifter emitting `Top`, or no-op optimizer** | `A5`, `A6`, `A7`, `A12` | Promise Bullet 2 (lines 109–113); Corollary 2, Bullet 3 (lines 201–204) |
| **26** | **Utility-destroying rewrites** (compiler, sandbox, sanitizer, or repair tool rewriting code to `abort()` / `loop {}`) | `A6`, `A9` | Promise Bullet 2 (lines 105–109); Corollary 2, Bullet 3 (lines 204–207) |
| **27** | **Silent divergence from language/hardware standards (ISO C, IEEE-754 floats) or undeclared custom dialects** | All (`A1`–`A13`) | Corollary 3, Bullet 1 (`No silent divergence from standards or hardware`, lines 217–225) |
| **28** | **Common-mode bugs shared by a co-authored custom domain model and tool** | All (`A1`–`A13`) | Corollary 3, Bullet 1 (`validated against real implementations`, lines 221–223) |
| **29** | **Omission of relevant physical/environmental behaviors, $\Delta$-smuggling of proof obligations, or boilerplate flooding** | All (`A1`–`A13`) | Belief 3 (lines 74–78); Corollary 3, Bullet 2 (lines 226–238); Decision Principle 2 (lines 304–309) |
| **30** | **Resolving the wrong project, `debug` vs. `release` skew, stale incremental caches, or skipping closures/`Drop`/macros** | All (`A1`–`A13`) | Corollary 4, Bullet 1 (`Exact input, configuration, and scope binding`, lines 246–254) |
| **31** | **Drifting pretty-printers/serializers, unverified `.S`/C downstream toolchains, or `-O3` erasing secret wipes/masks** | `A6`, `A7`, `A8`, `A9`, `A11`, `A12` | Corollary 4, Bullet 2 (`End-to-end output and downstream toolchain integrity`, lines 255–268) |
| **32** | **Claiming unbounded safety on depth-$k$ checks, exit-code `0` on skipped/inconclusive checks, or crashing/hanging** | All (`A1`–`A13`) | Promise Bullet 1 (lines 92–101); Corollary 4, Bullet 3 (`Honest verdicts and diagnostics`, lines 269–275) |
| **33** | **Self-validating circular specifications (`is_valid(x) := tool(x) == true` or semantics defined via tool's printer)** | All (`A1`–`A13`) | Corollary 5, Bullet 1 (`No self-validating or circular specifications`, lines 282–286) |
| **34** | **Silent TCB escapes (`sorry`, custom axioms, `#[assume]` annotations, unverified solver axioms, `native_decide`, `@[implemented_by]`/`@[csimp]`/`@[extern]`)** | All (`A1`–`A13`) | Corollary 5, Bullet 2 (`No silent proof or runtime escapes`, lines 287–296) |
| **35** | **Over-strict anti-vacuity rules (`SemanticallyClosedOn`, `PointSeparatingSpec`) locking out honest conservative tools** | `A1` (type/borrow checkers) | Decision Principle 3 (`Never lock out honest tools to block degenerate ones`, lines 310–315) |
