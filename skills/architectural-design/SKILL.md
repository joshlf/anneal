---
name: architectural-design
description: >-
  Orchestrate end-to-end architectural design from target grounding and
  empirical research through divergent 4-dial brainstorming, multi-agent
  swarm-model-refinement, post-refinement feature-weight pruning, and a
  self-contained design specification. Use when designing or redesigning a
  system, subsystem, semantic model, protocol, or framework with open design
  trade-offs or empirical unknowns. Not for routine implementation of a settled
  design, standalone conceptual minimization without end-to-end design framing,
  or pure empirical investigation without a target design deliverable.
---

# End-to-End Architectural Design

Turn an open architectural problem into a verified, conceptually minimal, and
self-contained design specification. Keep four layers distinct throughout the
workflow:

1. **The target problem contract** (what outcomes, invariants, and scope
   boundaries must hold in the target system, and why);
2. **Empirical system facts** (what the compiler, language specification,
   kernel, runtime, or workload actually does at the pinned revision);
3. **Candidate mechanisms and models** (how the design proposes to satisfy the
   contract, evaluated and minimized via `swarm-model-refinement` and
   `model-refinement`); and
4. **The delivered design specification and its lifecycle disposition** (a
   reader-oriented specification of the converged design, an appendix of
   rejected alternatives, and explicit qualification of any unresolved risks or
   policy choices).

Scale the workflow to the task and reuse still-valid work. When the caller
already supplies a calibrated problem contract, verified empirical findings, or
candidate architectures, enter at the relevant phase rather than replaying
settled checkpoints or manufacturing experiments. If a bounded design problem
has no unresolved empirical unknowns, skip Phase 2; if it has no coupled
multi-axis trade-offs warranting multi-agent fan-out, use single-agent
`model-refinement` (with an unanchored fresh critic when independent review adds
value) rather than spawning a full swarm.

## Composition, dependencies, and authority boundaries

Obtain peer skills through the host's supported mechanism or an explicitly
supplied package (reusing any already loaded in context); do not assume a
hardcoded sibling path or universal import facility:

- **`tech-lead`:** Requirement recovery, risk prioritization, and context
  persistence across compaction.
- **`reference-research`:** Multi-round empirical investigation, minimal
  reproducers, and (when separately authorized) reference corpus publication.
- **`swarm-model-refinement` and `model-refinement`:** Multi-agent and
  single-agent conceptual model minimization, generalization, counterexample
  search, comparative adjudication (including the incumbent), and
  completion-boundary rereads.
- **`robust-code` and repository trust/domain skills (such as `trust-review`):**
  Invariant-preserving representations, explicit effects, and trust-boundary
  compliance.
- **`reader-oriented-explanation` and `williams-style`:** Organizing and
  drafting calibration summaries and the final design specification for readers
  who did not witness the design session.

If a required peer skill is unavailable and not supplied in context, continue
only the work supported without it, explicitly name the unavailable skill and
its unperformed responsibilities, and report a **bounded stop** (or request the
missing package); never invent its rules from memory or claim it was applied.

Invoking this skill grants no authority to modify canonical source files outside
authorized design or scratch paths, commit or push changes, publish to external
or reference-corpus branches, spend unapproved compute, or create standing
background automation. Keep all intermediate exploration, reproducers, and swarm
artifacts inside the conversation's authorized scratch directory or an isolated
detached worktree.

## Persistence, heartbeats, and recovery

End-to-end architectural design spans multiple delegated stages and is
vulnerable to context compaction, sub-agent timeouts, and mid-run premise
changes:

1. **Persist phase checkpoints before advancing:** At the end of each phase,
   write the current state—the calibrated Checkpoint 1 contract and retired
   prototype assumptions, Phase 2 empirical findings and reproducer paths,
   Stage 3.1 brainstorm synthesis, and Stage 3.3/3.4 refinement records—to
   durable scratch or artifact files before launching the next phase. After
   compaction or interruption, reconstruct state from those files and live
   workspace artifacts rather than conversational memory.
2. **Read live state before retrying interrupted work:** A sub-agent or command
   timeout does not prove failure. Inspect the scratch directory or worktree
   output before re-running an experiment or sub-agent pass.
3. **Bound progress heartbeats to the active phase:** When delegating a
   long-running phase (`reference-research` or `swarm-model-refinement`)
   expected to run for more than 10 minutes, instruct the sub-agent coordinator
   upfront to emit progress updates every ~10 minutes using a task-scoped,
   non-daemon timer (`IsDaemon: false` where supported) summarizing completed
   checks, active workers, and remaining blockers, and cancel any active timer
   as soon as the phase finishes. Never create daemon schedules or fabricate
   progress telemetry when a worker is silent.
4. **Propagate invalidated premises explicitly:** If an empirical finding in
   Phase 2, a target-codebase check in Stage 3.4, or a user redirect invalidates
   an earlier premise, mark dependent downstream artifacts **superseded**,
   preserve still-valid evidence, and re-run only the affected stages.

## Phase 1: Target grounding, goal calibration, and research question discovery

Before proposing solutions or launching experiments, establish the problem
contract and align with the human at **Checkpoint 1**.

### 1.1 Partition Target Baseline from Historical/Prototype Foils

When surveying the workspace, explicitly separate sources by their epistemic
authority:

| Category | Examples | Permitted Epistemic Role |
| :--- | :--- | :--- |
| **Authoritative Target Baseline** | The exact target branch or worktree where the design will live, its live code and tests, and its governing architecture and principles documents. | Defines the actual interfaces, invariants, and workloads the new design must satisfy. |
| **Historical / Prototype Foils** | Older branches (including `main` when designing against an active refactoring branch), prior pull requests, superseded prototypes, or sibling repositories. | Supplies **failure modes, edge cases, and empirical lessons only**—never default features, file formats, CLI flags, or contract requirements. |

Apply the **Assumption-Survival Test** to every mechanism, feature, or
workaround encountered in a historical prototype or earlier codebase version:

1. **Record the generating problem and the prototype's generating assumption:**
   Identify *what underlying failure mode* the historical mechanism addressed
   and *what architectural assumption in that older system* made the mechanism
   necessary (for example, per-target-crate hand-edited proof files or
   intermediate transpiled snapshot files).
2. **Test whether the generating assumption still holds in the Authoritative
   Target Baseline:**
   - If the target baseline eliminated that assumption, classify the historical
     mechanism—and every directive, flag, or test mode that existed only to
     exercise or configure it—under **Retired Prototype Assumptions
     (Non-Goals)**.
   - If the underlying problem still exists in the target baseline, carry
     forward **only the problem or failure mode** (for example, attributing
     verification failures to a specific function or keeping parallel test runs
     from dirtying tracked lockfiles), leaving the mechanism open for fresh
     design against the target baseline.
3. **Propagate target-baseline boundaries to every sub-agent:** In all sub-agent
   prompts across Phases 1–3, state the exact path and revision of the
   Authoritative Target Baseline and include the **Retired Prototype
   Assumptions** list so sub-agents do not read stale branches or resurrect
   obsolete prototype features.

### 1.2 Formulate governing goals, orthogonal axes, and scope boundaries

Separate *what must hold and why* from *how to build it*:

1. **Orthogonal guarantee axes:** When a problem entangles distinct failure
   modes, factor them into orthogonal axes with explicit consequences (for
   example, separating *Soundness Forward-Compatibility*—where a violation
   permits runtime undefined behavior—from *Compilation and Verification
   Stability*—where a violation causes a compile-time error or requires
   re-verification without ever permitting undefined behavior).
2. **Fixed scope boundaries:** State what is held fixed for a single design or
   verification instance (for example, a single configured compilation $C$ with
   fixed target primitive layout and resolved conditional-compilation
   predicates, or the boundary between target-crate pipeline tests and host CLI
   containment tests).
3. **Explicit non-goals and retired prototype assumptions:** List capabilities
   from earlier iterations or adjacent systems that the target design will
   intentionally omit.

### 1.3 Discover falsifiable empirical research questions

Identify every non-obvious technical question where an unverified assumption
about a compiler, language specification, kernel/elaborator, runtime, or
workload could invalidate the architecture or force defensive over-engineering:

1. **Check existing reference knowledge first:** When a technical reference
   corpus (such as `CATALOG.json` and `reports/<package>/`) is accessible in the
   workspace, filter it programmatically and verify each report's pinned
   revisions, applicability, and boundaries before proposing new experiments.
2. **State concrete, falsifiable questions:** Frame each remaining unknown so it
   can be resolved by primary source inspection and minimal executable
   reproducers at the repository's pinned toolchain revision.

### 1.4 Pause at Checkpoint 1 (Goal, Scope, and Research Question Calibration)

Present a concise calibration summary (or artifact) to the human covering:

1. **Authoritative Target Baseline vs. Retired Prototype Assumptions:** Which
   branch/worktree is authoritative and which legacy mechanisms from prior
   iterations are retired as non-goals.
2. **Governing Goals, Orthogonal Axes, and Scope Boundaries:** What the design
   must guarantee and what lies outside scope.
3. **Proposed Empirical Research Plan:** The exact empirical questions to run in
   Phase 2, including whether `reference-research` corpus publication is
   proposed (requiring explicit user approval before any corpus push).
4. **High-Leverage Goal Clarifications:** Any genuine ambiguity in user goals,
   scope, or risk tolerance.

Wait for human confirmation at Checkpoint 1 before launching Phase 2 or Phase 3.

## Phase 2: Synchronous empirical research and goal-consistency gate

When Phase 1 identifies unresolved empirical questions, execute the empirical
investigation synchronously before design brainstorming:

1. **Run empirical research synchronously:** Execute the agreed research plan
   (using `reference-research` when available and approved, with ~10-minute
   progress heartbeats if long-running). Running research synchronously as a
   sequential stage avoids cross-track coordination overhead and ensures Phase 3
   builds on verified facts rather than speculation.
2. **Evaluate the Goal-Consistency Gate (Default: Auto-Advance):** When Phase 2
   completes, persist the empirical findings and compare them against the goals,
   scope boundaries, and premises agreed at Checkpoint 1:
   - **Auto-advance (default):** If the empirical findings are consistent with
     the Checkpoint 1 goals—even if they refute specific candidate
     mechanisms—advance immediately to Phase 3 without pausing for human input.
   - **Contradiction pause (exception):** Pause and consult the human *only* if
     an empirical finding directly contradicts or invalidates an agreed goal,
     scope boundary, or soundness premise from Checkpoint 1.

## Phase 3: Two-stage divergence-to-convergence funnel

Once goals and empirical facts are established, explore the design space broadly
and then compress it before presenting a specification to the human.

### Stage 3.1: Divergent 4-agent creativity-dial brainstorm

Spawn four parallel sub-agents in isolated scratch contexts, giving each the
Authoritative Target Baseline, the Checkpoint 1 goals and scope boundaries
(including Retired Prototype Assumptions), and the Phase 2 empirical findings.
Assign each sub-agent a distinct creativity dial and require concrete data
structures, state/data-flow boundaries, and trade-off accounting:

- **Dial 1 (Conservative / Textbook):** Proven, minimal-surprise mechanisms and
  standard idioms that satisfy the contract with zero novel abstractions.
- **Dial 2 (Moderately Conservative / Pragmatic Synthesis):** High-leverage
  structural unifications and clean boundary separations within the existing
  system architecture.
- **Dial 3 (Moderately Creative / Structural Redesign):** Rethinking internal
  representations, data flow, or stage boundaries to eliminate entire classes
  of plumbing, boilerplate, or failure modes.
- **Dial 4 (Extremely Creative / Radical Zero-Base Rethink):** Challenging
  every non-mandatory boundary to find radical theoretical or operational
  collapses, even if only individual component insights survive into the final
  model.

Coalesce the distinct component mechanisms, representations, and architectural
candidates into a scratch synthesis artifact (`Candidate Idea Pool`). **Do not
pause to ask the human to choose from this unrefined brainstorm menu.**

### Stage 3.2: Pre-swarm contract and holdout hygiene

Before launching `swarm-model-refinement`, audit the proposed Governing Contract
(`C1`–`Ck`) and Blind Holdouts (`H1`–`Hm`) against two strict hygiene rules:

1. **Outcome-only Governing Contract (zero prototype or mechanism lock-in):**
   Because `model-refinement` forbids dropping any clause in the Governing
   Contract $C$, writing a historical prototype feature or a Stage 3.1
   brainstormed mechanism (such as a specific archive format, directive syntax,
   or auxiliary subsystem) into `C1`–`Ck` locks that mechanism into every
   candidate model and prevents the swarm from deleting it. State `C1`–`Ck`
   strictly in terms of **required semantic or system outcomes, invariants, and
   concrete workloads of the Authoritative Target Baseline** (calibrated at
   Checkpoint 1 and Phase 2). Keep candidate mechanisms, file formats,
   directives, and optional sub-features in the mutable **Candidate Idea Pool**
   so the swarm can discard any mechanism whose value does not justify its
   total burden.
2. **Holdout scope compliance:** Verify that every blind holdout scenario in
   `H1`–`Hm` respects the scope boundaries agreed at Checkpoint 1 and represents
   a valid workload of the Authoritative Target Baseline. Never allow the
   `Steward`, `Holdout Stitcher`, or coordinator to invent holdout scenarios
   outside the agreed scope (such as cross-target compilation holdouts when
   verification is scoped to a fixed compilation target $C$), as out-of-scope
   holdouts force candidates to add artificial state parameters and fallback
   branches.

### Stage 3.3: Multi-agent `swarm-model-refinement`

Run `swarm-model-refinement` (with `model-refinement`) over the `Candidate Idea
Pool` and the sanitized outcome-only contract $C$:

1. **Adversarial exploration, holdout stitching, and fresh criticism:** Follow
   `swarm-model-refinement`'s full epistemic barrier rules—competing Architects
   (`α` minimization, `β` generalization, `γ` incumbent/surgical baseline),
   targeted Challengers, isolated `Holdout Stitcher` with cross-pass exposure
   accounting, and per-pass unanchored `Fresh Critics`—until the swarm reaches
   local convergence (or a documented bounded stop) on a canonical model $M^*$.
2. **10-minute progress heartbeats:** When delegated to a sub-agent coordinator,
   enforce the task-scoped ~10-minute progress heartbeat rule from the
   persistence section above.

### Stage 3.4: Post-refinement feature-weight audit and re-minimization

`swarm-model-refinement` minimizes the model $M$ while holding the Governing
Contract $C$ fixed ($\min_{M \models C} \text{complexity}(M)$). Once $M^*$
converges, the true implementation and reasoning cost of every requirement is
visible. Before writing the design specification, execute a three-step
post-refinement pass:

1. **Zero-base feature-weight audit against the concrete target codebase ($C \to
   C'$):** Inspect every surviving feature, directive, state parameter, and
   subsystem in $M^*$ against the actual files, types, and existing tests of the
   Authoritative Target Baseline:
   - *Does this feature carry its weight in the target repository specifically,
     or is it vestigial baggage from a prior prototype or an over-generalized
     contract clause?*
   - *Can existing primitives in the target repository (such as ordinary unit
     or integration tests, existing compiler checks, or existing kernel
     obligations) handle the cases this feature targets without bespoke
     machinery?*
   Prune any agent-inferred or prototype-carried feature that fails to carry its
   weight, producing a leaner contract $C' \subset C$ and recording the pruned
   feature in `Appendix A`. If an **explicit human requirement from Checkpoint
   1** exhibits disproportionate cost relative to its target-system benefit, do
   not drop it silently: either show how existing target primitives satisfy the
   underlying goal with zero bespoke machinery, or surface the exact
   cost-vs.-benefit trade-off prominently for human decision.
2. **Plumbing-equivalence check on remaining open decisions:** For every open
   question or "irreducible policy choice" surfaced during refinement, check:
   - *Is one branch already entailed by the Checkpoint 1 goals or fixed scope
     boundaries?* If so, resolve it immediately.
   - *Do the competing options require different architectural machinery, or do
     they use the exact same plumbing with a different configuration table or
     default boolean?* If the plumbing is identical, do not present it as an
     architectural fork: specify the single unified mechanism and state the
     default policy configuration concisely.
3. **Mandatory post-pruning `model-refinement` pass ($\min_{M \models C'}
   \text{complexity}(M)$):** Whenever Step 1 or Step 2 prunes a feature or
   resolves a pseudo-fork, run a dedicated `model-refinement` pass over $M^*$
   under the reduced contract $C'$ and concrete target codebase, including its
   required completion-boundary reread. Collapse any supporting scaffolding
   whose sole justification was $C \setminus C'$—such as multi-file archive
   parsers after all remaining fixtures become single files, stage-coupled
   directory trees, per-state fields that are actually crate-level constants, or
   heuristic diagnostic scanners that duplicate an existing check.

## Phase 4: Reader-oriented design specification and lifecycle boundary

Draft the final design specification as a standalone artifact (or repository
document when requested), applying `reader-oriented-explanation` and
`williams-style`.

### 4.1 Structure the main body around the final converged design only

A human reader evaluating or implementing the design should never have to
replay the swarm's chronological deliberation (`Round 1`, `Candidate α/β/γ`,
`Fresh Critic 002`) or filter out rejected proposals inside the specification.
Keep the main body strictly focused on the final, weight-checked, re-minimized
design:

1. **Purpose, Scope, and Governing Guarantees:** State the problem the design
   solves, the fixed scope boundaries, the orthogonal guarantee or stability
   axes, and explicit non-goals (including retired prototype assumptions).
2. **Architecture and System / Trust Boundaries:** Present a clear architectural
   overview showing how responsibilities are partitioned across components and
   how safety or trust-boundary invariants are enforced.
3. **Concrete Component and Semantic Specifications:** Specify the exact data
   structures, AST/state definitions, algorithms, file layouts, grammars, or
   CLI interfaces per component, grounded in the concrete files and types of the
   Authoritative Target Baseline.
4. **End-to-End Workflows, Verification Strategy, and Migration Plan:** Show how
   representative workloads and edge cases flow through the architecture end to
   end, how existing code or tests migrate, and how regressions are caught.
5. **Epistemic Calibration and Open Product-Policy Decisions:** Distinguish
   verified empirical facts (citing pinned toolchain/repository revisions and
   reproducers), formal or type-checked properties, conceptual
   `model-refinement` arguments, and any remaining unverified assumptions or
   Bounded-Stop limits. If any genuinely irreducible product or UX policy
   choices survive the Plumbing-Equivalence Check in Stage 3.4, list them
   concisely with their recommended default.

### 4.2 Record rejected mechanisms in `Appendix A: Alternatives Considered`

Place all rejected architectures, candidate mechanisms falsified during
`swarm-model-refinement`, and prototype features pruned during the
Feature-Weight Audit in a dedicated `## Appendix A: Alternatives Considered`
section at the end of the document, grouped by thematic cluster:

- For each entry, state **the alternative mechanism or feature** and **the
  concrete dominance argument, counterexample, holdout failure, cross-layer
  burden shift, or target-weight reason** that eliminated it.
- Frame each entry by *what the alternative was* and *why it is inferior,
  unsound, or unnecessary in the target system*, without session narrative.

### 4.3 Separate design delivery from downstream implementation or publication

Delivering a converged design specification does not itself authorize modifying
production code, committing to canonical branches, or publishing external
reports. Conclude by presenting the design specification, stating the refinement
disposition (`local convergence` or `bounded stop` with any qualifications), and
highlighting only the irreducible policy decisions or next implementation steps
that require human direction.
