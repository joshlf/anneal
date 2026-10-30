<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Design Ideas and Brainstorming

This document records design observations and architectural directions that have
emerged from building and using Anneal on real Rust verification workloads. Unlike
[`PRINCIPLES.md`](PRINCIPLES.md) and [`DESIGN.md`](DESIGN.md), which state
normative project commitments, the sections below capture motivating problems,
design trade-offs, and candidate implementation paths to guide future work.

---

## 1. Fast, Untrusted ("Provisional Evidence") Modes for Proof Engineering and Code Assessment

### Observation: Strict Kernel Replay Conflates Truth Discovery with Proof Engineering

Anneal's standard verification gate (`cargo anneal verify` and
`cargo anneal agent-verify`, backed by
[`trusted/audit/TrustedBoundary.lean`](trusted/audit/TrustedBoundary.lean))
enforces a strict `trustLevel := 0` kernel boundary:

- Every theorem statement (`ci.type`) must reference only definitions in
  [`trusted/lean/`](trusted/lean/README.md), the pinned Lean standard library,
  captured MIR (`Mir.*`), and locked specifications (`Specs.*`).
- Every proof term (`ci.value?`) is replayed through a fresh Lean 4 kernel
  environment and must depend only on Lean's three foundational axioms
  (`propext`, `Quot.sound`, `Classical.choice`), plus any explicitly locked
  `Assumptions.*` axioms when `--allow-assumptions` is active.
- `TrustedBoundary.lean` rejects `native_decide` (`decide +native`, which relies
  on the compiler-trust axiom `Lean.ofReduceBool`), `unsafe`, `partial`, and
  `sorryAx`.

This restriction is essential for a final `VerificationResult`. Allowing
`native_decide` inside an unconditional verification certificate would silently
expand the Trusted Computing Base (TCB) to include Lean's code generator, the
host C compiler, and `@[implemented_by]` / `@[csimp]` runtime overrides without
recording that dependency in the TCB audit log. Because Lean's kernel reducer
(`whnf`) cannot offload symbolic execution to compiled native code under this
policy, it must symbolically reduce every `Runtime(PostCleanup)` MIR statement,
place projection, Tree Borrows check, and terminator inside the kernel.

In day-to-day verification and review workflows, however, enforcing the full
`trustLevel := 0` kernel requirement from the very first iteration conflates
two distinct questions:

1. **The epistemic truth question ("Does this specification actually hold of
   this Rust code under Anneal's MIR semantics?"):** Is the implementation free
   of Undefined Behavior (UB) and consistent with its `requires` and `ensures`
   clauses across its input domain, or does it harbor a bug—such as an unguarded
   `transmute` byte (`raw[1] = 2` in `decode_wire_header`), a little-endian lane
   order mismatch (`checksum_frame_fast`), an arithmetic overflow, or a
   mismatched intermediate lemma?
2. **The kernel proof-engineering question ("How do we package that truth into a
   small-TCB proof term that Lean's `whnf` reducer accepts quickly?"):** Once we
   have high confidence that the claim holds on the captured MIR, how do we
   structure context records (`BlockCtx`), fast-path equivalence lemmas
   (`*Fast_eq`), and `Hold` barriers so kernel reduction finishes within
   heartbeat limits without `Lean.ofReduceBool`?

When a user or coding agent must solve Question 2 before getting any signal on
Question 1, two failure modes arise:

- **Wasted proof engineering on false claims or bad intermediate lemmas:** An
  agent or developer can spend hours fighting `whnf` timeouts on a multi-block
  loop or bitwise proof before discovering an off-by-one bug in the Rust code, a
  missing precondition in `Specs/<Item>.lean`, or an unprovable intermediate
  `have` hypothesis.
- **High latency for code review and architectural triage:** A reviewer or tech
  lead assessing a change often wants fast, high-confidence *provisional
  evidence* that a candidate implementation or optimization satisfies Anneal's
  exact `V2026_06_01` MIR semantics before deciding whether to merge a prototype,
  lock specifications (`cargo anneal lock-specs`), or invest hours in a
  zero-axiom kernel proof.

### How Provisional Evidence Fits Anneal's Design Contract

Supporting a fast, untrusted mode does not require weakening Anneal's core
promise in [`PRINCIPLES.md`](PRINCIPLES.md). [`DESIGN.md`](DESIGN.md) already
provides two distinct semantic categories that accommodate provisional evidence
cleanly:

1. **Policy-authorized extended-TCB verification (`DESIGN.md` §"Trust policy"):**
   A trust policy specifies which unchecked dependencies and evidence mechanisms
   Anneal may use in establishing a claim, provided that mandatory project-wide
   requirements (including baseline UB-freedom) remain in force and every
   unchecked dependency is recorded in the TCB. Explicitly selecting a
   development trust policy changes the verification being requested without
   claiming that the strict zero-axiom policy was satisfied.
2. **Tainted development outputs (`DESIGN.md` §"Verification outcomes" and
   `PRINCIPLES.md` footnote 2):**
   When Anneal bypasses a condition required for a `VerificationResult`—such as
   replacing universal quantification over a $2^{64}$ domain with bounded native
   sampling, or admitting an unproved subgoal—and emits a claim-bearing
   development artifact, that artifact is a **tainted output**, not a
   verification result. Both the CLI output and the TCB audit log must label it
   unambiguously as provisional or tainted.

Separating these outcomes yields a four-level evidence spectrum across a crate:

| Evidence Tier | What Is Checked | Unchecked Dependencies Added to TCB | Eligible as Final `VerificationResult`? |
| :--- | :--- | :--- | :--- |
| **1. `VerifiedUnconditional`** | Full kernel proof (`trustLevel := 0`) over `mirStatefulTree`; zero extra axioms. | Standard TCB only (`rustc` capture, `trusted/lean/`, Lean kernel). | **Yes** (default `verify` / `agent-verify` target). |
| **2. `VerifiedConditional`** | Full kernel proof modulo explicitly locked `Assumptions.<Crate>.<Item>` axioms (`--allow-assumptions`). | Standard TCB + named `Assumptions.*` axioms listed in audit log. | **Yes** (when policy authorizes the named assumptions). |
| **3. `ProvisionalNative`** | Complete proof over `Trusted.MirSemantics`, but proof term uses `native_decide` (`Lean.ofReduceBool` / `Lean.ofReduceNat`) or a policy-authorized external decision procedure. | Standard TCB + `Lean.ofReduceBool` (Lean native compiler, C compiler, `@[implemented_by]` runtime). | **Only under an explicit `--trust-policy=provisional-native` request**; rejected by default `verify` and `agent-verify`. |
| **4. `TaintedProvisional`** | Fast non-exhaustive native execution, bounded input-space sweep, or partial proof with admitted subgoals (`provisional_admit`). | Unchecked input paths or unproved subgoals; **not** a complete proof of the claim. | **No (`TAINTED OUTPUT`)**; emitted strictly for development triage and proof engineering. |

---

### Potential Directions for Implementation

#### Direction A: `ProvisionalNative` Mode via `Lean.ofReduceBool` (`native_decide`)

For functions with small or bounded finite domains—or for discharging expensive
ground/finite subgoals inside a larger symbolic proof—Lean's `native_decide`
(`decide +native`) compiles a decidable proposition `P : Prop` (`[Decidable P]`)
to native C code, executes it, and emits an axiom application
`Lean.ofReduceBool`.

1. **Decidable finite-domain wrappers in `theory/Anneal/Provisional.lean`:**
   Because `stepMirState`, `runCfgSteps`, and `evalSymNodeTree` in
   `Trusted.MirSemantics` and `Anneal.SymbolicEval` are already computable
   functions, `theory/` can provide decidable boolean checkers for stateless and
   stateful claims over any finite list of inputs `inputs : List (List Value)`
   (or exhaustive byte/word ranges such as all $2^8 = 256$ `u8` inputs in
   `parse_compression_flag` or all $17 \times 1025 = 17,425$ valid `(u16, u16)`
   pairs in `frame_total_len`):
   ```lean
   def checkClaimOnInputs
       (body : CapturedMir) (fuel : Nat)
       (preB : List Value → Bool) (postB : List Value → Value → Bool)
       (inputs : List (List Value)) : Bool :=
     inputs.all fun args =>
       if preB args then
         match runMirBounded body fuel args with
         | .normal (ret, _) => postB args ret
         | _ => false
       else true
   ```
   Paired with a kernel-checked soundness bridge theorem
   (`claim_holds_on_domain_of_checkClaimOnInputs`), a user or agent in
   provisional mode can discharge an entire finite-domain proof in one line via
   `by native_decide` in **milliseconds** rather than writing 1,000+ lines of
   `BlockCtx` and `dsimp` machinery.
2. **Scoped `Lean.ofReduceBool` admission in `TrustedBoundary.lean`:**
   - Add an explicit `--allow-provisional-native` flag to `TrustedBoundary.lean`
     (`verify-audit` mode) and `--provisional` to `cargo anneal verify` /
     `cargo anneal agent-verify`.
   - When `--allow-provisional-native` is **off** (the default), `TrustedBoundary`
     continues to reject `Lean.Parser.Tactic.nativeDecide` in syntax preflight
     and `Lean.ofReduceBool` / `Lean.ofReduceNat` in the constant closure.
   - When `--allow-provisional-native` is **on**, `TrustedBoundary` permits
     `native_decide` in `Proof/<Crate>/<Item>.lean`, tracks every item whose
     constant closure reaches `Lean.ofReduceBool`, and classifies that item as
     `ProvisionalNative` (recording `Lean.ofReduceBool` in the item's TCB entry)
     rather than `VerifiedUnconditional`.

#### Direction B: Fast Pre-Flight Native Execution & Counterexample Sweeps (`cargo anneal check --provisional`)

When the input domain is too large to enumerate exhaustively (such as
`decode_wire_header([u8; 4])` with $2^{32}$ inputs or
`checksum_frame_safe(&[u8; 8])` with $2^{64}$ inputs), developers and agents still
want immediate evidence of whether a specification and implementation agree on
representative, boundary, and randomized inputs before beginning a symbolic
proof.

1. **Automated boundary + PRNG sweep over captured MIR:**
   A new `cargo anneal check --provisional [--item <item>]` command can generate
   an ephemeral Lake target that runs `Trusted.MirSemantics` natively across:
   - boundary scalar values (`0`, `1`, `2`, `max - 1`, `max`, power-of-two edges,
     and values just inside and outside `requires` constants extracted from the
     MIR AST), and
   - $N$ deterministic pseudo-random input vectors (e.g., $10,000$ vectors in
     $< 50\text{ ms}$).
2. **Immediate counterexample promotion to kernel refutation:**
   If the native sweep finds an input vector `args₀` where `mirStatefulTree`
   reaches `ITree.fail .ub`, panics, or violates `ensures` (or disagrees with a
   reference `specBody` in `StatefulEquivItemSpec`), `cargo anneal` can
   immediately emit a concrete counterexample witness—and optionally instantiate
   `SymbolicEval.refuteClaimByBoundedUB` on `args₀` to turn the untrusted native
   finding into a **100% kernel-checked refutation theorem (`¬ claim.holds`)**!
3. **Clear `TAINTED` labeling when no counterexample is found:**
   If all sampled inputs pass, `cargo anneal check --provisional` reports a
   `TaintedProvisional` summary (e.g., `PROVISIONAL PASS (10,256 / 10,256 inputs
   checked natively; 0 UB, 0 postcondition failures; NOT A VERIFICATION RESULT)`),
   giving the user or agent immediate confidence to proceed with symbolic proof
   construction.

#### Direction C: Subgoal & Lemma Plausibility Probing in Interactive Proof Loops (`anneal-lean_lsp`)

During interactive proof engineering, the hardest part of discharging a complex
obligation is often formulating helper lemmas—such as byte-swap identities
(`swap_le_u16_lane`), precondition inversions (`wpReq_inversion`), or loop
invariants (`loopInv i acc mem`)—that are both *true* and *strong enough*.
Controlled A/B benchmarking of `anneal-lean_lsp` against a cold-CLI baseline
shows why separating **state inspection and plausibility probing** from **blind
tactic guessing** matters:

- When an agent uses in-memory `lean_multi_attempt` (~15 ms RPC latency) as a
  syntactic slot machine—probing 10–15 permutations of `dsimp only [...]` to
  force bottom-up reduction of `wpMirSym`—each extra LLM reasoning turn adds
  ~35 seconds of wall-clock latency without making structural progress.
- Conversely, when an agent uses **wildcard top-down `change ... _` +
  `lean_goal`** to inspect the exact kernel WHNF terms (`(advanceStmt ...).memory`,
  `{ ... }.sizeBytes.mul 8`, `scalarModulus 4`) in a single 15 ms query, it
  completes stateful Tree Borrows + `bitwiseOrBits` proofs **3.1x faster** in
  wall-clock time (`3m 48s` vs. `11m 38s`) and with **7.6x shorter proof
  scripts** (`43` lines vs. `328` lines) than a baseline agent that must read
  `trusted/lean/` sources and hand-author intermediate `MachineState` stepping
  lemmas.

Extending `anneal-lean_lsp` with provisional semantic probing builds directly on
this threshold:

1. **In-memory `native_decide` / `#eval` subgoal probing via LSP overlays:**
   Because `anneal-lean_lsp`'s `lean_multi_attempt` tool evaluates candidate
   tactics purely in memory via LSP `didChange` overlays without touching disk or
   `.anneal/spec-lock.json`, it can offer a `provisional_probe` helper:
   - Given a proposed lemma or open goal `∀ (b0 b1 : Nat), b0 < 256 → b1 < 256 → P b0 b1`,
     the tool tests `P` in memory over small/boundary instantiations using
     `decide +native` in ~15 ms.
   - If the proposed lemma fails on `b0 = 1, b1 = 2`, the agent learns in 15 ms
     that its intermediate lemma is false—before spending dozens of turns trying
     to prove it symbolically.
2. **Two-phase proof staging ("Fast Provisional First, Kernel Refinement Second"):**
   In multi-item crates or stacked PR workflows:
   - **Phase 1 (Provisional Milestone):** The agent or engineer discharges
     straightforward items unconditionally and closes computationally heavy
     arithmetic or bounded-execution subgoals using `native_decide` under
     `--provisional`. This confirms end-to-end specification alignment across the
     entire crate in minutes.
   - **Phase 2 (Kernel Hardening):** With the specification and proof structure
     validated by Phase 1, the agent systematically replaces each
     `Lean.ofReduceBool`-dependent lemma with a kernel-reducible proof (`omega`,
     `SymbolicEval`, `FunctionalTranslation`, wildcard `change` + projection
     `dsimp`, or `BlockCtx` fast-paths) until `cargo anneal agent-verify`
     certifies `VerifiedUnconditional` at `trustLevel := 0`.
