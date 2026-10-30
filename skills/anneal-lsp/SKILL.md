---
name: anneal-lsp
description: >-
  Interactive Lean 4 (`lake serve`) and Rust semantic workflow using the
  `anneal-lean` plugin's warm MCP tools (`lean_goal`, `lean_multi_attempt`,
  `lean_diagnostics`, `lean_hover`, `lean_definition`, `lean_outline`,
  `lean_local_search`, `anneal_audit_preview`, `anneal_item_bridge`,
  `rust_diagnostics`, `rust_symbols_and_def`), zero-turn hooks, and the Live
  InfoView AuxPane. Use whenever writing, debugging, or auditing Lean 4 proofs
  or Rust verification obligations in `anneal`, `anneal-private`, or `zerocopy`.
---

# Interactive Lean 4 & Rust Verification with `anneal-lean` (`anneal-lsp`)

Pair this skill with `anneal-prove` (which documents Anneal's proof patterns:
`verifyByWP`, `verifyStatefulByWP`, `wp_frame_disjoint`, and `Anneal.BitValidity`).
Instead of iterating with multi-second cold `(cd .anneal && lake env lean ...)`
subprocesses, drive proof construction interactively against the warm `lake serve`
worker pool (~11–25 ms incremental checks).

## Fast Interactive Proof Loop

1. **Map the Rust Item & Obligation (`anneal_item_bridge`)**:
   ```json
   {"workspace": "/home/groupagent-anneal-bot/Projects/<ldap>/zerocopy/zerocopy/anneal-slice", "query": "BigEndianU16"}
   ```
   Inspects `.anneal/spec-lock.json`, `DefId`, stateful vs. stateless claim kind,
   and exact paths to `Mir`, `Obligations`, `Specs`, and `Proof` modules.

2. **Inspect Signatures Token-Cheaply (`lean_outline`, `lean_local_search`, `lean_hover`, `lean_definition`)**:
   - Call `lean_outline` on `Obligations/<Crate>/<Item>.lean`, `Specs/<Crate>/<Item>.lean`,
     or `theory/Anneal/` files to view theorem/structure signatures without loading
     entire proof bodies into context.
   - Call `lean_local_search` (e.g., `{"query": "swapBytes16", "workspace": "..."}`)
     to discover existing `Anneal.*` and `Trusted.*` lemmas.
   - Call `lean_hover` or `lean_definition` with `symbol` (e.g., `{"file": "...", "line": 24, "symbol": "dischargeStatelessOk"}`)
     — no manual UTF-16 column counting required.

3. **Scaffold With `sorry` & Read Automatic Hook Goals**:
   - Write or edit `anneal/proofs/Proof/<Crate>/<Item>.lean` with `write_file` or `edit_file`.
   - The `PostToolUse` hook automatically elaborates the edited `.lean` file in the
     warm `lake serve` worker and appends compiler errors and open `sorry` proof
     goals directly to the `edit_file`/`write_file` tool result!

4. **Branch & Test Candidate Tactics In Memory (`lean_goal` & `lean_multi_attempt`)**:
   - Call `lean_goal({"file": "...", "line": 22})` to see **both** the goal *before*
     and *after* the tactic on `line` (plus `term_goal` in term mode).
   - Call `lean_multi_attempt` on a `sorry` or tactic line to test up to 12 candidate
     tactics in ~15 ms each with **zero disk writes**:
     ```json
     {
       "file": "/home/groupagent-anneal-bot/Projects/<ldap>/.../Proof/Crate/Item.lean",
       "line": 25,
       "tactics": [
         "rfl",
         "exact ⟨rfl, rfl⟩",
         "simp [ih]",
         "omega"
       ]
     }
     ```
   - Apply the winning tactic via `edit_file`.

5. **Pre-Flight Kernel Axiom & Isolation Audit (`anneal_audit_preview`)**:
   - Before running the full workspace `cargo anneal agent-verify`, run:
     ```json
     {"file": "/home/groupagent-anneal-bot/Projects/<ldap>/.../Proof/Crate/Item.lean"}
     ```
   - Verifies in ~30 ms:
     1. `0` Lean compiler errors and `0` `sorry`/`admit` tokens,
     2. `Anneal.*` (`theory/`) does not leak into the `verified` theorem statement,
     3. In-memory `#print axioms` confirms zero `sorryAx` and zero `Lean.ofReduceBool`
        (`native_decide`).

6. **Final End-to-End Acceptance**:
   - Run `cargo anneal agent-verify` via `run_command` from the crate root to
     regenerate `.anneal/generated/`, build all `Verify.*` targets, and replay
     `TrustedBoundary`. (The daemon automatically detects `.anneal/lakefile.toml`
     regeneration and refreshes that workspace's `lake serve` worker on the next query.)

## Kernel Proof Scaling Patterns & Bottleneck Antidotes

Because `TrustedBoundary` forbids `native_decide` (`Lean.ofReduceBool`), Lean's
kernel (`whnf`) must symbolically reduce every MIR step. When proving multi-block
CFGs, `#[anneal_spec::spec]` functions, bitwise operations, or loops:

1. **Pre-Project Basic Blocks (`BlockCtx` + `itemBB0..itemBBn`)**:
   Never unfold `Mir.<Crate>.<Item>.body` in `dsimp` across multi-block CFGs;
   unfolding `body` substitutes the entire basic-block list into every step
   state. Define top-level `itemBBk` constants and `O(1)` `rfl` lookup lemmas
   (`lookupBlock itemCtx k = some itemBBk`).
2. **Short-Circuit Symbolic Bit-Loops (`bitwiseAndBitsFast`)**:
   Unfolding recursive `bitwiseAndBits` / `bitwiseOrBits` over a symbolic
   `b : Nat` unrolls 8–64 nested `Nat.div · 2` trees and stalls kernel
   unification for `100s+`. Rewrite masks using closed-form arithmetic (`b % 2`,
   `b % 256`, `lo * 256 + hi`) or a fast-path wrapper proved equal to
   `bitwiseAndBits`.
3. **Shield Symbolic Execution States From `rw` (`Hold` Barrier)**:
   Wrap large weakest-precondition propositions in
   `private structure Hold (P : Prop) : Prop where val : P` so `rw` does not
   traverse the full symbolic execution AST before `dsimp only` collapses it.
4. **Factor `#[anneal_spec::spec]` Companions Into Boundary Theorems**:
   Prove standalone `wpReq_inversion` (extracting pure arithmetic bounds from
   `MirBoolPredicateHolds __anodized_fn_requires_*`) and `ensures_holds`
   (discharging `MirBoolPredicateHolds __anodized_fn_ensures_*` from arithmetic
   bounds) instead of stepping all three MIR bodies in one proof block.
5. **Substitute Loop `fuel` Only After Destructuring `Memory` (`verified_at_fuel`)**:
   In loop proofs (`runCfgSteps ctx state fuel`), parameterize by
   `(fuel : Nat) (h_fuel : fuel = N)`, `rcases` and `subst` all `Memory` fields
   first (`activeCallee = none`, `callerLocals`, `borrows`), and `subst h_fuel`
   last so kernel `whnf` never unfolds `N` steps over an abstract `mem : Memory`.
6. **Never Run `trace.profiler.threshold 1` on Symbolic MIR Proofs**:
   Low profiler thresholds recursively format huge nested MIR ASTs at thousands
   of elaborator steps, writing hundreds of megabytes of trace output and
   stalling background commands for hours. Prefer `lean_goal` and
   `lean_multi_attempt`; if CLI profiling is ever required, keep
   `trace.profiler.threshold >= 100` with `set_option pp.deepTerms false` and
   `timeout 30s`.

---

## Threshold Heuristic: When to Use Direct `edit_file` vs. Precision LSP Tools

Empirical A/B benchmarking shows a clear threshold between tasks where an educated
guess in a single `edit_file` is fastest and tasks where interactive `lean_goal` /
`lean_multi_attempt` saves 10–15+ minutes of blind source reading and `whnf` timeouts:

1. **Below the Threshold (Fast Path — Direct `edit_file` Relying on `PostToolUse` Hook)**:
   - For pure arithmetic (`omega`), standard `#[spec]` pin combinators (`dischargeRustEqU32`),
     or straightforward `verifyMirNoPanicSym` proofs where you already know the branch structure,
     **draft the proof directly with `edit_file`**.
   - Because `PostToolUse` automatically runs warm `lean_diagnostics` (~15–300 ms) on every
     `edit_file`, pre-testing obvious tactics with `lean_multi_attempt` first only adds an
     extra round-trip turn (~35s of LLM latency).
   - **Cap `lean_multi_attempt` at 1–2 probes per subgoal**: Use `lean_multi_attempt` to test
     distinct tactic strategies (`["rfl", "omega", "simp", "exact ⟨rfl, rfl⟩"]`), never to
     brute-force 10+ permutations of `dsimp only [...]` symbol lists.

2. **Above the Threshold (Precision Path — Switch Immediately to Wildcard `change` + `lean_goal`)**:
   - **Never unfold `wpMirExecSym` or `Trusted.Sequence.length` inside `dsimp`**:
     `dsimp` simplifies bottom-up inside unapplied continuation lambdas (`fun st' => wpMirExecSym fuel' ...`),
     building multi-megabyte branching trees over an abstract state `st'`, and unfolding
     `Trusted.Sequence.length` inside `dsimp` corrupts implicit `Decidable` instances (`Nat.decLt`)
     inside `@ite`. Keep straight-line `fuel` bounds tight (`#statements + 2`, typically `4–6`).
   - **Use the Wildcard `change` + `lean_goal` Pattern**:
     When `wpMirSym` or `holdBoolMirSym` needs to step through symbolic MIR branches, write:
     ```lean
     change
       match (4294967296 : Nat).ble _ with
       | true => False
       | false => myClaim.post _ _ _ _
     sorry
     ```
     and inspect the goal with `lean_goal` (or read the automatic `PostToolUse` `sorry` goal).
     Lean's top-down kernel `isDefEq` reduces the `SymTree` in lazy WHNF and fills the `_`
     wildcards with the exact unreduced terms (e.g. `shiftLeftBits hi 8 (scalarModulus 4)`,
     `bitwiseOrBits (Nat.mul 4 8) ...`, or `(advanceStmt ...).memory`).
   - **Escaping `whnf` Timeouts on `bitwiseOrBits` / Stateful `Memory`**:
     If specifying concrete arguments inside `change` triggers a `(deterministic) timeout at whnf`
     (typically because `isDefEq` tries to unify `32` against `{ bits := ..., sizeBytes := 4 }.sizeBytes.mul 8`
     and unfolds 32 recursive levels of `bitwiseOrBits`), keep `_` wildcards in `change`, run
     `dsimp only [advanceStmt, myClaim]` to collapse the record projections without unfolding
     `bitwiseOrBits`, and then `rw` your `shiftLeftBits` / `bitwiseOrBits_32_mul256_add` lemmas.
