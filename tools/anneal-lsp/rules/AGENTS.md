# Anneal Lean 4 & Rust Interactive LSP Tooling (`anneal-lean`)

When working on Lean 4 (`*.lean`) files or Anneal Rust verification crates (`~/Projects/<ldap>/{anneal,anneal-private,zerocopy}`):

1. **Prefer Warm Lean 4 LSP MCP Tools (`anneal-lean_lsp`) Over Cold `lake env lean` Loops**:
   - Use `lean_goal` to inspect tactic goals (both *before* and *after* a line) and expected term types in ~12–25 ms without cold process startup.
   - Use `lean_multi_attempt` to test up to 12 candidate tactics purely in memory via LSP `didChange` overlays (zero disk writes, never touches `.anneal/spec-lock.json`).
   - Use `lean_hover`, `lean_definition`, `lean_outline`, and `lean_local_search` to inspect `Trusted.*`, `Anneal.*`, `Mir.*`, `Specs.*`, and `Obligations.*` declarations without reading entire large `.lean` files.
   - Use `anneal_audit_preview` to verify 0 compiler errors, 0 `sorry` tokens, `Anneal.*` statement-origin isolation, and kernel `#print axioms` in memory before running final end-to-end `cargo anneal agent-verify`.
   - Use `anneal_item_bridge`, `rust_diagnostics`, and `rust_symbols_and_def` to map between Rust items (`#[spec]`, `#[anneal_spec::...]`) and generated/authored Lean modules.
   - Load the `anneal-lsp` skill (alongside `anneal-prove`) for full interactive proving workflows.

2. **Automatic Hook Feedback & Spec-Lock Enforcement**:
   - Editing or writing any `*.lean` file automatically appends `[Anneal Lean 4 LSP]` compiler diagnostics and open `sorry` goals directly to the tool output via `PostToolUse` — you do not need an extra `lean_diagnostics` call immediately after `edit_file` / `write_file`.
   - When `.anneal/spec-lock.json` is active in a crate, `PreToolUse` enforces that only `anneal/proofs/Proof/<Crate>/<Item>.lean` is modified.

3. **Threshold Heuristic — Educated Guess (`edit_file` + Hook) vs. Precision LSP Tooling (`lean_goal` / `lean_multi_attempt`)**:
   - **Below the Threshold (Routine Arithmetic, Known Combinator Calls, Straightforward Proofs)**:
     - Do **not** waste extra tool turns calling `lean_diagnostics` or `lean_multi_attempt` before an obvious `omega`, `simp`, `rfl`, or known `verifyMirNoPanicSym` proof template. Write the complete draft directly via `edit_file` — the `PostToolUse` hook automatically runs warm LSP verification in ~15–300 ms and returns any remaining `sorry` or error goals in the same turn.
     - **Cap `lean_multi_attempt` at 1–2 probes per subgoal**: Use `lean_multi_attempt` to test distinct tactic strategies in parallel (`["rfl", "omega", "simp"]`), never to brute-force 10+ permutations of `dsimp only [...]` symbol lists (each extra LLM turn costs ~35s).
   - **Above the Threshold (Turn On Precision LSP Tools Immediately When Any of These Occur)**:
     1. **Symbolic Evaluator (`wpMirSym` / `holdBoolMirSym`) Does Not Collapse via `simp`/`dsimp`**: Never include `wpMirExecSym` or `Trusted.Sequence.length` in `dsimp` (bottom-up `dsimp` unfolds `wpMirExecSym` inside unapplied `fun st' => ...` continuations over an abstract state `st'`, and unfolding `Trusted.Sequence.length` corrupts implicit `Decidable` instances inside `@ite`). Instead, write a **wildcard top-down `change`** (`change match _ with | true => _ | false => _` + `sorry`) via `edit_file` with tight `fuel` (`#statements + 2`, typically `4–6`), and call `lean_goal` once (~15 ms) to inspect the exact kernel WHNF terms (`(scalarModulus 4)`, `(advanceStmt ...).memory`, `Nat.mul 4 8`).
     2. **Opaque `whnf` / `isDefEq` Timeouts (e.g. `bitwiseOrBits 32` / `bitwiseAndBits` / `Memory` Post-States)**: When a full-proof `change` times out, use `lean_goal` with `_` wildcards in the `change` pattern to isolate which subterm has an unreduced projection (such as `{ bits := ..., sizeBytes := 4 }.sizeBytes.mul 8` vs. `32`, or `(advanceStmt ...).memory`), then collapse that projection with a targeted `dsimp only [advanceStmt, <claim>]` before rewriting.
     3. **Unfamiliar Lemma Names or Signatures**: Use `lean_local_search` and `lean_hover` (~15 ms) instead of reading hundreds of lines of `trusted/lean/` or `theory/Anneal/` source files.

4. **Kernel Proof Scaling & Anti-Stall Guardrails**:
   - **Never run `lake env lean` with `trace.profiler.threshold 1` (or `< 50`) on symbolic MIR proofs**: Low profiler thresholds recursively pretty-print huge symbolic ASTs at thousands of elaborator steps, generating hundreds of megabytes of logs and multi-hour task stalls. Use `lean_goal` / `lean_multi_attempt`, or keep `trace.profiler.threshold >= 100` with `set_option pp.deepTerms false` and `timeout 30s`.
   - **Multi-Block CFGs, Bitwise Ops, `#[spec]` Companions, and Loops**:
     - Do **not** include `Mir.<Crate>.<Item>.body` in `dsimp` across multi-block CFGs (which duplicates all basic blocks at every step); pre-project `itemBB0..itemBBn` with `O(1)` `rfl` lookup lemmas (`BlockCtx`).
     - Do **not** unfold recursive `bitwiseAndBits` / `bitwiseOrBits` over symbolic `b : Nat`; rewrite with closed-form masks (`b % 2`, `b % 256`, `lo * 256 + hi`) or a fast-path `bitwiseAndBitsFast` wrapper.
     - Shield large symbolic execution terms from `rw` AST traversal using `private structure Hold (P : Prop) : Prop where val : P`.
     - Factor `#[anneal_spec::spec]` proofs into standalone `wpReq_inversion` and `ensures_holds` boundary theorems.
     - In loop proofs (`runCfgSteps ctx state fuel`), parameterize by `(fuel : Nat) (h_fuel : fuel = N)` and `subst h_fuel` **only after** `rcases`/`subst` has made all `mem : Memory` fields concrete (`verified_at_fuel`).
