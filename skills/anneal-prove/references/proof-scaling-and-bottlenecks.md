# Diagnosing and Resolving Lean 4 Kernel Bottlenecks in Anneal Proofs

Because `TrustedBoundary.lean` replays every `Verify.<Crate>.<Item>.verified`
theorem at `trustLevel := 0` and forbids `native_decide` (`Lean.ofReduceBool`),
Lean's kernel reducer (`whnf`) and elaborator must symbolically reduce all MIR
statements, place projections, Tree Borrows checks, and terminators over
universally quantified symbolic inputs. On straight-line single-block functions,
`dsimp` and `rfl` finish in milliseconds. On multi-block branches, `#[spec]`
companions with short-circuiting `&&`/`||` control flow, bitwise operations, or
bounded `while` loops, naive `simp`/`dsimp`/`rw` proofs can trigger quadratic or
exponential term blowup and `maxHeartbeats` timeouts.

This reference catalogs nine primary proof-engineering and interactive-tooling
bottlenecks encountered in Anneal MIR verification and the structural patterns
that eliminate them.

---

## 1. Whole-Body `CapturedMir` Duplication Across Multi-Block CFGs (`BlockCtx` Pattern)

### Symptom
Unfolding `Mir.<Crate>.<Item>.body` inside `dsimp` or `simp` across a function
with multiple basic blocks causes `maxHeartbeats` or `maxRecDepth` timeouts after
a few block transitions.

### Root Cause
Every MIR stepping function (`stepMirState`, `dispatchBlock`, `evalStmt`,
`evalRvalue`) takes `body : CapturedMir` (or `body.localDecls` and
`body.layouts`). When `Mir.<Crate>.<Item>.body` is unfolded in place, Lean
substitutes the literal AST of **all** basic blocks (`BB0..BBn`) into every
intermediate symbolic state. Across $k$ basic-block jumps or branch splits, the
term size grows polynomially or exponentially.

### Solution
Never unfold `body` inside recursive CFG stepping. Instead:
1. Wrap `{ localDecls, layouts, body }` in a small `BlockCtx` structure.
2. Pre-project each basic block `0..n` into a top-level definition (`itemBB0`,
   `itemBB1`, ...).
3. Prove `O(1)` `rfl` lookup lemmas (`itemCtx_bb1 : lookupBlock itemCtx 1 = some itemBB1`,
   `itemCtx_localDecls`, `itemCtx_layouts`, `itemCtx_phase`).
4. Pass `itemCtx_bb1 .. itemCtx_bbn` and `itemBB0 .. itemBBn`—not `body`—to
   `dsimp only [...]` or `rw`.

```lean
private structure BlockCtx where
  localDecls : List LocalDecl
  layouts : LayoutTable
  body : CapturedMir

private def dummyBB : BasicBlockData :=
  { statements := [], terminator := { kind := .unreachable, span := "" }, isCleanup := false }

private def itemBB0 : BasicBlockData :=
  (get? Mir.MyCrate.my_fn.body.basicBlocks 0).getD dummyBB
private def itemBB1 : BasicBlockData :=
  (get? Mir.MyCrate.my_fn.body.basicBlocks 1).getD dummyBB

private def itemCtx : BlockCtx :=
  { localDecls := Mir.MyCrate.my_fn.body.localDecls
    layouts := Mir.MyCrate.my_fn.body.layouts
    body := Mir.MyCrate.my_fn.body }

private theorem itemCtx_localDecls :
    itemCtx.localDecls = Mir.MyCrate.my_fn.body.localDecls := rfl
private theorem itemCtx_layouts :
    itemCtx.layouts = Mir.MyCrate.my_fn.body.layouts := rfl
private theorem itemCtx_phase :
    itemCtx.body.phase = .runtimeOptimized := rfl
private theorem itemCtx_bb1 :
    lookupBlock itemCtx 1 = some itemBB1 := rfl
```

---

## 2. Bit-by-Bit Recursive Unrolling Over Symbolic `Nat`s (`bitwiseAndBitsFast` Pattern)

### Symptom
A single `rw`, `injection`, or final kernel declaration typecheck takes
`60s–150s+` (or hits `maxHeartbeats`) whenever the MIR contains `&`, `|`, `^`, or
bit-shifts over a symbolic input `b : Nat`.

### Root Cause
`Trusted`'s recursive `bitwiseAndBits width a b` (and `bitwiseOrBits` /
`bitwiseXorBits`) recurses `width` times (`8`, `16`, `32`, or `64` iterations),
generating deeply nested `((((b / 2) / 2) ...) % 2)` division trees when `b` is
symbolic. When `rw` or the kernel unifier compares two states containing those
unrolled trees, definitional equality checking explodes.

### Solution
Never include raw `bitwiseAndBits` or `bitwiseOrBits` in a `dsimp only` list
when one argument is symbolic:
- **Algebraic rewrite lemmas:** Prove closed-form rewrite lemmas before
  unfolding (for example, `bitwiseAndBits 8 b 1 = b % 2`,
  `bitwiseAndBits 16 w 255 = w % 256`, and
  `bitwiseOrBits 16 (lo * 256) hi = lo * 256 + hi` for `lo < 256` and
  `hi < 256`).
- **Fast-path evaluator wrapper:** Define a local `bitwiseAndBitsFast` that
  short-circuits the concrete masks used in the function (`1`, `255`, `65535`) to
  `b % 2`, `b % 256`, `b % 65536` and falls back to `bitwiseAndBits` otherwise,
  backed by a one-line `bitwiseAndBitsFast_eq` theorem.

---

## 3. Full-AST Traversal by `rw` on Symbolic Execution Goals (`Hold` Barrier Pattern)

### Symptom
Running `rw [h_eq]` on a goal or hypothesis of the form
`wpMirSym fuel body state post` (or `wpBlockLinear ...`) times out even when
`h_eq` is a tiny arithmetic identity like `Nat.mul 1 8 = 8`.

### Root Cause
Lean's `rw` tactic traverses the entire expression AST to locate occurrences of
the left-hand side. When the goal wraps an unreduced or partially reduced
multi-step symbolic execution tree, `rw` repeatedly traverses thousands of AST
nodes.

### Solution
Wrap large weakest-precondition or symbolic-execution propositions in a single-field
`Prop` wrapper:

```lean
private structure Hold (P : Prop) : Prop where
  val : P
```

Keep the symbolic execution goal wrapped inside `Hold (...)` while applying
structural stepping theorems (`refine hold_wp_full ...`), run a single targeted
`dsimp only [...]` to collapse the symbolic execution tree into a small boolean or
arithmetic residual, and unwrap `apply Hold.val` (or `rcases h_hold with ⟨h_val⟩`)
only at the boundary.

---

## 4. Factoring `#[anneal_spec::spec]` Companion MIR Inversion (`wpReq_inversion` & `ensures_holds`)

### Symptom
Functions with inline `#[anneal_spec::spec(requires: ..., ensures: ...)]` become
unmanageable when a single `verified` theorem tries to step
`__anodized_fn_requires_<item>`, the subject function `<item>`, and
`__anodized_fn_ensures_<item>` in one proof block.

### Root Cause
Each `requires` and `ensures` companion is lowered to its own `MirBoolPredicateHolds`
claim over a separate multi-block MIR body (often 25–45 symbolic steps with
short-circuiting `SwitchInt` branches and overflow checks). Combining all three
MIR executions in one tactic state multiplies the case splits and term size.

### Solution
Factor the proof into three cleanly separated theorems:
1. **`wpReq_inversion` (Backward Precondition Extraction):** A standalone theorem
   that takes `MirBoolPredicateHolds __anodized_fn_requires_<item>.body args` and
   returns pure Lean arithmetic hypotheses (e.g.,
   `∃ b1 b2, v1 = .scalar ⟨b1, 2⟩ ∧ v2 = .scalar ⟨b2, 2⟩ ∧ b1 ≤ 16 ∧ b2 ≤ 1024`),
   discharging impossible branches with `nomatch`.
2. **`ensures_holds` (Forward Postcondition Discharge):** A standalone theorem
   that takes pure arithmetic bounds on `b1, b2, ret` and proves
   `MirBoolPredicateHolds __anodized_fn_ensures_<item>.body [v1, v2, ret]`.
3. **`theorem verified` (Subject Function Execution):** Destructures `h_pre` via
   `wpReq_inversion`, steps only the subject function's MIR once, and closes the
   postcondition by applying `ensures_holds`.

---

## 5. Fuel-Bounded Loop Unrolling and `subst h_fuel` Ordering (`verified_at_fuel` Pattern)

### Symptom
In a loop proof (`runCfgSteps ctx state 120` or `wpCoalBounded ... 120`), all
tactic goals inside `by ...` close with `0` open goals, yet the theorem declaration
itself times out in kernel `whnf` at the `theorem verified` line.

### Root Cause
When `fuel` is instantiated to a large concrete numeral (`120`) in the theorem
statement or before `intro args mem h_pre` and `subst` have destructured `mem :
Memory`, Lean's elaborator or kernel unifier may unfold `runCfgSteps ctx state 120`
while `mem` is still an abstract variable. Without `mem.activeCallee = none` and
concrete `mem.callerLocals` / `mem.borrows` in place, every one of the 120 steps
branches symbolically on `match s.memory.activeCallee`.

### Solution
1. Parameterize the main helper theorem by `(fuel : Nat) (h_fuel : fuel = 120)`:
   ```lean
   private theorem verified_at_fuel (fuel : Nat) (h_fuel : fuel = 120) :
       StatefulVerificationResult Obligations.MyCrate.my_loop.statefulClaim := by
     refine verifySafeCfgSteps fuel ?_
     intro args mem h_pre
     rcases h_pre with ⟨..., h_callee, h_stack, h_borrows, h_caller⟩
     rcases mem with ⟨nextAllocId, globals, borrows, nextTag, callees,
       callStack, activeCallee, activeProtectors, nextProtector, callerLocals⟩
     dsimp at h_callee h_stack h_borrows h_caller
     subst h_callee h_stack h_borrows h_caller
     -- Only substitute `fuel = 120` AFTER `mem` fields are concrete!
     subst h_fuel
     ...
   ```
2. Prove `hasProtectedWriteConflict_nil` once by induction on `borrows` when
   `activeProtectors = .nil` so local variable writes inside the loop reduce
   `hasProtectedWriteConflict` to `false` in `O(1)` without unfolding `borrows`.
3. When indexing into `bb.statements` via `get?`, note that `dsimp` may expose
   `GetElem?.getElem?` (`List.instGetElem?NatLtLength`); keep a helper lemma
   `get?_append_cons : get? (pfx ++ (x :: rest)) (length pfx) = some x` so
   statement dispatch reduces cleanly at each loop step.

---

## 6. Safe Profiling Discipline: Never Use `trace.profiler.threshold 1` in Shell Tasks

### Symptom
Running `lake env lean` with `set_option trace.profiler true` and
`set_option trace.profiler.threshold 1` on a symbolic MIR proof stalls a
background command for hours and writes hundreds of megabytes of trace output to
disk.

### Root Cause
At `threshold 1` (1 ms), Lean's trace profiler pretty-prints the full goal and
expression AST at thousands of internal elaborator steps. Formatting deeply
nested MIR and symbolic bit-vector terms takes orders of magnitude longer than
elaboration itself.

### Solution
1. **Default to warm in-memory MCP tools (`anneal-lean_lsp`):** Use `lean_goal`,
   `lean_multi_attempt`, and `lean_diagnostics` to isolate slow lines in memory
   (~15–25 ms) without spawning cold CLI processes.
2. **If CLI profiling is ever required:**
   - Never set `trace.profiler.threshold` below `50` or `100` (milliseconds).
   - Always include `set_option pp.deepTerms false` and `set_option pp.maxSteps 500`.
   - Always bound the shell invocation with `timeout 30s` and `| head -c 200000`
     so a trace dump can never stall an agent turn.

---

## 7. Bottom-Up `dsimp` Continuation Unrolling and `Decidable` Corruption on `wpMirSym` (Top-Down `change` Pattern)

### Symptom
Passing `wpMirSym`, `wpMirExecSym`, `stepMirExecSymTree`, and
`Trusted.Sequence.length` to `dsimp only [...]` on a symbolic MIR execution goal
either produces a multi-megabyte goal term that takes 8–30+ seconds to elaborate
or causes subsequent `rw` / `simp` calls to fail with `motive is not type
correct` inside `@ite`.

### Root Cause
Two distinct mechanisms in `dsimp` interact poorly with `SymbolicEval`:

1. **Bottom-up simplification inside unapplied continuation lambdas:** `dsimp`
   simplifies subexpressions bottom-up before reducing outer `match` blocks. In
   `wpMirExecSym (fuel + 1) body st post`, the continuation passed to
   `stepMirExecSymTree` is a lambda `fun st' => wpMirExecSym fuel body st' post`.
   When `wpMirExecSym` and `stepMirExecSymTree` are in the `dsimp` unfold set,
   `dsimp` recursively expands `wpMirExecSym` inside that unapplied lambda over
   the **abstract** state parameter `st'` for all remaining `fuel` steps,
   building a full symbolic branching tree before `stepMirExecSymTree` reduces
   the concrete state `st` to `.leaf (.tau st₁)`. Passing an unnecessarily large
   fuel bound (such as `fuel = 10` or `16` on a 4-statement basic block)
   compounds this blowup by a factor of 20–25x.
2. **Implicit-transparency `Decidable` mismatch when unfolding
   `Trusted.Sequence.length`:** Inside `stepMirSymTree`, statement dispatch
   branches on `@ite _ (stmtIdx < length bb.statements)
   (Nat.decLt stmtIdx (length bb.statements)) ...`. Because `dsimp` does not
   simplify inside `implicit` instance arguments (`Nat.decLt ...`), including
   `Trusted.Sequence.length` in `dsimp only [...]` reduces the proposition
   `stmtIdx < length bb.statements` to `0 < 3` while leaving the `Decidable`
   instance typed at `Decidable (0 < length bb.statements)`. Any subsequent
   `rw` over the goal fails to typecheck the `@ite` application.

### Solution
1. **Use top-down `change` instead of `dsimp` to step `wpMirSym` /
   `holdBoolMirSym`:** Lean's kernel definitional equality (`isDefEq`, invoked by
   `change TargetProp` or `exact`) reduces `wpMirSym` lazily **top-down
   (weak-head normal form)**. It reduces `stepMirExecSymTree` on the concrete
   state `st` to `.leaf (.tau st₁)` *before* substituting `st₁` into the
   continuation, so `wpMirExecSym` never unfolds over an abstract state `st'`
   and `Decidable` instances remain definitionally consistent.
2. **Never include `wpMirExecSym` or `Trusted.Sequence.length` in `dsimp`:** If
   you must inspect one step manually without `change`, use `unfold wpMirSym;
   unfold wpMirExecSym` one step at a time rather than `dsimp`.
3. **Keep straight-line `fuel` bounds tight (`#statements + 2`):** On a single
   basic block with $k$ statements and a `return` terminator, pass `fuel = k + 1`
   or `k + 2` (typically `4`–`6`) to `verifyMirNoPanicSym`, `verifyByWP`, or
   `verifyStatefulByWP` rather than `10` or `64`.

---

## 8. Escaping `whnf` Timeouts on `bitwiseOrBits` and Stateful `Memory` Post-States (Wildcard `change ... _` Pattern)

### Symptom
On a stateful obligation (`StatefulVerificationResult`) or a function combining
bit-shifts (`<<`) with bitwise OR/AND (`|` / `&`), even when you have proved a
closed-form lemma like `bitwiseOrBits_32_mul256_add` and avoided `dsimp`,
writing an explicit `change` target that spells out `bitwiseOrBits 32 ...` or the
final `Memory` record fails with `(deterministic) timeout at whnf, maximum
number of heartbeats (800000) has been reached`.

### Root Cause
In the raw output of `wpMirSym`, the bit-width argument of `bitwiseOrBits` is an
unreduced layout projection `{ bits := ..., sizeBytes := 4 }.sizeBytes.mul 8`
(or `Nat.mul 4 8`), and the post-state memory is an unreduced projection
`(advanceStmt ...).memory`. When `change` asks `isDefEq` to unify
`bitwiseOrBits 32 (hi * 256) lo` against
`bitwiseOrBits ({ ... }.sizeBytes.mul 8) (shiftLeftBits hi 8 (scalarModulus 4)) ...`,
Lean's heuristic unfolds `bitwiseOrBits` 32 recursive levels deep before
reducing the width projection, triggering exponential unification over the
symbolic arguments `hi` and `lo`.

### Solution
Never force `change` to unify concrete bit-widths or explicit `Memory` records
at the same time that it reduces `wpMirSym`. Instead, separate symbolic stepping
from projection reduction in three fast steps:

1. **Step `wpMirSym` with `_` wildcards in `change` (~15 ms):** Leave `_`
   placeholders for the branch condition and postcondition arguments so `isDefEq`
   unifies the unreduced subterms by reflexivity without unfolding
   `bitwiseOrBits` or `Memory`:
   ```lean
   change
     match (4294967296 : Nat).ble _ with
     | true => False
     | false => myStatefulClaim.post _ _ _ _
   ```
2. **Collapse record projections with a minimal `dsimp only` (~15 ms):** Inspect
   the wildcard terms with `lean_goal`, then run:
   ```lean
   dsimp only [advanceStmt, myStatefulClaim]
   ```
   Because `bitwiseOrBits` is **not** in the `dsimp only` list, this reduces
   `{ ... }.sizeBytes.mul 8` to `32` and `(advanceStmt ...).memory` to the
   concrete post-state `Memory` literal in milliseconds without touching the
   bitwise operations.
3. **Rewrite the bitwise subterms and close with `omega` / `rfl` (~20 ms):** Now
   that the width argument is syntactically `32`, apply `rw [h_shl_hi, h_shl_lo,
   bitwiseOrBits_32_mul256_add]` and split on the overflow guard. This 3-step
   pattern replaces 300+ lines of manual per-statement `MachineState` stepping
   lemmas with a ~20-line proof block.

---

## 9. Interactive LSP Tooling Threshold Heuristic (`edit_file` + Hook vs. `lean_goal` / `lean_multi_attempt`)

### Symptom
An agent with access to warm Lean 4 LSP/MCP tools (`lean_goal`,
`lean_multi_attempt`, `lean_diagnostics`) takes *longer* on simple obligations or
spends 15+ consecutive turns calling `lean_multi_attempt` with slightly tweaked
`dsimp only [...]` lists.

### Root Cause
Although each in-memory `lean_multi_attempt` or `lean_diagnostics` call finishes
in ~15–25 ms, every extra tool call adds an LLM reasoning turn (~20–40 seconds
of wall-clock latency). Two anti-patterns dominate that overhead:

1. **Redundant pre-verification below the complexity threshold:** When an
   obligation is a straightforward arithmetic identity (`omega`), a known
   `#[spec]` combinator (`dischargeRustEqU32`), or a simple 1-block `rfl` proof,
   calling `lean_diagnostics` or `lean_multi_attempt` *before* `edit_file`
   doubles the turn count because the `PostToolUse` hook already runs warm
   `lean_diagnostics` automatically on every `edit_file`.
2. **The `lean_multi_attempt` "slot-machine" loop:** When `dsimp` fails to
   reduce a symbolic goal (see Sections 7 and 8), guessing 10–15 permutations of
   `dsimp only [...]` via `lean_multi_attempt` treats a structural WHNF problem
   as a syntax search problem.

### Solution
Follow a strict two-regime threshold heuristic:

1. **Below the threshold (routine arithmetic, standard combinators, known 1-block
   templates):** Write the complete candidate proof directly with `edit_file` and
   rely on the automatic `PostToolUse` hook to verify it in the same turn. Do not
   call `lean_diagnostics` or `lean_multi_attempt` first.
2. **Cap `lean_multi_attempt` at 1–2 probes per subgoal:** Use
   `lean_multi_attempt` to test distinct tactic strategies in parallel (e.g.,
   `["rfl", "omega", "simp", "exact ⟨rfl, rfl⟩"]`), never to brute-force symbol
   unfold lists. If 1–2 probes do not close the goal, stop probing.
3. **Above the threshold (switch immediately to wildcard `change ... _` +
   `lean_goal` and `lean_local_search`):** As soon as a goal involves multi-step
   `wpMirSym` branches, `bitwiseOrBits` / `bitwiseAndBits`, or stateful `Memory`
   / Tree Borrows updates, write a wildcard `change ... _` + `sorry` via
   `edit_file`, inspect the exact WHNF terms with `lean_goal` (~15 ms), and use
   `lean_local_search` / `lean_hover` to locate existing `Anneal.*` lemmas
   instead of reading `trusted/lean/` source files or hand-writing intermediate
   `MachineState` records.
