---
name: anneal-prove
description: >-
  Construct kernel-checked Lean 4 proofs for Rust verification obligations in an
  Anneal workspace. Use when discharging `VerificationResult` or
  `StatefulVerificationResult` theorems under `anneal/proofs/Proof/` using
  `cargo anneal agent-context`, `lake env lean`, and `cargo anneal agent-verify`.
---

# Proving Rust Obligations with Anneal (`anneal-prove`)

Discharge per-item Rust verification obligations by authoring Lean 4 proof
modules under `anneal/proofs/Proof/<Crate>/<Item>.lean` that establish
`VerificationResult Obligations.<Crate>.<Item>.claim` (for stateless contracts)
or `StatefulVerificationResult Obligations.<Crate>.<Item>.statefulClaim` (for
heap- and borrow-stateful contracts).

## Workspace boundaries and anti-cheating rules

Before an agent begins proof construction, the orchestrator or developer locks
the workspace's captured MIR and specification state into
`.anneal/spec-lock.json` via `cargo anneal lock-specs`. Final acceptance runs
`cargo anneal agent-verify` (`cargo anneal verify --locked-specs`), which
enforces four invariants:

1. **Write only to `anneal/proofs/Proof/<Crate>/<Item>.lean`.** Every other path
   in the workspace is read-only during proof construction.
2. **Do not create, edit, or delete `anneal/proofs/Specs/<Crate>/<Item>.lean`.**
   Generated `Obligations.<Item>` modules register a `priority := low`
   `defaultSpec` instance of `ItemSpec "<def_id>"`. Creating an unlocked
   `Specs/<Item>.lean` file with a normal-priority `ItemSpec` instance (or
   modifying an existing locked `Specs` file to weaken `pre` to `False` or
   `post` to `True`) fails `verify_spec_lock` and `check_specs_non_vacuous`
   before Lake runs.
3. **Do not declare `sorry`, `admit`, or unauthorized `axiom` constants.**
   `TrustedBoundary` replays the compiled `.olean` environment in the Lean 4
   kernel and inspects the transitive constant closure of
   `Verify.<Crate>.<Item>.verified`. Any dependency on `sorryAx` or on an axiom
   outside a locked `Assumptions.<Crate>.<Item>` module is rejected. When
   `.anneal/spec-lock.json` locks zero `Assumptions` files, `--allow-assumptions`
   and `VerifiedConditional` outcomes are forbidden altogether.
4. **Do not edit `.anneal/generated/**`, `.anneal/lakefile.toml`, or Rust
   sources.** `cargo anneal agent-verify` verifies captured MIR SHA-256 digests
   against `.anneal/spec-lock.json` and deterministically regenerates
   `.anneal/generated/{Mir,Obligations,Verify}` before invoking `lake build`.

## Step-by-step proof workflow

### 1. Inspect the obligation context

Run `cargo anneal agent-context` to inspect the workspace summary, proof status
(`Present` vs. `Missing`), active specification lock status, and per-item Lean
modules:

```bash
# Inspect all verification items in the workspace:
cargo anneal agent-context

# Focus on a single item by Rust DefId substring or Lean module suffix:
cargo anneal agent-context --item CanaryPkg.identity_u32

# Reuse already-extracted unit manifests without re-running cargo check:
cargo anneal agent-context --from-units --item identity_u32
```

For each matched item, `agent-context` prints:
- `def_id`, `item_module_suffix`, `is_stateful` (`StatefulItemSpec` vs.
  `ItemSpec`), and the target path `anneal/proofs/Proof/<Crate>/<Item>.lean`;
- `.anneal/generated/Obligations/<Crate>/<Item>.lean`, showing `defaultPre`,
  `defaultPost`, `claim`, and `statefulClaim`;
- `anneal/proofs/Specs/<Crate>/<Item>.lean`, when a locked specification
  override exists on disk;
- `.anneal/generated/Mir/<Crate>/<Item>.lean`, showing the lowered `layouts :
  LayoutTable` and `body : CapturedMir`; and
- a starter `Proof.<Crate>.<Item>` module template when the proof file does not
  yet exist.

### 2. Author `anneal/proofs/Proof/<Crate>/<Item>.lean`

Every proof file imports `Trusted`,
`Anneal`, `Mir.<Crate>.<Item>`, any locked `Specs.<Crate>.<Item>`, and
`Obligations.<Crate>.<Item>`. Its theorem name and type must match the signature
expected by `.anneal/generated/Verify/<Crate>/<Item>.lean`:

- **Stateless item (`is_stateful == false`)**:
  ```lean
  theorem verified : VerificationResult Obligations.<Crate>.<Item>.claim
  ```
- **Stateful item (`is_stateful == true`)**:
  ```lean
  theorem verified : StatefulVerificationResult Obligations.<Crate>.<Item>.statefulClaim
  ```

Never reference definitions from `Anneal.*` (`theory/`) in the theorem statement
(`ci.type`); `Anneal.*` lemmas belong exclusively inside the proof term
(`ci.value?`).

### 3. Iterate on a single proof file (`anneal-lean_lsp` or `lake env lean`)

When the `anneal-lean_lsp` MCP server (`anneal-lsp` skill) is active, editing a
`*.lean` file automatically runs warm `lake serve` diagnostics (~15–300 ms) via
the `PostToolUse` hook and appends compiler errors and open `sorry` goals to the
tool output:

- **Below the complexity threshold** (routine arithmetic `omega`, standard
  `#[spec]` pin combinators, or known 1-block `rfl` templates): Write the
  complete proof directly via `edit_file` and let the hook verify it in the same
  turn; do not waste a pre-edit turn calling `lean_diagnostics` or
  `lean_multi_attempt`.
- **Above the complexity threshold** (multi-step `wpMirSym` branches,
  `bitwiseOrBits`, or stateful `Memory` / Tree Borrows goals): Write a wildcard
  `change ... _` + `sorry` via `edit_file` and inspect the WHNF goal with
  `lean_goal` (~15 ms). Cap `lean_multi_attempt` at 1–2 probes per subgoal
  (never micro-looping to guess `dsimp` lists).

When iterating from the CLI without `anneal-lean_lsp`, ensure
`.anneal/lakefile.toml` registers the `Proof` library root, then run
`lake env lean` inside `.anneal/` wrapped with `anneal-lean-run` (or
`scripts/anneal-lean-run`) for single-file feedback without rebuilding the
entire workspace:

```bash
(cd .anneal && anneal-lean-run --mode file -- lake env lean ../anneal/proofs/Proof/<Crate>/<Item>.lean)
```

Never run bare unbounded `lake env lean` or rely solely on `lean -M <MB>` when
testing reproducers or proofs with elevated `maxHeartbeats`: Lean's `-M` flag
bounds only its internal small-object allocator and does not cap total process
RSS or prevent swap thrashing when kernel `whnf` diverges. `anneal-lean-run`
probes the host's CPU cores and physical RAM (`MemTotal` and `MemAvailable`),
scales thread count (`LEAN_NUM_THREADS`) by active worktree concurrency
(`--concurrency <W>`), and enforces a hard physical RAM cap (`MemoryMax` with
`MemorySwapMax=0`) and wall-clock timeout so runaway reductions fail fast (`exit
137` or `124`) with zero swap paging.

### 4. Apply standard Anneal proof patterns (lift first, evaluate last)

The primary workflow is to *lift* MIR into fuel-free judgments rather than to
evaluate a fuel-indexed weakest precondition: `#mir_lift` (Pattern A),
`#mir_lift_spec` (Pattern B), `forRangeUp` (Pattern C), and
`Anneal.SepLogicLenses` (Pattern D). Never hand-write `BlockCtx` wrappers or
pick `fuel` numerals in `Proof/` files.

`#mir_lift` itself is a command elaborator in the tool module
`theory/Anneal/MirLift.lean`, which imports `Lean` and sits outside the audited
`Anneal` umbrella; `TrustedBoundary` parses `Proof/*.lean` with only `Init` and
`Std` syntax and admits only declaration commands, so `Proof/` files (and
audited `theory/` modules) apply the lifting *rules* explicitly instead. Never
widen `trusted/audit/TrustedBoundary.lean` to admit `elab`, `syntax`, `macro`,
or `macro_rules`.

#### Pattern A: `#mir_lift` rules for call-free, alias-free bodies

Check `#eval Anneal.PureMirExec.checkPureMir Mir.<Crate>.<Item>.body` in a
scratch file first. If it is `true`, reduce the obligation to the alias-erased
executor with
`verifyMirNoPanic_of_pureExec` (or `verifyMirSafe_of_pureExec`,
`verifyTotalMir_of_pureExec`, `verifyStatefulMirNoPanic_of_pureExec`), which
are proved once and for all through `mirWpConverges_of_pureExec`. Then lift the
body block by block with `lift_PureMirConverges`, `LiftBlock.of_lookup`, and
`LiftStmtsTerminator.{cons_eval, term_assert, term_switchInt, term_goto,
term_drop, term_return}`:

```lean
theorem verified : VerificationResult Obligations.WireframeDemo.frame_total_len.claim := by
  refine verifyMirNoPanic_of_pureExec _ rfl fun args h_pre => ?_
  rcases h_pre with ⟨h_len, h_req⟩
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    rcases args with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
    all_goals first | exact ⟨_, _, rfl⟩ | nomatch h_len
  obtain ⟨b1, b2, rfl, rfl, hb1, hb2⟩ := wpReq_inversion v1 v2 h_req
  -- bb0: `_3 = AddWithOverflow(_1, _2); assert(!_3.1) -> bb1`
  apply lift_PureMirConverges (by rfl)
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_assert (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  · change (match Nat.ble 65536 (Nat.add b1 b2) with | true => 1 | false => 0) = 0
    rw [Anneal.FunctionalTranslation.nat_ble_eq_false_of_lt (by change b1 + b2 < 65536; omega)]
  -- bb1: `_0 = move _3.0; return`
  apply LiftBlock.of_lookup (by rfl)
  apply LiftStmtsTerminator.cons_eval (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  apply LiftStmtsTerminator.term_return (by rfl) (Or.inr rfl) (by rfl) (by rfl)
  -- the remaining goal is `claim.post args retVal`
  ...
```

- Use `apply`, not `refine … (fuel := ?_)`: the step budget is a natural
  metavariable that each rule instantiates (`term_goto` contributes `fuel + 1`,
  `term_return` closes it), so no fuel numeral is ever written. A named `?fuel`
  is synthetic-opaque and blocks this unification.
- Pass every evaluation premise as a postponed `(by rfl)` block, never as the
  term `rfl`: the rule must first unify with the goal so that `stmts`,
  `stmtIdx`, and `env` are known when the premise is checked. The phase
  premise is `Or.inr rfl` for the `.runtimeOptimized` bodies that
  `cargo anneal` captures and `Or.inl rfl` for `.runtimePostCleanup` fixtures.
- `cons_eval`, `term_assert`, and `term_switchInt` evaluate one statement or
  operand with symbolic values (for example `b1 + b2`). A symbolic `assert`
  leaves a `match Nat.ble … with` side goal; a symbolic `switchInt` needs a
  case split before it, passing `(target := …)` and proving the
  `lookupSwitchTarget` premise with `change` + `rw` (see
  `Proof/WireframeDemo/clamp_payload_window.lean`).
- On closed or argument-pinned bodies every premise is concrete, so one loop
  lifts the whole CFG, including loops it unrolls
  (`examples/mir/MirVerification.lean`, `countdownTotalClaim_verified`):

  ```lean
  apply Anneal.MirLiftCore.lift_PureMirConverges (by rfl)
  repeat (first
    | apply Anneal.MirLiftCore.LiftBlock.of_lookup (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.cons_eval (by rfl) (Or.inl rfl) (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_goto (by rfl) (Or.inl rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_switchInt (by rfl) (Or.inl rfl) (by rfl)
        (by rfl) (by rfl)
    | apply Anneal.MirLiftCore.LiftStmtsTerminator.term_return (by rfl) (Or.inl rfl) (by rfl)
        (by rfl))
  ```
- Long straight-line blocks: the `rfl` of `cons_eval` assigns the next locals
  unreduced, and nested `List.set` towers are re-evaluated without sharing, so
  per-statement cost with repeated `cons_eval` doubles across long basic blocks.
  Evaluate the rest of a block in one pass with
  `LiftStmtsTerminator.eval_rest (by rfl) (Or.inr rfl) (by rfl)`, which takes
  the statement count from the block and flattens the locals with
  `forcePureEnv?` after each statement, or step one statement with
  `LiftStmtsTerminator.cons_eval_norm`. For an rvalue that `rfl` cannot
  evaluate (a transmute of symbolic bytes, say), prove its value in a separate
  lemma and pass it to `evalPureStmtNorm_assign_local_of_evalRvalue` (see
  `Proof/WireframeDemo/decode_wire_header.lean`).
- Split a branching proof into lemmas that each conclude
  `PureMirConverges body (initPureState body args) post` and begin with
  `apply lift_PureMirConverges (by rfl)`, so every lemma infers its own step
  budget. Do not state `LiftBlock … 30`: a fuel numeral in a statement is a
  manual budget even when every rule below it is fuel-free.

#### Pattern B: `#mir_lift_spec` for companion predicates

`Anneal.PureMirExec` provides the `#mir_lift_spec` theorems for call-free,
alias-free companion bodies: `mirBoolPredicateHolds_of_pureExec` and
`mirBoolPredicateHolds_intro_of_pureExec` (introduction),
`mirBoolPredicateHolds_elim_of_pureExec` and
`mirBoolPredicateHolds_elim_of_uniqueTruePath` (elimination of a `requires`
hypothesis into a Lean proposition `P`), each taking `checkPureMir specBody =
true` by `rfl` and a `PureMirConverges` proof built with the Pattern A rules
(`examples/mir/MirVerification.lean`, `example_companion_bool_spec_holds`).

Check purity first: the `__anodized_fn_requires_*` / `__anodized_fn_ensures_*`
companions that `cargo anneal` generates from `#[anneal_spec::spec]` capture
their arguments by reference through a closure (`_6 = &_1`, `copy (*_10).0`), so
they fail `checkPureMir` and the theorems above do not apply. For those, invert
`requires` with `holdBoolReq_of_mirBool` and prove `ensures` with
`hold_mirBool_of_blockLinear`; both evaluate the companion with the
body-derived budget `defaultSpecSteps` (`16 * #blocks + 80`), so they are
bounded evaluations, not lifts. For concrete arguments,
`mirBoolPredicateHolds_of_evalMirSpecBool_true _ _ rfl rfl` decides the
companion by evaluation.

#### Pattern C: bounded loops with `forRangeUp`

Model `for i in lo..hi` / `while i < hi` loops with
`Anneal.MirLoops.forRangeUp lo hi init step` and reason about the model with
`forRangeUp_induction`, `forRangeUp_step_of_lt`, and `forRangeUp_eq_init_of_ge`.
`mirWpConverges_forRangeUp lo hi init step body LoopInv s₀ post h_init h_body
h_exit` turns a loop invariant `LoopInv i acc s` into a fuel-free
`MirWpConverges` proof (combined with `MirWpConverges.bind` for loop-entry
setup and `verifyStatefulMirNoPanic_of_wpConverges` at the top level).
Discharge every CFG segment with `runCfgToBlock body header cfg`, which steps
until the evaluator next enters the loop-header block `header`, halts, or
faults, so the proof never states a step count:

- loop entry and each iteration (`h_body`):
  `mirStepsConverges_of_runCfgToBlock body mid post rfl header s ?_`;
- the exit path once `i ≥ hi` (`h_exit`):
  `mirWpConverges_of_runCfgToBlock body post rfl header s ?_`.

Each leaves a `cfgStepsWP mid post (runCfgToBlock …)` (or `cfgStateWP`) goal
that one `dsimp only [runCfgToBlock, runCfgUntilAux, cfgAtBlock,
defaultCfgSteps, stepCfgState, …]` evaluates. List the claim
(`Obligations.<Crate>.<item>.statefulClaim`) there too, so that the body and
initial state taken from the goal unfold: a folded `statefulClaim.body`
leaves the evaluator stuck, and `dsimp` then times out. When the body indexes
memory by the counter (`frame[2 * i]`), keep the accumulator symbolic, split
the counter into its concrete values, and run one script on every case with
`all_goals` (see `Proof/WireframeDemo/checksum_frame_safe.lean`). Use
`mirWpConverges_whileRank` for loops with a decreasing rank instead of a
counter.

#### Pattern D: `&mut` / `&` arguments with `Anneal.SepLogicLenses`

For a body that reads and writes through reference arguments, describe each
pointee as a lens binding `(rp, v) : RawPtrVal × Value` backed by
`SepLensStateInv`, derive `LiftLensBlock body 0 env entries retVal entries'`
from the `LiftLensStmt` / `LiftDerefRead` / `LiftDerefFieldRead` /
`LiftDerefWrite` rules, and conclude with `verifyStatefulMir_of_sepLenses` (or
`mirWpConverges_of_sepLenses`, `verifyTotalMir_of_sepLenses`); the frame
outside the lenses is preserved by `LensFramePreserved` without destructuring
`Memory`. `LiftLensBlock` accepts `isRuntimeMirPhase body.phase = true` (`rfl`
for both `.runtimePostCleanup` fixtures and `.runtimeOptimized` bodies captured
by `cargo anneal`; see `Proof/WireframeDemo/advance_cursor.lean`). Discharge
each `set? env loc slot = some env'` premise of a lens rule with
`set?_of_forcePureEnv? rfl`, which instantiates `env'` with the flat slot list
rather than an unreduced `List.set` application. Concrete
pinned-memory contracts can also use `dischargeStatefulEqFuelFree` (a
fixed-budget wrapper; see Pattern E).

#### Pattern E: bounded fallbacks (`*FuelFree`, `wpBlockLinear`, `runCfgSteps`)

When no lift applies, `Anneal.Rustc.V2026_06_01.SymbolicEval` provides
wrappers that fix the budget of an existing bounded combinator inside
`Anneal`: despite their suffix, `dischargeRustEqU32FuelFree`,
`dischargeRustEq2U8FuelFree`, `verifyByWPFuelFree`, `verifyByWPSafeFuelFree`,
`dischargeStatefulEqFuelFree`, `mirBoolPredicateHolds_of_wp_fuelFree`, and the
`verify*MirFuelFree` family evaluate with a fixed `16`/`64`/`128`-step budget
(`verifyByWPFuelFree c h` is `verifyByWP c 16 h`), and their hypotheses still
mention `wpMirSym 16`. `Anneal.PureMirExec` provides whole-CFG evaluators
(`verifyMirNoPanic_of_blockLinear`, `verifyStatefulMirNoPanic_of_cfg`,
`verifyStatefulMirNoPanic_of_runCfgSteps`) whose budgets `defaultSpecSteps` /
`defaultCfgSteps` derive from `body.basicBlocks.length`. These are bounded
evaluators: no fuel numeral appears in the proof, but a body that needs more
steps than the budget cannot be discharged, and the proofs unfold the
evaluator with long `dsimp only` lists.

#### Pattern F: Byte-level validity and `zerocopy` traits (`Anneal.BitValidity`)

When discharging `#[anneal_spec::invariant]` or `#[anneal_spec::unsafe_impl]`
obligations for `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, or
`Unaligned`, open `Anneal.BitValidity`:

- Use `ValidityMode` (`.Uninit`, `.AsInitialized`, `.Initialized`, `.BitValid`,
  `.Valid`) and `ByteSeqValid` to relate `encodeValueToBytes` and
  `decodeValueFromBytes` over `Mir.<Crate>.<Item>.layouts`.
- Use `IsUnaligned`, `IsFromZeros`, `IsFromBytes`, `IsIntoBytes`,
  `IsTryFromBytes`, and `transmute_sound_of_into_from_bytes` to compose layout
  and bit-validity lemmas across fields and wrapper types.

### 5. Avoid Lean 4 kernel reduction bottlenecks on non-trivial MIR

Because `TrustedBoundary` forbids `native_decide` (`Lean.ofReduceBool`), Lean's
kernel reducer (`whnf`) must symbolically reduce every MIR step. When a proof
hits `maxHeartbeats`, `maxRecDepth`, or multi-second `rw`/`dsimp` stalls, read
[`references/proof-scaling-and-bottlenecks.md`](references/proof-scaling-and-bottlenecks.md)
and apply these nine rules:

1. **Lift instead of evaluating (Patterns A–D):** Never hand-write
   `BlockCtx` structures, per-block `itemBB0..itemBBn` boilerplate, or `fuel`
   numerals. Apply the `#mir_lift` rules (`lift_PureMirConverges`,
   `LiftBlock.of_lookup`, `LiftStmtsTerminator.*`) under
   `verifyMirNoPanic_of_pureExec`, which synthesize the step count by
   unification and never unfold `Mir.<Crate>.<Item>.body` into the goal.
2. **Use `forRangeUp` and `Anneal.SepLogicLenses` for loops and references:**
   Model bounded loops with `forRangeUp` and prove them with
   `mirWpConverges_forRangeUp` (or `mirWpConverges_whileRank`) and a loop
   invariant (`Proof/WireframeDemo/checksum_frame_safe.lean`); lift
   reference arguments with `LiftLensBlock` and `verifyStatefulMir_of_sepLenses`
   / `mirWpConverges_of_sepLenses` (`Proof/WireframeDemo/advance_cursor.lean`).
3. **Short-circuit symbolic bit-loops (`bitwiseAndBitsFast` & `swap_le_u16_lane`):**
   Never unfold recursive `bitwiseAndBits` / `bitwiseOrBits` over a symbolic
   `b : Nat` (which unrolls 8–64 nested `Nat.div · 2` trees and stalls kernel
   unification for `100s+`). Rewrite masks using closed-form arithmetic (`b % 2`,
   `b % 256`, `lo * 256 + hi`), `swap_le_u16_lane`, or a fast-path wrapper
   proved equal to `bitwiseAndBits`.
4. **Shield large symbolic states from `rw` (`Hold` barrier):** Wrap large
   weakest-precondition terms in `private structure Hold (P : Prop) : Prop where val : P`
   so `rw` does not traverse the full symbolic execution AST before `dsimp only`
   collapses it.
5. **Factor `#[anneal_spec::spec]` companions into boundary lemmas:**
   Prove a standalone `wpReq_inversion` (from `MirBoolPredicateHolds` of the
   `requires` companion to arithmetic bounds) and `ensures_holds` (from bounds
   to `MirBoolPredicateHolds` of the `ensures` companion) instead of stepping
   all three MIR bodies inside one proof block; use the `#mir_lift_spec`
   theorems when the companion passes `checkPureMir` (Pattern B).
6. **Parameterize `evalByteCastAfterOperand` lemmas over `{body : CapturedMir}` with `autoParam`s:**
   When `dsimp only` unfolds `Mir.<Crate>.<Item>.body` to look up basic blocks,
   any `evalByteCastAfterOperand` argument containing `body` also unfolds. State
   byte-cast rewrite lemmas over `{body : CapturedMir}` with
   `(h_decls : body.localDecls = ... := by rfl)` and
   `(h_layouts : body.layouts = ... := by rfl)` so `rw` matches any unfolded
   `CapturedMir` record in `O(1)`.
7. **Never run `trace.profiler.threshold 1` on symbolic MIR proofs:** Low
   profiler thresholds format huge nested MIR ASTs at thousands of elaborator
   nodes, producing hundreds of megabytes of output and multi-hour stalls. Use
   in-memory `lean_multi_attempt` / `lean_goal` (when `anneal-lean_lsp` is
   available), or keep `trace.profiler.threshold >= 100` with
   `set_option pp.deepTerms false` and `timeout 30s`.
8. **Escape `whnf` timeouts on `bitwiseOrBits` and stateful `Memory` via
   wildcard `change ... _` + projection `dsimp`:** Spelling out `bitwiseOrBits 32`
   or an explicit post-state `Memory` record inside `change` forces `isDefEq` to
   unify `32` against `{ ... }.sizeBytes.mul 8` and unfolds 32 recursive levels
   of `bitwiseOrBits`. Instead, use wildcard `change ... _`, collapse record
   projections with a targeted `dsimp only` excluding `bitwiseOrBits`, and then
   `rw` the shift and bitwise lemmas.
9. **Follow the interactive LSP threshold heuristic:** Write routine arithmetic
   and known combinator proofs directly via `edit_file` (relying on the
   automatic `PostToolUse` hook), cap `lean_multi_attempt` at 1–2 probes per
   subgoal, and switch immediately to wildcard `change ... _` + `lean_goal` and
   `lean_local_search` on stateful or bitwise MIR goals.

### 6. Run locked end-to-end verification

Once `lake env lean` succeeds on every target proof file, run `agent-verify`
from the workspace root:

```bash
cargo anneal agent-verify
```

`cargo anneal agent-verify` verifies `.anneal/spec-lock.json`, regenerates
`.anneal/generated/` from the captured MIR records, builds all `Verify.*`
targets with Lake, and runs `TrustedBoundary` in `verify-audit` mode to confirm
kernel replay, statement-origin isolation, and zero unauthorized axioms. A task
is complete only when `cargo anneal agent-verify` exits with status `0`.
