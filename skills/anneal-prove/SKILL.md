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

### 4. Apply standard fuel-free Anneal proof patterns

Anneal provides fuel-free functional lifting (`Anneal.MirLiftCore`,
`Anneal.PureMirExec`, `Anneal.MirFuelFree`) and fuel-free symbolic WP
combinators (`Anneal.Rustc.V2026_06_01.SymbolicEval`) as the **primary
recommended proof workflow**. Proofs under `anneal/proofs/Proof/` should never
hand-code `BlockCtx` wrappers or manual `fuel` step counts.

#### Pattern A: Fuel-free lifting with `#mir_lift`, `#mir_lift_spec`, and `mirWpConverges_of_pureExec`

For straight-line and branching MIR bodies (as well as `#[anneal_spec::spec]`
`requires` / `ensures` companions), use `#mir_lift` / `#mir_lift_spec` (in
interactive exploration or `Anneal.*` modules) and the fuel-free
`Anneal.PureMirExec` combinators (`verifyMirNoPanic_of_blockLinear`,
`mirWpConverges_of_pureExec`, `evalMirSpecBool_true_of_holds`, and
`mirBoolPredicateHolds_of_evalMirSpecBool_true`) which automatically derive step
budgets from `body.basicBlocks.length` (`defaultSpecSteps` / `defaultCfgSteps`):

```lean
import Trusted
import Anneal
import Mir.WireframeDemo.frame_total_len
import Obligations.WireframeDemo.frame_total_len

namespace Proof.WireframeDemo.frame_total_len

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.PureMirExec

-- 1. Invert `requires` companion via `evalMirSpecBool_true_of_holds`:
private theorem req_inversion {v1 v2 : Value}
    (h_holds : MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_requires_frame_total_len.body [v1, v2]) :
    ∃ b1 b2, v1 = .scalar ⟨b1, 2⟩ ∧ v2 = .scalar ⟨b2, 2⟩ ∧ b1 ≤ 16 ∧ b2 ≤ 1024 := by
  have h_eval := evalMirSpecBool_true_of_holds h_holds
  ...

-- 2. Discharge `ensures` companion via `mirBoolPredicateHolds_of_evalMirSpecBool_true`:
private theorem ensures_holds (b1 b2 : Nat) (h1 : b1 ≤ 16) (h2 : b2 ≤ 1024) :
    MirBoolPredicateHolds
      Mir.WireframeDemo.__anodized_fn_ensures_frame_total_len.body
      [.scalar ⟨b1, 2⟩, .scalar ⟨b2, 2⟩, .scalar ⟨b1 + b2, 2⟩] := by
  apply mirBoolPredicateHolds_of_evalMirSpecBool_true
  ...

-- 3. Discharge the subject obligation fuel-free via `verifyMirNoPanic_of_blockLinear`:
theorem verified : VerificationResult Obligations.WireframeDemo.frame_total_len.claim := by
  refine verifyMirNoPanic_of_blockLinear Obligations.WireframeDemo.frame_total_len.claim ?_
  intro args h_pre
  ...

end Proof.WireframeDemo.frame_total_len
```

For pin-style `#[spec]` obligations (`x == c && result == d`), use the
one-line fuel-free combinators `dischargeRustEqU8FuelFree ..
dischargeRustEqUsizeFuelFree` and `dischargeRustEq2U8FuelFree`:

```lean
theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  dischargeRustEqU32FuelFree
    Obligations.FrameTutor.pin_magic.claim
    Mir.FrameTutor.__anodized_fn_requires_pin_magic.body
    Mir.FrameTutor.__anodized_fn_ensures_pin_magic.body
    7
```

#### Pattern B: Stateless `verifyByWPFuelFree` with a locked `Specs.<Crate>.<Item>` override

When a locked `Specs.<Crate>.<Item>` module provides a relational `ItemSpec`
instance (or `refineSafeSpec` safety precondition), import
`Specs.<Crate>.<Item>` and apply `verifyByWPFuelFree` or
`verifyByWPSafeFuelFree` paired with `mirBoolPredicateHolds_of_wp_fuelFree`:

```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.advance_offset
import Specs.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Proof.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  verifyByWPSafeFuelFree
    Obligations.FrameTutor.advance_offset.claim
    (by
      intro args h_safe
      cases h_safe with
      | inl h2 =>
        subst h2
        exact fun _ =>
          And.intro
            (mirBoolPredicateHolds_of_wp_fuelFree
              Mir.FrameTutor.__anodized_fn_ensures_advance_offset.body
              [.scalar ⟨2, 1⟩, .scalar ⟨6, 1⟩]
              rfl)
            rfl
      | inr h255 =>
        subst h255
        exact True.intro)

end Proof.FrameTutor.advance_offset
```

#### Pattern C: Stateful obligations, `mirWpConverges_of_sepLenses`, and `forRangeUp` loop lifting

For pointer, reference, mutable-borrow, and bounded-loop obligations
(`StatefulItemSpec` / `StatefulVerificationResult`), use:

- **`dischargeStatefulEqFuelFree`** for concrete reference/borrow equality
  contracts;
- **`verifyStatefulMirNoPanic_of_cfg`** (and
  `verifyStatefulMirNoPanic_of_runCfgSteps` /
  `verifyStatefulEquivMir_of_runCfgSteps` with `runCfgStepsWith`) for general
  stateful CFG execution without `BlockCtx` boilerplate;
- **`mirWpConverges_of_sepLenses`** and **`forRangeUp`** (`forRangeUp_step`,
  `forRangeUp_done`, `forRangeUp_invariant`) for loops and separated memory
  lenses (`SepLens` / `DisjointSepLenses`);
- **`PtrInvariant`**, **`UnalignInvariant`**, **`PointsTo`**,
  **`BorrowToken`**, and **`LifetimeToken`** (`Anneal.SepLogic`) to destructure
  initial `Memory` states and frame disjoint footprints via `wp_frame_disjoint`.

#### Pattern D: Byte-level validity and `zerocopy` trait obligations (`Anneal.BitValidity`)

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

1. **Use fuel-free lifting (`#mir_lift`, `#mir_lift_spec`, `mirWpConverges_of_pureExec`, `verifyMirNoPanic_of_blockLinear`, `verifyStatefulMirNoPanic_of_cfg`):**
   Never hand-write `BlockCtx` structures, per-block `itemBB0..itemBBn`
   boilerplate, or manual `fuel` numerals. Use `Anneal.PureMirExec` and
   `Anneal.MirLiftCore` combinators (`#mir_lift`, `#mir_lift_spec`,
   `mirWpConverges_of_pureExec`, `lift_frame`, `verifyMirNoPanic_of_blockLinear`,
   `verifyStatefulMirNoPanic_of_cfg`) which derive step counts automatically
   from the CFG structure.
2. **Use `forRangeUp` and `mirWpConverges_of_sepLenses` for loops and stateful lenses:**
   Model bounded range loops via `forRangeUp` (`forRangeUp_step`,
   `forRangeUp_done`, `forRangeUp_invariant`) and separated mutable places via
   `mirWpConverges_of_sepLenses` or `runCfgStepsWith` (which holds `body` opaque
   during statement execution so `Mir.<Crate>.<Item>.body` is never duplicated
   across loop iterations).
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
5. **Factor `#[anneal_spec::spec]` companions into fuel-free boundary lemmas:**
   Prove standalone `wpReq_inversion` (via `evalMirSpecBool_true_of_holds`) and
   `ensures_holds` (via `mirBoolPredicateHolds_of_evalMirSpecBool_true`) instead
   of stepping all three MIR bodies inside one proof block.
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
