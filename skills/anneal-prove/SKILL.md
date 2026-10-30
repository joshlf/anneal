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

### 3. Iterate on a single proof file with `lake env lean`

After creating a new `Proof/<Crate>/<Item>.lean` file (or before the first
single-file check), ensure `.anneal/lakefile.toml` registers the `Proof` library
root, then run `lake env lean` inside `.anneal/` for sub-second feedback on that
file without rebuilding the entire workspace:

```bash
(cd .anneal && lake env lean ../anneal/proofs/Proof/<Crate>/<Item>.lean)
```

### 4. Apply standard Anneal proof patterns

#### Pattern A: Stateless `verifyByWP` with Rust `#[spec]` / `#[external_spec]` companions

When `Obligations.<Crate>.<Item>.defaultPre` and `defaultPost` lower Rust
`requires` and `ensures` clauses via `MirBoolPredicateHolds`, use
`wpBoolOrExhausted_of_mirBoolPredicateHolds` to extract a bounded step-by-step
hypothesis from `h_pre` and `mirBoolPredicateHolds_of_wp_bounded` to discharge
the postcondition:

```lean
import Trusted
import Anneal
import Mir.CanaryPkg.identity_u32
import Obligations.CanaryPkg.identity_u32

namespace Proof.CanaryPkg.identity_u32

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

set_option maxHeartbeats 2000000 in
theorem verified : VerificationResult Obligations.CanaryPkg.identity_u32.claim :=
  verifyByWP Obligations.CanaryPkg.identity_u32.claim 64 (by
    intro args h_pre
    have h_req := wpBoolOrExhausted_of_mirBoolPredicateHolds 64
      Mir.CanaryPkg.__anodized_fn_requires_identity_u32.body args h_pre.2
    -- Destructure `args` using `h_pre.1` (`length args = body.argCount`)
    -- and discharge impossible branches with `nomatch h_req`, then close
    -- the surviving branch with `mirBoolPredicateHolds_of_wp_bounded`.
    ...)

end Proof.CanaryPkg.identity_u32
```

#### Pattern B: Stateless `verifyByWP` with a locked `Specs.<Crate>.<Item>` override

When a locked `Specs.<Crate>.<Item>` module provides a relational `ItemSpec`
instance (for example, `pre args := args = [.scalar v]` and `post args ret :=
ret = .scalar ...`), import `Specs.<Crate>.<Item>` so Lean synthesizes that
normal-priority instance for `Obligations.<Crate>.<Item>.claim`:

```lean
import Trusted
import Anneal
import Mir.CanaryPkg.const_forty_two
import Specs.CanaryPkg.const_forty_two
import Obligations.CanaryPkg.const_forty_two

namespace Proof.CanaryPkg.const_forty_two

open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : VerificationResult Obligations.CanaryPkg.const_forty_two.claim :=
  verifyByWP Obligations.CanaryPkg.const_forty_two.claim 16 (by
    intro args h_pre
    subst h_pre
    exact ⟨rfl, rfl⟩)

end Proof.CanaryPkg.const_forty_two
```

#### Pattern C: Stateful `verifyStatefulByWP` and footprint framing (`wp_frame_disjoint`)

For pointer, reference, and mutable-borrow obligations (`StatefulItemSpec` /
`StatefulVerificationResult`), open `Anneal.SepLogic` and `Anneal.Memory`, and
apply `verifyStatefulByWP`:

- Use `PtrInvariant`, `UnalignInvariant`, `PointsTo`, `BorrowToken`, and
  `LifetimeToken` (or their `SepProp` counterparts `PointsToSep`,
  `BorrowTokenSep`, `LifetimeTokenSep`) to destructure the initial `Memory`
  hypothesis `h_pre : c.pre args mem`.
- When proving that a heap or Tree Borrows update preserves disjoint resources
  `frame : HeapPred` supported by `fp : Footprint` (`SupportedBy frame fp`),
  apply `wp_frame_disjoint` together with
  `agreeOnFootprint_of_disjoint_borrow_update`, `supportedBy_pointsTo`,
  `supportedBy_ptrInvariant`, or `supportedBy_unalignInvariant`.

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

### 5. Run locked end-to-end verification

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
