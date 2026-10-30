# Chapter 6: Guided Agentic Proof Workflow

[← Chapter 5 — Working with `unsafe` Code, Tree Borrows & Separation Logic](05-verifying-unsafe-rust.md) | [Back to Tutor Overview](README.md)

Writing formal proofs by hand is rewarding, but discharging routine weakest-precondition
obligations across dozens of functions is an ideal task for an AI coding agent—provided
the agent **cannot cheat** by weakening `.defined` (`safetyDomain`), dropping
`rustEnsures` from `.val`, slipping in an unapproved `axiom`, or bypassing a
custom `Specs` override.

Anneal provides a first-class, locked **Agentic Proof Workflow** built around a
strict division of labor between the **Human Architect** (who authors and locks
specifications) and the **AI Prover** (who edits only `anneal/proofs/Proof/<Crate>/<Item>.lean`
and validates with `cargo anneal agent-verify`).

For the standalone reference manual and skill specification, see
[`docs/agent-proof-workflow.md`](../agent-proof-workflow.md) and
[`skills/anneal-prove/SKILL.md`](../../skills/anneal-prove/SKILL.md).

---

## 1. The 5-Step Human-Architect / AI-Prover Workflow

```text
┌────────────────────────────────────────────────────────────────────────────┐
│HUMAN ARCHITECT                                                             │
│  Step 1: Author Rust #[anneal_spec::spec] contracts in src/lib.rs          │
│          and custom Lean overrides in anneal/proofs/Specs/FrameTutor/      │
│  Step 2: Run `cargo anneal lock-specs`                                     │
│          -> Runs non-vacuity & `rustEnsures` preservation checks on Specs/ │
│          -> Writes SHA-256 hashes of Mir/, Specs/, and Assumptions/        │
│             to `.anneal/spec-lock.json`                                    │
└───────────────────────────────────────┬────────────────────────────────────┘
                                        │
                                        ▼
┌────────────────────────────────────────────────────────────────────────────┐
│AI PROVER (loaded with `skills/anneal-prove/SKILL.md`)                      │
│  Step 3: Run `cargo anneal agent-context --item <filter>`                  │
│          -> Inspects generated Mir, Obligations, and locked Specs          │
│  Step 4: Edit ONLY `anneal/proofs/Proof/FrameTutor/<Item>.lean`            │
│          -> Applies `dischargeRustEq*`, `dischargeSafeRustBounded*`,       │
│             `verifyByWPSafe`, `dischargeStatefulEq`, or `verifyByWP`       │
│  Step 5: Run `cargo anneal agent-verify`                                   │
│          -> Verifies `.anneal/spec-lock.json` hashes & import hygiene      │
│          -> Runs `lake build` and `TrustedBoundary` `.olean` kernel replay │
└────────────────────────────────────────────────────────────────────────────┘
```

Let's walk through each of the 5 steps on `frame_tutor` (`examples/tutor/`).

---

### Step 1 (Human): Author Rust `#[spec]` Annotations and `Specs/` Overrides

The human engineer writes the Rust implementation and inline `#[anneal_spec::spec]`
annotations in `examples/tutor/src/lib.rs` (`magic_version`, `pin_magic`,
`total_frame_len`, `advance_offset`, `is_valid_version`, `FrameLen`, `WireHeader`,
`read_version_ref`, and `write_version_mut`), plus any Lean-level specification
overrides in `anneal/proofs/Specs/FrameTutor/`:
- `anneal/proofs/Specs/FrameTutor/advance_offset.lean` (using `refineSafeSpec`
  from [Chapter 4](04-manual-proof-workflow.md)),
- `anneal/proofs/Specs/FrameTutor/read_version_ref.lean` (using
  `StatefulItemSpec` from [Chapter 5](05-verifying-unsafe-rust.md)), and
- `anneal/proofs/Specs/FrameTutor/write_version_mut.lean` (using
  `StatefulItemSpec` with `.active` Tree Borrows permission from
  [Chapter 5](05-verifying-unsafe-rust.md)).

First, extract and scaffold the workspace so `.anneal/generated/` is up to date:

<!-- tutor: command step=ch6-extract,ch6-scaffold -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor/Cargo.toml
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or the same subcommands inside `examples/tutor/`):
cargo anneal extract --manifest-path examples/tutor/Cargo.toml
cargo anneal scaffold --manifest-path examples/tutor/Cargo.toml
```

---

### Step 2 (Human): Lock Specifications (`cargo anneal lock-specs`)

Before handing the workspace to an AI agent, the human runs `lock-specs`:

<!-- tutor: command step=ch6-lock-specs -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- lock-specs --manifest-path examples/tutor/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor && cargo anneal lock-specs`):
cargo anneal lock-specs --manifest-path examples/tutor/Cargo.toml
```

#### Interpreting the Spec-Lock Report

`cargo anneal lock-specs` audits every file in `anneal/proofs/Specs/` against
the non-vacuity checks and writes `.anneal/spec-lock.json`, printing the
**Spec-Lock Report** (`Anneal Spec-Lock Summary:`):

<!-- tutor: report step=ch6-lock-specs -->
```text
Anneal Spec-Lock Summary:
  Lock file: .anneal/spec-lock.json
  Locked MIR targets: 19
  Locked Specs files: 3
  Locked Assumptions files: 0
  Non-vacuity check: PASS
```

What `.anneal/spec-lock.json` records—and how it protects both `.defined` and
`.val` in `Partial`:
- **`locked_records` (`mir_module_sha256`)**: SHA-256 hashes of all generated
  `.anneal/generated/Mir/FrameTutor/*.lean` modules (both subjects and inline
  `requires` / `ensures` companions), guaranteeing the agent cannot alter
  `src/lib.rs` or `.anneal/generated/Mir/` to weaken `rustRequires`,
  `rustEnsures`, or a subject function body.
- **`locked_specs_files`**: SHA-256 hashes of every file under
  `anneal/proofs/Specs/` (`Specs/FrameTutor/advance_offset.lean`,
  `Specs/FrameTutor/read_version_ref.lean`, and
  `Specs/FrameTutor/write_version_mut.lean`). Because these files are hashed and
  frozen, the agent **cannot** shrink `.defined` (for example, deleting the
  overflowing `offset = 255` branch from `advanceOffsetSafetyDomain` in
  `refineSafeSpec`) and **cannot** weaken `.val` (for example, weakening
  `ret = .scalar { bits := 6, sizeBytes := 1 }` or dropping `rustEnsures`).
- **`locked_assumptions_files`**: SHA-256 hashes of every approved file under
  `anneal/proofs/Assumptions/` (here `0`).

---

### Step 3 (Human or Agent): Inspect Proof Obligations (`cargo anneal agent-context`)

To inspect the exact proof obligation for a specific item (or all items in the
crate), run `agent-context`:

<!-- tutor: command step=ch6-agent-context -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- agent-context --item read_version_ref --manifest-path examples/tutor/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor && cargo anneal agent-context --item read_version_ref`):
cargo anneal agent-context --item read_version_ref --manifest-path examples/tutor/Cargo.toml
```

`cargo anneal agent-context` prints a self-contained Markdown bundle containing:
1. The item's `def_id` (`frame_tutor::read_version_ref`), Rust source span, and
   `ContractRole`.
2. The target `Proof` path (`anneal/proofs/Proof/FrameTutor/read_version_ref.lean`)
   and expected theorem signature:
   ```lean
   theorem verified : StatefulVerificationResult Obligations.FrameTutor.read_version_ref.statefulClaim
   ```
   (or `VerificationResult Obligations.FrameTutor.pin_magic.claim` for stateless
   claims).
3. The full contents of `.anneal/generated/Obligations/FrameTutor/<Item>.lean`,
   any custom `anneal/proofs/Specs/FrameTutor/<Item>.lean`, and the captured
   subject and companion `Mir.FrameTutor.*` modules.
4. A summary of available proof tactics from `Anneal.Tactics` (`dischargeRustEq*`,
   `dischargeRustBounded*`, `dischargeSafeRustBounded*`, `dischargeStatelessEq`,
   `dischargeStatefulEq`, `verifyByWP`, and `verifyByWPSafe`).

---

### Step 4 (Agent): Load `anneal-prove` and Edit Only `anneal/proofs/Proof/`

The AI agent loads [`skills/anneal-prove/SKILL.md`](../../skills/anneal-prove/SKILL.md)
and authors or updates the proof modules under `anneal/proofs/Proof/FrameTutor/`:

- `anneal/proofs/Proof/FrameTutor/pin_magic.lean` (using `dischargeRustEqU32`)
- `anneal/proofs/Proof/FrameTutor/total_frame_len.lean` (using `dischargeRustEq2U8`)
- `anneal/proofs/Proof/FrameTutor/advance_offset.lean` (importing
  `Specs.FrameTutor.advance_offset` and using `verifyByWPSafe` plus
  `mirContractHoldsWithSafety_iff_mirContractHolds_imp`)
- `anneal/proofs/Proof/FrameTutor/read_version_ref.lean` (importing
  `Specs.FrameTutor.read_version_ref` and using `dischargeStatefulEq`)
- `anneal/proofs/Proof/FrameTutor/write_version_mut.lean` (importing
  `Specs.FrameTutor.write_version_mut` and using `dischargeStatefulEq` plus
  `BorrowTokenSep`)
- `anneal/proofs/Proof/FrameTutor/__anneal_unsafe_impl_WireHeader_for_FrameLen.lean`
  (using `verifyByWP` and proving `IsUnaligned`, `IsFromBytes`, `IsIntoBytes`,
  and `IsFromZeros`)
- (`magic_version` requires no file in `anneal/proofs/Proof/` because its
  generated `defaultProof` in `Verify/FrameTutor/magic_version.lean` already
  discharges it.)

---

### Step 5 (Human or Agent): Run Locked Verification (`cargo anneal agent-verify`)

Finally, the agent (or CI pipeline) runs `agent-verify`:

<!-- tutor: command step=ch6-agent-verify -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- agent-verify --manifest-path examples/tutor/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor && cargo anneal agent-verify`):
cargo anneal agent-verify --manifest-path examples/tutor/Cargo.toml
```

`cargo anneal agent-verify` performs four gates in sequence:
1. Re-extracts and re-scaffolds the crate into `.anneal/generated/`.
2. Verifies `.anneal/spec-lock.json` (`verify_spec_lock`): checks that no locked
   `Mir`, `Specs`, or `Assumptions` file was modified, no unauthorized `Specs` or
   `Assumptions` file was added, all non-vacuity checks pass, and every
   `Proof/<Crate>/<Item>.lean` that has a companion `Specs/<Crate>/<Item>.lean`
   explicitly imports `Specs.<Crate>.<Item>`.
3. Runs `lake build` in `.anneal/`.
4. Runs `TrustedBoundary.lean` in `verify-audit` mode to replay the compiled
   `.olean` environment in the Lean 4 kernel (`TrustedBoundary`).

When all checks pass, `cargo anneal agent-verify` prints the Verification Report:

<!-- tutor: report step=ch6-agent-verify -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen: UNCONDITIONAL
  Verify.FrameTutor.advance_offset: UNCONDITIONAL
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Verify.FrameTutor.pin_magic: UNCONDITIONAL
  Verify.FrameTutor.read_version_ref: UNCONDITIONAL
  Verify.FrameTutor.total_frame_len: UNCONDITIONAL
  Verify.FrameTutor.write_version_mut: UNCONDITIONAL
  Totals: 7 unconditional, 0 conditional
  TrustedBoundary kernel replay: PASS
```

---

## 2. The 5 Anti-Cheating Safeguards in Action

What happens if an AI prover tries to take a shortcut instead of proving the
locked `Partial` specification? Let's look at the exact failure produced by each
of Anneal's five anti-cheating safeguards:

| Safeguard | Attack Vector Against `Partial` (`.defined` / `.val`) | How `cargo-anneal` / `TrustedBoundary` Blocks It |
| :--- | :--- | :--- |
| **Safeguard 1: Locked `Specs/` & `Mir/` digests** | Agent edits `Specs/<Item>.lean` or `src/lib.rs` after `lock-specs` to shrink `safetyDomain` (`.defined`) or weaken `extraPost` (`.val`). | `verify_spec_lock` compares SHA-256 digests against `.anneal/spec-lock.json` and rejects modified, added, or deleted `Specs/` and `Mir/` files before running Lake. |
| **Safeguard 2: Locked `Assumptions/` digests** | Agent adds an `axiom` in `Assumptions/<Item>.lean` to assume `VerificationResult` without proving it. | `verify_spec_lock` rejects any `Assumptions/` file not hashed in `.anneal/spec-lock.json` (and forbids `--allow-assumptions` when zero assumptions are locked). |
| **Safeguard 3: Vacuous `.defined := False` rejection** | Author sets `pre := fun _ => False` in `Specs/<Item>.lean`, collapsing `MirContractSpec` to `Partial.ub` (which every implementation refines vacuously by `Partial.ub_top`). | `detect_vacuous_precondition` in `check_specs_non_vacuous_with_records` scans non-comment tokens in `Specs/` and rejects `False` preconditions. |
| **Safeguard 4: `rustEnsures` preservation in `.val`** | Author writes a custom `Specs/<Item>.lean` override for an item with Rust `#[spec(ensures: ...)]` that silently drops `rustEnsures` from `.val`. | Check 4 in `check_specs_non_vacuous_with_records` requires `Specs/<Item>.lean` to reference `rustEnsures`, `defaultPost`, `refineSpec`, `refineStatefulSpec`, `refineSafeSpec`, or `refineSafeStatefulSpec`. |
| **Safeguard 5: `import Specs` coherence & `.olean` kernel audit** | Agent omits `import Specs.<Item>` in `Proof/<Item>.lean` (falling back to `defaultSpec`), or uses `sorry` / `native_decide` / local `axiom` in `Proof/`. | Check 5 in `check_specs_non_vacuous_with_records` requires `import Specs.<Item>`, and `TrustedBoundary.lean` replays `.olean` files in the Lean 4 kernel, rejecting `sorryAx`, `native_decide`, and unauthorized axioms. |

### Safeguard 1: Modifying or Adding a File in `anneal/proofs/Specs/`

Suppose an agent edits `anneal/proofs/Specs/FrameTutor/read_version_ref.lean` to
weaken its postcondition, or edits `Specs/FrameTutor/advance_offset.lean` to
remove the overflowing `offset = 255` case from `advanceOffsetSafetyDomain`
(`.defined`), or creates a new file `anneal/proofs/Specs/FrameTutor/pin_magic.lean`
after `cargo anneal lock-specs` was run.

When `cargo anneal agent-verify` runs, `verify_spec_lock` compares the on-disk
`Specs/` directory against `.anneal/spec-lock.json` and aborts before `lake build`:

<!-- tutor: errors step=ch6-safeguard-1-modified-spec -->
```text
cargo-anneal error: spec-lock violation: locked Specs file 'anneal/proofs/Specs/FrameTutor/read_version_ref.lean' was modified (expected SHA-256 fd847dbb8d44845206ab154afce706b012c75ceefc1f3326317ab0f176246e71, got 1d979549c0789a855b78fcbc88ddd6f8376ba67df25b10ab4a4d698439b0bef8)
```

Or if the agent created a new `Specs/` file:

<!-- tutor: errors step=ch6-safeguard-1-added-spec -->
```text
cargo-anneal error: spec-lock violation: unlocked Specs file 'anneal/proofs/Specs/FrameTutor/pin_magic.lean' was added under anneal/proofs/Specs/ after `cargo anneal lock-specs`
```

### Safeguard 2: Adding an Unapproved File in `anneal/proofs/Assumptions/`

Suppose an agent creates `anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`
with an `axiom` after `cargo anneal lock-specs` locked zero assumptions:

<!-- tutor: errors step=ch6-safeguard-2-added-assumption -->
```text
cargo-anneal error: spec-lock violation: unlocked Assumptions file 'anneal/proofs/Assumptions/FrameTutor/pin_magic.lean' was added under anneal/proofs/Assumptions/ after `cargo anneal lock-specs`
```

Even if `--allow-assumptions` is passed to `agent-verify`, `verify_workspace_with_options`
rejects `--allow-assumptions` whenever `.anneal/spec-lock.json` locks zero
`Assumptions/` files.

### Safeguard 3 & 4: Vacuous `.defined := False` or Dropping `rustEnsures` in `Specs/`

What if a `Specs/<Crate>/<Item>.lean` file is authored *before* `lock-specs`
that sets `pre := fun _ => False` (collapsing `MirContractSpec` to `Partial.ub`)
or accidentally drops the Rust `#[anneal_spec::spec(ensures: ...)]` clause from
`.val`?

`check_specs_non_vacuous_with_records` (run by both `cargo anneal lock-specs`
and `cargo anneal agent-verify`) enforces:
- **No vacuous `False` precondition in `.defined`**: Setting `pre := fun _ => False`
  would make `(MirContractSpec pre pre post args).defined = False` (`Partial.ub`),
  which any implementation refines vacuously (`Partial.ub_top`). Given this
  `Specs/FrameTutor/pin_magic.lean`:
  <!-- tutor: file step=ch6-safeguard-3-vacuous-spec path=anneal/proofs/Specs/FrameTutor/pin_magic.lean strip_module_doc -->
  ```lean
  import Trusted
  import Mir.FrameTutor.pin_magic
  import Obligations.FrameTutor.pin_magic

  namespace Specs.FrameTutor.pin_magic

  open Trusted.MirSemantics
  open Trusted.VerificationResult

  instance : ItemSpec "frame_tutor::pin_magic" where
    pre := fun _ => False
    post := fun args ret => Obligations.FrameTutor.pin_magic.rustEnsures args ret

  end Specs.FrameTutor.pin_magic
  ```
  `cargo anneal lock-specs` rejects it immediately:
  <!-- tutor: errors step=ch6-safeguard-3-vacuous-spec -->
  ```text
  cargo-anneal error: vacuous specification precondition rejected in anneal/proofs/Specs/FrameTutor/pin_magic.lean: found `pre := fun _ => False`
  ```
- **Check 4 (`rustEnsures` preservation in `.val`)**: Whenever an item has inline
  Rust `#[anneal_spec::spec(ensures: ...)]` companions, `Specs/<Crate>/<Item>.lean`
  **must** preserve the lowered Rust postcondition by referencing one of the six
  recognized identifiers in non-comment code:
  - `refineSafeSpec` (separating `safetyDomain` in `.defined` from `rustRequires → rustEnsures` in `.val`),
  - `refineSafeStatefulSpec` (stateful counterpart of `refineSafeSpec`),
  - `refineSpec` (conjoining `rustRequires` and `rustEnsures`),
  - `refineStatefulSpec` (stateful counterpart of `refineSpec`), or
  - `rustEnsures` / `defaultPost` directly (unless explicitly opted out with
    `-- @anneal-allow-replace-rust-spec`).

  If a `Specs` override omits all six identifiers, such as this
  `Specs/FrameTutor/advance_offset.lean` that restates the contract without
  mentioning `rustEnsures`:
  <!-- tutor: file step=ch6-safeguard-4-dropped-ensures path=anneal/proofs/Specs/FrameTutor/advance_offset.lean strip_module_doc -->
  ```lean
  import Trusted
  import Mir.FrameTutor.advance_offset
  import Obligations.FrameTutor.advance_offset

  namespace Specs.FrameTutor.advance_offset

  open Trusted.MirSemantics
  open Trusted.VerificationResult

  instance : ItemSpec "frame_tutor::advance_offset" where
    pre args := args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil
    post _ ret := ret = .scalar { bits := 6, sizeBytes := 1 }

  end Specs.FrameTutor.advance_offset
  ```
  `lock-specs` and `agent-verify` fail with:
  <!-- tutor: errors step=ch6-safeguard-4-dropped-ensures -->
  ```text
  cargo-anneal error: spec override in anneal/proofs/Specs/FrameTutor/advance_offset.lean drops the Rust #[spec] `ensures` clause; use `Obligations.FrameTutor.advance_offset.refineSpec`, `Obligations.FrameTutor.advance_offset.refineSafeSpec`, or `Obligations.FrameTutor.advance_offset.rustEnsures` (or add `-- @anneal-allow-replace-rust-spec`)
  ```

### Safeguard 5: Omitting `import Specs.<Crate>.<Item>` or Using `sorry` / Rogue `axiom` in `Proof/`

Suppose `anneal/proofs/Specs/FrameTutor/read_version_ref.lean` exists, and an
agent edits `anneal/proofs/Proof/FrameTutor/read_version_ref.lean` to remove
`import Specs.FrameTutor.read_version_ref` so that `Obligations.FrameTutor.read_version_ref.claim`
falls back to the low-priority `defaultSpec` (`post := True`).

Check 5 in `check_specs_non_vacuous_with_records` (and typechecking in
`.anneal/generated/Verify/FrameTutor/read_version_ref.lean`) catches this
immediately:

<!-- tutor: errors step=ch6-safeguard-5-missing-import -->
```text
cargo-anneal error: missing `import Specs.FrameTutor.read_version_ref` in anneal/proofs/Proof/FrameTutor/read_version_ref.lean: `Proof/FrameTutor/read_version_ref.lean` must `import Specs.FrameTutor.read_version_ref` so `Obligations.FrameTutor.read_version_ref.claim` resolves to the overridden `ItemSpec` instance
```

And if an agent leaves `sorry` inside `anneal/proofs/Proof/FrameTutor/pin_magic.lean`
or declares a local `axiom cheat : VerificationResult Obligations.FrameTutor.pin_magic.claim`
inside the `Proof.FrameTutor.pin_magic` namespace, `lake build` still succeeds,
but `TrustedBoundary.lean` rejects the proof:

- For `sorry` (`sorryAx`) in `Proof/FrameTutor/pin_magic.lean`:
  <!-- tutor: file step=ch6-safeguard-5-sorry path=anneal/proofs/Proof/FrameTutor/pin_magic.lean strip_module_doc -->
  ```lean
  import Trusted
  import Anneal
  import Mir.FrameTutor.pin_magic
  import Obligations.FrameTutor.pin_magic

  namespace Proof.FrameTutor.pin_magic

  open Trusted.VerificationResult

  theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim := by
    sorry

  end Proof.FrameTutor.pin_magic
  ```
  the kernel-replay audit finds `sorryAx` in the constant closure of
  `Verify.FrameTutor.pin_magic.verified` (the `VERIFY_AUDIT_ITEM` lines are the
  verdicts for the items it had already classified):
  <!-- tutor: errors step=ch6-safeguard-5-sorry -->
  ```text
  cargo-anneal error: TrustedBoundary verify-audit failed in examples/tutor/.anneal (status exit status: 1):
  VERIFY_AUDIT_ITEM	Verify.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen	VerifiedUnconditional
  VERIFY_AUDIT_ITEM	Verify.FrameTutor.advance_offset	VerifiedUnconditional
  VERIFY_AUDIT_ITEM	Verify.FrameTutor.magic_version	VerifiedUnconditional
  policy:Verify.FrameTutor.pin_magic.verified depends on sorryAx
  ```
- For a rogue `axiom` inside `Proof.*`:
  <!-- tutor: file step=ch6-safeguard-5-axiom path=anneal/proofs/Proof/FrameTutor/pin_magic.lean strip_module_doc -->
  ```lean
  import Trusted
  import Anneal
  import Mir.FrameTutor.pin_magic
  import Obligations.FrameTutor.pin_magic

  namespace Proof.FrameTutor.pin_magic

  open Trusted.VerificationResult

  axiom cheat : VerificationResult Obligations.FrameTutor.pin_magic.claim

  theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
    cheat

  end Proof.FrameTutor.pin_magic
  ```
  the audit's source inspector rejects the `axiom` command before any kernel
  replay takes place:
  <!-- tutor: errors step=ch6-safeguard-5-axiom -->
  ```text
  cargo-anneal error: TrustedBoundary verify-audit failed in examples/tutor/.anneal (status exit status: 1):
  policy:unsupported source form Lean.Parser.Command.axiom (axioms are only permitted in Assumptions.* modules)
  ```

---

## Summary of `cargo anneal` Commands

| Command | Purpose |
| :--- | :--- |
| `cargo anneal extract` | Capture `Runtime(PostCleanup)` MIR and contract companions into `.anneal/generated/Mir/` and `.anneal/manifest.json`. |
| `cargo anneal scaffold [--init-specs] [--init-proofs]` | Generate `.anneal/generated/Obligations/`, `.anneal/generated/Verify/`, and `.anneal/lakefile.toml` (optionally initializing starter templates in `anneal/proofs/`). |
| `cargo anneal verify [--allow-assumptions]` | Run `extract`, `scaffold`, `lake build`, and the `TrustedBoundary` `.olean` kernel audit (defaulting to `--disallow-assumptions`). |
| `cargo anneal lock-specs` | Run the non-vacuity and `rustEnsures`-preservation checks on `anneal/proofs/Specs/` and write SHA-256 hashes of `Mir/`, `Specs/`, and `Assumptions/` to `.anneal/spec-lock.json`. |
| `cargo anneal agent-context [--item <filter>]` | Render a self-contained Markdown proof obligation bundle for an AI prover or human engineer. |
| `cargo anneal agent-verify [--allow-assumptions]` | Verify `.anneal/spec-lock.json` integrity, `rustEnsures` preservation, and `import Specs` hygiene, then run `lake build` and the `TrustedBoundary` `.olean` kernel audit. |
