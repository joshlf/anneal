# The Anneal Tutor

Anneal verifies Rust programs—including `unsafe` code—by extracting typed
`Runtime(PostCleanup)` Mid-level Intermediate Representation (MIR) and compiler
layout facts via `anneal-rustc-capture` and checking per-item
`VerificationResult` (or `StatefulVerificationResult`) theorems inside the
Lean 4 kernel. After `lake build` compiles the generated Lean workspace,
`trusted/audit/check_trusted.py` replays the compiled `.olean` environment
against the Lean 4 kernel and checks that no unapproved axioms (`sorryAx`,
`unsafe`, `partial`, `native_decide`) or `theory/Anneal/` dependencies leak into
any top-level theorem statement.

This six-chapter tutorial walks a Rust developer through Anneal from first
principles to unsafe memory verification and locked AI-assisted proof workflows.
Every chapter builds on the same runnable crate, `frame_tutor`
([`examples/tutor/`](../../examples/tutor/)), so you can inspect the exact Rust
source, generated Lean modules, and CLI reports at each stage.

---

## What Anneal Proves (and What It Assumes)

To understand what an Anneal proof establishes, start with how Anneal models
program behavior in [`trusted/lean/Trusted/Refinement.lean`](../../trusted/lean/Trusted/Refinement.lean).

### The `Partial B` Refinement Model

In Rust, an execution that triggers Undefined Behavior (UB)—such as
dereferencing a dangling pointer or reading uninitialized memory—renders the
entire execution meaningless: the compiler may assume UB never happens and
transform a UB-exhibiting program into any target code whatsoever. By contrast,
a safe function that panics on out-of-range input (such as `offset + 4`
overflowing `u8` at `offset = 255`) or returns an `Err` variant does **not**
trigger Undefined Behavior; its behavior is completely well-defined by the
language specification.

Anneal captures this distinction constructively through the `Partial B`
structure:

```lean
structure Partial (B : Type u) : Type u where
  /-- Whether the execution is well-defined (free of Undefined Behavior). -/
  defined : Prop
  /-- Dependent extraction of the underlying behavior in `B`, gated on `defined`. -/
  val : defined → B
```

Two design choices in `Partial B` shape every specification and proof in Anneal:

1. **Undefined Behavior (`Partial.ub`) is the top element of the refinement order**:
   `Partial B` is ordered by the Smyth (demonic) refinement preorder
   (`instPreorderPartial`):
   $$p_1 \sqsubseteq p_2 \iff \forall (h_2 : p_2.\text{defined}),\; \exists (h_1 : p_1.\text{defined}),\; p_1.\text{val}\; h_1 \sqsubseteq p_2.\text{val}\; h_2$$
   When a specification $p_2$ has $p_2.\text{defined} = \text{False}$
   (`Partial.ub`), universal quantification over $h_2 : \text{False}$ holds
   vacuously (`Partial.ub_top`): *anything* refines UB, because a compiler may
   translate a UB execution into any target behavior. Conversely, if a
   specification requires defined execution ($p_2.\text{defined} = \text{True}$,
   such as `Partial.pure b`), then `Partial.ub` can **never** refine $p_2$
   (`Partial.not_ub_refines_pure`), because there is no proof $h_1 : \text{False}$
   to witness $p_1.\text{defined}$.
2. **Dependent behavioral extraction (`val : defined → B`)**:
   Notice that `val` is not a plain value of type `B`, but a **dependent
   function** from a proof of `defined` to `B`. Neither a proof script nor a
   caller at a call site can extract any behavioral property from `p.val h`
   without first supplying a proof term `h : p.defined` establishing that the
   execution is free of Undefined Behavior.

### Safety Preconditions (`.defined`) vs. Functional Preconditions (`.val`)

Because `Partial` separates `.defined` from `.val`, Anneal distinguishes two
fundamentally different kinds of preconditions in Rust:

| Precondition Kind | Where It Lives in `Partial` | Rust Meaning | Behavior Outside the Precondition | Example in `frame_tutor` |
| :--- | :--- | :--- | :--- | :--- |
| **Safety precondition** | `.defined` (`safetyPre` in `MirContractSpec` / `MirStatefulContractSpec`) | `# Safety` obligation on an `unsafe fn` (or well-typed entry arguments on a safe function). | Undefined Behavior (`Partial.ub`, `defined = False`) is permitted by the specification; callers **must** prove `.defined` before invoking the function. | `pub unsafe fn read_version_ref(hdr: &u8) -> u8` ([Chapter 5](05-verifying-unsafe-rust.md)): `hdr` must point to an initialized, aligned byte with active Tree Borrows permission. |
| **Functional precondition** | Inside `.val` (`funcPre → post` in `Partial.contract` / `refineSafeSpec`) | Logical `requires` domain under which a safe function returns a normal value satisfying `ensures`. | Execution **remains defined** (`.defined = True`, `MirNoUB` holds)—the function may panic, abort, or diverge, but it never triggers Undefined Behavior. | `pub fn advance_offset(offset: u8) -> u8 { offset + 4 }` ([Chapters 1](01-basic-usage-and-outputs.md), [2](02-rust-specifications.md), [4](04-manual-proof-workflow.md)): returns `offset + 4` when `offset < 4`, and panics safely (`TerminationKind.panic`) when `offset >= 252`. |

### Evidence Boundaries

Anneal keeps verification claims strictly within their evidence:

1. **Kernel-checked MIR refinement (`VerificationResult` / `StatefulVerificationResult`)**:
   An `[UNCONDITIONAL]` (`UNCONDITIONAL`) certificate proves in the Lean 4
   kernel that `MirExecPartial body` refines `MirContractSpec safetyPre pre post`
   (or `MirStatefulExecPartial body` refines `MirStatefulContractSpec`): for
   every input in `.defined` (`safetyPre`), the captured `Runtime(PostCleanup)`
   MIR body executes in `Trusted.MirSemantics` without Undefined Behavior
   (`MirNoUB`), and whenever the functional precondition (`pre`) holds, every
   normally returning execution satisfies `post`.
2. **Lowered Rust boolean contracts (`MirBoolPredicateHolds`)**:
   When you write `#[anneal_spec::spec(requires: ..., ensures: ...)]` in Rust,
   `anneal-spec` expands those clauses into companion Rust functions whose
   `Runtime(PostCleanup)` MIR bodies are captured alongside the subject
   function. `MirBoolPredicateHolds` asserts that the companion MIR body
   evaluates safely (`MirNoUB`) and returns `true` (`.scalar ⟨1, 1⟩`).
3. **Explicit scoped assumptions (`Assumptions.<Crate>.<Item>`)**:
   When you defer a proof or axiomatize a hardware or FFI boundary, you place
   a named `axiom` in `anneal/proofs/Assumptions/<Crate>/<Item>.lean`. Default
   verification (`cargo anneal verify`) rejects all assumptions; passing
   `--allow-assumptions` labels any dependent theorem `[CONDITIONAL]`
   (`CONDITIONAL [...]`) and names the exact `Assumptions.*` constants in the
   report.
4. **The audited `trusted/` correspondence boundary**:
   The Lean 4 kernel checks proofs relative to the operational semantics in
   [`trusted/lean/`](../../trusted/lean/) and the MIR captured by
   [`trusted/rustc-capture/`](../../trusted/rustc-capture/). Correspondence
   between `Trusted.MirSemantics` and `rustc` is established by human-audited,
   version-pinned citations ([`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md))
   and enforced by [`trusted/audit/check_trusted.py`](../../trusted/audit/check_trusted.py),
   not proved inside Lean.

---

## Two-Directory Workspace Split: `.anneal/` vs. `anneal/proofs/`

When `cargo anneal` runs on a Rust crate, it separates disposable machine-generated
plumbing from durable human- or agent-authored specifications and proofs:

```text
<crate-root>/
├── Cargo.toml
├── src/
│   └── lib.rs
├── .anneal/                                  # DISPOSABLE — regenerated on every run, never hand-edited
│   ├── lakefile.toml                         # Generated Lake workspace configuration
│   ├── manifest.json                         # Captured MIR target manifest
│   ├── spec-lock.json                        # SHA-256 integrity lock created by `cargo anneal lock-specs`
│   └── generated/
│       ├── Mir/FrameTutor/<Item>.lean        # Captured Runtime(PostCleanup) MIR AST & layouts
│       ├── Obligations/FrameTutor/<Item>.lean# Low-priority defaultSpec / defaultStatefulSpec & Claim
│       └── Verify/FrameTutor/<Item>.lean     # Top-level `theorem verified` audited by TrustedBoundary
└── anneal/
    └── proofs/                               # DURABLE — checked into version control
        ├── Specs/FrameTutor/<Item>.lean      # Optional human-authored ItemSpec / StatefulItemSpec override
        ├── Assumptions/FrameTutor/<Item>.lean# Optional scoped `axiom` declarations (`--allow-assumptions`)
        └── Proof/FrameTutor/<Item>.lean      # Authoritative `VerificationResult` / `StatefulVerificationResult` proof
```

| Directory | Lifecycle | Role | Typeclass Priority & Audit Rule |
| :--- | :--- | :--- | :--- |
| `.anneal/generated/Mir/` | Disposable | Serialized `CapturedMir` AST, `LocalDecl` table, basic blocks, and compiler layouts for each subject and companion function. | Imported by `Obligations` and `Proof`; audited to import only `Init.Core` and `Trusted`. |
| `.anneal/generated/Obligations/` | Disposable | Defines `defaultPre`, `defaultPost`, `rustRequires`, `rustEnsures`, `refineSpec`, `refineStatefulSpec`, `refineSafeSpec`, `refineSafeStatefulSpec`, `claim`, and `statefulClaim`. | Registers `instance (priority := low) defaultSpec` and `defaultStatefulSpec`. Never imports `Anneal.*`. |
| `.anneal/generated/Verify/` | Disposable | Exposes the top-level `theorem verified` audited by `TrustedBoundary`. | Uses `defaultProof` (`priority := low`) when no `Proof/<Crate>/<Item>.lean` exists; otherwise aliases `Proof.<Crate>.<Item>.verified`. |
| `anneal/proofs/Specs/` | Durable (Human) | Strengthens or replaces `defaultSpec` / `defaultStatefulSpec` in Lean 4 using `refineSafeSpec`, `refineSafeStatefulSpec`, `refineSpec`, `refineStatefulSpec`, or a custom instance. | Normal typeclass priority overrides `priority := low` defaults in `Obligations`. Locked by `cargo anneal lock-specs`. |
| `anneal/proofs/Assumptions/` | Durable (Human) | Declares explicit `axiom` constants when adopting Anneal incrementally or modeling external boundaries. | Rejected by default (`--disallow-assumptions`); surfaced as `CONDITIONAL` under `--allow-assumptions`. Locked by `cargo anneal lock-specs`. |
| `anneal/proofs/Proof/` | Durable (Human or Agent) | Discharges `VerificationResult` or `StatefulVerificationResult` using `Anneal.Tactics`, `Anneal.WP` (`WP` and `WPSafe`), or manual Lean 4 proofs. | The **only** directory writable during `cargo anneal agent-verify`. |

---

## Shared Running Example: `frame_tutor` (`examples/tutor/`)

All six chapters trace the verification of `frame_tutor` (`package.name = "frame_tutor"`,
Lean module prefix `FrameTutor`). The crate grows chapter by chapter, and each
chapter's crate is checked in so you can open, run, and diff exactly the code
the chapter refers to; `cargo anneal` always operates on a whole crate, so each
is complete on its own:

| Chapter | Crate the chapter's commands run against | Contents |
| :--- | :--- | :--- |
| [1](01-basic-usage-and-outputs.md) | [`examples/tutor-ch1/`](../../examples/tutor-ch1/) | `magic_version` only, no dependencies (Section 6 invites you to add `advance_offset`). |
| [2](02-rust-specifications.md) | [`examples/tutor-ch2/`](../../examples/tutor-ch2/) | Annotated safe functions, a `#[model]` helper, an `#[invariant]` newtype; no proofs. |
| [3](03-assumptions-and-incremental-adoption.md) | [`examples/tutor-ch3/`](../../examples/tutor-ch3/) | `magic_version` and `pin_magic`, with `pin_magic` deferred to a scoped axiom. |
| [4](04-manual-proof-workflow.md) | [`examples/tutor-ch4/`](../../examples/tutor-ch4/) | Four safe items with kernel-checked proofs and a `refineSafeSpec` specification. |
| [5](05-verifying-unsafe-rust.md), [6](06-agentic-proof-workflow.md) | [`examples/tutor/`](../../examples/tutor/) | The complete companion crate, adding the `unsafe` items. |

The complete crate in [`examples/tutor/`](../../examples/tutor/) contains:

| Rust Item in `examples/tutor/src/lib.rs` | Generated & Authored Lean Modules | Verification Mechanism | Introduced In |
| :--- | :--- | :--- | :--- |
| `pub const fn magic_version() -> u32 { 1 }` | `Mir.FrameTutor.magic_version`<br>`Obligations.FrameTutor.magic_version`<br>`Verify.FrameTutor.magic_version` | Zero-argument safe function verified automatically by `defaultProof` (`verifyByWP ... 64`) with zero files under `anneal/proofs/`. | [Chapter 1](01-basic-usage-and-outputs.md) |
| `pub fn pin_magic(magic: u32) -> u32 { magic }`<br>`#[anneal_spec::spec(requires: magic == 7, ensures: \|ref ret\| *ret == 7)]` | `Mir.FrameTutor.pin_magic`<br>`Mir.FrameTutor.__anodized_fn_requires_pin_magic`<br>`Mir.FrameTutor.__anodized_fn_ensures_pin_magic`<br>`Obligations.FrameTutor.pin_magic`<br>`Proof.FrameTutor.pin_magic` | Lowered Rust boolean contract (`MirBoolPredicateHolds`), first axiomatized in `Assumptions` and then proved unconditionally via `dischargeRustEqU32`. | [Chapter 2](02-rust-specifications.md)<br>[Chapter 3](03-assumptions-and-incremental-adoption.md)<br>[Chapter 4](04-manual-proof-workflow.md) |
| `pub fn total_frame_len(header_len: u8, payload_len: u8) -> u8 { header_len + payload_len }`<br>`#[anneal_spec::spec(requires: header_len == 1 && payload_len == 2, ensures: \|ref ret\| *ret == 3)]` | `Mir.FrameTutor.total_frame_len`<br>`Mir.FrameTutor.__anodized_fn_requires_total_frame_len`<br>`Mir.FrameTutor.__anodized_fn_ensures_total_frame_len`<br>`Obligations.FrameTutor.total_frame_len`<br>`Proof.FrameTutor.total_frame_len` | Two-parameter lowered Rust boolean contract (`MirBoolPredicateHolds`) proved unconditionally against `defaultSpec` via `dischargeRustEq2U8`. | [Chapter 2](02-rust-specifications.md)<br>[Chapter 4](04-manual-proof-workflow.md) |
| `pub fn advance_offset(offset: u8) -> u8 { offset + 4 }`<br>`#[anneal_spec::spec(requires: offset < 4, ensures: \|ref ret\| *ret == offset + 4)]` | `Mir.FrameTutor.advance_offset`<br>`Mir.FrameTutor.__anodized_fn_requires_advance_offset`<br>`Mir.FrameTutor.__anodized_fn_ensures_advance_offset`<br>`Obligations.FrameTutor.advance_offset`<br>`Specs.FrameTutor.advance_offset`<br>`Proof.FrameTutor.advance_offset` | Contrasts panic-free `WP` with safety-preserving `WPSafe`: unannotated `offset + 4` panics safely (`TerminationKind.panic`, `.defined = True`) on `offset >= 252`; specified via `refineSafeSpec` and proved via `verifyByWPSafe` and `MirContractHoldsWithSafety` (plus 256-input `dischargeSafeRustBoundedU8`). | [Chapter 1](01-basic-usage-and-outputs.md)<br>[Chapter 2](02-rust-specifications.md)<br>[Chapter 4](04-manual-proof-workflow.md) |
| `#[anneal_spec::model]`<br>`pub const fn is_valid_version(v: u8) -> bool { v == 1 }`<br>`#[anneal_spec::invariant(self.0 <= 64)]`<br>`pub struct FrameLen(pub u8);` | `Mir.FrameTutor.is_valid_version`<br>`Mir.FrameTutor.FrameLen___anneal_invariant` | Pure specification helper (`ContractRole.model`) and type invariant helper (`ContractRole.typeInvariant`) captured as companion MIR modules. | [Chapter 2](02-rust-specifications.md) |
| `pub unsafe fn read_version_ref(hdr: &u8) -> u8 { *hdr }` | `Mir.FrameTutor.read_version_ref`<br>`Obligations.FrameTutor.read_version_ref`<br>`Specs.FrameTutor.read_version_ref`<br>`Proof.FrameTutor.read_version_ref` | Stateful memory and Tree Borrows specification (`StatefulItemSpec "frame_tutor::read_version_ref"`, where pointer validity lives in `.defined`) proved via `dischargeStatefulEq`. | [Chapter 5](05-verifying-unsafe-rust.md)<br>[Chapter 6](06-agentic-proof-workflow.md) |
| `pub unsafe fn write_version_mut(hdr: &mut u8, ver: u8) -> u8 { *hdr = ver; *hdr }` | `Mir.FrameTutor.write_version_mut`<br>`Obligations.FrameTutor.write_version_mut`<br>`Specs.FrameTutor.write_version_mut`<br>`Proof.FrameTutor.write_version_mut` | Stateful mutable reference write under `.active` Tree Borrows permission (`StatefulItemSpec "frame_tutor::write_version_mut"`) proved via `dischargeStatefulEq` and `BorrowTokenSep`. | [Chapter 5](05-verifying-unsafe-rust.md)<br>[Chapter 6](06-agentic-proof-workflow.md) |
| `#[anneal_spec::unsafe_trait]`<br>`pub unsafe trait WireHeader {}`<br>`#[anneal_spec::unsafe_impl(true)]`<br>`unsafe impl WireHeader for FrameLen {}` | `Mir.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen`<br>`Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen`<br>`Proof.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen` | `unsafe trait` / `unsafe impl` contract verified via `verifyByWP` paired with `Anneal.BitValidity` theorems (`IsUnaligned`, `IsFromBytes`, `IsIntoBytes`, `IsFromZeros`). | [Chapter 5](05-verifying-unsafe-rust.md)<br>[Chapter 6](06-agentic-proof-workflow.md) |

---

## Chapters

1. **[Chapter 1: Basic Tool Usage & Interpreting Outputs](01-basic-usage-and-outputs.md)**
   Run `cargo anneal extract`, `cargo anneal scaffold`, and `cargo anneal verify`;
   read the Extract, Scaffold, and Verification reports; inspect `.anneal/generated/`
   for `magic_version`; understand how `VerificationResult` checks `MirContractHolds`
   as a `Partial` refinement; and see why an unannotated `advance_offset(offset: u8) -> u8 { offset + 4 }`
   is free of Undefined Behavior (`.defined = True`) across all `u8` inputs yet
   fails `defaultProof`'s panic-forbidding `WP` check—leaving two ways forward
   (`WPSafe` well-formedness vs. functional `#[anneal_spec::spec]` contracts).
2. **[Chapter 2: Adding Specifications in Rust](02-rust-specifications.md)**
   Compare the two approaches to resolving a panic-free `WP` failure—proving
   well-formedness (`MirNoUB`) across non-overflowing and panicking `u8` inputs
   via `WPSafe` (`verifyByWPSafe`) without a Rust `#[spec]` contract vs. adding
   functional pre/postconditions—then annotate `pin_magic`, `total_frame_len`,
   and `advance_offset` with `#[anneal_spec::spec(requires: ..., ensures: ...)]`,
   define `#[anneal_spec::model]` and `#[anneal_spec::invariant]` helpers, master
   the distinction between **safety preconditions (`.defined`)** and **functional
   preconditions (`.val`)** (`safe_contractSpec_preserves_wellFormed` vs.
   `misplaced_contractSpec_violates_wellFormed`), and inspect the four combinators
   (`refineSpec`, `refineStatefulSpec`, `refineSafeSpec`, `refineSafeStatefulSpec`)
   generated in `Obligations/FrameTutor/pin_magic.lean`.
3. **[Chapter 3: Explicit Assumptions & Incremental Adoption](03-assumptions-and-incremental-adoption.md)**
   Defer the proof of `pin_magic` using a scoped axiom in
   `anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`, observe how default
   `cargo anneal verify` rejects assumptions, and use `cargo anneal verify --allow-assumptions`
   to distinguish `[UNCONDITIONAL]` theorems from `[CONDITIONAL]` theorems.
4. **[Chapter 4: Completing a Manual Proof Workflow](04-manual-proof-workflow.md)**
   Replace the `pin_magic` assumption with a one-call kernel-checked proof using
   `dischargeRustEqU32`, prove two-parameter `total_frame_len` directly against
   `defaultSpec` using `dischargeRustEq2U8`, specify `advance_offset` in
   `Specs/FrameTutor/advance_offset.lean` using `refineSafeSpec` (separating its
   safety domain `.defined` from its functional contract `.val`), discharge
   `Proof/FrameTutor/advance_offset.lean` using `verifyByWPSafe` alongside the
   `MirContractHoldsWithSafety` corollary (and compare with `dischargeSafeRustBoundedU8`
   and `dischargeRustBoundedU8`), delete `Assumptions/FrameTutor/pin_magic.lean`,
   and verify every safe item as `[UNCONDITIONAL]`.
5. **[Chapter 5: Working with `unsafe` Code, Tree Borrows & Separation Logic](05-verifying-unsafe-rust.md)**
   Contrast safe functional preconditions in `.val` with `# Safety` preconditions
   in `.defined` (`MirStatefulExecPartial` and `MirStatefulContractSpec`), see
   how `val : defined → B` enforces soundness at call sites, explore byte-level
   layouts (`AbstractByte`), sub-place Tree Borrows (`BorrowPerm`, `ProtectedTags`),
   partial-heap separation logic (`Anneal.SepLogic`), and `unsafe_trait` /
   `unsafe_impl` (`Anneal.Polymorphism` and `Anneal.BitValidity`), then verify
   `pub unsafe fn read_version_ref(hdr: &u8) -> u8 { *hdr }`,
   `pub unsafe fn write_version_mut(hdr: &mut u8, ver: u8) -> u8 { *hdr = ver; *hdr }`, and
   `unsafe impl WireHeader for FrameLen` using `StatefulItemSpec`,
   `dischargeStatefulEq`, `BorrowTokenSep`, `verifyByWP`, and `Anneal.BitValidity`.
6. **[Chapter 6: Guided Agentic Proof Workflow](06-agentic-proof-workflow.md)**
   Walk through the five-step human-architect / AI-prover workflow (`#[spec]` and
   `Specs/` authoring, `cargo anneal lock-specs`, `cargo anneal agent-context`,
   [`skills/anneal-prove/SKILL.md`](../../skills/anneal-prove/SKILL.md), and
   `cargo anneal agent-verify`) across all seven subject items and see how
   spec-locking and the five anti-cheating safeguards prevent an agent from
   weakening either `.defined` (`safetyDomain`) or `.val` (`rustEnsures`).

---

## How the Chapters Stay in Sync with `cargo anneal`

Every command, report, error message, and file listing quoted in Chapters 1–6
is generated from an executable description of the tutorial,
[`workflow/tutor.toml`](workflow/tutor.toml), which runs each chapter's commands
against a disposable copy of that chapter's crate and checks that every
committed chapter crate is the previous one plus the edits the chapter
describes. The blocks are marked with `<!-- tutor: ... -->` directives
(invisible when rendered) and are checked against a fresh run by
`cargo test -p cargo-anneal --test end_to_end_tutor`. After an intentional CLI
or tutorial change, refresh them with
`python3 docs/tutor/workflow/tutor_workflow.py render`; see
[`workflow/README.md`](workflow/README.md) for the directive reference.

---

## Two Command Flavours: Inside an Anneal Checkout vs. Standalone `cargo anneal`

Throughout the six chapters, every CLI instruction is shown in **two flavours** so
you can follow along whether you are working inside an `anneal` repository
checkout or verifying an external crate using an installed `cargo anneal`
subcommand:

### Flavour A — Running Inside an Anneal Checkout

Build the `anneal-rustc-capture` compiler wrapper and `cargo-anneal` CLI once
from the root of the Anneal repository, then invoke `cargo run -p cargo-anneal --`
with a relative (or absolute) `--manifest-path`:

```bash
# One-time build from the Anneal repository root:
cargo build -p anneal-rustc-capture -p cargo-anneal

# Run pipeline commands from the Anneal repository root:
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor/Cargo.toml
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor/Cargo.toml
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor/Cargo.toml

# Or run the automated end-to-end tutor integration test suite:
cargo test -p cargo-anneal --test end_to_end_tutor --locked
```

### Flavour B — Using `cargo anneal` from Outside the Checkout (or Inside a Target Crate)

Install `cargo-anneal` and `anneal-rustc-capture` onto your `PATH` (or add
`<anneal-checkout>/target/debug` to `PATH`), then invoke `cargo anneal` directly
from your target crate directory or pass `--manifest-path`:

```bash
# One-time install from an Anneal checkout:
cargo install --path crates/cargo-anneal --path trusted/rustc-capture
# (Optional when verifying a crate outside the checkout tree:)
export ANNEAL_ROOT=/path/to/anneal

# Run directly inside a crate directory (e.g., `cd examples/tutor` or your own crate):
cargo anneal extract
cargo anneal scaffold
cargo anneal verify

# Or run from any working directory with a relative or absolute `--manifest-path`:
cargo anneal extract --manifest-path path/to/Cargo.toml
cargo anneal scaffold --manifest-path path/to/Cargo.toml
cargo anneal verify --manifest-path path/to/Cargo.toml
```
