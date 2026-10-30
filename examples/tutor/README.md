# `frame_tutor`: Runnable Companion for the Anneal Tutor

`examples/tutor/` (`frame_tutor`) is a standalone `#![no_std]` Rust crate and
durable Lean 4 proof bundle that accompanies the six-chapter
[Anneal Tutor](../../docs/tutor/README.md). It is the crate as it stands when
[Chapter 5](../../docs/tutor/05-verifying-unsafe-rust.md) and
[Chapter 6](../../docs/tutor/06-agentic-proof-workflow.md) run their commands;
the earlier chapters' crates are checked in next to it as
[`examples/tutor-ch1/`](../tutor-ch1/), [`tutor-ch2/`](../tutor-ch2/),
[`tutor-ch3/`](../tutor-ch3/), and [`tutor-ch4/`](../tutor-ch4/), and each
chapter's commands name its own crate.

You can run every `cargo anneal` subcommand against this directory to observe
how Rust contracts, disposable generated obligations, and durable Lean 4 proofs
interact across the verification pipeline.

## Directory Layout and Chapter Mapping

| Path | Tutor Chapter | Role |
| :--- | :--- | :--- |
| `src/lib.rs` (`magic_version`) | [Chapter 1](../../docs/tutor/01-basic-usage-and-outputs.md) | Zero-argument constant function verified automatically by `Verify.FrameTutor.magic_version.defaultProof` without authored `Specs` or `Proof` files. |
| `src/lib.rs` (`pin_magic`, `total_frame_len`, `advance_offset`, `is_valid_version`, `FrameLen`) | [Chapter 2](../../docs/tutor/02-rust-specifications.md) | Inline `#[anneal_spec::spec(requires: ..., ensures: ...)]` contracts, a `#[anneal_spec::model]` helper, and a `#[anneal_spec::invariant(...)]` type invariant. |
| `anneal/proofs/Assumptions/` *(only in [`examples/tutor-ch3/`](../tutor-ch3/))* | [Chapter 3](../../docs/tutor/03-assumptions-and-incremental-adoption.md) | Explicit `Assumptions.FrameTutor.*` axioms audited under `--allow-assumptions` (`CONDITIONAL`) and rejected under strict verification. |
| `anneal/proofs/Proof/FrameTutor/pin_magic.lean` & `Proof/FrameTutor/total_frame_len.lean` | [Chapter 4](../../docs/tutor/04-manual-proof-workflow.md) | Discharges `Obligations.FrameTutor.pin_magic.claim` (`dischargeRustEqU32`) and `Obligations.FrameTutor.total_frame_len.claim` (`dischargeRustEq2U8`) directly against the generated `defaultSpec` without a `Specs` override. |
| `anneal/proofs/Specs/FrameTutor/advance_offset.lean` & `Proof/FrameTutor/advance_offset.lean` | [Chapter 4](../../docs/tutor/04-manual-proof-workflow.md) | Separates the safe function's `.defined` safety domain (`advanceOffsetSafetyDomain`: `offset = 2` and overflowing `offset = 255`) from its `.val` functional contract (`rustRequires` guarding `rustEnsures`) via `Obligations.FrameTutor.advance_offset.refineSafeSpec`, discharging `VerificationResult` with `verifyByWPSafe` (`WPSafe = True` on `.panic` at `offset = 255`, `*ret == 6` at `offset = 2`) and proving `MirContractHoldsWithSafety`. |
| `src/lib.rs` (`read_version_ref`), `Specs/FrameTutor/read_version_ref.lean`, & `Proof/FrameTutor/read_version_ref.lean` | [Chapter 5](../../docs/tutor/05-verifying-unsafe-rust.md) | Stateful `unsafe` reference read whose `# Safety` pointer-validity precondition lives in `.defined` of `MirStatefulContractSpec` via `StatefulItemSpec "frame_tutor::read_version_ref"`, verified against `StatefulVerificationResult` with `dischargeStatefulEq`. |
| `src/lib.rs` (`write_version_mut`), `Specs/FrameTutor/write_version_mut.lean`, & `Proof/FrameTutor/write_version_mut.lean` | [Chapter 5](../../docs/tutor/05-verifying-unsafe-rust.md) | Stateful `unsafe` mutable reference write under `.active` Tree Borrows permission whose `# Safety` precondition lives in `.defined` of `MirStatefulContractSpec` via `StatefulItemSpec "frame_tutor::write_version_mut"`, verified against `StatefulVerificationResult` with `dischargeStatefulEq` and `BorrowTokenSep`. |
| `src/lib.rs` (`WireHeader`, `unsafe impl WireHeader for FrameLen`) & `Proof/FrameTutor/__anneal_unsafe_impl_WireHeader_for_FrameLen.lean` | [Chapter 5](../../docs/tutor/05-verifying-unsafe-rust.md) | `#[anneal_spec::unsafe_trait]` and `#[anneal_spec::unsafe_impl(true)]` verification via `verifyByWP` paired with `Anneal.BitValidity` theorems (`IsUnaligned`, `IsFromBytes`, `IsIntoBytes`, `IsFromZeros`) over the 1-byte `FrameLen` layout. |
| `.anneal/spec-lock.json` *(generated on demand)* | [Chapter 6](../../docs/tutor/06-agentic-proof-workflow.md) | Cryptographic specification lock enforced by `cargo anneal lock-specs`, `cargo anneal agent-context`, and `cargo anneal agent-verify`. |

## Running the Pipeline

You can run the automated multi-stage integration test suite with:

```sh
cargo test -p cargo-anneal --test end_to_end_tutor --locked
```

That suite also replays the tutorial itself: [`docs/tutor/workflow/tutor.toml`](../../docs/tutor/workflow/tutor.toml)
drives disposable copies of the chapter crates through Chapters 1–6, checks
that each committed chapter crate is the previous one plus the edits its
chapter describes, and checks that every command, report, error message, and
file listing in the chapters matches that run (see
[`docs/tutor/workflow/README.md`](../../docs/tutor/workflow/README.md)).

Or run each CLI stage directly using either **Flavour A** (inside an Anneal
checkout) or **Flavour B** (using an installed `cargo anneal` binary):

### Flavour A — Inside an Anneal Checkout (from the repository root)

```sh
# 0. Build the capture wrapper and CLI once:
cargo build -p anneal-rustc-capture -p cargo-anneal

# 1. Extract MIR and companion contracts (Chapters 1 & 2):
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor/Cargo.toml

# 2. Scaffold .anneal/generated/ while preserving anneal/proofs/ (Chapters 1 & 2):
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor/Cargo.toml --from-units

# 3. Lock specifications and run non-vacuity checks (Chapter 6):
cargo run -p cargo-anneal -- lock-specs --manifest-path examples/tutor/Cargo.toml --from-units

# 4. Render structured agent context for an item (Chapter 6):
cargo run -p cargo-anneal -- agent-context --item read_version_ref --manifest-path examples/tutor/Cargo.toml --from-units

# 5. Run locked-spec kernel verification and TrustedBoundary audit (Chapters 4, 5 & 6):
cargo run -p cargo-anneal -- agent-verify --manifest-path examples/tutor/Cargo.toml --from-units
```

### Flavour B — Using `cargo anneal` Outside the Checkout (or Inside `examples/tutor/`)

```sh
# 0. Install `cargo-anneal` and `anneal-rustc-capture` onto PATH:
cargo install --path crates/cargo-anneal --path trusted/rustc-capture

# Run from inside the crate directory (or pass `--manifest-path path/to/Cargo.toml`):
cd examples/tutor
cargo anneal extract
cargo anneal scaffold --from-units
cargo anneal lock-specs --from-units
cargo anneal agent-context --item read_version_ref --from-units
cargo anneal agent-verify --from-units
```

> **Note:** Running `cargo anneal` directly against a tutor crate creates
> disposable `target/`, `.anneal/`, and `Cargo.lock` artifacts inside it. They
> are ignored by `.gitignore` (`/examples/tutor*/...`), so the repository tree
> keeps only durable source and proof files; delete them to start fresh.
