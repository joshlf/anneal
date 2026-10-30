# End-to-End Anneal User Journeys & Post-Demo Roadmap

This document walks through the four human-and-agent workflows demonstrated in
[`examples/wireframe-demo/`](../examples/wireframe-demo/README.md) (`wireframe_demo`)
and tested end-to-end in
[`crates/cargo-anneal/tests/end_to_end_demo_journeys.rs`](../crates/cargo-anneal/tests/end_to_end_demo_journeys.rs)
and [`examples/wireframe-demo/run_live_demo.py`](../examples/wireframe-demo/run_live_demo.py).

## 1. Architectural Foundations Used Across the Four Journeys

Every journey reduces to a kernel-checked certificate in
[`trusted/lean/Trusted/VerificationResult.lean`](../trusted/lean/Trusted/VerificationResult.lean)
replayed from compiled `.olean` artifacts by
[`trusted/audit/TrustedBoundary.lean`](../trusted/audit/TrustedBoundary.lean):

- **Layer 1A Smyth `Partial` refinement (`Trusted.Refinement`):** Specifications
  and program behaviors live in the Smyth partial-specification lattice `Partial α`,
  where `.defined` governs safety (`TreeSafe`: absence of `ITree.fail .ub`) and
  `.val` constrains observable outcomes and memory transformations.
- **Layer 1B coinductive interaction trees (`Trusted.ITree`):** Captured
  `Runtime(PostCleanup)` MIR executes over `ITree MirEffect MirOutcome`
  (`mirStatefulTree`), separating Undefined Behavior (`MirFailE`), branch
  observations (`MirObsE`), and unresolved external calls (`MirCallE`).
- **Byte-level `V2026_06_01` memory and Tree Borrows (`Trusted.Rustc.V2026_06_01`):**
  Every memory byte carries initialization, provenance, and scalar `validRange`
  metadata alongside per-location Tree Borrows permission trees, so unaligned
  dereferences, out-of-range `transmute` bit patterns, out-of-bounds projections,
  and aliasing violations emit `ITree.fail .ub`.
- **Two complementary untrusted proof engines (`theory/Anneal/`):**
  - [`Anneal.Rustc.V2026_06_01.SymbolicEval`](../theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean)
    evaluates bounded straight-line and branching MIR symbolically in a single pass
    and constructs kernel-checked UB counterexamples (`refuteClaimByBoundedUB`)
    and non-vacuity witnesses (`proveNonVacuousPre`, `proveNonVacuousStatefulPre`).
  - [`Anneal.FunctionalTranslation`](../theory/Anneal/FunctionalTranslation.lean)
    (`#109`) lifts structured safe Rust—including mutable references (`MutLens` +
    `PointsTo`) and `Nat`-ranked `while` loops (`TransPlan.loop`)—into pure Lean
    goals amenable to `simp` and `omega`.
- **Whole-crate rollup (`CrateVerificationResult`):** `cargo anneal` generates a
  per-item `Verify.<Crate>.<Item>` shard (preserving Lake artifact caching across
  single-function `--item` edits) plus a disposable `CrateVerify` rollup audited
  by `TrustedBoundary`.

---

## 2. Journey 1 — Bootstrapping Verification on a Rust Codebase

**Goal:** Apply Anneal incrementally to an existing `#![no_std]` packet-framing
module without writing boilerplate for trivial items, while progressively adding
Rust-level contracts and stateful invariants.

1. **Zero-configuration baseline (`defaultProof`):**
   Running `cargo anneal verify` on `wireframe_demo` extracts `Runtime(PostCleanup)`
   MIR and scaffolds `Verify.WireframeDemo.*` modules. Zero-argument items such as
   `WIRE_VERSION_V1` and `wire_protocol_version` pass `defaultProof`
   (`SymbolicEval.verifyByWP`) immediately with **zero** authored files under
   `anneal/proofs/`.
2. **Rust-level models, invariants, and bounded arithmetic (`#[spec]`):**
   - `#[anneal_spec::model] pub const fn is_valid_payload_len(len: u16) -> bool`
     and `#[anneal_spec::invariant(self.offset <= self.limit)] pub struct FrameCursor`
     are captured alongside subject functions as typed MIR companions.
   - `frame_total_len(header_len: u16, payload_len: u16) -> u16` declares
     `requires: header_len <= 16 && payload_len <= 1024` and
     `ensures: |ref ret| *ret == header_len + payload_len`. `cargo anneal scaffold`
     lowers both clauses to `MirBoolPredicateHolds` in
     `Obligations.WireframeDemo.frame_total_len`, and
     `Proof/WireframeDemo/frame_total_len.lean` discharges `VerificationResult`
     universally across all `17 * 1025 = 17,425` valid input pairs.
3. **Stateful mutable-reference verification via `FunctionalTranslation` (`#109`):**
   `advance_cursor(cursor: &mut FrameCursor, step: u16) -> bool` mutates
   `cursor.offset` in place when `step <= cursor.limit - cursor.offset`. Using
   `StatefulItemSpec` + `Anneal.FunctionalTranslation` (`PointsTo`, `MutLens`, and
   `TransPlan`), `Proof/WireframeDemo/advance_cursor.lean` proves across all valid
   `FrameCursor` allocations that `advance_cursor` never overflows or triggers UB,
   preserves `cursor.offset <= cursor.limit`, and returns `true` if and only if
   `step <= limit - offset`.

---

## 3. Journey 2 — Finding and Repairing an Existing `unsafe` Bug

**Goal:** Expose a subtle bit-validity Undefined Behavior bug in zero-copy
`unsafe` parsing code, produce a concrete machine-checked counterexample witness,
and prove the repaired implementation sound across all inputs.

1. **The latent bug:**
   `WireHeader` is a 4-byte `#[repr(C)]` struct `{ version: u8, compressed: bool, payload_len: u16 }`.
   In the buggy revision of `decode_wire_header(raw: [u8; 4]) -> u16`, the parser
   checks `if raw[0] != 1 { return 0; }` and immediately executes
   `unsafe { core::mem::transmute::<[u8; 4], WireHeader>(raw) }`, forgetting to
   check `raw[1] <= 1`.
2. **Kernel-checked UB refutation (`refuteClaimByBoundedUB`):**
   In Rust (and in `Trusted.Rustc.V2026_06_01.MirSemantics`), `bool` carries
   scalar `validRange = 0..=1`. On input `raw = [1, 2, 4, 0]`, `CastKind.transmute`
   attempts to decode byte `1` (`2`) as `RigidTy.bool`, emitting `ITree.fail .ub`.
   `SymbolicEval.refuteClaimByBoundedUB` evaluates the captured MIR on
   `raw = [1, 2, 4, 0]` and proves `¬ buggyClaim.holds` inside the Lean 4 kernel.
3. **Verified repair:**
   Adding `if raw[1] > 1 { return 0; }` before the `transmute` restores bit-validity
   for `WireHeader::compressed`. `Proof/WireframeDemo/decode_wire_header.lean`
   proves `VerificationResult` unconditionally across all `2^32` 4-byte arrays.

---

## 4. Journey 3 — Keeping Code Authors and Reviewers in Check

### Journey 3A — Agent Authoring Code Under Locked Specifications

**Workflow:** A human tech lead specifies `clamp_payload_window(requested: u16, max_window: u16) -> u16`
using `#[anneal_spec::spec(...)]` on a stub body and locks the contract while
authorizing edits only to `clamp_payload_window`'s implementation and proof:

```bash
cargo run -p cargo-anneal -- lock-specs \
  --manifest-path examples/wireframe-demo/Cargo.toml \
  --allow-impl-edit clamp_payload_window
```

`.anneal/spec-lock.json` records SHA-256 digests for `Specs/**`, `Assumptions/**`,
every sibling function's MIR, and `clamp_payload_window`'s `requires`/`ensures`
companion MIR modules, listing only `wireframe_demo::clamp_payload_window` under
`mutable_subjects`. During `cargo anneal agent-verify`:

- **Weakening `#[anneal_spec::spec]` or adding an unlocked `Specs/` override**
  fails `verify_spec_lock` immediately before invoking Lean.
- **Submitting an incorrect implementation** (for example, returning `max_window`
  when `requested < max_window`) fails the `MirBoolPredicateHolds` `ensures`
  obligation in Lean.
- **Attempting `sorry` or a rogue `axiom`** fails `TrustedBoundary` source and
  kernel-replay checks.
- **Submitting the sound implementation and proof** passes `agent-verify` with
  `UNCONDITIONAL` and `TrustedBoundary kernel replay: PASS`.

### Journey 3B — Agent Reviewing Human-Authored Code

**Workflow:** A human author submits a PR implementing safe
`pub fn parse_compression_flag(flags_byte: u8) -> bool` with
`requires: (flags_byte & 1) == flags_byte` and an internal `unsafe` shortcut:
`unsafe { core::mem::transmute::<u8, bool>(flags_byte) }`.

The review agent applies two complementary checks:

1. **Safe-function total safety outside `requires` (`refineSafeSpec`, `#125`):**
   In Rust, a safe `pub fn` must never exhibit Undefined Behavior for *any*
   well-typed caller argument, even when its functional `requires` clause does not
   hold. `Specs/WireframeDemo/parse_compression_flag.lean` uses `refineSafeSpec`
   (`MirContractHoldsWithSafety`) to place all `256` valid `u8` scalars (`0..=255`)
   in `.defined` while guarding `rustEnsures` behind `rustRequires` in `.val`.
   At `flags_byte = 2`, the human's `transmute` triggers `ITree.fail .ub`, and
   `refuteClaimByBoundedUB` refutes the PR! Replacing the body with safe
   `(flags_byte & 1) != 0` satisfies `MirContractHoldsWithSafety` across all `256`
   inputs.
2. **Precondition non-vacuity (`NonVacuousPre`):**
   `cargo anneal lock-specs` checks specification non-vacuity and
   `proveNonVacuousPre` witnesses satisfiability of `rustRequires`, preventing
   contradictory preconditions from vacuously discharging `.defined`.

---

## 5. Journey 4 — Iterative Verified `safe -> unsafe` Performance Optimization

**Goal:** Refactor safe, idiomatic `checksum_frame_safe(frame: &[u8; 8]) -> u32`
(a four-iteration `while i < 4` loop performing eight checked byte loads) into a
branch-free `unsafe` word-lane implementation `checksum_frame_fast` proved both
free of Undefined Behavior and **behaviorally equivalent** to `checksum_frame_safe`
across all `2^64` 8-byte frames.

1. **Freezing `checksum_frame_safe` as the specification (`StatefulEquivItemSpec`):**
   `Specs/WireframeDemo/checksum_frame_fast.lean` uses
   `Obligations.WireframeDemo.checksum_frame_fast.refineEquivSpec Mir.WireframeDemo.checksum_frame_safe.body ...`
   to require `StatefulEquivVerificationResult`:
   - `RefinesStatefulMir`: `(mirObsErasedStatefulTree fast args mem).toPartial ≤ (mirObsErasedStatefulTree safe args mem).toPartial`
     (silencing `MirObsE` branch-counter differences via `silenceMirObs` so the
     branch-free `transmute` fast path refines the 4-iteration `while` loop in
     Layer 1A's `Partial` lattice), and
   - `TotalClaim.holds`: `TreeSafe`, `Productive`, `¬ MayDiverge`, panic-freedom,
     and memory preservation across every valid `&[u8; 8]` reference.
   Running `cargo anneal lock-specs --allow-impl-edit checksum_frame_fast` freezes
   `checksum_frame_safe`'s MIR and `Specs/WireframeDemo/checksum_frame_fast.lean`.
2. **Iteration 1 — Fast `unsafe` `transmute`, rejected on little-endian lane order:**
   The agent first writes `let words: [u16; 4] = unsafe { core::mem::transmute(*frame) };`
   and sums `words[0..4]` directly without byte-swapping. On little-endian targets,
   bytes `[0x01, 0x02]` decode as `0x0201` rather than big-endian `0x0102`.
   Running single-item verification:
   ```bash
   cargo run -p cargo-anneal -- agent-verify \
     --manifest-path examples/wireframe-demo/Cargo.toml \
     --item checksum_frame_fast
   ```
   recompiles only `checksum_frame_fast`'s shard against warm Lake artifacts and
   rejects Iteration 1 in seconds.
3. **Iteration 2 — Byte-swapped word lanes, `UNCONDITIONAL` across all `2^64` frames:**
   Adding `(((words[k] & 0x00ff) << 8) | (words[k] >> 8)) as u32` aligns every lane
   with `((frame[2*k] as u32) << 8) | (frame[2*k + 1] as u32)`. Both
   `--item checksum_frame_fast` and full-crate `agent-verify` (including
   `CrateVerify.verified : CrateVerificationResult crateClaim`) verify as
   `UNCONDITIONAL` with `0` extra axioms, and `run_live_demo.py` benchmarks the
   optimized release binary against `checksum_frame_safe`.

---

## 6. Expedient Choices & Post-Demo Refactoring Ledger

To deliver a fast, live-demoable end-to-end stack, the current convergence branch
makes six deliberate engineering trade-offs. Each preserves soundness of the stated
kernel claims and carries a concrete post-demo refactoring item:

| # | Expedient Choice in Current Stack | Why Chosen for Demo Velocity & Latency | Post-Demo Refactoring / Generalization Work |
| ---: | :--- | :--- | :--- |
| **1** | **Permit Lean `Init` + `Std` (including `Classical.choice`) in the environment auditor** rather than locking `trusted/lean/` to `Init.Core`-only constructive axioms | Enables `omega`, `simp`, `Std.Do`, and `coinductive_fixpoint`, cutting proof authoring effort and single-item rebuild times by 3–5x. | Split the axiom gate in `TrustedBoundary.lean` so `trusted/lean/` declarations remain `Classical.choice`-free (`propext` + `Quot.sound` only) while `theory/` and `Proof/` remain free to use `Std` and classical tactics. |
| **2** | **Verify concrete / monomorphized Rust functions** rather than parametric generics and trait-polymorphic MIR | `Runtime(PostCleanup)` MIR capture operates directly on concrete codec functions without requiring polymorphic layout quantification. | Build parametric polymorphism and trait-contract composition over `ITree.interp` and `ModularClaim` so generic wrappers (such as `zerocopy` abstractions) verify once parametrically. |
| **3** | **Capture host target layout tables (`64`-bit little-endian `LayoutTable`) per compilation unit** | Allows `rfl`-decidable `BitValidity` and `transmute` checks matching the `rustc` target binary in `< 0.5s`. | Thread explicit target ABI parameters (`pointerBits`, endianness, alignment bounds) into `Trusted.Layout` and `ArtifactIdentity` per `DESIGN.md` so portable claims quantify over admissible targets. |
| **4** | **Sequential byte-level `Memory` + Tree Borrows without weak-memory view fronts** | All four demo journeys target sequential safe and `unsafe` Rust where `AbstractByte` validity and Tree Borrows permissions are the primary bug surface. | Compose the byte-level Tree Borrows heap with timestamp/view-front weak-memory state as an open concurrency/atomic `Effect` layer over `ITree`. |
| **5** | **Scope `Anneal.FunctionalTranslation` (`TransPlan` + `MutLens`) to structured safe Rust** (acyclic borrows, structured `while` loops, non-unwinding paths) | Covers the safe baseline functions in Journeys 1, 3, and 4 cleanly while `unsafe` `transmute` code drops down seamlessly to `SymbolicEval` / `DWP`. | Extend `FunctionalTranslation` to general multi-exit loops, nested `&mut` projections, unwind cleanup paths, and automatic `TransPlan` synthesis in `cargo-anneal` (`#109`). |
| **6** | **Lightweight `CrateVerify.lean` + `.anneal/spec-lock.json` verification output** | Reuses `cargo-anneal`'s SHA-256 manifest handshake and per-item Lake artifact cache with minimal CLI surface area. | Package `.anneal/` outputs into the self-contained, offline-auditable `VerificationResult` bundle specified in `DESIGN.md` (explicit `TCBItem` ledger, `TrustPolicy` identity, and lowering assumption inventory). |
