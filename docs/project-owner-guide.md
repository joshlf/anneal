# Project owner guide: Adopting Anneal in a Rust codebase

This guide explains how Rust library and system maintainers can adopt Anneal to
specify and verify Rust code—including `unsafe` blocks, byte parsers, and
performance-critical optimizations—without requiring project maintainers or code
reviewers to write Lean 4 proofs by hand.

Anneal separates **specification** (owned by Rust maintainers) from **proof
construction** (delegated to autonomous coding agents or verification engineers
and checked by the Lean 4 kernel and Anneal's outer auditor). As a project
owner, your primary responsibilities are:

1. selecting the verification slice and writing contracts in Rust using
   `#[anneal_spec::*]` attributes,
2. locking those specifications with `cargo anneal lock-specs` before handing
   proof obligations to an agent, and
3. reviewing the resulting pull request using a concise verification checklist.

For interactive step-by-step exercises, see [**The Anneal Tutor**](tutor/README.md).
For configuring agent harnesses and anti-cheating sandboxes, see
[**Agent harness setup**](agent-harness-setup.md) and
[**Agentic proof construction workflow**](agent-proof-workflow.md).

---

## 1. Installing Anneal and its pinned toolchain

Install `cargo-anneal` and download the pinned prebuilt `anneal-rustc-capture`
driver, Lean 4 toolchain (`v4.34.1`), and precompiled `.olean` libraries into
`~/.anneal/toolchain/<version>/`:

```bash
cargo install cargo-anneal
cargo anneal setup
```

If you are working inside an offline environment or from a local release bundle,
install the archive directly:

```bash
cargo anneal setup --local-archive /path/to/anneal-toolchain.tar.zst
```

Alternatively, in repositories using Nix flakes, run `nix develop` to enter a
hermetic shell containing the pinned Rust nightly toolchain, Lean 4 (`v4.34.1`),
`cargo-anneal`, and `anneal-rustc-capture`.

---

## 2. Adding `anneal-spec` to `Cargo.toml`

Add `anneal-spec` to your crate's `[dependencies]`:

```toml
[dependencies]
anneal-spec = { version = "0.1" }
```

`anneal-spec` procedural macros expand into inert, hidden companion items
(`#[doc(hidden)]`) that impose zero runtime overhead in normal `cargo build`,
`cargo test`, and `cargo clippy` runs while preserving typed specification bodies
in `Runtime(PostCleanup)` MIR for `cargo anneal extract`.

---

## 3. Choosing a first verification slice

Start with a small, high-leverage module or function rather than attempting to
verify an entire workspace at once:

- **Arithmetic and framing helpers:** Functions computing buffer offsets, packet
  lengths, alignment rounding, or bitfield masks (`#[anneal_spec::spec]`).
- **Low-level parsers and codecs:** Functions that validate untrusted byte
  slices or header flags (`#[anneal_spec::spec(safe_total, ...)]`).
- **Types with representation invariants:** Wrappers around raw pointers,
  indices, or bounded integers (`#[anneal_spec::invariant(...)]` and
  `#[anneal_spec::unsafe_impl]`).
- **`safe` $\to$ `unsafe` optimizations:** Fast-path functions (such as
  unaligned loads, SIMD/SWAR loops, or unchecked indexing) that must behave
  identically to a readable safe reference function
  (`#[anneal_spec::spec(equivalent_to: <reference_fn>, ...)]`).

Use `--filter <substring>` during extraction and scaffolding when focusing on a
specific module or function:

```bash
cargo anneal scaffold --filter frame_header --init-proofs
```

---

## 4. Writing specifications in Rust

Anneal provides seven specification attributes in `anneal_spec` so that most
contracts can be authored and reviewed directly in Rust source files without
writing custom `anneal/proofs/Specs/*.lean` overrides:

| Attribute | Target | Purpose |
| --- | --- | --- |
| `#[anneal_spec::spec(...)]` | `fn`, `trait`, `impl` | Attaches `requires`, `ensures`, `maintains`, and `captures` clauses to a function or method. |
| `#[anneal_spec::spec(safe_total, ...)]` (or `total: true`) | `fn` | Enforces `MirNoUB` (definedness and panic-freedom) across **all** well-formed inputs while guarding functional `ensures` clauses behind `requires` (`refineSafeSpec`). |
| `#[anneal_spec::spec(equivalent_to: <fn>, ...)]` | `fn` | Requires the annotated function to refine and terminate identically to `<fn>` (`StatefulEquivItemSpec` / `RefinesStatefulMir`). |
| `#[anneal_spec::external_spec(for = <path>, ...)]` | sidecar `fn` | Attaches a `requires`/`ensures` contract to an unowned dependency or `core` function with a compile-time signature check. |
| `#[anneal_spec::model]` | `fn`, `struct`, `enum`, `const` | Marks a pure Rust helper item as a ghost specification model (`CapturedItemKind::Model`). |
| `#[anneal_spec::invariant(...)]` | `struct`, `enum` | Declares a boolean representation invariant over `&self` (`CapturedItemKind::TypeInvariant`). |
| `#[anneal_spec::unsafe_trait]` / `#[anneal_spec::unsafe_impl(...)]` | `unsafe trait`, `unsafe impl` | Turns an `unsafe impl Trait for Type` block into a first-class verification obligation (`CapturedItemKind::UnsafeTraitImpl`). |

### Example: Safe total specification vs. conditional precondition

When verifying a safe function that accepts untrusted inputs, use `safe_total`
so the function is proved free of Undefined Behavior and panics on *every*
well-typed input, while the functional postcondition is asserted when `requires`
holds:

```rust
#[anneal_spec::spec(
    safe_total,
    requires: (b & 1) == b,
    ensures: |ret| *ret == (b == 1),
)]
pub fn parse_compression_flag(b: u8) -> bool {
    b == 1
}
```

### Example: Verified `safe` $\to$ `unsafe` behavioral equivalence

When optimizing a safe reference function `checksum_frame_safe` with an `unsafe`
or bitwise fast path `checksum_frame_fast`, link them directly in Rust:

```rust
#[anneal_spec::spec(
    equivalent_to: checksum_frame_safe,
    requires: true,
    ensures: |ret| *ret == *ret,
)]
pub fn checksum_frame_fast(frame: &[u8; 8]) -> u32 {
    // Fast implementation proved behaviorally equivalent to `checksum_frame_safe`
    u32::from_le_bytes([frame[0], frame[1], frame[2], frame[3]])
        wrapping_add(u32::from_le_bytes([frame[4], frame[5], frame[6], frame[7]]))
}
```

---

## 5. Workspace layout: What to commit to Git

Running `cargo anneal scaffold` populates two distinct trees in your crate:

1. **`.anneal/` (Disposable generated workspace — do not hand-edit):**
   - `.anneal/generated/Mir/<Crate>/<Item>.lean`: Lowered MIR ASTs and layout
     tables regenerated on every run.
   - `.anneal/generated/Obligations/<Crate>/<Item>.lean`: Default `ItemSpec`
     instances and `refine*Spec` combinators lowered from your Rust attributes.
   - `.anneal/generated/Verify/<Crate>/<Item>.lean` and `CrateVerify.lean`:
     Audited theorem assembly roots.
   - `.anneal/spec-lock.json`: Cryptographic SHA-256 specification lockfile
     created by `cargo anneal lock-specs`.
2. **`anneal/proofs/` (Durable human- and agent-authored artifacts — commit to Git):**
   - `anneal/proofs/Proof/<Crate>/<Item>.lean`: Kernel-checked Lean 4 proofs
     discharging `Verify.<Crate>.<Item>.verified`.
   - `anneal/proofs/Specs/<Crate>/<Item>.lean` *(optional)*: Explicit Lean
     specification refinements when a property cannot be stated purely in Rust
     (must use `refineSpec` / `refineStatefulSpec` / `refineSafeSpec` /
     `refineEquivSpec` so Rust `#[spec]` clauses remain conjoined).
   - `anneal/proofs/Assumptions/<Crate>/<Item>.lean` *(optional)*: Explicit,
     audited conditional assumptions surfaced as `CONDITIONAL` in verification
     reports.

Add `.anneal/generated/` and `.anneal/.lake/` to `.gitignore` if you do not wish
to check in generated Lean files; always commit `anneal/proofs/` (and
`.anneal/spec-lock.json` during active verification workflows).

---

## 6. Understanding verification tiers

Every `cargo anneal verify` and `cargo anneal agent-verify` run classifies each
verified item and the overall crate into one of four explicit verification
tiers:

| Status | Meaning | Suitable for |
| --- | --- | --- |
| `UNCONDITIONAL` | Proved in the Lean 4 kernel from standard axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero project assumptions and zero `native_decide` trust. | Final sign-off on safe and `unsafe` production code. |
| `CONDITIONAL` | Proved in the Lean 4 kernel relative to explicit `axiom` declarations isolated in `anneal/proofs/Assumptions/<Crate>/<Item>.lean` (requires `--allow-assumptions`). | Incremental adoption while modeling external hardware, FFI, or unverified callees. |
| `UB_EXCEPTION` | Proved under a scoped UB-exception contract (`UbExceptionVerificationResult`, requires `--allow-ub-exceptions`) that documents a known strict-safety subdomain boundary. | Explicit, audited boundary documentation for legacy `unsafe` APIs. |
| `PROVISIONAL_NATIVE` | Proved in `Proof.*` using `native_decide` (`Lean.ofReduceBool` / `Lean.trustCompiler`, requires `--provisional` or `--allow-provisional-native`). | Rapid Phase 1 agentic triage and bounded exploration before converting to kernel-checked symbolic proofs. |

---

## 7. Pull request review checklist for Rust maintainers

You do **not** need to read tactic scripts inside `anneal/proofs/Proof/**/*.lean`
to review a verification pull request safely. Because `TrustedBoundary` replays
every compiled `.olean` theorem in the Lean 4 kernel and enforces statement-origin
isolation (`Verify.<Crate>.<Item>.verified` can never mention declarations from
`theory/Anneal/`), a valid proof in `Proof/` cannot weaken the theorem statement.

When reviewing a PR that adds or updates Anneal proofs, check only the following
four items:

1. **Inspect Rust specification diffs (`src/**/*.rs`):**
   Verify that `#[anneal_spec::spec]`, `#[anneal_spec::invariant]`, and
   `#[anneal_spec::unsafe_impl]` annotations on your Rust functions accurately
   express the preconditions and postconditions you intend.
2. **Check for changes under `anneal/proofs/Specs/` and `anneal/proofs/Assumptions/`:**
   - If the PR only adds or edits files under `anneal/proofs/Proof/**`, the
     specification is untouched and follows directly from your Rust attributes.
   - If the PR touches `anneal/proofs/Specs/<Crate>/<Item>.lean`, confirm that it
     uses `Obligations.<Crate>.<Item>.refineSpec` (or `refineStatefulSpec`,
     `refineSafeSpec`, `refineEquivSpec`) with non-vacuous `extraPre` predicates
     and that a `non_vacuous` witness theorem is present in `Proof/<Crate>/<Item>.lean`.
   - If the PR touches `anneal/proofs/Assumptions/<Crate>/<Item>.lean`, review
     every `axiom` declaration in that file as an explicit unproved assumption.
3. **Verify the CI gate (`cargo anneal agent-verify --lock-git-ref origin/main`):**
   Ensure CI ran `cargo anneal agent-verify` (with `--lock-git-ref` or a locked
   `.anneal/spec-lock.json`) and exited `0`.
4. **Check the reported verification tier:**
   Confirm that the verification summary reports `UNCONDITIONAL` (or the
   explicitly authorized `CONDITIONAL` / `PROVISIONAL_NATIVE` tier for staged
   work).
