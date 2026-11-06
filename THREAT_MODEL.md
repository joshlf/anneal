<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Threat Model

[`PRINCIPLES.md`](PRINCIPLES.md) defines Anneal's central promise to its users:

> One of Anneal's outputs is a *TCB audit log*, a list of code and assumptions
> Anneal trusts (including itself) to compile your code and prove it correct.
> Anneal's promise is this:
>
> ***If** the code in your TCB audit log is correct, its assumptions are valid,
> **and** Anneal emits no errors, **then** your code is correct.*

In modern verification workflows, untrusted or reward-hacking AI coding agents
(as well as external human contributors) author Rust implementations,
specifications, proof automation, and crate-specific Lean 4 proof scripts. An
agent optimizing for a passing exit code (`cargo anneal verify` exiting `0`) has
a strong incentive to make verification succeed without proving the intended
property of the production Rust code.

For an incorrect Rust program to appear to pass verification, an untrusted
actor must subvert one of the three parts of [`PRINCIPLES.md`](PRINCIPLES.md)'s
promise:

1. **Subvert the execution environment** so *"Anneal emits no errors"* is forged
   or bypassed—for example, by replacing the `cargo-anneal` binary on a shared
   workstation, injecting environment variables, or executing a malicious
   `build.rs` script or procedural macro during compilation.
2. **Subvert the proof** so *"Anneal emits no errors"* on a false theorem
   statement—for example, by sneaking `sorry`, custom `axiom`s, `opaque`
   declarations, native code execution (`native_decide`), compiler overrides
   (`@[implemented_by]`, `@[extern]`), or elaboration-time I/O (`#eval`,
   `run_cmd`, `initialize`) into Lean proof files.
3. **Subvert the specification or scope** so *"the code in your TCB audit log
   is correct and its assumptions are valid"* silently proves a weaker claim—for
   example, by weakening a postcondition (`ensures(true)`), shrinking the input
   domain via a contradictory or over-constrained precondition
   (`requires(false)` or `requires(len == 0)`), modifying a helper function
   called by a relational reference function (`spec_fn`), adding
   `#[anneal::trusted]` waivers, mutating a private invariant field from an
   unverified function in the same module, or placing undefined behavior (UB)
   inside uncalled link-level hooks or `static mut` items.

This document is the controlling specification for how Anneal defends against
these three attack surfaces:

- **Section 1** defines the **execution-isolation boundary** (when a
  verification run is authoritative vs. advisory) and the four requirements of a
  well-configured CI environment.
- **Section 2** defines the **three-layer trust partition** and **two-stage
  boundary audit** that allow Anneal to trust pre-audited toolchain modules
  without re-auditing them on user machines while mechanically auditing
  user-supplied Lean files.
- **Section 3** defines how every class of user-brought artifact is handled and
  what human reviewers must inspect in the **TCB audit log
  (`anneal-tcb.lock`)**.

For how Anneal's internal codebase (`trusted/` and `trusted/audit/`) implements
these guarantees, see [`docs/trust-model.md`](docs/trust-model.md).

## 1. Execution-isolation boundary: when verification is authoritative

### The Outside-the-Write-Boundary Rule

No user-space verifier can defend against a process running concurrently with
the same operating-system privileges. When an un-sandboxed AI coding agent runs
under the developer's own OS user account on a workstation, it does not need to
sneak an axiom past the Lean 4 kernel or exploit a file-descriptor race: it can
overwrite `~/.cargo/bin/cargo-anneal`, shadow `cargo` on `PATH`, set
`LD_PRELOAD`, or print fabricated terminal output. Attempting to defend against
same-UID host tampering inside `cargo-anneal`—such as via per-file
`lstat`/`fstat` inode checks or re-hashing the installed toolchain directory on
every invocation—adds complexity without closing the attack.

Anneal therefore defines an explicit execution precondition for
[`PRINCIPLES.md`](PRINCIPLES.md)'s promise:

> **Outside-the-Write-Boundary Rule:** A verification result and its emitted TCB
> audit log are authoritative against an untrusted actor if and only if
> `cargo-anneal` (or `anneal-audit`), the installed Anneal toolchain archive,
> the verification staging directory, and the channel delivering the TCB audit
> log execute **outside that actor's OS write, environment-injection, and
> process-control boundary**.

This rule classifies execution environments into authoritative gates and
advisory developer loops:

| Execution environment | Actor isolation | Status under `PRINCIPLES.md` |
| :--- | :--- | :--- |
| **1. Anneal release CI** | Ephemeral CI runner evaluating a pull request to `joshlf/anneal`. | **Authoritative** for auditing and packaging Anneal toolchain releases. |
| **2. Downstream project CI** | Ephemeral CI runner evaluating a pull request to a user repository with `cargo anneal verify --locked`. | **Authoritative** for verifying the target crate and gating merges to `main`. |
| **3. Host-sandboxed local agent** | Workstation where the agent runs inside an unprivileged container, VM, or distinct OS UID, and the host runs `cargo anneal verify` outside that sandbox. | **Authoritative** against the sandboxed agent. |
| **4. Un-sandboxed same-UID workstation** | Developer machine where an agent shares write access to the user's home directory, binaries, or shell environment. | **Advisory fast-feedback loop only.** Catches accidental errors and naive agent shortcuts (`sorry`, `axiom`), but must be confirmed by CI (or a host sandbox) before trusting the result. |

### Requirements for a well-configured CI pipeline

To satisfy the Outside-the-Write-Boundary Rule in a downstream project's CI
pipeline (or host sandbox), four conditions must hold:

1. **Immutable verifier and pinned toolchain:** `cargo-anneal` and the Anneal
   toolchain archive are installed from a pinned release digest (verified once
   at installation time by `cargo anneal setup`) onto a filesystem path not
   writable by untrusted code during verification.
2. **Pre-execution gating of `build.rs` and procedural macros:** During MIR
   capture, Cargo compiles and executes `build.rs` scripts and procedural macros
   under the CI runner's own user account. If a pull request introduces or
   modifies a `build.rs` script or procedural macro that executes before the TCB
   audit check, that code could compromise the CI runner. Under
   `cargo anneal verify --locked`, `cargo-anneal` hashes all `build.rs` scripts
   and non-TCB procedural macros in the resolved build graph and verifies them
   against the committed `anneal-tcb.lock` **before** compiling or executing
   them—failing closed prior to execution when any unapproved build hook is
   present—and stages verification inputs in a private temporary directory
   outside the repository checkout.
3. **Scrubbed child-process environment and repository-input hygiene:**
   `cargo-anneal` clears ambient environment variables when invoking `rustc`,
   `anneal-rustc-capture`, and `lean` (stripping `LD_PRELOAD`,
   `DYLD_INSERT_LIBRARIES`, `RUSTC_WRAPPER`, `RUSTFLAGS`,
   `CARGO_ENCODED_RUSTFLAGS`, `LEAN_PATH`, and unpinned environment variables).
   Because the checked-out Git repository tree is untrusted input,
   `cargo-anneal` and `anneal-rustc-capture` also reject symlinks and `..` path
   traversal inside the crate, ignore or reject pre-compiled `.olean`/`.ir`
   files and pre-existing `.anneal/` outputs, reject repo-local
   `rust-toolchain*` and `.cargo/config*` compiler overrides, reject
   out-of-tree `include!`/`#[path]` files and unpinned `env!`/`option_env!`
   reads via `rustc` session tracking, and require identical MIR across `debug`
   and `release` configurations.
4. **Locked TCB audit log and protected workflows:** CI runs
   `cargo anneal verify --locked` so any unreviewed change to the crate's TCB or
   assumptions fails the build, and repository branch protection requires human
   review on changes to CI workflow configurations, toolchain version pins,
   `anneal-tcb.lock`, and specifications.

## 2. Three-layer trust partition and two-stage boundary audit

### The three universal trust layers

Every verification run combines artifacts from Anneal itself and from the target
Rust crate. Both sets of artifacts are governed by the same **three-layer trust
partition**, defined by each artifact's role in the Lean 4 kernel:

| Layer | Role in verification | In Anneal (`joshlf/anneal`) | In a downstream user crate | TCB audit log (`anneal-tcb.lock`) & human review |
| :--- | :--- | :--- | :--- | :--- |
| **Layer 1: Execution & foundation TCB** | Executes MIR extraction, Lean elaboration, and kernel typechecking. | Pinned `lean` + `Init.*` prelude (`foundation-lock.json`), `rustc`, `trusted/rustc-capture/`, `trusted/audit/`, `trusted/cargo-anneal/`, `root-manifest.sha256`. | Target triple, Cargo features/cfgs, `[profile]` settings, and any approved `build.rs` or proc-macro hooks (`build_hooks`). | **In the TCB audit log.** Pinned by version/digest; `build_hooks` gated before execution. |
| **Layer 2: Specification & assumption TCB** | Defines *what* program is verified, *what* theorem statement is claimed, and *what* obligations are waived. | `trusted/lean/` (`Trusted.*` MIR AST and operational semantics, module-tiered as `vetted` or `candidate:<feature>`). | Captured `Mir.lean` (`src/**`, inline `requires`/`ensures`/`invariant` specs, Mode 4 `spec_fn` closures, waivers, unverified functions in private-invariant scopes, ambient items) and user mathematical models (`Spec/*.lean`). | **In the TCB audit log.** Pure, tactic-free, and transparent; reviewed by humans. |
| **Layer 3: Untrusted proof layer** | Constructs proof terms discharging Layer 2's theorem statement. | `theory/` (`Anneal.*`: IR lowering passes, simulation theorems, WP & separation-logic lemmas, and proof automation). | Crate-specific Lean proof modules (`Proof/*.lean`) and the generated root `Proof.lean` entrypoint. | **Outside the TCB audit log.** Mechanically audited and kernel-checked; **zero human review**. |

### Statement-Origin Separation

In the Lean 4 kernel, every compiled theorem has two distinct parts:

- **The theorem statement (`ConstantInfo.type`):** The proposition claiming
  *what* holds (Layer 2).
- **The proof term (`ConstantInfo.value?`):** The lambda term showing *why* that
  proposition holds (Layer 3).

Anneal enforces **Statement-Origin Separation** across both its own repository
and downstream crates:

1. **One-way dependency DAG (`Trusted.*` $\to$ `Spec.*` $\to$ `Mir` $\to$
   `Proof.*`):** Every constant referenced in the target theorem statement
   (`Trusted.CrateTheorem Mir.crate`)—and every constant referenced by any Layer
   2 specification module—must originate in Layer 1 (`Init.*`) or Layer 2
   (`Trusted.*`, user `Spec.*`, and captured `Mir`). No constant from Layer 3
   (`theory/` or user `Proof.*`) may appear anywhere in Layer 2 or in the
   theorem statement.
2. **Mechanical proof purity:** Every Layer 3 module is mechanically verified to
   be free of elaboration side effects (`#eval`, `run_cmd`, `by_elab`,
   `initialize`), compiler overrides (`@[implemented_by]`, `@[extern]`,
   `@[csimp]`), native evaluation (`native_decide`), custom `axiom`s, `sorry`,
   `opaque`, `partial`, and `unsafe` declarations, and is rechecked by the
   standalone Lean 4 kernel (`trustLevel := 0`, `loadExts := false`).

Because Layer 3 proofs cannot alter the theorem statement and cannot introduce
axioms or side effects, a buggy or adversarial proof script in `theory/` or
`Proof/*.lean` can cause verification to fail, but can never cause a false
theorem statement to pass.

### Two-stage boundary auditing: Anneal CI vs. user CI

Splitting the boundary audit along the toolchain release boundary explains why
Anneal does not need to re-audit its own shipped code on user machines, while
still auditing extra Lean files brought along by the user's crate:

- **Stage A — In Anneal's release CI (`anneal-audit --mode audit`):** Before an
  Anneal release is packaged, Anneal's CI audits all of Anneal's Layer 2
  (`trusted/lean/`) and Layer 3 (`theory/`) modules from scratch against the
  pinned `Init.*` foundation, enforces `vetted` vs. `candidate:<feature>` tier
  separation, and packages the resulting pre-compiled `.olean` modules and tier
  metadata (`toolchain-manifest.json`) into the toolchain archive.
- **Stage B — In downstream crate verification (`cargo anneal verify`):** When
  verifying a user crate, `cargo-anneal` loads Anneal's pre-audited `.olean`
  modules from the installed toolchain archive as an immutable base environment
  (without re-parsing, re-compiling, or re-auditing `trusted/lean/` or
  `theory/`) and runs syntactic preflight and incremental standalone kernel
  replay (`--mode audit-delta`) **only on the user crate's delta** (`Mir.lean`,
  `Proof.lean`, and any user-supplied `Spec/*.lean` or `Proof/*.lean` files).

## 3. User-brought artifacts and the `anneal-tcb.lock` review contract

### How Anneal handles every class of user-brought artifact

To prevent an untrusted agent from subverting verification through the crate's
source code, specifications, or dependencies without human visibility, Stage B
enforces the following contract across all five classes of user-brought
artifacts:

| User-brought artifact | Reward-hacking vector | Mechanical defense & `anneal-tcb.lock` visibility |
| :--- | :--- | :--- |
| **1. User proof modules (`Proof/*.lean`)** | Agent sneaks in `sorry`, `axiom`, `#eval`, `@[implemented_by]`, or proves a weakened theorem instead of `Trusted.CrateTheorem Mir.crate`. | **Mechanically audited in Stage B; omitted from `anneal-tcb.lock`.** `anneal-rustc-capture` generates the root `Proof.lean` entrypoint pinning the theorem statement to `Trusted.CrateTheorem Mir.crate`, and Stage B audits `Proof/*.lean` before replaying it in the kernel. Proof edits require **zero human review**. |
| **2. User specification models (`Spec/*.lean`) & inline contracts (`requires`, `ensures`, `invariant`, Mode 4 `spec_fn`)** | Agent weakens a postcondition (`ensures(true)`), shrinks the domain via a contradictory or over-constrained precondition (`requires(false)`, `requires(x == 0)`, or dead `const` assertions), modifies a helper called by a Mode 4 `spec_fn`, or hides tactics/axioms in `Spec/*.lean`. | **Mechanically checked for transparency & non-vacuity; logged in `anneal-tcb.lock`.** Contradictory preconditions are rejected by existential non-vacuity checks; `Spec/*.lean` must be tactic-free and `opaque`-free; and `anneal-tcb.lock` records every verified function's `requires`, `ensures`, non-empty `required_consts`, `Spec/*.lean` digests, and the normalized bodies/digests of Mode 4 `spec_fn`s **and their entire transitive callee/constant closures**. |
| **3. Partially verified crates & private-invariant visibility scopes ($\mathcal{V}_T$)** | An unverified function in the same module mutates a private field of a type $T$, breaking $T$'s `#[anneal::invariant]` assumed by verified methods. | **Scoped encapsulation check + explicit waiver in `anneal-tcb.lock`.** For any type $T$ with a private invariant (`allFieldsPubSafe = false`), let $\mathcal{V}_T$ be the union of visibility scopes of $T$'s non-`pubSafe` fields. Any unverified function inside $\mathcal{V}_T$ is recorded as an explicit `unverifiedFn` waiver in `anneal-tcb.lock`, and verified safe functions in $\mathcal{V}_T$ cannot return `&mut` references to non-`pubSafe` invariant fields unless the invariant holds universally on that field type. |
| **4. Uncalled ambient & link-level items** | Agent places UB or state corruption in `#[no_mangle]`, `#[export_name]`, `#[link_section]`, `#[global_allocator]`, `#[panic_handler]`, `static mut`, interior-mutable `static`s, or `extern` blocks never called by verified functions. | **Inventoried in `anneal-tcb.lock` (`ambient_items`).** `anneal-rustc-capture` scans the crate HIR for link-level entrypoints, global runtime hooks, and mutable statics outside the verified call graph and records them in `anneal-tcb.lock`. |
| **5. Cross-crate verified dependencies** | Downstream crate `B` consumes a spoofed or stale verification summary from upstream crate `A`, or `A` hides a `#[anneal::trusted]` waiver or `candidate:<feature>` dependency. | **Compositional `UnitId` verification & transitive TCB union.** Workspace dependencies are verified in topological order in private staging, bound by a recursive Merkle digest over compilation inputs (`UnitId`), and their Layer 1/Layer 2 waivers, `Spec.*` models, and `candidate:<feature>` closures propagate transitively into `B`'s `anneal-tcb.lock`. |

### Zero-churn `anneal-tcb.lock` and what human reviewers check

If the git-committed `anneal-tcb.lock` recorded target-crate `src/**/*.rs` file
hashes, sequential `BodyId` integers, or `file:line:col` source spans, every
internal refactoring, comment edit, or `cargo fmt` run would produce a lockfile
diff—training human reviewers to rubber-stamp TCB changes.

Anneal therefore separates volatile compilation digests (used only in ephemeral
staging certificates during a run) from the committed `anneal-tcb.lock`:

- `anneal-tcb.lock` keys items by canonical module-qualified Rust paths (such as
  `my_crate::foo::bar`) and records only Layer 1 execution hooks/configuration
  and Layer 2 specifications, `Spec/*.lean` digests, active
  `candidate:<feature>` tags, waivers, and unverified/ambient item inventories.
- **Editing a verified function's implementation body (outside a Mode 4
  `spec_fn` closure), reformatting Rust code, or rewriting `Proof/*.lean`
  produces zero diff in `anneal-tcb.lock`.**

When a pull request passes `cargo anneal verify --locked` in a well-configured
CI pipeline:

- If `anneal-tcb.lock` has **no diff**, the crate's trusted surface,
  specifications, and assumptions are unchanged; the reviewer does not need to
  inspect `Proof/*.lean` for soundness.
- If `anneal-tcb.lock` **has a diff**, the human reviewer inspects that diff
  against four questions:
  1. **Preconditions and `required_consts` (no unintended domain shrinking):**
     Are `requires` clauses and post-monomorphization `required_consts`
     realistic rather than over-constraining the function to a trivial subset of
     inputs?
  2. **Postconditions, `Spec/*.lean`, and Mode 4 `spec_fn` closures (no weakened
     claims):** Do `ensures` clauses, pure `Spec/*.lean` definitions, and any
     Mode 4 `spec_fn` (including its transitive helpers) express the intended
     correctness property?
  3. **Verification scope (`unverified_functions` and `ambient_items`):** Are
     any newly added unverified functions (especially those tagged
     `[contains_unsafe_block]` or `[unsafe_fn]`) or link-level `ambient_items`
     expected to remain outside verification?
  4. **Explicit waivers, candidate features, and `build_hooks`:** Are any
     `#[anneal::trusted]` waivers, unverified-callee waivers (including those in
     private-invariant scopes $\mathcal{V}_T$), `candidate:<feature>` TCB
     modules, or `build.rs` / procedural-macro changes justified?
