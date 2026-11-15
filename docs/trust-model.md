<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trust Model and Boundary Enforcement

> **Note:** Anneal is under active development. Parts of the design and
> architecture described in this document are not yet implemented or may be
> implemented differently; this document may be aspirational or stale relative
> to the codebase.

[`META_PRINCIPLES.md`](../META_PRINCIPLES.md),
[`PRINCIPLES.md`](../PRINCIPLES.md), and [`THREAT_MODEL.md`](../THREAT_MODEL.md)
are the controlling documents for Anneal's correctness promise and threat
model: if the code in a verification result's Trusted Computing Base (TCB)
audit log is correct, its assumptions are valid, and Anneal emits no errors in
an uncompromised execution environment, then the verified code is sound and
satisfies any stated specifications.

A modern verification tool needs tens of thousands of lines of intermediate
representation (IR) lowering passes, weakest-precondition (WP) rules,
separation-logic lemmas, and proof automation—much of it written by untrusted
AI agents. To keep the human audit surface small, Anneal isolates all
first-party trusted code inside [`trusted/`](../trusted) and places all
lowering passes, program logics, and tactics outside the TCB in `theory/`. To
ensure that adversarial or buggy code in `theory/` cannot use side effects, OS
APIs, or custom axioms to undermine the guarantees established by `trusted/`,
Anneal runs a standalone boundary auditor ([`trusted/audit/`](../trusted/audit))
**in Anneal's own repository CI**.

For related architectural details, see:

- [`docs/design.md`](design.md) for an overview of Anneal's verification
  workflow and specification modes.
- [`docs/architecture.md`](architecture.md) for the three-stage MIR pipeline
  and how untrusted lowering passes in `theory/` connect to `trusted/lean/`.

## 1. The `trusted/` boundary and how verification stays sound

Anneal divides its repository into two active zones for user-crate verification
(Pass 1), augmented by planned Pass 2 zones in repository CI for the MIR
correspondence audit (see [`docs/architecture.md`](architecture.md)):

| Zone | Directory | Role | Trust status |
| :--- | :--- | :--- | :--- |
| **Trusted foundation** | [`trusted/`](../trusted) (plus planned `trusted/correspondence/`) | Extracts MIR and emits pure proof scripts (`trusted/rustc-capture/`), defines captured MIR syntax and verification operational semantics (`trusted/lean/`), orchestrates CLI invocation (`trusted/cargo-anneal/`), audits the Anneal repository in CI (`trusted/audit/`), and—in planned Pass 2—states MIR correspondence claims and reference-adapter specifications (`trusted/correspondence/`). | **In the TCB.** Audited by humans (alongside external files pinned by hash manifests inside `trusted/`). |
| **Proof theory** (and planned **correspondence proofs**) | `theory/` (and planned `correspondence/`) | Defines the normalized `StableAst`, proves lowering passes (`Abstracts`), provides WP calculi, separation logic, and proof tactics invoked by generated proof scripts (`theory/`), and—in planned Pass 2—proves the MIR correspondence theorems and canaries (`correspondence/`, CI-only and never shipped in the user toolchain archive). | **Outside the TCB.** Treated as potentially adversarial; audited mechanically in Anneal's CI via syntactic preflight and Lean 4 kernel replay. |
| **Vendored reference model** *(planned Pass 2)* | `vendor/lean-miri/` *(planned)* | Pinned snapshot of `proofs-rs/lean-miri` (plus any human-audited local delta) serving as the MIR correspondence reference model in repository CI. Never shipped in the user toolchain archive. | **In the correspondence TCB (Pass 2).** Exempt from `theory/` syntactic preflight because upstream contains compile-time metaprograms and `partial` definitions; admitted by content-addressed SHA-256 pin, human semantic and compile-time review of upstream pin diffs and local patches, standalone kernel replay of non-`partial` declarations, and cone-purity checks. |

### How CI auditing and user-machine verification fit together

A key design question is how Anneal guarantees soundness without requiring a
human to audit `theory/` and without running a heavy repository auditor on
every user's machine.

Anneal splits the enforcement across **Anneal's repository CI** and **the
user's machine**:

```mermaid
flowchart TD
    subgraph RepoCI ["In Anneal's Repository CI (before shipping)"]
        THEORY["Untrusted theory/ (.lean) & trusted/lean/"] --> AUDIT["anneal-audit (trusted/audit/)\nEnforces pure, effect-free, axiom-free theory/\nand vetted vs. candidate:<feature> module-tier separation"]
        AUDIT --> ARCHIVE["Packaged Anneal Toolchain Archive"]
    end

    subgraph UserMachine ["On a User's Machine (cargo anneal)"]
        CRATE["Target Rust Crate + inline annotations"] --> CAPTURE["trusted/rustc-capture/ (TCB)\nGenerates Mir.lean (Mir.crate : Trusted.Crate)\nand pure Proof.lean (Proof.verify_crate : Trusted.CrateTheorem Mir.crate)"]
        CAPTURE --> KERNEL["Lean 4 Kernel\nChecks Proof.verify_crate against Trusted.CrateTheorem Mir.crate\nusing CI-audited theory/"]
        ARCHIVE --> CAPTURE & KERNEL
    end
```

1. **On the user's machine (`trusted/rustc-capture/` + Lean 4 kernel):**
   - Users do not write raw Lean files that could spoof the theorem statement or
     introduce `sorry`. Instead, users annotate their Rust source code, and
     `trusted/rustc-capture/` (which is part of the human-audited TCB)
     deterministically generates both `Mir.lean` (defining
     `Mir.crate : Trusted.Crate`) and `Proof.lean` (a pure proof script that
     states `theorem Proof.verify_crate : Trusted.CrateTheorem Mir.crate` and
     calls into `theory/` to prove it).
   - Because `trusted/rustc-capture/` generates `Mir.lean` and `Proof.lean`
     directly, the theorem *statement* (`ConstantInfo.type`) is guaranteed to
     be `Trusted.CrateTheorem Mir.crate` over the extracted crate, and
     `Proof.lean` is guaranteed to contain no axioms or effectful code.
   - The Lean 4 kernel on the user's machine then typechecks `Proof.lean`,
     verifying that the proof term (`ConstantInfo.value?`) constructed by
     `theory/` is a valid proof of `Trusted.CrateTheorem Mir.crate`.
2. **In Anneal's repository CI (`trusted/audit/`):**
   - For the Lean 4 kernel check on the user's machine to be sufficient, the
     `theory/` library shipped with Anneal must not be able to cheat the kernel
     or subvert the host process when `lean` imports and elaborates `theory/`.
   - In raw Lean 4, an unrestricted `.lean` file in `theory/` could execute
     arbitrary OS and filesystem operations during elaboration (`#eval`,
     `run_cmd`, `initialize`), attach compiler overrides (`@[implemented_by]`,
     `@[extern]`, `@[csimp]`), introduce custom `axiom`s or `sorryAx`, or
     inject spoofed definitions into the `Trusted` namespace. Similarly, a Rust
     crate outside `trusted/` could run arbitrary code via `build.rs` or
     procedural macros.
   - Therefore, **Anneal's CI runs `anneal-audit` (`trusted/audit/`)** on the
     Anneal repository before any commit can merge or be packaged into the
     toolchain archive. `anneal-audit` does **not** run on a user's machine; its
     job is to verify in CI that all first-party Lean code outside `trusted/`
     (`theory/`, and planned Pass 2 `correspondence/`) is pure, effect-free, and
     within the locked foundation axiom allowlist (and that no Rust crate
     resides outside `trusted/`). In planned Pass 2, vendored reference-model
     sources under `vendor/lean-miri/` are never packaged into the user
     toolchain archive and are admitted by content-addressed SHA-256 pinning,
     human semantic and compile-time review of upstream pin diffs and local
     patches, standalone kernel replay, cone-purity enforcement, and
     archive-bound correspondence provenance verification rather than `theory/`
     syntactic preflight.

### Statement-Origin Separation (`ConstantInfo.type` vs. `ConstantInfo.value?`)

Within the Lean 4 kernel environment, every compiled theorem
(`ConstantInfo.thmInfo`) has two distinct components:

- **The theorem statement (`ConstantInfo.type`):** The proposition claiming
  *what* holds.
- **The proof term (`ConstantInfo.value?`):** The lambda term explaining *why*
  that proposition holds.

Anneal's architecture enforces **Statement-Origin Separation** between the two:

- Every constant referenced in the *statement* (`ConstantInfo.type`) of
  `Trusted.CrateTheorem Mir.crate` originates in `Trusted.*` (or the allowlisted
  Lean `Init.*` foundation) and the generated `Mir.crate`. No definition from
  `theory/` ever appears in the theorem statement.
- Declarations from `theory/` appear only inside the *proof term*
  (`ConstantInfo.value?`). Because `anneal-audit` verifies in CI that `theory/`
  is pure, effect-free, and free of custom axioms, and the Lean 4 kernel checks
  that `ConstantInfo.value?` inhabits `ConstantInfo.type`, `theory/` can supply
  arbitrarily rich lowering passes and tactics without being able to weaken the
  theorem statement.

### Staging TCB changes (`vetted` vs. `candidate:<feature>` modules)

Auditing a new semantic rule in `trusted/lean/` to full TCB standards—including
line-by-line Rust Reference citations and human review—takes deliberate effort.
If `trusted/lean/` treated all merged code as equally trusted, contributors
would face an unproductive tradeoff when adding support for a new Rust feature:

- **Block downstream work:** Hold back the `trusted/lean/` definitions until
  full human auditing is complete, blocking contributors and agents from
  building the corresponding lowering passes and WP lemmas in `theory/` or
  testing the feature on real crates; or
- **Dilute the TCB guarantee:** Merge unreviewed definitions into
  `trusted/lean/` immediately, making it impossible to tell whether a
  verification result depends only on audited rules or also on work-in-progress
  semantics.

Anneal resolves this by assigning every module in `trusted/lean/` an explicit
module-level trust tier via a leading header comment directive:

- **`-- anneal-trust-tier: vetted`:** Modules whose definitions have completed
  full Rust Reference auditing.
- **`-- anneal-trust-tier: candidate:<feature>`:** Work-in-progress TCB modules
  belonging to a named subsystem feature `<feature>` (such as `refinement`,
  `step_result`, `memory`, `mir_ast`, `mir_semantics`, or `rustc_capture`) that
  have not yet completed human auditing.

Assigning trust tiers at the module boundary rather than via per-declaration
attributes keeps `trusted/lean/` completely free of custom attribute macros or
metaprogramming: every constant compiled into a `Trusted` module's `.olean`
file—including constructors, recursors (`rec`, `casesOn`), pattern matchers
(`match_1`), equational lemmas (`eq_1`), and `where`/`private` helpers—
automatically inherits its defining module's trust tier via
`Environment.getModuleIdxFor?`.

To prevent unreviewed candidate modules from contaminating audited definitions,
`TrustedBoundary.lean` enforces a strict one-way dependency rule across all
compiled constants: constants in a `vetted` module may reference only the
locked `Init.*` foundation and other `vetted` modules, never a
`candidate:<feature>` module.

## 2. Repository CI boundary enforcement (`anneal-audit`)

[`trusted/audit/`](../trusted/audit) implements the CI gatekeeper
(`anneal-audit` and
[`TrustedBoundary.lean`](../trusted/audit/TrustedBoundary.lean)) that audits
the Anneal repository. For Pass 1 (`trusted/lean/` and `theory/`), it
classifies every module into a single `ModuleRole` (`.foundation`,
`.trusted .vetted`, `.trusted (.candidate f)`, or `.theory`) and enforces five
invariants across two phases over an isolated staging directory; planned Pass 2
extends `anneal-audit` with the correspondence audit controls summarized below.

### Cargo workspace containment

Before inspecting Lean files, `anneal-audit` verifies the repository's root
manifests against [`root-manifest.sha256`](../trusted/root-manifest.sha256)
(`trusted/root-manifest.sha256`) and checks that every Cargo workspace member
and `path` dependency resides under `trusted/`. Because Rust code (including
`build.rs` scripts and proc-macros) is effectful and not checked by the Lean
kernel, no Rust crate is permitted outside `trusted/`.

### Phase 1: Syntactic source preflight (`--mode preflight`)

Before compiling any `.lean` file in `trusted/lean/` or `theory/`,
`anneal-audit` stages the source files into a private temporary directory,
verifies that no pre-existing `.olean` or `.ir` files exist in the source tree,
and parses every file using `Parser.parseHeader` and `Parser.parseCommand`
against the locked `Init.*` foundation parser environment (without invoking
Lean's Turing-complete elaborator). Rather than relying on an open-ended
blocklist of dangerous Lean features, `TrustedBoundary.lean` classifies each
source file into a `SourceRole` (`trusted (tier : TrustTier)` vs. `theory`) and
validates the module header and every top-level command in a single top-down
traversal (`inspectSyntax` and `inspectNodeKind`) against a closed, role-aware
`SyntaxNodeKind` allowlist:

- **`SourceRole.trusted` (`trusted/lean/`):** Restricted to
  `allowedTrustedSyntaxKinds`—pure declarations, types, and term-mode proofs
  only, excluding `byTactic` and all tactic syntax so TCB specifications remain
  direct, tactic-free definitions—and required to carry exactly one valid
  `-- anneal-trust-tier: vetted` or `-- anneal-trust-tier: candidate:<feature>`
  directive.
- **`SourceRole.theory` (`theory/`):** Restricted to
  `allowedTheorySyntaxKinds`, which extends `allowedTrustedSyntaxKinds` with a
  closed allowlist of pure proof tactics (`allowedTheoryTacticKinds`) while
  rejecting trust-tier directives and any unallowlisted syntax node, command,
  modifier, attribute, or tactic configuration (excluding `unsafe`, `partial`,
  `noncomputable section`, `meta`, `axiom`, `macro`, `syntax`, `elab`, `sorry`,
  `native_decide`, `decide!`, `bv_decide`, `rfl'`, `grind`, tactic `configItem`
  flags such as `+native` and `+kernel`, `by_elab`, `run_tac`, `#eval`,
  `include_str`, `set_option`, `@[implemented_by]`, `@[extern]`, `@[csimp]`,
  and `initialize` hooks).

### Phase 2: Standalone kernel replay and DAG audit (`--mode audit`)

After compiling the staged `.lean` modules synchronously with kernel checking
enabled (`-t0 -DElab.async=false -Ddebug.skipKernelTC=false`), `anneal-audit`
loads the resulting `.olean` files with `trustLevel := 0`, `plugins := #[]`,
and `loadExts := false` (so no `[init]` initializers or persistent environment
extensions from audited modules are deserialized or executed) and performs a
full kernel-level audit:

1. **Module, namespace, and axiom verification (`verifyAndCollectLocals`):**
   Verifies that only allowlisted modules are loaded; that every constant's
   recorded module origin (`env.getModuleIdxFor?`) matches its module's
   `ModuleRole`; that non-`Trusted` modules declare no constants in the
   `Trusted` root namespace (`(privateToUserName ci.name).getRoot == `Trusted`)
   and no `opaque` definitions; that no non-foundation declaration in
   `Trusted.*` or `theory/` is `unsafe`, `partial`, an `axiom`, or a quotient
   primitive (`.quotInfo`); and that the transitive dependency closure reaches
   only the locked foundation axiom allowlist
   (`{Classical.choice, Quot.sound, propext}`).
2. **Origin and trust-tier separation (`checkTierReferences`):** Traverses
   every kernel dependency edge `c → dep` (`declarationEdges`) across all
   `Trusted.*` constants and enforces two rules:
   - **Origin rule:** A `.trusted _` constant may reference only `.foundation`
     or `.trusted _` constants (never `.theory`).
   - **Vetted rule:** A `.trusted .vetted` constant may reference only
     `.foundation` or `.trusted .vetted` constants (never
     `.trusted (.candidate _)`).
3. **Fresh kernel replay (`base.toKernelEnv.replay locals`):** Finally,
   `TrustedBoundary.lean` constructs a clean kernel environment containing only
   the pinned `Init.*` foundation (`base`) and replays every non-foundation
   constant (`Trusted.*` and `theory/`) through the standalone Lean 4 kernel
   typechecker from scratch.

### Planned Pass 2: MIR correspondence audit (`vendor/lean-miri/` and `correspondence/`)

To mechanically anchor `Trusted.MirSemantics` against an independent reference
model without expanding the user-machine TCB or weakening Pass 1's pure
`theory/` gate, Anneal's planned Pass 2 extends `anneal-audit` in repository CI
with a separate correspondence audit pass (detailed in
[`docs/architecture.md`](architecture.md)). Neither `vendor/lean-miri/`,
`trusted/correspondence/`, nor `correspondence/` is ever packaged into the user
toolchain archive. Pass 2 enforces five controls:

1. **Content-addressed vendor pinning, semantic diff review, and
   source-to-`.olean` provenance binding:** `vendor/lean-miri/UPSTREAM_PIN.json`
   (recording upstream commit pins and per-file SHA-256 digests, plus any
   human-audited local patch allowlist) is locked by SHA-256 inside
   `trusted/audit/`, alongside authenticated Lean sysroot (`Init`/`Std`/`Lean`)
   `.olean` digests. Because vendored `lean-miri` contains compile-time
   metaprograms (`run_cmd`, `initialize`, custom tactic `elab`s) and `partial`
   definitions, it is admitted by cryptographic pin and human review rather than
   `theory/` syntactic preflight. Every `vendor/lean-miri/` pin update must
   expose and receive human semantic review of the resolved old-to-new
   reference-model diff—not only compile-time metaprograms and local patches—so
   pure, well-typed upstream semantic regressions (such as removed UB checks or
   miscomputed operations) cannot pass silently through hash checks and kernel
   replay. On `merge_group`, `push` to `main`, `workflow_dispatch`, and any
   `UPSTREAM_PIN.json` or `lean-toolchain` change, CI compiles the pinned
   `vendor/lean-miri/` slice cold from source with no external `.olean` cache.
   Because candidate vendor code contains compile-time metaprograms (`run_cmd`,
   `initialize`, custom `elab`s) that execute during Lean elaboration before
   merge, cold compilation of candidate `vendor/lean-miri/` sources—as well as
   any Pass 2 preflight or build step that executes vendored metaprograms—must
   run inside an OS-level isolated sandbox with no credentials or writable
   access to the repository worktree, home directory, or auditor state
   (restricting writes strictly to an isolated build output directory, after
   which the outer auditor checks `.olean` SHA-256 digests and runs standalone
   kernel replay in a separate `loadExts := false` process). Regular PR runs on
   unchanged pins may reuse a digest-gated `.olean` cache outside the checkout
   only when exact source-pin and toolchain digests match and every restored
   `.olean` sidecar passes SHA-256 verification.
2. **Pass 2 syntactic preflight and isolation:** Before compiling
   `trusted/correspondence/` or `correspondence/`, `anneal-audit` runs
   syntactic preflight on both first-party directories—requiring
   `trusted/correspondence/` to follow trusted declaration rules and restricting
   `correspondence/` to pure, effect-free proof syntax while preventing
   untrusted declarations from injecting into `Trusted.*` or `Miri.*` or
   importing scoped metaprogramming extensions.
3. **Standalone vendor and correspondence kernel replay plus cone purity:** On
   every run (cold build and warm cache hit alike), `TrustedBoundary.lean` loads
   the verified `.olean` environment with `trustLevel := 0`, `plugins := #[]`,
   and `loadExts := false`, validates module origins and declaration edges,
   rejects `axiom`, `unsafe`, quotient primitives, `sorryAx`, and
   compiler-reflection primitives (`Lean.ofReduceBool`, `Lean.ofReduceNat`,
   `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`), and replays every
   non-`isPartial` vendored declaration followed by `trusted/correspondence/`
   and `correspondence/` from scratch through the standalone Lean 4 kernel
   (`toKernelEnv.replay`) onto an authenticated sysroot base. This closes both
   warm-cache kernel trust assumptions and scoped
   `set_option debug.skipKernelTC true` bypasses. `TrustedBoundary.lean` also
   verifies that the reference-evaluator and correspondence dependency cones
   contain no reachable `unsafe`, `partial`, vendored `opaque`, or unapproved
   axioms.
4. **Correspondence witness locks and evaluator independence:** `anneal-audit`
   mechanically verifies that every required correspondence, fault-equivalence,
   wiring, and canary claim in `trusted/correspondence/` is inhabited by a
   universe-monomorphic theorem in `correspondence/` with the exact expected
   kernel type and required constants. To prevent a shared helper bug or
   narrowing from making both models silently agree on `unsupported`,
   `anneal-audit` checks that the reference evaluator and staged support gate
   depend on the expected `Miri.*` primitives and rejects dependencies from
   them into the entire Anneal execution and support-rule cone (permitting only
   explicitly allowlisted shared boundary data types such as AST, value, query,
   and behavior types).
5. **Archive-embedded correspondence provenance and fail-closed digest
   verification:** To uphold [`THREAT_MODEL.md`](../THREAT_MODEL.md)'s bounded
   human-review guarantee without shipping `vendor/lean-miri/` or
   `correspondence/` in user toolchain archives, every packaged user toolchain
   archive and `cargo-anneal` bundle embeds a compact, CI-checked, digest-bound
   **correspondence provenance record** (pinned Anneal revision,
   `trusted/lean/` source and `.olean` digests, `vendor/lean-miri/` upstream
   commit, `UPSTREAM_PIN.json` SHA-256, `patched_files` allowlist and digests,
   `Trusted/Correspondence.lean` digest, and Pass 2 attestation metadata).
   Archive construction and `cargo anneal verify` must hash the actual packaged
   `trusted/lean/` artifacts and fail closed unless those computed digests
   exactly match the attested provenance record (as well as failing closed if
   the embedded provenance is missing or malformed), and `cargo anneal verify`
   surfaces the verified provenance record in every verification result's TCB
   audit log so an auditor inspecting only stated specifications and the TCB
   audit log can identify and audit every certifying Pass 2 artifact.

Introducing `vendor/lean-miri/` and `correspondence/` into the repository—and
treating Pass 2 correspondence certification as a substitute for human semantic
audit of `initState` and `evalStep` inside `trusted/lean/` (which otherwise
remains governed by standard `trusted/lean/` semantic-review rules)—requires
updating `AGENTS.md`, `.gemini/styleguide.md`, and
`skills/trust-review/SKILL.md` in lockstep with `trusted/audit/` so code-review
and TCB rules reflect both the active Pass 2 roots and the exact boundary
between human-audited definitions and Pass 2-certified step rules.

### Including external files in the `trusted/` boundary via hashes

The invariant of [`trusted/`](../trusted) is that an auditor only needs to
inspect `trusted/` to verify that Anneal upholds
[`META_PRINCIPLES.md`](../META_PRINCIPLES.md),
[`PRINCIPLES.md`](../PRINCIPLES.md), and
[`THREAT_MODEL.md`](../THREAT_MODEL.md). However, some files that belong to the
effective TCB cannot practically reside inside the `trusted/` subdirectory:

- Standard tooling expects workspace and environment manifests (`Cargo.toml`,
  `Cargo.lock`, `flake.nix`, and `flake.lock`) to sit at the repository root;
  moving them into `trusted/` would require symlinks or custom wrapper flags
  for every Cargo and Nix command.
- Pre-built upstream toolchain artifacts (the `lean` binary and its `Init.*`
  standard prelude) live outside the repository altogether.

To include these files in `trusted/`'s effective TCB without relocating them,
`trusted/` stores their SHA-256 digests in two checked-in lock files:

- **[`trusted/root-manifest.sha256`](../trusted/root-manifest.sha256):** Pins
  the SHA-256 digests of the repository's root build files (`Cargo.toml`,
  `Cargo.lock`, `flake.nix`, and `flake.lock`), verified by CI and
  `anneal-audit`.
- **[`foundation-lock.json`](../trusted/lean/foundation-lock.json)**
  (`trusted/lean/foundation-lock.json`): Pins the SHA-256 digests of the `lean`
  executable and all `Init.*` prelude source and `.olean` companion files,
  verified by both the Nix toolchain build (`flake.nix`) and `anneal-audit`.
- **Planned `vendor/lean-miri/UPSTREAM_PIN.json` lock:** When Pass 2 lands,
  `trusted/audit/` will likewise lock the SHA-256 digest of
  `vendor/lean-miri/UPSTREAM_PIN.json` (and any allowlisted local patch hashes),
  so any change to the vendored reference model requires a reviewable diff
  inside `trusted/`.

Because CI and `anneal-audit` reject any mismatch against these files, changing
a root manifest or toolchain artifact requires a corresponding diff inside
`trusted/`, ensuring an auditor inspecting `trusted/` sees every change to the
effective TCB.

## 3. External dependencies and commenting in `trusted/`

Because every file in [`trusted/`](../trusted) must be auditable by humans,
Anneal optimizes `trusted/` for **human comprehension and review accuracy**, not
merely minimum dependency count:

- **Standard libraries over hand-rolled plumbing:** `trusted/` uses widely
  audited Rust ecosystem crates (such as `serde`, `clap`, and `sha2`, all
  pinned with SHA-256 checksums in `Cargo.lock`) for generic utilities like
  serialization, CLI parsing, and hashing. Hand-rolling bespoke parsers or
  cryptographic primitives inside `trusted/` would add hundreds of lines of
  security-critical code and increase audit burden.
- **Mandatory provenance citations:** Any code in `trusted/` that models Rust
  semantics or extracts `rustc` internal structures must explain the
  correspondence in its comments and both quote and cite the relevant Rust
  Reference section (`rust-lang/reference`) or compiler source file
  (`rust-lang/rust`) at a pinned commit hash.
