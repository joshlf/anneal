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

This document defines the threat model under which that promise holds. For how
Anneal's internal codebase (`trusted/` and `trusted/audit/`) implements these
defenses, see [`docs/trust-model.md`](docs/trust-model.md).

## 1. Background: adversarial humans and reward-hacking agents

Unlike testing, which checks that a program behaves as expected on specific
inputs, formal verification claims that a mathematical proof establishes
correctness for *all* valid inputs. Because writing specifications and machine-
checked proofs requires significant effort, projects increasingly rely on
external contributors and AI coding agents to write Rust code, specifications,
proof automation, and crate-specific Lean 4 proofs.

An honest developer uses `cargo anneal` to find genuine bugs in their code or
proofs. By contrast, a malicious contributor—or a reward-hacking AI coding agent
optimizing to make `cargo anneal` exit `0`—has an incentive to make verification
succeed *without* proving the intended property of the Rust code:

- An agent stuck on a difficult proof may try to sneak `sorry`, a custom
  `axiom`, or a compiler override (`@[implemented_by]`, `@[extern]`) into a Lean
  proof file.
- An agent unable to prove a function's specification may weaken the
  postcondition (`ensures(true)`), add a contradictory precondition
  (`requires(false)`), or mark the function `#[anneal::trusted]`.
- An agent running on a developer's machine may bypass verification altogether
  by modifying or shadowing the `cargo-anneal` binary or its toolchain
  dependencies so the command exits `0` unconditionally.

A sound verification workflow must account for adversarial humans and
reward-hacking agents rather than assuming that all inputs to Anneal are
written in good faith.

## 2. Compromised execution environments and the dev vs. CI boundary

The most direct threat to [`PRINCIPLES.md`](PRINCIPLES.md)'s promise is a
**compromised execution environment**: an environment in which an untrusted
human or agent can modify or interpose on `cargo-anneal`, its binary
dependencies (`cargo`, `rustc`, `lean`, or pre-compiled `.olean` toolchain
files), its environment variables (`PATH`, `LD_PRELOAD`), its working files
during verification, or the channel reporting the verification result and TCB
audit log.

**There is no in-principle way for a user-space tool to defend against a
compromised execution environment.** If an agent running under the same OS user
account as `cargo-anneal` has write access to the user's binaries or shell
environment, it does not need to find a soundness bug in Anneal or the Lean 4
kernel: it can replace `cargo-anneal` (or `lean`) with a script that prints a
clean TCB audit log and exits `0`. Adding in-process file-descriptor or
binary-hashing checks inside `cargo-anneal` cannot close this hole when the
binary performing those checks can itself be modified.

**Anneal's threat model therefore assumes an uncompromised execution
environment:** the operating system, filesystem, environment, and installed
Anneal toolchain binaries are intact and outside the untrusted actor's write or
process-control access.

This assumption naturally aligns with the standard split between **local
development environments** and **Continuous Integration (CI)**:

- **Local development machines (advisory convenience loop):** When a developer
  runs an un-sandboxed AI agent under their own user account on a laptop or
  workstation, the execution environment is potentially compromised. Running
  `cargo anneal` locally is still useful as a fast feedback loop for catching
  ordinary mistakes and naive agent shortcuts, but a local pass is not by itself
  a security guarantee. (A local run is authoritative against an agent only when
  the agent is confined inside a separate OS sandbox, container, or VM while
  `cargo-anneal` runs outside that sandbox.)
- **Well-configured CI (authoritative verification gate):** In CI, an untrusted
  contributor or AI agent cannot touch the runner's binaries or environment
  directly; their only interface is **proposing changes to repository files in a
  pull request**. Because software projects already rely on CI and human code
  review to gate merges to `main`, running `cargo anneal` in an isolated CI
  environment with protected workflow configurations and a pinned Anneal
  toolchain satisfies the non-compromised execution environment assumption.

## 3. In-scope threats from untrusted repository contents

Assuming an initially uncompromised CI runner does *not* mean Anneal can trust
the contents of the repository checkout being verified. In a pull request, the
repository files (`Cargo.toml`, `build.rs`, procedural macros, Rust source code,
and Lean specification and proof files) are authored by the untrusted human or
agent.

Under Anneal's threat model, an adversarial change to the repository checkout
can attack verification in three ways—all three of which **are in scope**:

### 1. Compromising the execution environment from within the repository

Even when CI starts in a clean environment, compiling a Rust crate or
elaborating a Lean file can execute code from the repository under the CI
runner's user account:

- **Rust `build.rs` scripts and procedural macros:** Cargo compiles and runs
  `build.rs` scripts and procedural macros on the host during compilation. An
  adversarial pull request could add or modify a `build.rs` script or procedural
  macro to overwrite files, tamper with the runner, or inject `cargo:rustc-*`
  compiler flags.
- **Lean metaprogramming and FFI directives:** Lean 4 is a general-purpose
  programming language whose elaborator can run arbitrary host commands and I/O
  (`#eval`, `run_cmd`, `by_elab`, `initialize`) or link external native symbols
  (`@[extern]`, `@[implemented_by]`, `@[csimp]`).
- **Repository configuration and path overrides:** Repository files such as
  `.cargo/config.toml`, `rust-toolchain.toml`, symlinks, `include!` macros
  pointing outside the crate, or pre-compiled `.olean` binaries could redirect
  `cargo`, `rustc`, or `lean` to attacker-controlled code or flags.

**How Anneal defends against this:** Before invoking Cargo or `rustc`,
`cargo-anneal` stages repository inputs in a private directory, scrubs ambient
environment variables, rejects symlinks, pre-compiled `.olean` files, and
repo-local Cargo/toolchain configuration files, and resolves the package graph
via `cargo metadata --locked` (which does not execute build scripts or macros).
In CI (`--locked`), `cargo-anneal` hashes every `build.rs` script and
non-built-in procedural macro (along with its transitive host dependencies) and
verifies them against the committed TCB audit log **before** compiling or
executing them—aborting prior to execution if any unapproved build hook is
present. Likewise, Anneal's syntactic preflight rejects all Lean
metaprogramming, I/O, and FFI directives before `lean` elaborates any file.

### 2. Subverting the proof without proving the theorem

Without compromising the host OS, an adversarial proof script in `Proof/*.lean`
(or in Anneal's own `theory/` library) can try to make Lean accept a false claim
by declaring custom `axiom`s, `sorry`, `opaque`, `partial`, or `unsafe`
definitions, invoking native evaluation (`native_decide`), or proving a weakened
theorem statement instead of the theorem Anneal generated for the crate.

**How Anneal defends against this:** Anneal separates **specification modules**
(which define *what* theorem is claimed) from **proof modules** (`Proof/*.lean`
and `theory/`, which prove *why* it holds). Anneal generates the root proof
entrypoint (`Proof.lean`) pinning the exact theorem statement
(`Trusted.CrateTheorem Mir.crate`), enforces a one-way dependency boundary so
specifications can never depend on proof modules, mechanically audits proof
modules for axiom and side-effect freedom, and replays the compiled proof in the
standalone Lean 4 kernel (`trustLevel := 0`). Because a buggy or adversarial
proof module can cause verification to fail but can never cause a false theorem
statement to pass, **proof files (`Proof/*.lean` and `theory/`) sit outside the
TCB and require zero human review**.

### 3. Silently weakening the specification or expanding assumptions

Even when the execution environment is clean and the Lean proof is sound, a
reward-hacking agent can make verification pass by proving a weaker or narrower
claim than the human reviewer intended:

- Weakening a postcondition (`ensures(true)`) or invariant;
- Shrinking the verified input domain via a contradictory or over-constrained
  precondition (`requires(false)` or `requires(len == 0)`);
- Modifying a reference Rust function (`spec_fn`) or one of its transitive
  helper functions in a relational equivalence specification;
- Adding `#[anneal::trusted]` waivers, leaving functions unverified (especially
  functions in the same module that can mutate private fields of a type with an
  `#[anneal::invariant]`), or placing undefined behavior inside uncalled
  link-level hooks (`#[no_mangle]`, `#[global_allocator]`, `static mut`).

**How Anneal defends against this:** Anneal enforces automatic existential
non-vacuity checks (so contradictory preconditions fail verification outright)
and records every item that affects *what* is proved or trusted in the crate's
committed **TCB audit log (`anneal-tcb.lock`)**:

1. Approved `build.rs` and procedural-macro hooks (`build_hooks`), target
   configuration, and active work-in-progress TCB features
   (`candidate:<feature>`);
2. Every verified function's preconditions (`requires`), postconditions
   (`ensures`), compile-time constant assumptions (`required_consts`), pure
   mathematical specification models (`Spec/*.lean`), and reference `spec_fn`
   closures (including their transitive callees); and
3. Every explicit waiver (`#[anneal::trusted]`), unverified function in the
   crate (including unverified functions inside private-invariant visibility
   scopes), and uncalled link-level or `static mut` item (`ambient_items`).

To prevent review fatigue, `anneal-tcb.lock` omits volatile implementation
details such as function body hashes and source line numbers: **editing a
verified function's implementation or rewriting `Proof/*.lean` produces zero
diff in `anneal-tcb.lock`.** In CI (`cargo anneal verify --locked`), any
uncommitted change to `anneal-tcb.lock` fails the build, focusing human code
review strictly on changes to specifications, assumptions, and build hooks.
