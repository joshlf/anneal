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

This document defines what Anneal does and does not aim to defend against so
that promise holds. For how Anneal's architecture implements these defenses, see
[`docs/trust-model.md`](docs/trust-model.md).

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

Anneal's threat model therefore assumes that repository changes may be authored
by adversarial humans or reward-hacking AI coding agents rather than assuming
good-faith inputs.

## 2. Compromised execution environments and the dev vs. CI boundary

The overarching threat that Anneal **does not** aim to defend against is a
**compromised execution environment**: an environment in which an untrusted
human or agent can modify or interpose on `cargo-anneal`, its binary
dependencies (`cargo`, `rustc`, `lean`, or pre-compiled toolchain files), its
environment variables (`PATH`, `LD_PRELOAD`), its working files during
verification, or the channel reporting the verification result and TCB audit
log.

**There is no in-principle way for a user-space tool to defend against a
compromised execution environment.** If an agent running under the same OS user
account as `cargo-anneal` has write access to the user's binaries or shell
environment, it does not need to find a soundness bug in Anneal or the Lean 4
kernel: it can replace `cargo-anneal` (or `lean`) with a script that prints a
clean TCB audit log and exits `0`. In-process checks inside `cargo-anneal`
cannot defend against an actor who can modify the binary performing those
checks.

**Anneal's threat model therefore assumes an uncompromised execution
environment:** the operating system, filesystem, environment, and installed
Anneal toolchain binaries are intact and outside the untrusted actor's write or
process-control access when verification runs.

This assumption naturally aligns with the standard split between **local
development environments** and **Continuous Integration (CI)**:

- **Local development machines (outside the threat model when shared with an
  un-sandboxed agent):** When a developer runs an un-sandboxed AI agent under
  their own user account on a laptop or workstation, the execution environment
  is potentially compromised. Running `cargo anneal` locally remains useful as a
  fast feedback loop for catching ordinary mistakes and naive agent shortcuts,
  but a local pass is not a security guarantee. (A local run satisfies the
  threat model only when the agent is confined inside a separate OS sandbox,
  container, or VM while `cargo-anneal` runs outside that sandbox.)
- **Well-configured CI (within the threat model):** In CI, an untrusted
  contributor or AI agent cannot touch the runner's binaries or environment
  directly; their only interface is **proposing changes to repository files in a
  pull request**. Because software projects already rely on CI and human code
  review to gate merges to `main`, running `cargo anneal` in an isolated CI
  environment with protected workflow configurations and a pinned Anneal
  toolchain satisfies the non-compromised execution environment assumption.

## 3. In-scope threats from untrusted repository contents

Assuming an initially uncompromised execution environment (such as a clean CI
runner) does *not* mean Anneal trusts the contents of the repository checkout
being verified. In a pull request, the repository files (`Cargo.toml`,
`build.rs`, procedural macros, Rust source code, and Lean specification and
proof files) are controlled by the untrusted human or agent.

Anneal's threat model treats **all files in the repository checkout as
untrusted** and aims to defend against three categories of repository-borne
threats:

### 1. Compromising the execution environment from within the repository

Even when verification starts in a clean CI environment, building a Rust crate
or elaborating a Lean file can trigger arbitrary host code execution or compiler
redirection from files inside the repository:

- **Rust `build.rs` scripts and procedural macros:** Cargo compiles and runs
  `build.rs` build scripts and procedural macros on the host during compilation.
  An adversarial pull request can add or modify a `build.rs` script or
  procedural macro to tamper with the runner, overwrite files, or inject
  compiler flags.
- **Lean metaprogramming, I/O, and FFI directives:** Lean 4 is a general-purpose
  programming language whose elaborator can run arbitrary host commands and I/O
  (`#eval`, `run_cmd`, `by_elab`, `initialize`) or link external native symbols
  (`@[extern]`, `@[implemented_by]`, `@[csimp]`).
- **Repository configuration and path overrides:** Repository files such as
  `.cargo/config.toml`, `rust-toolchain.toml`, symlinks, out-of-tree `include!`
  paths, or pre-compiled `.olean` binaries can redirect `cargo`, `rustc`, or
  `lean` to attacker-controlled code or flags.

Anneal aims to prevent untrusted repository files from executing unapproved code
or overriding toolchain behavior during verification, while surfacing any
project-required `build.rs` scripts or procedural macros in the TCB audit log
for human review before they are allowed to run.

### 2. Subverting the proof without proving the theorem

Without compromising the host environment, an adversarial proof in the crate (or
in Anneal's own proof-automation library) can try to make Lean accept a false
claim by introducing unsound axioms or partial/unsafe definitions (`sorry`,
`axiom`, `opaque`, `partial`, `unsafe`), invoking unverified native evaluation
(`native_decide`), or proving a weakened theorem statement instead of the one
corresponding to the crate's Rust code and specifications.

Anneal aims to prevent any untrusted proof from altering the theorem statement
or causing a false claim to pass, so that **proof files never need to be trusted
or reviewed by humans**.

### 3. Silently weakening specifications or expanding assumptions

Even when the execution environment is clean and the proof is mathematically
sound, a reward-hacking agent can make verification pass by proving a weaker or
narrower claim than a human reviewer expects—for example, by:

- Weakening a postcondition (`ensures(true)`) or data-structure invariant;
- Shrinking the verified input domain via a contradictory or over-constrained
  precondition (`requires(false)` or `requires(len == 0)`);
- Modifying a reference Rust function or helper used by a specification; or
- Adding explicit trust waivers (`#[anneal::trusted]`), leaving functions
  unverified (including unverified functions in the same module that can break a
  private type invariant, or waivers hidden in upstream workspace dependencies),
  or placing undefined behavior inside uncalled link-level hooks
  (`#[no_mangle]`, `#[global_allocator]`, `static mut`).

Because only a human can judge whether a specification or assumption matches the
project's intent, Anneal aims to reject contradictory preconditions
automatically and to surface **every** specification, assumption, waiver,
unverified item, and build hook in the TCB audit log—without noise from ordinary
implementation or proof edits—so human reviewers in CI can audit any change to
*what* is proved or trusted.
