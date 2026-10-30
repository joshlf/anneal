# Agentic proof construction workflow and anti-cheating safeguards

Anneal supports autonomous proof construction by AI coding agents while
guaranteeing that an agent can satisfy a verification task only by supplying a
kernel-checked Lean 4 proof of the locked specification. This document describes
the threat model for autonomous proof authoring, the four-layer defense-in-depth
architecture that enforces the boundary, and the `cargo anneal` CLI workflow
used with the portable [`anneal-prove` skill](../skills/anneal-prove/SKILL.md)
and [`anneal-lsp` skill](../skills/anneal-lsp/SKILL.md). For configuring MCP
servers, `PreToolUse`/`PostToolUse` hooks, and OS-level `bwrap` sandboxes, see
[**Agent harness setup and anti-cheating configuration**](agent-harness-setup.md).
For adopting Anneal in a Rust project and reviewing verification pull requests,
see the [**Project owner guide**](project-owner-guide.md).

## Threat model: four cheating vectors in autonomous proof authoring

When an unconstrained coding agent is asked to make a formal verification build
succeed, optimizing for a zero exit code creates four classes of specification
or soundness bypasses:

1. **Proof-term shortcuts (`sorry`, `admit`, or rogue `axiom` declarations).**
   The agent leaves a hole in `anneal/proofs/Proof/<Crate>/<Item>.lean` or
   postulates an unsound helper axiom so `lake build` succeeds without proving
   the obligation.
2. **Specification-override injection (`Specs/<Crate>/<Item>.lean`).**
   Anneal's pure generated-assembly design emits a `priority := low`
   `defaultSpec : ItemSpec "<def_id>"` instance in
   `.anneal/generated/Obligations/<Crate>/<Item>.lean` and allows human
   verifiers to override that contract by placing a normal-priority `ItemSpec`
   or `StatefulItemSpec` instance in `anneal/proofs/Specs/<Crate>/<Item>.lean`.
   Without specification locking, an agent can create a new `Specs/<Item>.lean`
   file—or edit an existing one—setting `pre := fun _ => False` or
   `post := fun _ _ => True`, reducing the proof obligation to `True.intro`.
3. **Unauthorized conditional assumption injection
   (`Assumptions/<Crate>/<Item>.lean`).**
   Anneal tracks scoped axioms declared in `Assumptions.<Crate>.<Item>` as
   `VerificationStatus::VerifiedConditional` when `--allow-assumptions` is
   enabled. An unconstrained agent could move an unproven subgoal into a newly
   created `anneal/proofs/Assumptions/<Crate>/<Item>.lean` file or invoke
   verification with `--allow-assumptions`.
4. **Target narrowing and generated-artifact tampering.**
   The agent could modify the Rust source or inline `#[spec]` attributes to
   weaken the extracted contract, pass `--filter` to drop difficult items from
   the capture set, or edit `.anneal/generated/Obligations/<Item>.lean`,
   `.anneal/generated/Verify/<Item>.lean`, or `.anneal/generated/Mir/<Item>.lean`
   directly on disk before invoking Lake.

## Four-layer defense-in-depth architecture

`cargo anneal` and `trusted/audit/` close all four vectors by separating the
pre-session specification lock (`lock-specs`) from the agent's editable proof
directory (`anneal/proofs/Proof/**`) and gating acceptance on `agent-verify`:

| Layer | Mechanism | Cheating vectors blocked |
| --- | --- | --- |
| **1. Cryptographic specification and target lock (`.anneal/spec-lock.json`)** | `lock_workspace_specs` records the sorted list of captured `UnitTargetRecord` entries (including each `def_id`, `lean_module_name`, `item_kind`, `associated_subject_def_id`, and `mir_module_sha256`), together with the exact workspace-relative path and SHA-256 digest of every `.lean` file under `anneal/proofs/Specs/` and `anneal/proofs/Assumptions/`. | Blocks Rust source edits, inline `#[spec]` weakening, and `--filter` target narrowing (vector 4). |
| **2. Pre-build specification-override and assumption gates (`verify_spec_lock`, `check_specs_non_vacuous`)** | Before Lake runs, `verify_spec_lock` compares the current on-disk `anneal/proofs/Specs/**` and `anneal/proofs/Assumptions/**` trees against `.anneal/spec-lock.json`. Adding an unlocked `Specs/<Item>.lean` or `Assumptions/<Item>.lean` file, deleting a locked file, or modifying any locked file's bytes fails immediately. `check_specs_non_vacuous` additionally rejects `Specs` files containing constant `False` preconditions (`pre := fun _ => False`, `pre := fun _ _ => False`), and `verify_workspace_with_options` forbids `--allow-assumptions` and `VerifiedConditional` outcomes whenever `locked_assumptions_files` is empty. | Blocks the `Specs/<Item>.lean` override loophole (vector 2) and unauthorized `Assumptions/<Item>.lean` injection (vector 3). |
| **3. Deterministic `.anneal/generated/` regeneration** | During `agent-verify` (and `verify --locked-specs`), `verify_workspace_with_options` wipes and regenerates `.anneal/generated/Obligations/`, `.anneal/generated/Verify/`, `.anneal/lakefile.toml`, and `.anneal/lean-toolchain` from the locked capture records, restores `.anneal/generated/Mir/` from unit capture outputs, and verifies every generated `Mir/<Item>.lean` file against its locked SHA-256 digest. | Overwrites any manual edits or rogue modules inside `.anneal/generated/` or `.anneal/lakefile.toml` before Lake builds (vector 4). |
| **4. `TrustedBoundary` kernel replay and constant-closure audit** | After `lake build` succeeds, `TrustedBoundary.lean` (`verify-audit`) replays the compiled `.olean` environment through the Lean 4 kernel, verifies that theorem statements (`ci.type`) reference only `Trusted.*`, `Init.*`, `Mir.*`, and `Specs.*` (`checkStatementOrigins`—never `Anneal.*`), and traverses the transitive constant closure of every `Verify.<Crate>.<Item>.verified` theorem to reject `sorryAx` and any `axiom` outside locked `Assumptions.*` modules. | Blocks `sorry`, `admit`, rogue axioms in `Proof/<Item>.lean`, and `theory/` pollution of theorem statements (vector 1). |

Because Layers 1–3 enforce that the captured MIR, generated `Obligations` and
`Verify` assembly modules, and `Specs`/`Assumptions` files are identical to the
locked baseline, and Layer 4 replays `Verify.<Crate>.<Item>.verified` in the
Lean 4 kernel, the only degree of freedom available to the agent is supplying a
valid proof term in `anneal/proofs/Proof/<Crate>/<Item>.lean`.

## End-to-end CLI workflow

### Step 1: Lock the workspace specifications (orchestrator / human)

Before handing the workspace to a proof-authoring agent, extract the crate's MIR
and write `.anneal/spec-lock.json`:

```bash
cargo anneal lock-specs
```

`cargo anneal lock-specs` runs `anneal-rustc-capture` across the workspace (or
aggregates existing unit manifests when `--from-units` is passed), scaffolds
`.anneal/generated/`, and writes `.anneal/spec-lock.json` containing the digests
of all captured MIR targets, existing `anneal/proofs/Specs/**/*.lean` files, and
existing `anneal/proofs/Assumptions/**/*.lean` files.

### Step 2: Inspect obligations and iterate on proofs (agent)

Equipped with the [`anneal-prove` skill](../skills/anneal-prove/SKILL.md), the
agent inspects the target items using `cargo anneal agent-context`:

```bash
# Render Markdown context for all items or a single filtered item:
cargo anneal agent-context --item <def_id_or_module_suffix>
```

The rendered report summarizes proof status (`Present` vs. `Missing`), confirms
whether `.anneal/spec-lock.json` is active, lists the read-only vs. writable
rules, and bundles each item's `Obligations/<Item>.lean`, locked
`Specs/<Item>.lean` (if any), `Mir/<Item>.lean`, and starter proof template.

The agent writes or updates `anneal/proofs/Proof/<Crate>/<Item>.lean` and
checks individual proof files rapidly using Lake's single-file Lean environment:

```bash
(cd .anneal && lake env lean ../anneal/proofs/Proof/<Crate>/<Item>.lean)
```

### Step 3: Verify under the locked specification gate (agent & orchestrator)

To complete the task, the agent or orchestrator runs:

```bash
cargo anneal agent-verify
```

(Equivalently, `cargo anneal verify --locked-specs`.) This command:

1. Verifies `.anneal/spec-lock.json` against the captured unit records and the
   on-disk `anneal/proofs/Specs/**` and `anneal/proofs/Assumptions/**` trees.
2. Deterministically regenerates `.anneal/generated/{Mir,Obligations,Verify}`
   and `.anneal/lakefile.toml`, discarding any edits made outside
   `anneal/proofs/Proof/**`.
3. Runs `lake build` in `.anneal/` to type-check every `Verify.<Crate>.<Item>`
   root in the Lean 4 kernel.
4. Runs `TrustedBoundary.lean` in `verify-audit` mode to enforce kernel replay,
   statement-origin containment, and axiom hygiene.
