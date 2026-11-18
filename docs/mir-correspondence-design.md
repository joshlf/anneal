<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR Correspondence Design

[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md) defines
how Anneal validates its Rust Mid-level Intermediate Representation (MIR)
operational semantics ($M_{\text{anneal}}$): we prove in the Lean 4 kernel that
$M_{\text{anneal}}$ refines an independently developed reference model
($M_{\text{ref}}$) over every program and input query where $M_{\text{anneal}}$
is well-formed.

This document specifies the architecture that implements that strategy:

1. **Reference model ($M_{\text{ref}}$):** Anneal vendors `lean-miri` under
   `vendor/lean-miri/` as part of its pinned, human-audited correspondence TCB
   and enables a surgical opt-in flag (`deinitMovedPlace : Bool`) so that
   moving a MIR place deinitializes the source location at runtime, matching
   post-cleanup runtime MIR semantics.
2. **Anneal MIR syntax and semantics ($M_{\text{anneal}}$):**
   `Trusted.MirModel` represents MIR programs with structural types (`MirTy`)
   carried directly by value, and `Trusted.MirSemantics` defines a small-step
   operational semantics that shares its boundary input and output value types
   (`Query`, `Out`, `TerminalOut`) directly with the reference adapter.
3. **Canonical type codec and correspondence (`Trusted.Correspondence`):**
   A total encoder (`encodeProg`) interns structural `MirTy` values into a
   deduplicated type table (`RefProg.types`) indexed by `TyId := Nat`, and a
   total decoder (`decodeProg`) inverts `encodeProg` unconditionally (`∀ p,
   decodeProg (encodeProg p) = some p`). Over this codec,
   `anneal_corresponds_to_miri` proves, via a bijective simulation invariant
   (`SimulationInv`), that every program well-formed in $M_{\text{anneal}}$ is
   well-formed in $M_{\text{ref}}$ and that the two models agree exactly on its
   terminal behaviors and on whether it diverges. In addition,
   `reachesResult_fault_iff_refReachesOutcome` proves that Undefined Behavior
   (`.undefined` vs. `.ub`) and unsupported constructs (`.unsupported` vs.
   `.blocked`) correspond in both directions.

---

## 1. Repository Layout, Two-Pass Audit, and Trust Boundary

Anneal separates the core semantics shipped in the downstream verification
archive (`trusted/lean/` and `theory/`) from the repository-only correspondence
proof against `vendor/lean-miri/` (`trusted/correspondence/` and
`correspondence/`):

```text
trusted/lean/                   Core TCB (Pass 1; shipped in omnibus-archive)
  Trusted.lean                  Umbrella module
                                (-- anneal-trust-tier: vetted)
  Trusted/
    MirModel.lean               Compiler-independent ground MIR syntax
                                (-- anneal-trust-tier: candidate:mir_ast)
    Rustc/<Dialect>/MirAst.lean Versioned captured rustc MIR syntax
                                (-- anneal-trust-tier: candidate:mir_ast)
    MirSemantics.lean           Anneal small-step semantics & dialect interpreters
                                (-- anneal-trust-tier: candidate:mir_semantics)

theory/                         Core untrusted theory (Pass 1; shipped in
                                omnibus-archive)
  Anneal.lean                   Umbrella module
  Anneal/
    MirWp.lean                  Fuel-bounded weakest precondition (wpProg,
                                wpFaultProg) and M_anneal non-vacuity canaries

vendor/lean-miri/               Vendored lean-miri reference model
                                (correspondence TCB; Pass 2)
  UPSTREAM_PIN.json             Pinned commit, 608 file SHA-256s, 10 patched
                                file SHA-256s, and 160 ExecutionMachine
                                .olean SHA-256s
  Miri/
    MIR/...                     Reference MIR syntax (TyId-indexed)
    Interpreter/
      MachineHooks.lean         MachineState + pendingMoveDeinit flag
      LocalAccess.lean          Pure local operand helpers + deinitMovedPlace
      OperandMachine.lean       Operand evaluation + immediate move deinit
      Place.lean                copyRuntimePlaceNoValidate + indirect move
                                deinit
      PlaceMachine.lean         readImmediate + takePendingMoveDeinit wiring
      Cast.lean                 Cast.cast + atomic pendingMoveDeinit deinit
      ExecutionCast.lean        CastHooks wiring for takePendingMoveDeinit
      Call.lean                 Call argument move deinitialization
      ExecutionCalls.lean       CallHooks wiring for deinitMovedPlace
      ExecutionMachine.lean     Top-level step engine (M_ref) + Config flag

trusted/correspondence/Trusted/ Correspondence TCB specification (Pass 2)
  Correspondence.lean           Codec, MiriRefMachine hooks, reference
                                machine, RefWellFormed, RefBehavior,
                                RefDiverges, CorrespondenceClaim, and
                                FaultEquivalenceClaim
                                (-- anneal-trust-tier: candidate:mir_semantics)

correspondence/Anneal/          Untrusted correspondence proof (Pass 2)
  MirCorrespondenceBase.lean    Codec round-trip, canonicality, SimulationInv,
                                and Miri scalar/discriminant bridge lemmas
  MirCorrespondenceProof.lean   Per-step simulation, correspondence theorems,
                                and M_ref correspondence canaries (D6-D13)

trusted/audit/                  Two-pass source + binary .olean auditor
  src/lib.rs                    Pass 1 (51-module core lock) + Pass 2
                                (UPSTREAM_PIN.json + correspondence closure)
  TrustedBoundary.lean          Syntactic preflight, namespace and
                                constant-cone checks, statement-origin
                                verification, and kernel replay
```

### 1.1 Separating Pass 1 (Core Omnibus) from Pass 2 (Correspondence)

Anneal's Nix build (`omnibus-archive` in `flake.nix`) copies `trusted/lean/`
and `theory/` into `share/anneal/` inside `anneal-exocrate.tar.zst`, and
`anneal-audit` Pass 1 (`Checker::run`) verifies that every module under
`trusted/lean/` and `theory/` starts with `prelude` and imports only the 51
locked `Init.*` modules in `trusted/lean/foundation-lock.json`. By contrast,
`vendor/lean-miri/Miri/` (608 files total; 160 `Miri.*` modules in the
transitive import closure of `Miri.Interpreter.ExecutionMachine`) uses standard
Lean 4 module headers without `prelude`, transitively importing `Init.*`,
`Std.*`, and `Lean.*` modules from the Lean 4.34.1 toolchain sysroot (whose
`.olean`, `.olean.server`, and `.olean.private` artifacts are authenticated in
memory by `AdmittedToolchain::ensure_sysroot_foundation` against
`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` in `trusted/audit/src/lib.rs`).

Although `Trusted/MirSemantics.lean` resides in `trusted/lean/` so that
`Trusted.CrateTheorem` and `Anneal.MirWp` can state per-crate obligations in
Pass 1 without importing `vendor/lean-miri/`, only its outer theorem-stating
boundary (`Query`, `TerminalOut`, `WellFormed`, `ReachesResult`,
`SatisfiesPost`, `Behavior`, `WpSoundnessClaim`, and `WpFaultSoundnessClaim`)
is a human-audited specification surface. Its internal operational execution
rules (`initState` and `evalStep` of $M_{\text{anneal}}$) are kernel-certified
against $M_{\text{ref}}$ (`vendor/lean-miri/`) in Pass 2 by
`CorrespondenceClaim` and `FaultEquivalenceClaim` (`correspondence/`), keeping
evolving execution rules out of the human-audited semantic TCB in accordance
with [`docs/architecture.md`](architecture.md) and
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md).

Placing `Trusted.Correspondence` and `Anneal.MirCorrespondenceProof` in
`trusted/correspondence/` and `correspondence/` preserves both invariants:

1. **Pass 1 (`Checker::run` on `trusted/lean/` and `theory/`):** Audits
   `Trusted.MirModel`, `Trusted.Rustc.<Dialect>.MirAst`, `Trusted.MirSemantics`,
   and `Anneal.MirWp` against the
   unmodified 51-module `trusted/lean/foundation-lock.json` and unmodified
   `allowedTrustedSyntaxKinds` / `allowedTheorySyntaxKinds` allowlists in
   `TrustedBoundary.lean`. Whenever `Anneal.PureLift`, `Trusted.MirModel`,
   `Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst`,
   `Trusted.MirSemantics`, or `Anneal.MirWp` is present (or `require_mir_wp` is
   enabled), `TrustedBoundary.lean` (`verifyMirWpCoreTheorems`) requires
   `Trusted.MirModel`, `Trusted.Rustc.V2026_10_22_R7189d39d9.MirAst`, and
   `Trusted.MirSemantics` in `trusted/` and `Anneal.MirWp`
   in `theory/`, and verifies that `wellFormed_and_spec_of_wp`,
   `reaches_fault_and_exclusive_of_wpFault`, and all 19 Pass 1 canary theorems
   in `Anneal.MirWp` prove the exact trusted `*Claim` propositions (referencing
   the trusted `prog*` fixtures) defined in `Trusted.MirSemantics`. Only
   `trusted/lean/` and `theory/` ship in `omnibus-archive`, keeping downstream
   per-crate verification completely independent of `vendor/lean-miri/`.
2. **Pass 2 (`Checker::run_correspondence` on `vendor/lean-miri/`,
   `trusted/correspondence/`, and `correspondence/`):** Runs in repository CI
   (`--require-correspondence`) to audit the correspondence claim against
   `vendor/lean-miri/`:
   - **Fail-closed `UPSTREAM_PIN.json` check pinned from `trusted/`:** Before
     reading `vendor/lean-miri/UPSTREAM_PIN.json`, `trusted/audit/src/lib.rs`
     verifies that the manifest's own SHA-256 digest matches the TCB constant
     `LOCKED_UPSTREAM_PIN_SHA256`, that its `upstream_commit` equals
     `LOCKED_MIRI_COMMIT`, and that its patched-file map matches the closed TCB
     allowlist `LOCKED_PATCHED_MIRI_FILES` inside `trusted/audit/`, so an
     untrusted change outside `trusted/` cannot alter `UPSTREAM_PIN.json` to
     admit modified `vendor/lean-miri/` sources or `.olean`s. It then verifies
     that all 608 `.lean` files in `vendor/lean-miri/` are regular files (no
     symlinks or pre-existing `.olean`/`.ilean`/`.ir` files) matching their
     pinned SHA-256 digests: 598 files match unmodified upstream
     `proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, and
     the 10 patched files match their pinned `patched_sha256` digests in
     `UPSTREAM_PIN.json`.
   - **160-module `ExecutionMachine` slice build and cache:** Compiles (or links
     from `--miri-cache-dir` after verifying each module's pinned `olean_sha256`
     in `UPSTREAM_PIN.json`) the 160 `Miri.*` modules in the transitive import
     closure of `Miri.Interpreter.ExecutionMachine` with
     `-DElab.async=false -Ddebug.skipKernelTC=false`.
   - **Syntactic preflight on `Trusted.Correspondence` and
     `Anneal.MirCorrespondenceProof`:** Enforces the unmodified
     `allowedTrustedSyntaxKinds` and `allowedTheorySyntaxKinds` allowlists,
     `prelude`, and explicit root-identifier checks on both modules.
   - **Root-namespace provenance for vendored and sysroot modules:**
     `verifyAndCollectCorrLocals` rejects every constant that a `.vendorMiri`
     or `.sysrootFoundation` module declares in the `Trusted` or `Anneal` root
     namespace, so neither the vendored tree nor the toolchain sysroot can
     inject declarations into the namespaces that hold the claims and their
     proofs.
   - **Constant-cone purity, statement-origin verification, and kernel replay:**
     Traverses the constant-level dependency graph (`declarationEdges`) from
     `Trusted.Correspondence` and `Anneal.MirCorrespondenceProof` across all 5
     module roles (`.foundation`, `.sysrootFoundation`, `.vendorMiri`,
     `.trusted tier`, and `.theory`). `TrustedBoundary.lean` verifies that no
     reachable constant is `unsafe` or `isPartial`, that no reachable
     `.vendorMiri` constant is `.opaqueInfo` (guaranteeing that none of the 24
     `partial def` JSON parser helpers in `Miri.Input.*` is reachable), that
     the only reachable axioms belong to `{propext, Classical.choice,
     Quot.sound}`, that `correspondence_claim_holds`,
     `fault_equivalence_claim_holds`, `miri_move_deinit_wiring_claim_holds`, and
     all Pass 2 codec, simulation, and canary theorems in
     `Anneal.MirCorrespondenceProof` prove the exact `Prop` constants (and
     trusted `prog*` fixtures) defined in `Trusted.Correspondence` and
     `Trusted.MirSemantics`, that the 160 `.vendorMiri` `.olean` modules match
     their locked SHA-256 digests in `UPSTREAM_PIN.json`, and that
     `toKernelEnv.replay` replays every constant in `Trusted.Correspondence` and
     `Anneal.MirCorrespondenceProof` on top of the verified base environment.

### 1.2 Compliance with `TrustedBoundary.lean` and `TrustTier` Discipline

Every `Trusted.*` and `Anneal.*` module satisfies `TrustedBoundary.lean` with
zero changes to `trusted/lean/foundation-lock.json` or the syntax/tactic
allowlists:

- **Trust-tier headers (`-- anneal-trust-tier:`):** `Trusted/MirModel.lean` and
  `Trusted/Rustc/*/MirAst.lean` carry `-- anneal-trust-tier: candidate:mir_ast`;
  `Trusted/MirSemantics.lean` and `Trusted/Correspondence.lean` carry
  `-- anneal-trust-tier: candidate:mir_semantics`; and `Trusted.lean` carries
  `-- anneal-trust-tier: vetted`. Because `Trusted.lean` is a pure umbrella
  module that declares zero constants, `checkTierReferences` (which inspects
  constant-level `declarationEdges`) permits `Trusted.lean` to import
  `Trusted.MirModel`, `Trusted.Rustc.*.MirAst`, and `Trusted.MirSemantics` while
  forbidding any `vetted` module from referencing `candidate:*` constants.
- **Tactic-free, `deriving`-free `Trusted.*` definitions:**
  `Trusted/MirModel.lean`, `Trusted/Rustc/*/MirAst.lean`,
  `Trusted/MirSemantics.lean`, and `Trusted/Correspondence.lean` start with
  `prelude`, import locked modules
  from `foundation-lock.json` (`Init.NotationExtra`,
  `Init.Data.BitVec.BasicAux`, `Init.Data.Int.Basic`,
  `Init.Data.Nat.Div.Basic`, `Init.Data.Nat.Bitwise.Basic`, and
  `Init.Control.Except`), omit `deriving` clauses in favor of explicit
  structural `beq` functions, and mark recursive definitions `noncomputable def`
  so Lean 4.34.1 elaborates the identical pure kernel `.defnInfo` without
  emitting partial `._unsafe_rec` compiler helpers. Beyond locked modules and
  the `Trusted.*` modules they build on, only `Trusted/Correspondence.lean`
  imports anything else: `Miri.Interpreter.ExecutionMachine` and its
  sub-modules (`LocalAccess`, `Place`, `Rvalue`, `Step`, `ControlFlow`) from
  `vendor/lean-miri/`, which places the vendored tree inside the
  correspondence TCB (Section 1.3).
- **Allowlisted tactics in `theory/` and `correspondence/`:**
  `Anneal/MirWp.lean` and `Anneal/MirCorrespondenceProof.lean` use only the 30
  tactics in `allowedTheorySyntaxKinds` (such as `let ⟨a, b⟩ := h`, `cases`,
  `induction`, `dsimp`, `simp`, `rw`, `exact`, `apply`, and `decide`) and unfold
  multi-arm `Trusted.*` definitions via `dsimp only [Trusted.foo]` rather than
  `simp [Trusted.foo]` or `unfold Trusted.foo` (preventing
  `Lean.Meta.getEqnsFor?` from lazily emitting `Trusted.foo.eq_N` theorems into
  `theory/` `.olean`s).

### 1.3 Human-Audited Correspondence TCB and Human-Comprehension Priority

The audit checks in Section 1.1 establish that the correspondence theorems are
kernel-checked proofs of the exact claims stated in `Trusted.Correspondence`.
They cannot establish that those claims mean what a reader expects, because a
claim is only as strong as the definitions it unfolds to. For example,
narrowing `WellFormed` or dropping caller-visible memory from `TerminalOut`
would weaken the locked theorems, yet the statement-origin checks would still
pass, because they inspect only which constants a claim names and where those
constants are defined.

**Human comprehension of the correspondence theorem statements
(`CorrespondenceClaim`, `FaultEquivalenceClaim`, and
`MiriMoveDeinitWiringClaim`) and every definition in their transitive dependency
cone is therefore the highest design priority in `Trusted.MirModel`,
`Trusted.MirSemantics`, and `Trusted.Correspondence`.** It must be immediately
clear to a human reviewer that each theorem statement means in mathematical
terms what they intend it to mean in intuitive terms. Clever encodings, indirect
formulations, or non-obvious subtleties in the theorem statements or their
transitive definitions are unacceptable: any proof-engineering complexity must
live in the untrusted proof (`correspondence/`), while every definition in the
theorem-statement dependency cone must be maximally direct, self-evident to a
human auditing the file, and documented so that every boundary condition is
explicit.

Human reviewers audit every definition that controls the meaning of the claims,
together with every later change to those definitions:

| Component | Theorem-controlling definitions |
| :--- | :--- |
| `Trusted.MirModel` | `Program` (`pointerWidthBits`, `mirProfileVersion`) and AST types |
| `Trusted.MirSemantics` | `Val`, `Query`, `Out`, `TerminalOut`, `StepResult` |
| | `Reaches`, `ReachesResult` |
| | `WellFormed`, `Behavior`, `Diverges`, `SatisfiesPost` |
| | `WpSoundnessClaim`, `WpFaultSoundnessClaim`, `prog*`, `Canary*Claim` |
| `Trusted.Correspondence` | Codec, reference machine, top-level claims, and `CanaryD*Claim` |
| `vendor/lean-miri/` | Pinned `ExecutionMachine` slice and 10-file patch |

- **`Trusted.MirModel` and `Trusted.MirSemantics` (`trusted/lean/`):** These
  modules define the programs, inputs, and observable outcomes that the claims
  quantify over, the trace predicates (built from `Step` and `ValidChoice`)
  that turn `initState` and `evalStep` into the claims' hypotheses and
  conclusions, and the concrete `prog*` fixtures and `*Claim`
  propositions enforced on `Anneal.MirWp`. `SatisfiesPost` is the contract that
  per-function specifications discharge through `Anneal.MirWp`. The
  correspondence theorems cross-check the execution rules inside `initState`
  and `evalStep` against $M_{\text{ref}}$, but they assume, rather than check,
  the meaning of the predicates built on those rules.
- **`Trusted.Correspondence` (`trusted/correspondence/`):** This module defines
  the codec (`RefProg`, `encodeProg`, and `decodeProg`); the reference machine
  that the claims observe (`initRefState`, `callerSentinelFrame`,
  `evalRefStep`, `ValidRefChoice`, `RefStep`, `RefReaches`, and the operator
  tables `toMiriBinOp` and `toMiriUnOp`); the reference predicates
  (`RefReachesOutcome`, `RefWellFormed`, `RefBehavior`, `RefDiverges`, and
  `faultToRefOutcome`); and the claims and canary propositions themselves
  (`CorrespondenceClaim`, `FaultEquivalenceClaim`, `MiriMoveDeinitWiringClaim`,
  and `CanaryD6*Claim`–`CanaryD13*Claim`).
- **`vendor/lean-miri/`:** `Trusted.Correspondence` drives `evalRefStep`
  through `lean-miri`'s interpreter modules (`Miri.Interpreter.evalOperand`,
  `Miri.Interpreter.evalRvalueIntoPlace`, `Miri.Interpreter.Step.evalStatement`,
  `Miri.Interpreter.Frame.storageLive`, `Miri.Interpreter.Frame.storageDead`,
  `Miri.Interpreter.ControlFlow.evalTerminator`,
  `Miri.Interpreter.ControlFlow.goToBlock`,
  `Miri.Interpreter.ControlFlow.returnFromCurrentFrame`,
  `Miri.Interpreter.IntegerOps.binary`, `Miri.Interpreter.IntegerOps.unary`,
  `Miri.Memory.ScalarInt`, and `Miri.Interpreter.ExecutionMachine` via
  `MiriMoveDeinitWiringClaim` in Section 5.2), so those definitions control the
  meaning of the reference machine. The vendored tree is therefore part of the
  pinned, human-audited correspondence TCB, not merely an input checked for
  forbidden axioms. `UPSTREAM_PIN.json` pins every file to its audited digest,
  any change to a pinned digest (including a new patch) requires the same human
  audit as a change to `trusted/`, and `verifyCorrCone` keeps vendored
  declarations out of the `Trusted` and `Anneal` namespaces.

---

## 2. Reference Model ($M_{\text{ref}}$) and Move Deinitialization

### 2.1 Vendored `lean-miri` Core

Anneal uses `lean-miri` (pinned at upstream `proofs-rs/lean-miri` commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, which targets `miri` commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `rustc` commit
`8144389c895da997dbdecaa635e41d6a50be6ffd` and compiles cleanly on
`leanprover/lean4:v4.34.1`) as $M_{\text{ref}}$. Because `anneal-rustc-capture`
extracts Stage 2 `Runtime(PostCleanup)` MIR from Anneal's pinned `rustc`
toolchain (`7189d39d9ce936881b8132c6addeaf3e295cd455` / `V2026_10_22_R7189d39d9`,
along with supported local dialects `V2026_05_31_R14210df0e` and
`V2026_05_30_Rf8a08b688`) and interprets it into `Trusted.MirModel`, the
correspondence TCB audits that every enabled Stage 2 MIR construct in
`Trusted.MirModel` has identical post-cleanup operational rules across the
pinned `rustc` revisions, and
stamps captured programs with an explicit semantic profile version
(`mirProfileVersion : Nat := 1`; Section 3.1) that both `initState` and
`initRefState` verify fail-closed. `lean-miri` is a mechanized Lean 4
interpreter modeled line-by-line on `rustc_const_eval::interpret`. Each
invocation of `evalRefStep` in `Trusted.Correspondence` executes one MIR
statement or terminator in a single deterministic step without an internal
substep fuel cutoff (and `ExecutionMachine.step` in `vendor/lean-miri` is
parameterized over `limits : ExecutionMachine.Limits`, which is universally
quantified in `MiriMoveDeinitWiringClaim`), taking a nondeterminism oracle
(`choice : Choice`) and a reference state and returning one of five outcomes:

- `.running nextState`: the statement or terminator stepped normally.
- `.returned out`: the root frame executed `TerminatorKind.Return` and popped
  into the caller sentinel frame.
- `.exhaustedStepLimit`: the execution reached its configured step budget
  (`stepsExecuted ≥ maxSteps`).
- `.ub`: the execution triggered modeled Rust Undefined Behavior (such as
  reading uninitialized data, dividing by zero, overflowing an unchecked
  arithmetic operator, or accessing a dead local).
- `.blocked`: the execution encountered an unmodeled feature, missing hook, or
  malformed MIR invariant (such as an out-of-bounds basic-block index or an
  unsupported statement, rvalue, or terminator).

### 2.2 Single-Source Type and Layout Hooks (`MiriRefMachine`)

`lean-miri` parameterizes its interpreter over a `Machine` typeclass (`Hooks`)
that supplies type layouts (`localLayout`, `scalarTypeClass`, `castTypeInfo`,
`pointeeTypes`, `retagTypeShape`). Rather than maintaining five separate tables
that could disagree on a type's size or signedness, `Trusted.Correspondence`
defines a single program wrapper:

```lean
structure RefProg where
  bodies : List RefBody
  entryDefId : DefId := 0
  types : List MirTy
  pointerWidthBits : Nat := 64
  mirProfileVersion : Nat := 1
```

Every `MiriRefMachine` hook derives its layout answer purely by indexing into
`rp.types[tyId]?`:

- `MirTy.unit` maps to a 0-byte zero-sized layout (`Size.ZERO`, alignment 1,
  `FieldsShape.Arbitrary`).
- `MirTy.bool` maps to a 1-byte unsigned scalar layout with valid range
  `0..=1`.
- `MirTy.int width signed` maps to a scalar layout of size `width.byteSize`
  (`1`, `2`, `4`, `8`, or `16` bytes) and signedness `signed`. Because
  `isize` and `usize` use 8 bytes, which is correct only on 64-bit targets,
  `initRefState` rejects every `RefProg` whose `pointerWidthBits` is not `64`
  (Section 3.1).
- `MirTy.unsupported` (or any out-of-bounds `tyId`) returns `none`, which causes
  `lean-miri` to halt with `.blocked (.missingHook ...)`.

In `lean-miri`, `OperandMachine.localToOp` lazily caches `LocalState.layout` in
`frame.locals` on the first read of a local variable. To prevent read-only
operand evaluations (`Operand.copy`) from mutating `frame.locals` with layout
cache updates, `initRefState` pre-populates `cachedLayout := some ty` on every
local slot at function entry.

### 2.3 Two-Frame Call-Stack Sentinel Protocol

In `lean-miri`, executing `TerminatorKind.Return` on a 1-frame call stack
(`stack.length == 1`) with a `returnPlace` destination triggers
`CallError.returnFromRootFrameWithDest`, which `ExecutionMachine.step`
classifies as `.ub`. When a caller frame is present (`stack.length == 2`),
`Return` copies the root frame's `_0` local into `rootFrame.returnPlace`, pops
`rootFrame`, and halts cleanly with `.returned` when the remaining sentinel
frame has `returnContinuation == none`.

`Trusted.Correspondence` mirrors this protocol with an explicit sentinel
frame:

```lean
def callerSentinelFrame (retTy : MirTy) : RefFrameState
```

`callerSentinelFrame retTy` never executes. Its only local is the caller's
live destination slot (`local 0`) of type `retTy`, and it marks the suspended
caller frame (`returnContinuation := true`), whereas the active entry frame has
no further return continuation (`returnContinuation := false`). `initRefState`
builds every initial reference state with the two-frame stack
`frames := [callerSentinelFrame retTy, rframe]`, where `retTy` is the entry
body's return-place type (`localTys[0]`) and `rframe` begins executing
`rp.bodies[rp.entryDefId]` at block `0`, statement `0`.

`evalRefStep` steps the top frame `rframe` of a two-frame stack
`[sentinel, rframe]`, leaving the sentinel unchanged, and returns `.blocked`
for any other stack shape. When `rframe` executes `Return` with an initialized
`_0`, `evalRefStep` returns the terminal outcome
`.returned ⟨retVal, callerMem⟩`, matching `lean-miri`, which validates
and copies `_0` into the sentinel's slot `0`, pops the root frame, and halts
with `.returned`. Because `Return` is terminal in both machines (`evalStep`
returns `.done (.returned ⟨retVal, callerMem⟩)`), no running state ever
holds the one-frame stack that would remain after the pop, and
`SimulationInv` (Section 5.3) relates every running $M_{\text{anneal}}$ state
to a two-frame reference stack.

### 2.4 Runtime Move Deinitialization

Upstream `lean-miri` follows `rustc_const_eval/src/interpret/operand.rs`, which
implements `Operand::Move(place)` identically to `Operand::Copy(place)` (`//
FIXME: do some more logic on 'move' to invalidate the old location`). While
treating `move` as `copy` is benign for compile-time constant evaluation of
borrow-checked safe Rust, Anneal captures `Runtime(PostCleanup)` MIR—after the
elaborate-drops and drop-shim passes have run—and verifies `unsafe` Rust code
where raw pointer dereferences can alias moved locals. In runtime MIR, moving a
non-zero-sized place deinitializes the source place so that any subsequent read
(before reinitialization) triggers Undefined Behavior.

To make $M_{\text{ref}}$ enforce runtime move deinitialization without breaking
upstream `lean-miri` proofs or tests, we add an opt-in configuration flag
`deinitMovedPlace : Bool := false` across 10 files in `vendor/lean-miri/Miri/`
(`MachineHooks.lean`, `LocalAccess.lean`, `OperandMachine.lean`, `Place.lean`,
`PlaceMachine.lean`, `Cast.lean`, `ExecutionCast.lean`, `Call.lean`,
`ExecutionCalls.lean`, and `ExecutionMachine.lean`) and set `deinitMovedPlace :=
true` in Anneal's `MiriRefMachine`.

In `lean-miri`, `OperandMachine.evalOperand` evaluates a `Place` via
`evalPlaceToOp` into an `OpTy` whose runtime payload is either:

- **`Operand.immediate imm`:** For an unprojected local
  (`place.projection.isEmpty`), the local variable's scalar or zero-sized value
  has already been copied by value out of `frame.locals[localId]` into `imm`.
  When `deinitMovedPlace` is `true` and `evalOperand` evaluates `.Move place`,
  it first runs `evalPlaceToOp` (so any out-of-bounds or dead-local error fires
  before mutation), then resets `frame.locals[place.localId]` to `.live
  (.immediate .uninit)` and clears `pendingMoveDeinit := false`:
  - In `_1 = move _1` (self-move), `evalOperand` extracts the old value of `_1`
    and marks `_1` as `.uninit`, after which `writePlaceImmediate` overwrites
    `_1` with the extracted value.
  - In `BinOp(lhs, rhs)`, `Rvalue.BinaryOp` evaluates and reads `lhs` before
    evaluating `rhs`. Hence `BinOp(copy _1, move _1)` reads `_1` in `lhs` and
    moves `_1` in `rhs`, whereas `BinOp(move _1, copy _1)` and `BinOp(move _1,
    move _1)` deinitialize `_1` during `lhs` and fault with `.ub` when `rhs`
    reads `_1`.
  - When `_1 : ()` has the 0-byte unit type, `.immediate .uninit` is already the
    canonical valid representation of a 0-byte zero-sized value in `lean-miri`
    (`Immediate.lean`, `ValidityVisitor.lean`), so moving a `()` local leaves it
    valid and initialized.
- **`Operand.indirect mplace`:** For memory-backed locals, projected fields in
  memory, and pointer dereferences (`*_1`) in Phase 2, `evalPlaceToOp` returns a
  lazy pointer (`MemPlace`) into `state.machine.memory` that consumers
  (`PlaceMachine.readImmediate`, `Place.copyRuntimePlaceNoValidate`,
  `Cast.cast`, and `Call.passArgument` / `Call.allocateVarargs`) read *after*
  `evalOperand` returns. (If `evalPlaceToOp` succeeds with `.immediate _` on a
  projected local `!place.projection.isEmpty`, meaning the local has no `.Deref`
  projection and every projection step is valid, `evalOperand` in both
  `OperandMachine.lean` and `LocalAccess.lean` materializes the base local via
  `forceAllocation` / `forceLocalAllocation` and re-runs `evalPlaceToOp` to
  obtain `.indirect mplace` for the projected sub-place.) Rather than adding a
  field to `OpTy` (which would break 2-argument `⟨op, layout⟩` constructors
  across 174 files in `vendor/lean-miri/Miri/`), `evalOperand (.Move place)`
  sets `pendingMoveDeinit := true` on `MachineHooks.MachineState` (while
  `evalPlaceToOp` and non-`Move` arms of `evalOperand` reset
  `pendingMoveDeinit := false`):
  - Inside `PlaceMachine.readImmediate` (`BinaryOp`, `UnaryOp`, `SwitchInt`,
    `Assert`), the consumer atomically takes `pendingMoveDeinit`, runs
    upstream `Miri.Interpreter.readImmediate` (checking scalar layout, pointer
    alignment, borrow-tracker permissions, and `.uninit` bytes), and then writes
    `.uninit` to `⟨mplace, operand.layout⟩` via
    `writeImmediateToMplaceNoValidate`.
  - Inside `Place.copyRuntimePlaceNoValidate` (`Rvalue.Use`, `Aggregate`,
    `Repeat`, `WrapUnsafeBinder`), the consumer atomically takes
    `h.takePendingMoveDeinit` after `compatible` and `hasPadding` checks. In the
    `.immediate value` branch, it deinitializes `⟨mplace, source.layout⟩`
    via `h.writeMemoryNoValidate choice .uninit` *before* writing
    `value.value` to `dest` (preserving indirect self-moves
    `*_1 = move *_1`); in the `.place memory` branch (padded or memory-backed
    structs/arrays), it runs `copy.memoryCopy` (which enforces
    `nonoverlapping = true`, rejecting non-ZST overlapping `Assign` places as
    `overlapping copy_nonoverlapping` UB per Rust MIR's disjoint-`Assign` rule)
    and then, when `shouldDeinit` is `true`, deinitializes
    `⟨memory.mplace, source.layout⟩` via `h.writeMemoryNoValidate choice
    .uninit` (which is a no-op on zero-sized places because their byte length is
    `0`), before `copyRuntimePlace` runs destination validity checks
    (`h.validate choice dest`). On the zero-length `Repeat` (`[move x; 0]`) path
    where `writeRepeat` skips `copyOp`, `ExecutionMachine.rvalueHooks`
    explicitly consumes `takePendingMoveDeinit` and deinitializes `source`'s
    `mplace` after `getPlaceAllocMut` validates the destination.
  - Inside `Cast.cast` (`Rvalue.Cast`), `Cast.cast` atomically takes
    `shouldDeinit ← h.takePendingMoveDeinit` at entry before any intermediate
    helper read (`checkFunctionPointer`, `BoxDerefTransmute`, or per-field
    `copyNoValidate` inside `unsizeInto`) can consume the flag, then
    deinitializes the complete source operand via `h.deinitSource choice source`
    once the cast or unsizing copy completes.
  - Inside `Call.evalCalleeAndArgs`, `Call.evalFnCallArgumentAt`,
    `Call.passArgument`, `Call.allocateVarargs`,
    `Call.materializeAndDeinitArgs`, `Call.initFnCallStep`, `Call.initFnCall`,
    and `Call.initFnTailCall` (`TerminatorKind.Call` and `TailCall`), moving an
    unprojected `.immediate` argument deinitializes
    `frame.locals[place.localId]` (preserving valid ZST immediates when
    `layout.isZst`) when `h.deinitMovedPlace` is `true`. In
    `evalCalleeAndArgs`, whenever `hasMove` is `true` (`isMoveFunc || args.any
    ...`) and `func` evaluates to an indirect `.indirect mplace`,
    `evalCalleeAndArgs` snapshots `func` into a temporary stack allocation
    (`tmpFunc` via `h.copyToMemory`, preserving Tree Borrows, race, alignment,
    and initialization checks) before argument evaluation can deinitialize an
    alias of `func`, and deinitializes `⟨mplace, func.layout⟩` via
    `h.deinitInPlaceArgument` only when `isMoveFunc` is `true` (while
    `ExecutionCalls.make` clears `pendingMoveDeinit := false` and
    `pendingMoveDeinits := #[]` after `evalOperand` / `evalOperandAt`). When a
    `.Move` argument resolves to an `.InPlace` memory place during
    `evalCalleeAndArgs`, `evalFnCallArgumentAt` snapshots the argument into a
    temporary stack allocation (`tempAllocs`) and marks the source `MPlaceTy`'s
    raw bytes `.uninit` (`h.markInPlaceMovedUninit`) immediately during argument
    evaluation so any later operand evaluation that reads the moved place sees
    `.uninit` and reports UB; indirect `.Copy` arguments in calls with `hasMove
    = true` are likewise snapshotted into `tempAllocs` via `h.copyToMemory`
    (preserving canonical read access checks). Inside `passArgument`,
    `allocateVarargs`, and `materializeAndDeinitArgs`, `.InPlace` arguments
    restore `srcPlace`'s raw bytes from the snapshot
    (`h.restoreInPlaceMovedBytes`), copy from `srcPlace` via
    `h.copyAllowTransmute` / `h.copyToMemory` (so the copy runs with full Tree
    Borrows, data-race, alignment, and validity checks on `srcPlace`), and
    deinitialize `srcPlace` via `h.deinitInPlaceArgument` (followed by
    `h.protectArgument` in `passArgument`). On non-copying call paths
    (`findMirOrEvalFn = none`, empty `isRustCall` tuple, and `.Virtual` receiver
    dispatch), `deinitInPlaceArg` restores the source `MPlaceTy`'s raw bytes
    from the snapshot and invokes `h.deinitInPlaceArgument`
    (`writeMemoryNoValidate .uninit`) before temporary stack allocations are
    deallocated via `deallocateStack`.
  - Finally, `ExecutionMachine.step` clears `pendingMoveDeinit := false` and
    `pendingMoveDeinits := #[]` before and after every statement or terminator
    step so no unconsumed flag can leak into a subsequent step.

---

## 3. MIR Representation (`Trusted.MirModel`) and Canonical Type Codec

### 3.1 Structural Types by Value in `Trusted.MirModel`

In `Trusted.MirModel`, MIR types (`MirTy`) are structural inductive values carried
directly inside AST nodes (`Body.locals : List MirTy`, `ConstOperand.ty :
MirTy`, and `ProjectionElem.field : FieldIdx → MirTy → ProjectionElem`):

```lean
inductive IntWidth where
  | i8 | i16 | i32 | i64 | i128 | isize

inductive Mutability where
  | shared | mut

inductive MirTy where
  | bool
  | int (width : IntWidth) (signed : Bool)
  | unit
  | tuple (fields : List MirTy)
  | ref (mutability : Mutability) (pointee : MirTy)
  | rawPtr (mutability : Mutability) (pointee : MirTy)
  | unsupported
```

Carrying `MirTy` by value eliminates out-of-bounds type-table indices (`TyId`)
and duplicate-index aliasing from `Trusted.MirModel` and `Trusted.MirSemantics`:
two types in $M_{\text{anneal}}$ are equal if and only if they are structurally
equal (`t₁ = t₂`). To satisfy `TrustedBoundary.lean`'s `deriving`-free
syntax allowlist in `trusted/`, `Trusted.MirModel` defines structural equality
via pure pattern-matching functions (`IntWidth.beq`, `Mutability.beq`,
`MirTy.beq`).

Similarly, constant literals (`ConstLit`) represent only modeled constant shapes
(`.scalar (bits : BitVec 128)` and `.zeroSized`). When `anneal-rustc-capture`
encounters any unmodeled constant, statement, rvalue, terminator, or type in
Stage 2 `Runtime(PostCleanup)` MIR, it fails closed with a hard capture error
and never rewrites unsupported MIR into generic `.unsupported` nodes. The
`.unsupported` constructors (`MirTy.unsupported`, `StatementKind.unsupported`,
`Rvalue.unsupported`, and `TerminatorKind.unsupported`) exist solely in
`Trusted.MirModel` as explicit AST sentinels for testing and verifying fail-closed
`.unsupported` / `.blocked` fault handling in `CorrespondenceClaim`,
`FaultEquivalenceClaim`, and negative canaries (`CanaryD5`).

`Program` collects the function bodies and records both the pointer width of
the captured target and the Stage 2 MIR semantic profile version:

```lean
structure Program where
  bodies : List Body
  entryDefId : DefId := 0
  pointerWidthBits : Nat := 64
  mirProfileVersion : Nat := 1
```

`anneal-rustc-capture` records the target layout and compiler/MIR profile in the
`CaptureManifest` ([`docs/architecture.md`](architecture.md)), and the capture
serializer must set both `pointerWidthBits` and `mirProfileVersion` from that
manifest rather than rely on the defaults:

- **Target pointer-width gating (`pointerWidthBits = 64`):** Both semantics
  model `isize` and `usize` as 8-byte integers (`IntWidth.byteSize .isize = 8`
  in $M_{\text{anneal}}$, and `toMiriSize .isize` is 8 bytes in
  $M_{\text{ref}}$), so both fail closed on every other target: `initState` and
  `initRefState` return `.error .unsupported` whenever `p.pointerWidthBits` is
  not `64` (`!Nat.beq p.pointerWidthBits 64`). Without this check, both models
  could share the 64-bit layout, agree with each other, and still accept
  overflow, shift, and layout behavior that differs from the compiled program on
  a 32-bit target.
- **Semantic revision and profile gating (`mirProfileVersion = 1`):** Because
  `anneal-rustc-capture` runs on Anneal's pinned `rustc` toolchain
  (`7189d39d9ce936881b8132c6addeaf3e295cd455`, plus supported local dialects)
  while `vendor/lean-miri/` tracks
  upstream `miri`/`rustc` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), the
  correspondence TCB audit verifies that every enabled Stage 2
  `Runtime(PostCleanup)` MIR construct has identical operational rules across
  both compiler revisions under profile version `1`. Both `initState` and
  `initRefState` check `Nat.beq p.mirProfileVersion 1` and return
  `.error .unsupported` on any other profile version, ensuring that any future
  change to `anneal-rustc-capture`'s MIR lowering profile or target ABI rules
  must bump `mirProfileVersion` and undergo a coordinated update and audit of
  both models.

### 3.2 Canonical Type Interning (`encodeProg` and `decodeProg`)

Because `lean-miri` indexes types via `TyId := Nat`, `Trusted.Correspondence`
provides a pure, total codec between `Program` (with inline `MirTy`) and
`RefProg` (with `TyId` indices into `RefProg.types : List MirTy`):

1. **Seeded initial type table (`initTypeTable`):**
   Type collection starts from `initTypeTable := [.unit, .bool, .int .isize
   false]` (`TyId`s `0`, `1`, and `2`). Pre-seeding these three primitive types
   guarantees that `lean-miri` hooks that look up `bool` or `isize` without
   referencing an AST node—such as `TerminatorKind.SwitchInt` calling
   `h.boolLayout`—always find valid layouts even when `MirTy.bool` does not
   appear syntactically in `p : Program`.
2. **Recursive bottom-up sub-type interning (`collectTy`):**
   `collectTy` traverses every `MirTy` appearing in `Body.locals`,
   `ConstOperand.ty`, and `ProjectionElem.field`, recursively interning child
   types (`pointee` in `.ref`/`.rawPtr` and `fields` in `.tuple`) via
   `insertTy` before interning the enclosing composite type.
3. **Stateless-per-table encoding and decoding:**
   Once `collectProgTypes p` constructs the program's `types : List MirTy`
   table, `encodeProg p` replaces each `ty : MirTy` with `lookupTyId types ty`,
   and `decodeProg rp` resolves each `id : TyId` back to `rp.types[id]?`
   (returning `none` if any `TyId` is out of bounds). Both directions copy
   `entryDefId`, `pointerWidthBits`, and `mirProfileVersion` unchanged, so the
   reference machine checks the exact target width and semantic profile version
   that the capture recorded.

### 3.3 Unconditional Anti-Laundering Guarantees

`Anneal.MirCorrespondenceProof` proves the following unconditional theorems
about the codec defined in `Trusted.Correspondence`:

1. **Exact round-trip (`decodeProg_encodeProg`):**
   ```lean
   theorem decodeProg_encodeProg (p : Program) :
       decodeProg (encodeProg p) = some p
   ```
   Every `p : Program` round-trips through `encodeProg` and `decodeProg` with
   zero well-formedness preconditions. `encodeProg` is therefore injective and
   cannot collapse distinct `Program`s onto the same `RefProg`.
2. **Canonical type deduplication (`encodeProg_types_canonical`):**
   ```lean
   theorem encodeProg_types_canonical (p : Program) :
       typesAreCanonical (encodeProg p).types = true
   ```
   Every `MirTy` in `(encodeProg p).types` appears at a unique `TyId`. As a
   result, nominal `TyId` equality inside `lean-miri` (`assertSameType` in
   binary operations and `assertRvalueLayout` in assignments) is equivalent to
   structural `MirTy` equality in $M_{\text{anneal}}$.
3. **No dormant no-op laundering (`encodeStmt_no_dormant_noops`):**
   `encodeStmt` maps a statement to `RefStatementKind.nop` if and only if the
   source statement is `StatementKind.nop` (`encodeStmt ts s = .nop ↔ s =
   .nop`), ensuring that `encodeProg` never silences an active or unsupported
   MIR statement by turning it into a no-op.
4. **Structural constructor and field preservation (`encodePlace_eq`,
   `encodeOperand_eq`, `encodeRvalue_binaryOp_iff`, `encodeRvalue_unaryOp_iff`,
   `encodeRvalue_use_iff`, `encodeStmt_assign_iff`,
   `encodeStmt_storageLive_iff`, `encodeStmt_storageDead_iff`, and
   `encodeTerminator_eq`):**
   Every encoder step in the one-to-one adapter preserves both its constructor
   tag and all encoded subfields in order: `encodePlace` preserves `localId` and
   `projection`; `encodeOperand` preserves `.copy place`, `.move place`, and
   `.constant (lookupTyId ts c.ty, c.lit)`; `encodeRvalue` produces
   `RefRvalue.binaryOp op (encodeOperand ts lhs) (encodeOperand ts rhs)` if and
   only if the source rvalue is `Rvalue.binaryOp op lhs rhs` with the exact same
   operator `op` and ordered operands `(lhs, rhs)` (and likewise for
   `RefRvalue.unaryOp op (encodeOperand ts opnd)` and `RefRvalue.use
   (encodeOperand ts opnd)`); `encodeStmt` preserves `.assign (encodePlace ts
   dst) (encodeRvalue ts rv)`, `.storageLive l`, `.storageDead l`, `.nop`, and
   `.unsupported`; and `encodeTerminator` preserves `.goto target`,
   `.switchInt (encodeOperand ts discr) targets`, `.return`, `.unreachable`, and
   `.unsupported` with their exact target blocks and branch lists.

Guarantees 1–3 alone would not rule out semantic permutation: an encoder that
exchanged `.add` and `.addUnchecked`, reversed `(lhs, rhs)` on `.sub`/`.div`, or
exchanged `.storageLive` and `.storageDead`, paired with a decoder that reversed
the permutation, would still satisfy round-trip (`decodeProg (encodeProg p) =
some p`). Guarantee 4 rules out both constructor and field permutations across
the entire 1-to-1 AST adapter.

Two further checks pin the meaning of the shared operators. Inside
`Trusted.Correspondence`, the reference machine maps each `BinOp` and `UnOp` to
its `lean-miri` counterpart through the audited tables `toMiriBinOp` and
`toMiriUnOp` (Section 1.3). The canary
`canary_negative_ub_add_unchecked_overflow_u32` (Section 5.4) evaluates an
unchecked `u32` addition whose mathematical sum exceeds `u32::MAX` and proves
that it reaches `.fault .undefined`, whereas wrapping `.add` on the same
operands wraps modulo $2^{32}$. Because `FaultEquivalenceClaim` transfers that
fault to `.ub` in $M_{\text{ref}}$, an encoder or operator table that mapped
`.addUnchecked` to wrapping addition, or an $M_{\text{anneal}}$ rule that
wrapped instead of faulting, would fail CI.

---

## 4. Anneal Operational Semantics (`Trusted.MirSemantics`)

### 4.1 Shared Boundary Value Domain

`Trusted.MirSemantics` and `Trusted.Correspondence` share the exact same
boundary value types (`ScalarVal`, `PtrVal`, `AllocByte`, `Val`, `Allocation`,
`CallerMemory`, `Query`, `Out`, and `TerminalOut`):

```lean
structure ScalarVal where
  width : IntWidth
  signed : Bool
  bits : BitVec 128

inductive Val where
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | unit
  | tuple (fields : List Val)
  | bytes (data : List AllocByte)

structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)
```

In Day 1 / Phase 1, unwinding is outside the supported domain (`unwindEnabled =
false`), so every unwinding transition maps to `FaultKind.unsupported` /
`.blocked` and `TerminalOut.unwound` is never produced by either machine; when a
future phase enables unwinding (`unwindEnabled = true`), `TerminalOut.unwound`
must also carry the canonical unwind payload alongside `callerMem` so
corresponding unwind outcomes preserve both the payload and caller-visible
memory.

Sharing `Query` and `TerminalOut` across both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ eliminates any external input conversion or output projection
function $\pi : \text{Out}_{\text{anneal}} \to \text{Out}_{\text{ref}}$ from the
correspondence theorem statement, preventing a constant or lossy projection from
hiding disagreements in return values or memory state. Inside
`Trusted.Correspondence`, `initRefState` and `evalRefStep` bridge boundary
`Val`s (`Val.scalar ⟨w, s, bits⟩`, `Val.bool b`, `Val.unit`) to and from
`lean-miri`'s `Miri.Memory.ScalarInt` representation via `checkRefVal`,
`toMiriScalar` (`ScalarInt.tryFromUInt bits (toMiriSize w)`, rejecting any
out-of-width bit pattern rather than truncating), and `fromMiriScalar` (reading
`sc.data` at static type `.int w s` or `sc.tryToBool` at `.bool`).
`Anneal.MirCorrespondenceProof` proves unconditional field-preservation and
agreement lemmas for these boundary adapters (`checkRefVal_eq : checkRefVal v
ty = checkVal v ty`, `checkRefArgsMatch_eq : checkRefArgsMatch vs tys =
checkArgsMatch vs tys`, and `match_tryFromUInt_eq`, guaranteeing that a
validated `ScalarInt` preserves `sc.data = bits` and `sc.size = toMiriSize w`
with zero truncation or signedness mutation).

### 4.2 Factored Entry Initialization and Small-Step State Machine

Rather than embedding a synthetic `.entry q` state inside the running state type
(which would introduce a 1-step stuttering offset relative to `initRefState`),
`Trusted.MirSemantics` factors entry validation (`initState`) from the running
state machine (`State` and `evalStep`):

```lean
inductive LocalSlot where
  | dead
  | live (val : Option Val)

structure FrameState where
  defId : DefId
  blockIdx : BasicBlockId
  stmtIdx : Nat
  locals : List LocalSlot

structure State where
  frames : List FrameState
  callerMem : CallerMemory := ⟨[]⟩
```

At function entry, `initState : Program → Query → Except FaultKind State`
checks that:

1. `p.pointerWidthBits` is `64` and `p.mirProfileVersion` is `1` (any other
   target width or semantic profile version returns `.error .unsupported`; see
   Section 3.1).
2. `q.callerMem.allocations` is empty on Day 1 (non-empty initial caller memory
   returns `.error .unsupported`).
3. `p.bodies[p.entryDefId]?` exists, has at least one basic block, satisfies
   `body.argumentCount < body.locals.length`, has all `.storageLive` and
   `.storageDead` indices in bounds (`< body.locals.length`, matching
   `CallMachine.alwaysLiveVarsAndTemps`), and declares supported scalar or unit
   local types.
4. `q.args` has length `body.argumentCount` and each argument `v` satisfies
   `v.ty? = some paramTy` (including `ScalarVal.wf`: `v.bits.toNat <
   v.width.modulus`).

`initRefState` applies the same checks to `encodeProg p` and fails with the
same `.error .unsupported`, so the two machines reject exactly the same entry
inputs.

When validation succeeds, `initState` constructs the initial `FrameState` at
`blockIdx := 0, stmtIdx := 0`:

- Return place `_0` is initialized to `liveUninitSlot body.locals[0]`.
- Argument locals `1 .. body.argumentCount` are initialized to `.live (some
  q.args[idx - 1])`.
- Non-argument locals (`idx > body.argumentCount`) start as `.dead` if any
  basic block in `body` contains a `.storageLive idx` or `.storageDead idx`
  statement, and start as `liveUninitSlot body.locals[idx]` otherwise.

### 4.3 Three-Pole Outcome Partition, Well-Formedness, and Behavior

Each step of `evalStep : Program → Choice → State → StepResult State
TerminalOut` returns one of three outcomes:

- `.step next`: execution advances to `next : State`.
- `.done out`: execution terminates normally with `out : TerminalOut`.
- `.fault .undefined`: execution triggers modeled Rust Undefined Behavior.
- `.fault .unsupported`: execution reaches an unmodeled MIR construct or state.

Over `initState` and `evalStep`, `Trusted.MirSemantics` defines reachability,
all-prefix well-formedness, and observable behavior:

```lean
def Step (p : Program) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res

inductive Reaches (p : Program) : State → State → Prop where
  | refl (s : State) : Reaches p s s
  | tail : Reaches p s₁ s₂ → Step p s₂ (.step s₃) →
      Reaches p s₁ s₃

def ReachesResult (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, Reaches p s₀ s ∧ Step p s res

def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s →
      ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

def Behavior (p : Program) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult p q (.done out)

def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State, initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧ ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))

def SatisfiesPost (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out
```

`WellFormed p q` requires both that `initState p q` succeeds and every
reachable state has at least one admissible choice
(`∃ c, ValidChoice p s c`, preventing a vacuous choice predicate from making
`WellFormed` hold on a stuck machine) and that no reachable transition faults
with either `.undefined` or `.unsupported`.

`Diverges p q` states that entry succeeds (`initState p q = .ok s₀`) and that
there exists a single coherent infinite execution trace `trace : Nat → State`
starting at `trace 0 = s₀` in which every state `trace n` steps to
`trace (n + 1)`. Defining divergence via a single state stream `trace : Nat →
State` (rather than `∀ n, ∃ s, ReachesN p n s₀ s`) ensures that even when
`ValidChoice` admits infinitely many nondeterministic branches (such as
allocator address choices), an infinitely branching tree of finite-only paths is
not misclassified as divergent. Termination versus divergence is observable
behavior under
[`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md), and
Section 5.2 relates `Diverges` to its reference counterpart in both
directions. `SatisfiesPost` is a partial-correctness contract: it constrains
every terminal behavior but does not by itself require termination, so a
specification that must also rule out divergence can add `¬ Diverges p q`.

### 4.4 Core Operational Rules Matching `lean-miri`

To maintain a 1-to-1 step correspondence with `lean-miri` across all inputs
(both well-formed executions and faulting executions), `Trusted.MirSemantics`
aligns its operational checks with `lean-miri`'s evaluation order:

1. **Zero-sized `MirTy.unit` initialization (`liveUninitSlot`):**
   ```lean
   def liveUninitSlot : MirTy → LocalSlot
     | .unit => .live (some .unit)
     | _ => .live none
   ```
   In `lean-miri`, a 0-byte zero-sized type (`Size.ZERO`) has `.immediate
   .uninit` as its unique valid representation. Defining `liveUninitSlot .unit =
   .live (some .unit)` ensures that `fn empty() { return }` (which returns `_0 :
   ()` without an explicit `_0 = const ()` assignment) succeeds in both
   machines, and that `StorageLive` and `Operand.move` on a `.unit` local
   preserve state correspondence.
2. **Two-stage operand evaluation and move threading (`evalOperandToSlot` and
   `evalPrimitiveOperand`):**
   - **Stage 1 (`evalOperandToSlot`):** Resolves an `Operand` to `(ty : MirTy,
     optVal : Option Val, locals' : List LocalSlot)` without yet checking
     whether `optVal` is initialized (`some v`). If the operand is `.move
     place` on a live unprojected local, `evalOperandToSlot` updates
     `locals[place.localId]` to `liveUninitSlot ty` and returns the updated
     `locals'`.
   - **Stage 2A (`evalPrimitiveOperand`):** Used by `Rvalue.binaryOp`,
     `Rvalue.unaryOp`, and `TerminatorKind.switchInt`. Checks
     `isPrimitiveReadableTy ty` (`.bool` or `.int w s`) *before* checking
     whether `optVal` is `some v`, matching `MemoryOperand.readImmediate`
     (which checks `BackendRepr.Scalar` on the static layout before inspecting
     the runtime `Immediate` for `.uninit`).
   - **Stage 2B (`Rvalue.use` inside `evalRvalue`):** Calls `evalOperandToSlot`,
     checks `srcTy = dstTy` first (matching `copyRuntimePlaceNoValidate`), and
     then checks `optVal = some v` (matching `h.validate`).
3. **Assignment evaluation order (`StatementKind.assign`):**
   `evalStatement` checks that `dst.projection` is empty and looks up `dstTy :=
   body.locals[dst.localId]?` first, then evaluates `evalRvalue` (producing
   `(val, localsAfterRval)` with any source `.move` deinitializations applied),
   and finally calls `writePlace localsAfterRval dst.localId dstTy val` (which
   checks `checkVal val dstTy` and verifies that `dst` is `.live`). Because
   `writePlace` runs after `evalRvalue`, self-moves (`_1 = move _1`) first
   deinitialize `_1` during `evalRvalue` and then write the extracted value back
   into `_1`.
4. **Six-width integer and boolean operations (`evalBinOp` and `evalUnOp`):**
   - Non-shift integer binary operators require matching width and signedness
     (`l.width = r.width ∧ l.signed = r.signed`), faulting with `.unsupported`
     on mismatched types.
   - Wrapping `.add`, `.sub`, and `.mul` wrap modulo $2^{\text{bitWidth}}$;
     `.addUnchecked`, `.subUnchecked`, and `.mulUnchecked` fault with
     `.undefined` when the mathematical result falls outside the target signed
     or unsigned range.
   - `.div` and `.rem` fault with `.undefined` on division/remainder by zero and
     on signed `INT_MIN / -1` and `INT_MIN % -1`.
   - Shift operators (`.shl`, `.shr`, `.shlUnchecked`, `.shrUnchecked`) accept
     any integer RHS width and signedness, mask the shift amount modulo
     `l.width.bitWidth`, perform arithmetic right shift on signed `l`, and fault
     with `.undefined` on `.shlUnchecked`/`.shrUnchecked` when `r.toInt < 0` or
     `r.toInt ≥ l.width.bitWidth`.
   - `UnOp.not` complements booleans and bitwise-inverts integers; `UnOp.neg`
     wraps signed integers (`-INT_MIN == INT_MIN`) and faults with
     `.unsupported` on unsigned integers or booleans.
5. **Terminator evaluation and block-bounds checking (`evalTerminator`):**
   - `.goto target` and `.switchInt discr targets` update `frame.blockIdx :=
     target, stmtIdx := 0` (with `.switchInt` also storing the post-discriminant
     `localsAfterDiscr` into the frame). Target basic-block existence is checked
     once at the start of the next step in `evalStep` (faulting with
     `.unsupported` if `body.basicBlocks[frame.blockIdx]? = none`), matching
     `ControlFlow.goToBlock` and `Step.step` in `lean-miri`.
   - `.return_` faults with `.unsupported` if `bb.cleanup` is `true`, returns
     `.done (.returned ⟨retVal, callerMem⟩)` if `frame.locals[0]` is `.live
     (some retVal)`, and faults with `.undefined` if `_0` is `.dead` or
     uninitialized (`.live none`).
   - `.unreachable` faults with `.undefined`.

---

## 5. Correspondence Theorem, Step Budgets, and Verification Layer

### 5.1 Step-Budget Quantification (`maxSteps`)

In `lean-miri`, `ExecutionMachine.step` executes a single interpreter step (via
`Step.step (stepHooks cfg limits) c`, clearing `pendingMoveDeinit` and
`pendingMoveDeinits` before and after the step), while `ExecutionMachine.run`
enforces the outer step budget `limits.maxSteps`. In `Trusted.Correspondence`,
`evalRefStep` mirrors that step-budget check around `ExecutionMachine.step`: at
the start of each step it checks `rs.stepsExecuted < rs.maxSteps`, returning
`.exhaustedStepLimit` if the budget is reached and otherwise calling
`ExecutionMachine.step` and incrementing `stepsExecuted := rs.stepsExecuted +
1`.

To keep `Trusted.Correspondence` maximally auditable without resetting step
counters between transitions, `initRefState` takes `maxSteps : Nat` as an
explicit parameter (`stepsExecuted := 0, maxSteps := maxSteps`), and
`RefReaches` chains `RefStep` transitions completely unmodified:

```lean
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail : RefReaches rp rs₁ rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReaches rp rs₁ rs₃

def RefReachesOutcome (rp : RefProg) (q : Query) (maxSteps : Nat)
    (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out
```

`RefWellFormed`, `RefBehavior`, and `RefDiverges` then quantify over
`maxSteps : Nat` according to their polarity:

```lean
def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs →
        ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

def RefBehavior (rp : RefProg) (q : Query) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)

def RefDiverges (rp : RefProg) (q : Query) : Prop :=
  ∃ rs₀ : RefState, initRefState rp q 0 = .ok rs₀ ∧
    ∃ trace : Nat → RefState,
      trace 0 = rs₀ ∧
      ∀ n : Nat,
        RefStep rp
          { trace n with stepsExecuted := n, maxSteps := n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := n + 1, maxSteps := n + 1 })
```

- In `RefWellFormed rp q`, quantifying universally over `∀ maxSteps : Nat`
  asserts that no finite execution prefix of any length ever reaches `.ub` or
  `.blocked` (treating `.exhaustedStepLimit` as the step-budget horizon rather
  than a program fault).
- In `RefBehavior rp q out`, quantifying existentially over `∃ maxSteps : Nat`
  asserts that there exists a finite step budget large enough (specifically
  `maxSteps := n + 1` for an $n$-step trace in $M_{\text{anneal}}$) for
  `lean-miri` to run from `stepsExecuted = 0` to `.returned out`.
- In `RefDiverges rp q`, a single coherent infinite state stream `trace : Nat →
  RefState` starts at `trace 0 = rs₀` (`initRefState rp q 0 = .ok rs₀`), and at
  every step `n`, `trace n` (with step budget `maxSteps := n + 1` so the step
  limit does not fire at step `n`) transitions via `RefStep` to `trace (n + 1)`.
  Quantifying `∃ trace : Nat → RefState` outside `∀ n : Nat` forces a single
  connected infinite execution path rather than allowing different finite
  branches at different horizons `n`.

### 5.2 Correspondence, Fault-Equivalence, and Move-Deinit Wiring Theorems

`Trusted.Correspondence` states three top-level claims: correspondence for
well-formed programs, unconditional bidirectional fault equivalence, and the
vendored `ExecutionMachine` move-deinitialization wiring contract:

```lean
def CorrespondenceClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
      RefWellFormed (encodeProg p) q ∧
      (∀ out : TerminalOut,
        Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
      (Diverges p q ↔ RefDiverges (encodeProg p) q)

def FaultEquivalenceClaim : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

def MiriMoveDeinitWiringClaim : Prop :=
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits)
      (c : C)
      (state : Miri.Interpreter.MachineHooks.State K U),
    Miri.Interpreter.ExecutionMachine.step cfg limits c state =
      let (state', out) := Miri.Interpreter.Step.step
        (Miri.Interpreter.ExecutionMachine.stepHooks cfg limits) c
        { state with
          machine := {
            state.machine with
            pendingMoveDeinit := false
            pendingMoveDeinits := Array.empty
          } }
      ( { state' with
          machine := {
            state'.machine with
            pendingMoveDeinit := false
            pendingMoveDeinits := Array.empty
          } },
        out )) ∧
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits),
    cfg.deinitMovedPlace = true →
    (Miri.Interpreter.ExecutionMachine.withValidation
        cfg limits).access.deinitMovedPlace = true ∧
    (Miri.Interpreter.ExecutionMachine.operandHooks
        cfg).deinitMovedPlace = true) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame : Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = false →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame frame₁ frame₂ :
        Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state state₁ : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (imm : Miri.Interpreter.Immediate Prov)
      (layout : Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = true →
    Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩ →
    frame₁.replaceLocalValue localId
        (.live (if layout.layout.isZst then .immediate imm
          else .immediate .uninit)) =
      .ok frame₂ →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      ⟨frame₂, state₁, .ok ⟨.immediate imm, layout⟩⟩) ∧
  (∀ {K U : Type}
      (m : Miri.Interpreter.MachineHooks.MachineState K U)
      (mplace : Miri.Interpreter.MemPlace Miri.Memory.Provenance)
      (isMove : Bool),
    (Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit
      (Miri.Interpreter.MachineHooks.recordPendingMoveDeinit m mplace
        isMove)).2 = isMove) ∧
  (∀ {P S C E Other Extern FnABI ArgABI : Type}
      (h : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI)
      (choice : C)
      (place : Miri.Interpreter.MPlaceTy P)
      (snap : Miri.Interpreter.OpTy P),
    Miri.Interpreter.FnArg.copyFnArg (.InPlace place (some snap)) = snap ∧
    Miri.Interpreter.Call.deinitInPlaceArg h choice place (some snap) =
      Bind.bind (h.restoreInPlaceMovedBytes choice snap place)
        (fun _ => h.deinitInPlaceArgument choice place))
```

where `faultToRefOutcome .undefined = .ub` and
`faultToRefOutcome .unsupported = .blocked`. `Anneal.MirCorrespondenceProof`
proves all three with zero `sorry`. Its theorems `anneal_corresponds_to_miri p
q` and `reachesResult_fault_iff_refReachesOutcome p q k` state the
correspondence and fault-equivalence bodies, including the bidirectional
behavior and divergence clauses, for fixed arguments, and
`correspondence_claim_holds : CorrespondenceClaim`,
`fault_equivalence_claim_holds : FaultEquivalenceClaim`, and
`miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim` generalize
them over all arguments.

On Day 1, both $M_{\text{anneal}}$ and $M_{\text{ref}}$ are deterministic
(`ValidChoice _ _ c := c = 0` and `ValidRefChoice _ _ c := c = 0`), so there is
at most one execution path from `(p, q)` and existential quantification in
`CorrespondenceClaim` and `FaultEquivalenceClaim` is identical to per-execution
coupling. When Phase 2 introduces nondeterministic choices (such as base-address
allocation draws `c : Choice` along a choice trace `choices : List Choice`),
comparing aggregate behavior sets, existential divergence predicates, or
existential fault sets across unrelated branches would allow one machine to
return (or reach `.undefined`/`.ub`) on branch $c_1$ and diverge (or reach
`.unsupported`/`.blocked` or a different return value) on branch $c_2$ while the
other machine permutes those outcomes across $c_1$ and $c_2$. Phase 2 therefore
indexes finite terminating and faulting executions along a shared finite choice
trace `choices : List Choice`, and diverging executions along a shared infinite
choice stream `choiceStream : Nat → Choice` (or a total, surjective,
outcome-preserving choice-trace relation when $M_{\text{anneal}}$
over-approximates):

```lean
def CorrespondenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
      RefWellFormed (encodeProg p) q ∧
      (∀ (choices : List Choice) (out : TerminalOut),
        BehaviorAtChoices p q choices out ↔
          RefBehaviorAtChoices (encodeProg p) q choices out) ∧
      (∀ (choiceStream : Nat → Choice),
        DivergesAtChoices p q choiceStream ↔
          RefDivergesAtChoices (encodeProg p) q choiceStream)

def FaultEquivalenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query) (choices : List Choice) (k : FaultKind),
    ReachesResultAtChoices p q choices (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeAtChoices (encodeProg p) q choices maxSteps
          (faultToRefOutcome k)
```

so that every nondeterministic execution branch is coupled across normal
returns, unwinds, divergence, and fault classifications in both models.

Each conjunct of `CorrespondenceClaim` closes a distinct gap:

- **`RefWellFormed (encodeProg p) q`** transfers UB-freedom: no finite
  execution prefix in $M_{\text{ref}}$ reaches `.ub` or `.blocked`.
- **Forward simulation** (the `→` direction of the behavior equivalence)
  shows that every terminal behavior of $M_{\text{anneal}}$ is one that
  $M_{\text{ref}}$ permits.
- **Backward simulation** (the `←` direction) shows that $M_{\text{ref}}$
  has no terminal behavior that $M_{\text{anneal}}$ lacks. This is the
  direction that sound specification transfer requires: without it, once a
  valid choice (such as an allocation address) can affect a returned value or
  a branch, `SatisfiesPost` could prove a postcondition over
  $M_{\text{anneal}}$'s behaviors while another permitted reference execution
  violates it.
- **Divergence equivalence** (`Diverges p q ↔ RefDiverges (encodeProg p) q`)
  makes termination versus divergence observable. Terminal behaviors and
  faults alone cannot distinguish two machines that agree on every finite
  outcome while only one of them also permits an infinite execution.

### 5.3 Bijective Simulation Invariant (`SimulationInv`)

Because both $M_{\text{anneal}}$ and $M_{\text{ref}}$ deinitialize moved locals
in lockstep via `liveUninitSlot` and pre-cache local types via
`zipRefLocals`, the simulation relation `SimulationInv p s rs` in
`Anneal.MirCorrespondenceProof` requires no slack or ghost state and pins the
entire `RefState` structure (up to the explicit step counters `stepsExecuted`
and `maxSteps`):

```lean
def liftFrame (bodyLocals : List MirTy) (f : FrameState) : RefFrameState :=
  { defId := f.defId
    blockIdx := f.blockIdx
    stmtIdx := f.stmtIdx
    locals := zipRefLocals bodyLocals f.locals
    returnContinuation := false }

def FrameSimInv (p : Program) (f : FrameState) (rf : RefFrameState) : Prop :=
  ∃ body : Body,
    MirSemantics.getElem? p.bodies f.defId = some body ∧
    f.locals.length = body.locals.length ∧
    rf = liftFrame body.locals f

def entryRetTy? (p : Program) : Option MirTy :=
  match MirSemantics.getElem? p.bodies p.entryDefId with
  | some body => MirSemantics.getElem? body.locals 0
  | none => none

def SimulationInv (p : Program) (s : State) (rs : RefState) : Prop :=
  ∃ f : FrameState, ∃ rf : RefFrameState, ∃ retTy : MirTy,
    s.frames = [f] ∧
    rs.frames = [callerSentinelFrame retTy, rf] ∧
    rs.callerMem = s.callerMem ∧
    entryRetTy? p = some retTy ∧
    FrameSimInv p f rf
```

`SimulationInv` constrains every semantic field of `s` and `rs` (`frames` and
`callerMem`, up to the explicit step counters `rs.stepsExecuted` and
`rs.maxSteps`) and embeds each `RefState` into `vendor/lean-miri`'s
`ExecutionState` with `pendingMoveDeinits := []`, canonical empty Day 1 memory
allocations, and deterministic frame metadata (`returnPlace := ⟨0, #[]⟩`,
`unwindAction := .Unreachable`). Because `ExecutionMachine.step` clears
`pendingMoveDeinits := []` at the completion of every step, no leftover
pending-deinitialization entry or hidden machine state can persist between
steps. Pinning `retTy` to the entry body's return-place type makes the sentinel
frame a function of `p` alone and keeps `SimulationInv` a total bijection at
fixed step counters:

```lean
theorem state_unique_of_simulationInv
    (h₁ : SimulationInv p s₁ rs) (h₂ : SimulationInv p s₂ rs) :
    s₁ = s₂

theorem refState_unique_of_simulationInv
    (h₁ : SimulationInv p s rs₁) (h₂ : SimulationInv p s rs₂)
    (h_steps : rs₁.stepsExecuted = rs₂.stepsExecuted)
    (h_max : rs₁.maxSteps = rs₂.maxSteps) : rs₁ = rs₂
```

### 5.4 Fuel-Bounded Verification Layer (`Anneal.MirWp`) and Canaries

To let per-function proofs in `theory/` and generated crate obligations
discharge `WellFormed`, `Behavior`, and `SatisfiesPost` by symbolic
computation, `Anneal.MirWp` defines a single fuel-bounded weakest-precondition
recursor (`wpOutcomeState`) over `evalStep`:

```lean
def wpOutcomeState (p : Program)
    (onDone : TerminalOut → Prop) (onFault : FaultKind → Prop) :
    Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
      (∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step s' => wpOutcomeState p onDone onFault fuel s'
        | .done out => onDone out
        | .fault k => onFault k
```

Instantiating `wpOutcomeState` with `onFault := fun _ => False` yields `wpProg`
(for proving `SatisfiesPost p q post` and
`∃ out, Behavior p q out ∧ post out` via `wellFormed_and_spec_of_wp`), and
instantiating it with `onDone := fun _ => False` and
`onFault := (· = expected)` yields `wpFaultProg` (for proving negative fault
canaries via `reaches_fault_and_exclusive_of_wpFault`). Both core soundness
theorems discharge exact parameterized propositions defined in
`Trusted.MirSemantics`:

```lean
def WpSoundnessClaim
    (wp : Program → Query → Nat → (TerminalOut → Prop) → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (post : TerminalOut → Prop),
    wp p q fuel post →
      SatisfiesPost p q post ∧ ∃ out : TerminalOut, Behavior p q out ∧ post out

def WpFaultSoundnessClaim
    (wpFault : Program → Query → Nat → FaultKind → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (fuel : Nat) (expected : FaultKind),
    wpFault p q fuel expected →
      ReachesResult p q (.fault expected) ∧
      (∀ k : FaultKind, k ≠ expected →
        ¬ ReachesResult p q (.fault k)) ∧
      (∀ out : TerminalOut, ¬ ReachesResult p q (.done out)) ∧
      ¬ WellFormed p q
```

`Anneal.MirWp` (Pass 1) and `Anneal.MirCorrespondenceProof` (Pass 2) include
kernel-checked non-vacuity and parameter-boundary canary theorems that exercise
all three outcome poles, every supported Day 1 MIR statement, rvalue,
terminator, unary and binary operator, all six integer widths (`i8`, `i16`,
`i32`, `i64`, `i128`, `isize`) in signed and unsigned modes, and runtime move
semantics across both $M_{\text{anneal}}$ and $M_{\text{ref}}$. All concrete
canary `Program` fixtures (`prog*`) and their `*Claim : Prop`
definitions live in the human-audited trusted gating modules
(`Trusted.MirSemantics` in `trusted/lean/` and `Trusted.Correspondence` in
`trusted/correspondence/`), whose transitive constant cones are forbidden by
`TrustedBoundary.lean` from referencing any `Anneal.*` declaration, and
`TrustedBoundary.lean` (`verifyMirWpCoreTheorems` and
`verifyCorrespondenceClaims`) verifies that each exported theorem in
`Anneal.MirWp` and `Anneal.MirCorrespondenceProof` has a type syntactically
equal to the corresponding `Trusted.*Claim` constant, so an untrusted edit to
`theory/` or `correspondence/` cannot weaken any canary program or expected
outcome.

The Pass 1 canaries in `Anneal.MirWp` check $M_{\text{anneal}}$ directly:

- **`canary_positive_add_anneal`:** `_0 = copy _1 + copy _2; return`
  (`30u32 + 12u32`) is `WellFormed` and returns `42u32`.
- **`canary_positive_empty_unit_fn`:** `fn empty() { return }` (`_0 : ()`) is
  `WellFormed` and returns `()`.
- **`canary_positive_stmts_and_cf_anneal`:** Exercises `StatementKind.nop`,
  `StatementKind.storageLive`, `StatementKind.storageDead` (followed by
  re-allocating with `storageLive` and initializing), `TerminatorKind.goto`,
  and `TerminatorKind.switchInt` across both a matched branch arm and the
  `otherwise` fallback arm, proving `WellFormed` and expected return values.
- **`canary_positive_unop_anneal`:** Exercises `UnOp.not` on `bool` (`!true =
  false`, `!false = true`), `UnOp.not` on integers (`!0x0fu8 = 0xf0u8`), and
  `UnOp.neg` on signed integers (`-42i32 = -42i32` and wrapping `-INT_MIN ==
  INT_MIN` on `i8`).
- **`canary_positive_all_binops_anneal`:** Exercises every supported `BinOp`
  variant at boundary values: wrapping `.add`, `.sub`, `.mul` (including
  overflow wrapping modulo $2^W$), in-bounds `.addUnchecked`, `.subUnchecked`,
  `.mulUnchecked`, `.div`, `.rem`, bitwise `.bitXor`, `.bitAnd`, `.bitOr`,
  shifts `.shl` and `.shr` (including shift amounts $\ge W$ masked modulo $W$
  and arithmetic right shift on negative signed integers), `.shlUnchecked` and
  `.shrUnchecked` at maximum valid shift (`W - 1`), and all six comparisons
  (`.eq`, `.ne`, `.lt`, `.le`, `.gt`, `.ge`) on signed integers, unsigned
  integers, and booleans.
- **`canary_positive_all_int_widths_anneal`:** Exercises all six `IntWidth`
  variants (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`) in both signed and
  unsigned modes at their respective width boundaries (`MAX` wrapping to `0` on
  unsigned `.add` and `INT_MAX` wrapping to `INT_MIN` on signed `.add`).
- **`canary_negative_ub_div_zero_anneal`:**
  `_0 = copy _1 / const 0u32; return` reaches `.fault .undefined` (not
  `.unsupported`) and is not `WellFormed`.
- **`canary_negative_ub_signed_rem_overflow_i8`:**
  `_0 = copy _1 % copy _2; return` (`-128i8 % -1i8`) reaches
  `.fault .undefined` (not `.unsupported`) and is not `WellFormed`.
- **`canary_negative_ub_add_unchecked_overflow_u32`:** an unchecked `u32`
  addition (`BinOp.addUnchecked`) whose mathematical sum exceeds `u32::MAX`
  reaches `.fault .undefined` (not `.unsupported`) and is not `WellFormed`,
  whereas wrapping `.add` on the same operands wraps modulo $2^{32}$.
- **`canary_negative_ub_shift_unchecked_at_bitwidth_anneal`:**
  `BinOp.shlUnchecked` with shift amount equal to the bit width (`32` on `u32`)
  and `BinOp.shrUnchecked` with a negative signed shift amount (`-1i8`) each
  reach `.fault .undefined` (not `.unsupported`).
- **`canary_negative_ub_storage_dead_read_anneal`:** Reading an in-bounds local
  after `StatementKind.storageDead` reaches `.fault .undefined` (not
  `.unsupported`).
- **`canary_negative_ub_unreachable_anneal`:** Executing
  `TerminatorKind.unreachable` reaches `.fault .undefined` (not
  `.unsupported`).
- **`canary_negative_unsupported_anneal`,
  `canary_negative_unsupported_unsigned_neg_anneal`, and
  `canary_negative_ub_storage_dead_return_place_anneal`:**
  `StatementKind.unsupported`, `UnOp.neg` on an unsigned integer (`u32`), and
  `StatementKind.storageDead 0` on return place `_0` (matching
  `StackError.storageDeadReturnPlace`) reach `.fault .unsupported` (not
  `.undefined`) and are not `WellFormed`.
- **`canary_positive_enum_explicit_repr_anneal`,
  `canary_positive_zst_single_enum_anneal`, and
  `canary_negative_ub_enum_invalid_tag_and_uninit_anneal`:**
  Exercise fieldless enum encoded-tag constant decoding (`#[repr(u8)]` and
  signed `i8` -> `isize`), explicit-width `Rvalue.discriminant`, inhabited
  1-variant zero-sized enums (`EnumTagRepr.zeroSized`, `ConstLit.zeroSized`),
  invalid scalar enum tag UB, and uninitialized enum discriminant read UB.
- **`canary_crate_and_body_verified_anneal`:**
  Exercises `CrateTheorem`, `UnitTheorem`, `BodyVerified` (including
  `p.bodies[defId]` lookup binding, `isUnsafe` contract gating, and
  uninhabited `MirTy.never` parameter `BodyStaticAdmitted` non-vacuity), and
  empty-`bodies` / out-of-bounds `entryDefId` / duplicate-`identity` rejection.

The Pass 2 canaries in `Anneal.MirCorrespondenceProof` check both models:

- **`canary_D6_use_after_move_ub`:** `_2 = move _1; _0 = copy _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D7a_binop_copy_then_move_ok`:** `_0 = copy _1 + move _1; return`
  (`42u32`) is `WellFormed` and `RefWellFormed` and returns `84u32` in both.
- **`canary_D7b_binop_move_then_copy_ub`:** `_0 = move _1 + copy _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D7c_binop_move_then_move_ub`:** `_0 = move _1 + move _1; return`
  reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$.
- **`canary_D8_self_move_ok`:** `_1 = move _1; _0 = copy _1; return`
  (`42u32`) is `WellFormed` and `RefWellFormed` and returns `42u32` in both.
- **`canary_D9_move_unit_zst_ok`:** `_2 = move _1; _0 = copy _1; return`
  (`_1 : ()`) is `WellFormed` and `RefWellFormed` and returns `()` in both.
- **`canary_D10_add_unchecked_overflow_ub`:** on `(u32::MAX, 1)`,
  `_0 = AddUnchecked(_1, _2)` reaches `.fault .undefined` in $M_{\text{anneal}}$
  and `.ub` in $M_{\text{ref}}$, while wrapping `_0 = Add(_1, _2)` returns `0`
  in both.
- **`canary_D11_enum_discriminant_and_const_ok`,
  `canary_D12_zst_enum_move_and_discr_ok`, and
  `canary_D13_enum_invalid_tag_and_uninit_ub`:**
  Verify agreement between $M_{\text{anneal}}$ and $M_{\text{ref}}$
  (`Miri.Interpreter.Discriminant`) across explicit-repr and signed-tag
  fieldless enums, 1-variant zero-sized enums, invalid scalar enum tags, and
  uninitialized enum discriminant reads.

---

## 6. Phase 2 Roadmap and Deferred Design Decisions

### 6.1 Crossing the `forceAllocation` Boundary for Aggregates and Pointers

On Day 1, `Rvalue.aggregateTuple`, `Rvalue.ref`, `Rvalue.addressOf`, and
non-empty place projections (`place.projection ≠ []`) step to `.fault
.unsupported` in $M_{\text{anneal}}$ and `.blocked` in $M_{\text{ref}}$.

When Phase 2 adds support for tuples, field projections, and references/raw
pointers, it must address how `lean-miri` represents compound and address-taken
locals:

- In `lean-miri`, evaluating `Rvalue.Ref` or `Rvalue.AddressOf` on a local held
  as `LocalValue.live (.immediate imm)` invokes `Place.forceAllocation`
  (`Place.lean:160–194`), which dynamically allocates a fresh `AllocId` in
  `state.machine.memory`, serializes `imm` into bytes, and mutates the local
  slot in `frame.locals` from `.immediate imm` to `.indirect mplace`.
- Furthermore, `Rvalue.Aggregate` (`Rvalue.lean:245–293`) writes multi-field
  tuples into an in-memory `MPlaceTy` destination (calling `forceAllocation` on
  the destination local), whereas `ProjectionElem.Field`
  (`Place.lean:202–228`) can project over `.immediate (.scalar ..)` or
  `.immediate .uninit` only when the projected field has offset 0 and equal
  size (such as a 1-element newtype wrapper).

Two candidate representations remain open for Phase 2 adjudication:

1. **Option 1A (Mirror `forceAllocation` in $M_{\text{anneal}}$):**
   Equip $M_{\text{anneal}}$'s `LocalSlot` with both immediate values and
   in-memory stack allocations (`LocalSlot.indirect mplace`), allocating a block
   in `Memory` whenever a tuple is constructed or a local's address is taken.
   Option 1A keeps `SimulationInv` a near-identity bijection over `LocalSlot`
   and `Memory`, at the cost of routing tuple accesses in `wpProg` proofs
   through byte-level memory reads and writes.
2. **Option 1B (Pure value trees in $M_{\text{anneal}}$ until address-taken):**
   Keep non-address-taken tuples as pure `Val.tuple` trees inside `LocalSlot` in
   $M_{\text{anneal}}$ (allocating in `Memory` only upon `Rvalue.ref` or
   `Rvalue.addressOf`), while `SimulationInv` relates each pure `Val.tuple`
   local in $M_{\text{anneal}}$ to its `forceAllocation`-backed stack block in
   `lean-miri`'s `Memory` via an explicit disjointness and byte-decoding
   invariant. Option 1B keeps `wpProg` proofs over non-address-taken tuples
   purely structural, at the cost of a relational local-to-memory injection in
   `SimulationInv`.

**Adjudication trigger:** We defer choosing between Option 1A and Option 1B
until the first Phase 2 PR that enables `ProjectionElem.field`,
`Rvalue.aggregateTuple`, or `Rvalue.ref` / `Rvalue.addressOf`. At that point, we
will benchmark whether keeping non-address-taken tuples as pure `Val.tuple`
trees simplifies `wpProg` proofs enough to repay the local-to-stack-memory
simulation invariant.

### 6.2 Supporting Constructs Unmodeled by `lean-miri`

On Day 1, `anneal_corresponds_to_miri` requires that `MiriRefMachine` models
every construct that $M_{\text{anneal}}$ models
(`WellFormed p q → RefWellFormed (encodeProg p) q`), ensuring that
`RefWellFormed` cannot vacuously excuse bugs via `.blocked`. This requirement
does not lapse as coverage grows. Supporting a Rust feature (such as a
compiler intrinsic or inline assembly construct) that upstream `lean-miri`
leaves unimplemented means extending the reference model, never exempting the
feature from correspondence while presenting it as correspondence-checked.
Two paths extend the reference model:

1. **Preferred path (extend `MiriRefMachine` hooks):** `lean-miri` already
   delegates intrinsics (`evalIntrinsic`), foreign calls (`callExtraFn`), place
   projections (`evalPlaceProjectionExtra`), and pointer casts (`intToPtr`,
   `ptrToInt`) to its `Machine` typeclass. Implementing the corresponding hook
   in `MiriRefMachine` preserves `anneal_corresponds_to_miri` without changing
   its statement.
2. **Fallback path (audited extension or second reference model):** If a
   construct hits a hardcoded `.blocked` branch inside `lean-miri` that cannot
   be routed through `Machine` hooks, we either extend `vendor/lean-miri/` with
   an audited patch suitable for upstreaming, pinned in `UPSTREAM_PIN.json`
   like the `deinitMovedPlace` patch, or compose a second, explicit reference
   model for that construct inside the correspondence TCB (Section 1.3).
   `CorrespondenceClaim` keeps its statement in either case.

---

## Appendix: Alternatives Considered and Rejected

### A.1 Reference Model and Move-Semantics Alternatives

#### MiniRust as a Standalone Reference Model

We considered formalizing [MiniRust](https://github.com/minirust/minirust) from
scratch as $M_{\text{ref}}$. MiniRust specifies runtime MIR semantics directly
(including deinitialization on `Operand::Move`), but it is written in prose and
`specr` (a Rust-like pseudocode DSL) with no existing Lean 4 mechanization.
Writing our own Lean 4 port of MiniRust and proving that $M_{\text{anneal}}$
refines that port would mean comparing two Anneal-authored models, losing the
independent bug-finding value of an external mechanization.

#### Aeneas / Charon LLBC as a Reference Model

We also considered using Aeneas or Charon's Low-Level Borrow Calculus (LLBC) as
$M_{\text{ref}}$. Aeneas translates safe, borrow-checked MIR into pure Lean 4
functions by *assuming* the input program is free of Undefined Behavior. Because
Anneal's primary goal is to verify `unsafe` Rust code (such as `zerocopy`) by
proving the absence of UB from operational semantics, a reference model that
assumes UB-freedom cannot serve as a ground-truth UB oracle.

#### Hybrid `lean-miri` + MiniRust Shadow Move Automaton

We evaluated keeping `vendor/lean-miri/` completely unmodified and defining a
hybrid reference model in `Trusted.Correspondence` that runs `lean-miri`'s
`ExecutionMachine.step` in lockstep with a declarative MiniRust move-tracking
mask (`RefState := MiriInterpState × List Bool`). Under this hybrid design,
every `Operand.move` clears the local's initialization bit in the shadow mask,
every `Operand.copy` or `Operand.move` checks the shadow mask (halting with
`.ub` if the local was previously moved), and every assignment or `StorageLive`
restores the bit.

While this lockstep product works cleanly on Day 1 (~45 lines of Lean for
unprojected scalar locals), it does not scale to Phase 2:

- Partial field moves (`_1.0 = move _2.1`) deinitialize only the byte sub-range
  of field `1` inside `_2`, leaving `_2.0` initialized.
- Raw pointers aliasing a local (`_p = &raw const _1; _2 = move _1; _3 = *_p`)
  observe move deinitialization through memory addresses (`AllocId`, `Offset`)
  rather than syntactic `LocalId`s.
- Copying a partially moved `MaybeUninit<T>` copies the underlying `.uninit`
  bytes in `Memory` without faulting.

Tracking these cases in an external shadow automaton would require duplicating
`lean-miri`'s place-projection, layout-offset, and byte-level memory engine
inside `Trusted.Correspondence`. By contrast, the 10-file `deinitMovedPlace`
patch in [Section 2.4](#24-runtime-move-deinitialization) reuses `lean-miri`'s
existing `evalPlaceToOp` and `writeMemoryNoValidate choice .uninit` machinery
directly.

#### Eager `.indirect` Deinitialization in `evalOperand` vs. `OpTy.deinitOnRead`

When designing the `deinitMovedPlace` patch in `vendor/lean-miri/`, we also
evaluated two alternative ways to handle `Operand.indirect mplace`:

1. **Eager deinitialization inside `evalOperand`:** Deinitializing `mplace`
   immediately inside `OperandMachine.evalOperand` before returning `OpTy`
   fails because `evalOperand` returns `OpTy.indirect mplace` *by address*
   before the consumer (`PlaceMachine.readImmediate` or
   `Place.copyRuntimePlaceNoValidate`) reads the memory bytes. Deinitializing
   `mplace` inside `evalOperand` wipes the source bytes to `.uninit` before the
   consumer reads them, causing valid moves of indirect places to fault with
   `.invalidUninitBytes`.
2. **Adding `deinitOnRead : Bool := false` to `structure OpTy`:** Carrying the
   deferred deinitialization bit as a third field on `OpTy` in `Projection.lean`
   breaks 2-argument anonymous constructor applications (`⟨op, layout⟩`)
   across 174 files in `vendor/lean-miri/Miri/`. Recording
   `pendingMoveDeinit : Bool := false` on `MachineHooks.MachineState` and
   `takePendingMoveDeinit : PlaceM S Bool := pure false` on `PlaceHooks` avoids
   touching `OpTy.mk` while compiling cleanly across all 53 reverse-dependent
   modules in the `ExecutionMachine` closure.

#### Unmodified `lean-miri` with a Non-Bijective `SimulationInv` Carve-Out

We also analyzed leaving `lean-miri` unmodified (so `Operand.move` does not
deinitialize in $M_{\text{ref}}$) while deinitializing moved places in
$M_{\text{anneal}}$ and relaxing the untrusted `SimulationInv` so that a local
slot can be `.live none` in $M_{\text{anneal}}$ while remaining `.live (some v)`
in $M_{\text{ref}}$.

Mechanizing this approach revealed four structural flaws:

1. **Ghost move sets collapse to arbitrary `.live none` slack:**
   Adding an existential ghost set `movedSet : Finset LocalId` inside the
   untrusted `SimulationInv` (allowing `annealSlot = .live none` while
   `miriSlot = .live (some v)` only when `id ∈ movedSet`) is logically
   equivalent (`↔`) to allowing `annealSlot = .live none` whenever `miriSlot =
   .live (some v)`. Because `SimulationInv` is existentially quantified inside
   the untrusted proof, the proof can always instantiate `id ∈ movedSet` as
   `decide (annealSlot = .live none ∧ miriSlot ≠ .live none)`, regardless of
   whether `id` was deinitialized by `Operand.move` or by a bug.
2. **Blindness to missing move deinitialization in $M_{\text{anneal}}$:**
   Because `anneal_corresponds_to_miri` is gated on `WellFormed p q`, if a bug
   or future refactor in $M_{\text{anneal}}$ forgets to deinitialize on
   `Operand.move`, both $M_{\text{anneal}}$ and unmodified `lean-miri` treat
   `move` as `copy`, and `anneal_corresponds_to_miri` still compiles without
   error.
3. **Blindness to wrong-local deinitialization and reversed operand order:**
   If $M_{\text{anneal}}$ accidentally deinitializes local `j ≠ i` on
   `move _i`, or evaluates `BinOp(lhs, rhs)` right-to-left instead of
   left-to-right, any execution that reads the extra `.live none` local faults
   in $M_{\text{anneal}}$—making the premise `WellFormed p q` false and
   vacuously satisfying `anneal_corresponds_to_miri`.
4. **Phase 2 falsification on `MaybeUninit<T>` and padding copies:**
   In Phase 2, copying `MaybeUninit<u8>` (or struct padding bytes) copies
   `.uninit` bytes without faulting (`WellFormed p q` holds). If `_1 :
   MaybeUninit<u8>` holds `init 42`, is moved via `_2 = move _1` (setting `_1`
   to `uninit` in $M_{\text{anneal}}$ while leaving `_1` as `init 42` in
   unmodified `lean-miri`), and is then copied and returned via `_0 = copy _1;
   return`, $M_{\text{anneal}}$ returns `uninit` while unmodified `lean-miri`
   returns `init 42`. On such a program, `WellFormed p q` holds, but `Behavior p
   q out → RefBehavior (encodeProg p) q out` is mathematically false.

### A.2 Type Representation and Codec Alternatives

#### Nominal `TyId` Indirection Inside `Trusted.MirModel`

We considered mirroring `lean-miri`'s `TyId := Nat` index table inside
`Trusted.MirModel` (`Program.types : List MirTy`). We rejected this because a
nominal `TyId` table inside $M_{\text{anneal}}$ introduces two classes of
representation artifacts:

1. Programs can contain out-of-bounds `TyId`s (`tyId ≥ p.types.length`), forcing
   every type lookup in `Trusted.MirSemantics` and `Anneal.MirWp` to handle
   missing-type faults.
2. A program's `types` table can list the same structural `MirTy` (such as
   `u32`) at two distinct indices (`TyId 0` and `TyId 1`). In `lean-miri`,
   `assertSameType` and `assertRvalueLayout` compare nominal `TyId`s
   (`0 ≠ 1`), whereas structural type checks compare `MirTy` values
   (`u32 = u32`), breaking correspondence unless every `Program` carries an
   extra canonical-table well-formedness side condition. Carrying `MirTy` by
   value in `Trusted.MirModel` and deduplicating during `encodeProg` eliminates
   both issues by construction.

#### Unseeded Type Collection (`initTypeTable := []`)

We considered starting `collectProgTypes` from an empty type table `[]` rather
than `initTypeTable := [.unit, .bool, .int .isize false]`. We rejected this
because `lean-miri`'s `TerminatorKind.SwitchInt` evaluator unconditionally calls
`h.boolLayout` even when switching on an integer discriminant in a program that
never mentions `MirTy.bool` syntactically. Pre-seeding `initTypeTable` ensures
those ambient layout hooks always succeed.

### A.3 State Machine and Step-Budget Alternatives

#### Synthetic `State.entry q` Constructor Inside `State`

We considered including `State.entry (q : Query)` as a constructor of `State` so
that `evalStep p c (.entry q)` performs entry initialization as the first step
of `Reaches`. We rejected this because `lean-miri` performs entry frame
construction inside `initRefState` *before* the first call to
`ExecutionMachine.step`. Making entry initialization a transition step in
$M_{\text{anneal}}$ created a 1-step stuttering offset on every trace and
prevented `initState` and `initRefState` from corresponding directly.

#### Fixed Constant Step Budget (`maxSteps := K`)

We considered initializing `initRefState` with a fixed large constant step
budget (such as `maxSteps := 2^64`). We rejected this because `Behavior p q out`
in $M_{\text{anneal}}$ is an unbounded finite-step reachability predicate: for
any fixed constant $K$, there exists a terminating loop of length $K + 1$ that
returns `out` in $M_{\text{anneal}}$ but halts with `.exhausted .stepLimit` in
$M_{\text{ref}}$, making `Behavior p q out → RefBehavior (encodeProg p) q out`
unprovable.

#### Resetting `stepsExecuted := 0` Inside `RefStep`

We also considered initializing `limits.maxSteps := 1` and resetting
`stepsExecuted := 0` before each single-step call inside `RefStep`. While
mathematically equivalent to quantifying over `maxSteps : Nat`, resetting
`stepsExecuted` inside `RefStep` mutates the `RefState` returned by
`evalRefStep` between steps. Quantifying over `maxSteps : Nat` in
`RefWellFormed` (`∀ maxSteps`) and `RefBehavior` (`∃ maxSteps`) allows
`RefReaches` to chain the exact states returned by `evalRefStep` without
modification.

### A.4 Local Initialization and Evaluation-Order Alternatives

#### Initializing `MirTy.unit` Locals to `.live none`

We considered initializing all non-argument locals (including `_0 : ()`) to
`.live none` at function entry and after `.storageLive` or `Operand.move`. We
rejected this because `rustc` emits `fn empty() { return }` without an explicit
`_0 = const ()` assignment, and in `lean-miri`, `.immediate .uninit` is already
the valid runtime representation of the 0-byte unit type `()`. Initializing
`.unit` locals to `.live none` caused `fn empty() { return }` to fault with
`.undefined` in $M_{\text{anneal}}$ while succeeding in `lean-miri`.

#### Single-Stage `evalOperand` Checking Initialization Before Types

We considered a single `evalOperand` function that immediately faults with
`.undefined` whenever a local slot is `.live none`, before the caller checks
whether the operand's static type is supported by the enclosing operation. We
rejected this because `lean-miri` evaluates operands in two stages:
`OperandMachine.evalOperand` constructs an `OpTy` (carrying `.immediate .uninit`
together with its static `LayoutAndTy`), and the consumer then checks static
type compatibility (`BackendRepr.Scalar` in `readImmediate` or `src.layout.ty ==
dest.layout.ty` in `copyRuntimePlaceNoValidate`) *before* validating that the
runtime value is initialized. Splitting operand evaluation into
`evalOperandToSlot` and `evalPrimitiveOperand` / `evalRvalue` matches
`lean-miri`'s exact fault precedence on ill-typed uninitialized locals.
