<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Multi-Step MIR and Toolchain Architecture

> **Note:** Anneal is under active development. Parts of the design and
> architecture described in this document are not yet implemented or may be
> implemented differently; this document may be aspirational or stale relative
> to the codebase.

Anneal verifies Rust crates by extracting their Mid-level Intermediate
Representation (MIR) from `rustc` and proving verification obligations over
that MIR in the Lean 4 theorem prover. Designing this pipeline requires
balancing **Trusted Computing Base (TCB) auditability** against **proof
ergonomics and stability**:

- **Auditability pulls toward raw `rustc` MIR and simple, first-order code:**
  Any transformation performed inside the Rust extractor happens outside the
  Lean kernel. If the extractor rewrites control flow, desugars projections, or
  synthesizes Lean `Prop` formulas in Rust, a bug in that Rust code can silently
  alter what is being proved. Likewise, if the Lean semantics inside `trusted/`
  rely on tactic blocks, well-founded recursion proofs, or mutual inductive
  types, Lean's elaborator generates complex auxiliary definitions in the
  compiled `.olean` environment. Keeping the TCB small and auditable requires a
  thin, purely syntactic Rust extractor and a transparent, tactic-free Lean
  semantic model.
- **Verification ergonomics and stability pull toward normalized MIR:**
  `rustc`'s `Runtime(PostCleanup)` MIR contains low-level control-flow chains,
  storage markers, and `nop` statements that are tedious to step through
  directly and can shift across compiler releases.

Anneal resolves this tension with a **three-stage MIR pipeline** split across
the repository's `trusted/` and `theory/` boundary:

1. **Stage 1 — Mechanical, First-Order Capture (`trusted/rustc-capture/`):** A
   thin `rustc_driver` wrapper transcribes `rustc`'s `Runtime(PostCleanup)` MIR
   and inline specification attributes 1-to-1 into a purely first-order Lean
   data module (`.anneal/Mir.lean`) and a fixed, crate-independent 8-line proof
   entrypoint (`.anneal/Proof.lean`), performing zero semantic normalization in
   Rust.
2. **Stage 2 — Flat Captured MIR & Reference Semantics
   (`trusted/lean/Trusted/`):** A tactic-free, fuel-bounded Lean AST and
   small-step operational semantics evaluate captured MIR over a flat,
   `BodyId`-indexed table (`Crate.bodies`) and a value-tree memory model with
   explicit uninitialized leaves (`MirVal.uninit`). Unmodeled Rust constructs
   are captured as explicit `.unsupported` nodes and fail closed in the
   semantics only when a verified obligation reaches them.
3. **Stage 3 — In-Place Verified Lowering & Compositional Proof Engine
   (`theory/Anneal/`):** Untrusted, kernel-checked passes in `theory/` normalize
   `MirBody` in place (`lowerBody : MirBody → MirBody`), prove a backward
   simulation (`lowerBody_simulates`) back to the Stage 2 semantics, and
   discharge `Trusted.CrateTheorem` compositionally per ADT and per function.

Because Stage 3 lives in `theory/`, is verified by `anneal-audit` in CI to be
pure and axiom-free, and proves its own soundness inside the Lean 4 kernel, all
control-flow normalization, compositional checkers, and symbolic execution
lemmas remain **outside the human-audited TCB**.

For related context, see:

- [`docs/design.md`](design.md) for Anneal's end-to-end user workflow,
  library-centric verification model, and incremental adoption.
- [`docs/trust-model.md`](trust-model.md) for how Anneal's CI enforces the
  boundary between `trusted/` and `theory/`.

## Architectural goals

Anneal's MIR pipeline is organized around six concrete goals:

1. **No semantic desugaring or formula synthesis in Rust:** Stage 1 maps
   `rustc` data structures directly to first-order Lean constructors. It never
   rewrites places or control flow, never filters out unverified items via
   duplicate semantic analyses in Rust, and never formats Lean propositions or
   per-function tactic scripts.
2. **Static, crate-independent `Proof.lean`:** Every crate receives the exact
   same 8-line `.anneal/Proof.lean` file stating `theorem verify_crate :
   Trusted.CrateTheorem Mir.crate := Anneal.proveCrate Mir.crate rfl`. No crate
   name, function name, or user annotation is ever interpolated into
   `Proof.lean`.
3. **Tactic-free, flat, and `opaque`-free `trusted/lean/`:** Stage 2 uses a
   flat `BodyId` table instead of mutual inductive types, uses explicit `Nat`
   fuel (`noncomputable`) instead of `partial` or `WellFounded.fix`, contains
   zero `by` tactic blocks (`SourceRole.trusted`), and contains zero dummy
   `opaque` constants.
4. **Syntax-total capture with demand-driven fail-closed semantics:** A real
   library crate often contains functions or types that use Rust features
   Anneal does not yet model. Stage 1 captures those constructs as explicit
   `.unsupported` AST nodes rather than aborting capture of the whole crate,
   while Stage 2 steps `.unsupported` to `.failed` (undefined behavior) if a
   verified obligation depends on it.
5. **In-place Stage 3 normalization without AST duplication:** Rather than
   duplicating `MirBody`, `Stmt`, `Rvalue`, and `MirVal` into a parallel AST
   hierarchy, Stage 3 normalizes `Trusted.MirBody` in place (`lowerBody`) and
   verifies functions compositionally.
6. **Source-span diagnostics:** Captured declarations, statements, and
   terminators carry Rust source `Span` metadata (`file`, `line`, `col`) so
   verification failures identify the exact Rust statement or assertion that
   could not be discharged.

## The three-stage MIR pipeline

```mermaid
flowchart TD
    subgraph Stage1 ["Stage 1: Mechanical Capture (trusted/rustc-capture/) — TCB"]
        RC["anneal-rustc-capture\n1-to-1 transcription of Runtime(PostCleanup) MIR,\ninline spec ASTs, TargetLayout, & Span"]
        FILES[".anneal/Mir.lean (first-order Mir.crate : Trusted.Crate)\n.anneal/Proof.lean (static 8-line verify_crate)"]
        RC --> FILES
    end

    subgraph Stage2 ["Stage 2: Captured MIR & Reference Semantics (trusted/lean/Trusted/) — TCB"]
        REF["Trusted/Refinement.lean & StepResult.lean\nAbstracts, Compiles, VerificationResult, Obligation.assumed"]
        AST["Trusted/MirAst.lean\nFlat BodyId-indexed Crate.bodies, Place, MirBody, TCBItem"]
        SEM["Trusted/MirSemantics.lean\nFuel-bounded semantics, MirVal.uninit, Place lenses,\nConstsTotal, & Trusted.CrateTheorem"]
        REF --> AST --> SEM
    end

    subgraph Stage3 ["Stage 3: Lowering & Compositional Verifier (theory/Anneal/) — Untrusted"]
        LOW["Anneal/Lowering.lean\nIn-place lowerBody : MirBody -> MirBody\n& lowerBody_simulates"]
        LEM["Anneal/MirLemmas.lean\nCompositional per-ADT & per-function checker,\ninline/modular/assumed calls, & execNormal_join"]
        LOW --> LEM
    end

    FILES -->|"Instantiates"| AST
    SEM -->|"Defines obligation"| LEM
    LEM -->|"Anneal.proveCrate Mir.crate rfl"| SEM
```

### Stage 1: Mechanical, first-order `rustc` capture (`trusted/rustc-capture/`)

`trusted/rustc-capture/` links against `rustc_driver` and `rustc_middle` to
extract the compiled crate's `Runtime(PostCleanup)` MIR, layout facts, and
inline specification attributes into `.anneal/Mir.lean` and
`.anneal/Proof.lean`.

#### 1-to-1 transcription without Rust-side desugaring

Stage 1 translates each `rustc_middle::mir` construct directly into its
corresponding constructor in `Trusted/MirAst.lean`:

- **Places and projections (`Place`, `PlaceElem`):** A MIR `Place` is emitted
  directly as `(LocalId, List PlaceElem)` with `.deref` and `.field idx`
  projection elements. Stage 1 never pattern-matches projection chains in Rust
  to synthesize special-case rvalues.
- **Operands and rvalues (`Operand`, `Rvalue`):** `Operand::Copy(p)`,
  `Operand::Move(p)`, and `Operand::Constant(...)` map 1-to-1 to
  `Operand.copy`, `Operand.move`, and `Operand.constVal` / `Operand.constParam`.
  `Rvalue::Use`, `Rvalue::Ref`, `Rvalue::RawPtr`, `Rvalue::BinaryOp`,
  `Rvalue::Aggregate`, and `Rvalue::Cast(Transmute)` map directly to `Rvalue`
  constructors.
- **Statements and terminators (`Stmt`, `Terminator`):** `Assign`,
  `StorageLive`, `StorageDead`, `PlaceMention`, and `Nop` map 1-to-1 to `Stmt`;
  `Return`, `Goto`, `SwitchInt`, `Call`, and `Assert` map 1-to-1 to
  `Terminator`.

Because Stage 1 performs no control-flow restructuring or expression
simplification, a human reviewer can audit each arm in
`trusted/rustc-capture/src/extract.rs` directly against the cited `rustc`
definition.

#### First-order `.anneal/Mir.lean` and static `.anneal/Proof.lean`

Stage 1 separates the crate-specific data payload from the proof entrypoint:

- **`.anneal/Mir.lean` is 100% first-order algebraic data:** `Mir.lean` defines
  `def crate : Trusted.Crate := ...` using only constructors, natural numbers,
  booleans, strings, and lists. Inline Rust specifications
  (`#[anneal::requires]`, `#[anneal::ensures]`, `#[anneal::invariant]`,
  `#[anneal::trusted]`) are parsed into first-order specification AST
  constructors (`RequiresSpec`, `PostSpec`, `InvariantSpec`) inside `Mir.crate`
  and denoted into `Prop` by pure functions in `Trusted/MirSemantics.lean`.
  `rustc-capture` never emits raw Lean `Prop` syntax, quantifiers, or tactic
  blocks.
- **`.anneal/Proof.lean` is fixed and crate-independent:** Regardless of what
  the Rust crate contains, `rustc-capture` writes the exact same 8-line file:

  ```lean
  prelude
  import Trusted
  import Mir
  import Anneal.MirLemmas

  namespace Proof
  theorem verify_crate : Trusted.CrateTheorem Mir.crate :=
    Anneal.proveCrate Mir.crate rfl
  end Proof
  ```

  Because `Proof.lean` contains no crate-derived strings or identifiers, an
  untrusted crate annotation cannot alter the theorem statement or inject Lean
  commands into the proof script.

#### Syntax-total capture with `.unsupported` nodes

To support incremental verification inside existing libraries, Stage 1 is
**syntax-total** over valid Rust crates. When `rustc-capture` encounters a Rust
type, ADT definition, constant, rvalue, statement, terminator, or function body
outside the currently modeled subset, it emits an explicit `.unsupported` AST
constructor in `Mir.lean` rather than aborting capture of the whole crate or
running bespoke semantic rejection passes in Rust.

All semantic gating happens fail-closed in `Trusted/MirSemantics.lean`:

- If a verified function's specification, layout calculation, or reachable
  execution path encounters `.unsupported`, evaluation steps to `.failed`
  (undefined behavior), making `Trusted.CrateTheorem` unprovable.
- If a verified function calls an unverified or `.unsupported` function body,
  the call is permitted only when the callee is either given an explicit
  modular contract (`TCBItem.assumedContract`) or explicitly waived in the
  crate's TCB ledger (`TCBItem.unverifiedFn`).
- Unverified functions in the same crate that are never called by verified code
  do not block verification of the functions in scope.

### Stage 2: Captured MIR and reference semantics (`trusted/lean/Trusted/`)

Stage 2 defines the verification framework and the Rust MIR reference semantics
in four tactic-free Lean modules under `trusted/lean/Trusted/`:

1. **`Trusted/Refinement.lean`:** Defines labeled transition systems (`Sem`),
   verification backward simulation (`Abstracts`), compiler forward simulation
   (`Compiles` and `ProductiveCompiles`), `Obligation`, `TrustPolicy`, and
   `VerificationResult`. Unproved assumptions (such as `rustc`'s compilation of
   MIR to machine code, assumed external contracts, or waived unverified
   functions) are represented uniformly via
   `def Obligation.assumed (id : Id) : Obligation Id := ⟨id, False⟩`, which can
   only be discharged in `VerificationResult` when `id` appears explicitly in
   the crate's audited `c.tcb` waiver list. This eliminates the need for dummy
   `opaque` target-language constants in the TCB.
2. **`Trusted/StepResult.lean`:** Defines bounded small-step fuel execution
   (`StepResult`, `Outcome`, and `ExecSteps`) with explicit `.continue`,
   `.terminated`, `.stuck`, `.failed` (undefined behavior), and `.outOfFuel`
   outcomes.
3. **`Trusted/MirAst.lean`:** Defines the first-order captured MIR data
   structures: `AdtId`, `BodyId`, `MirTy`, `Place` (`LocalId × List PlaceElem`),
   `Operand`, `Rvalue`, `Stmt`, `Terminator`, `MirBody`, `BodyDecl`
   (`BodyPayload` and `FnContract`), `TargetLayout`, `Span`, `TCBItem`, and
   `Crate`.
4. **`Trusted/MirSemantics.lean`:** Defines the small-step operational
   semantics, value-tree memory model (`MirVal`), place projection lenses,
   target layout and type-size predicates (`ValidTargetLayout`,
   `ValidTySizes`), post-monomorphization constant checks (`ConstsTotal`), ADT
   invariant admissibility (`AdmissibleAdtInv`), per-function verification
   (`Compiler.Verified`), and the top-level crate obligation
   (`Trusted.CrateTheorem`).

#### Flat `BodyId`-indexed `Crate.bodies` table (no `mutual` inductive types)

In `Trusted/MirAst.lean`, every captured function—whether local and verified,
an inline helper, an external callee with an assumed contract, or an
unsupported body—is stored once as a `BodyDecl` in the flat `Crate.bodies`
table and referenced elsewhere by `BodyId`:

- `Terminator.call` stores `callee : Callee` (`Callee.body (id : BodyId) ...` or
  `Callee.panic`) rather than recursively embedding a `MirBody` inside
  `Terminator`.
- `TCBItem` (`rustcLowering`, `assumedContract`, `unverifiedFn`) identifies
  functions by `(fnName : String)` and `(id : BodyId)` rather than embedding
  `MirBody`.

Keeping `MirBody` out of `Terminator` and `TCBItem` eliminates `mutual`
inductive types in `Trusted/MirAst.lean`, avoids duplicating shared callee ASTs
across the call graph, and allows `theory/` to decide structural equality on
`MirBody` without fuel bounds or manual mutual recursors.

#### Value-tree memory model, `Place` lenses, and partial-move soundness

`Trusted/MirSemantics.lean` represents values as functional trees (`MirVal`):

- Scalar and aggregate nodes (`unit`, `bool`, `int`, `adt`, `tuple`),
- Logical references and raw pointers (`ref`, `rawPtr`, `rawAddr`, `dangling`),
  and
- Leaf-granular uninitialized markers (`MirVal.uninit`).

Composite places `(local, projs)` are read and updated through two fuel-bounded
lens helpers over `List PlaceElem` (`.deref` and `.field idx`):

- **`evalProjFuel` and `isFullyInitFuel`:** Reading (`Operand.copy` or
  `Operand.move`) or borrowing (`Rvalue.ref`) a place traverses its projection
  path, verifies that every intermediate dereference targets a live, valid
  place, and requires `isFullyInitFuel` on the resulting `MirVal`—stepping to
  `.failed` (UB) if any leaf of the read or borrowed value is `MirVal.uninit`.
- **`updateProj` on moves and assignments:** Assigning to a projected place
  writes the new subvalue back into the root local's `MirVal` tree. Crucially,
  evaluating `Operand.move p` both returns the value at `p` and updates `p` to
  `MirVal.uninit` via `updateProj`. If a function moves a field `_1.0` out of a
  non-`Copy` struct and subsequently reads or moves `_1` or `_1.0` again before
  reinitializing it, `isFullyInitFuel` detects the `MirVal.uninit` leaf and
  steps to `.failed`. Struct padding bytes are represented with the same
  `MirVal.uninit` primitive so raw byte copies and transmutes track
  uninitialized padding without a separate shadow byte array.

#### UB faults vs. panics (`Terminator.assert` vs. `Callee.panic`)

Rust distinguishes compiler-inserted validity checks from explicit program
panics, and `Trusted/MirSemantics.lean` models the two distinctly:

- **`Terminator.assert` (compiler validity and overflow checks):** `rustc`
  lowers checked arithmetic overflow (`+`, `-`, `*`), division or remainder by
  zero, and slice bounds checks to `TerminatorKind::Assert`. In Anneal's
  semantics, a failing `Terminator.assert` steps to `.failed` (undefined
  behavior), requiring verified functions to prove that arithmetic overflow and
  division by zero cannot occur.
- **`Callee.panic` (explicit Rust panics):** Calls to `core::panicking::panic*`
  (from `panic!` or `assert!`) step to `.terminated .unwind`. Under Anneal's
  safety semantics, clean unwinding is not undefined behavior, though a
  postcondition (`PostSpec`) is checked against normal returns.

### Stage 3: In-place lowering and compositional verification (`theory/Anneal/`)

Stage 3 (`theory/Anneal/`) provides the normalization passes, compositional
checkers, and symbolic execution lemmas that prove
`Trusted.CrateTheorem Mir.crate`:

- **In-place CFG lowering (`theory/Anneal/Lowering.lean`):** Rather than
  translating `Trusted.MirBody` into a separate AST type, `lowerBody :
  MirBody → MirBody` simplifies a captured body in place. It strips `Stmt.nop`
  and coalesces straight-line single-predecessor `goto` chains while preserving
  `b.blocks.length`, `BlockId` numbering, and `storageLive`/`storageDead`
  statements (so use-after-`StorageDead` checks on dangling borrows remain
  sound). The theorem `lowerBody_simulates` proves a backward simulation:
  proving `ExecNormal c (lowerBody b) s P` suffices to establish
  `ExecNormal c b s P` on the unlowered body.
- **Compositional per-ADT and per-function verification
  (`theory/Anneal/MirLemmas.lean`):** `Anneal.proveCrate` decomposes
  `Trusted.CrateTheorem` across the crate's tables:
  1. `NoDupIds` for `c.tcb`, `c.adts`, and `c.bodies`;
  2. `ValidTargetLayout c.layout`;
  3. Per-ADT invariant admissibility (`checkAdtInv` for each `AdtDecl` in
     `c.adts`); and
  4. Per-function verification (`checkFn` / `proveFunctionOpt` for each
     `CapturedFn` in `c.fns`).
- **Inline, modular, and assumed call verification:** At `Terminator.call`
  targeting `Callee.body calleeId args`, Stage 3 supports three verification
  modes over the unified `BodyDecl` entry in `c.bodies`:
  1. **Inline execution:** Step into the callee's `BodyPayload.mir` body by
     pushing a `CallFrame` onto `MirState.stack`.
  2. **Modular contract application:** When the callee carries a verified
     `FnContract` (`requires` and `ensures`), check the callee's preconditions
     at the call site and assume its postcondition for the destination place
     without re-executing the callee's body.
  3. **Explicitly waived calls:** When an external or unverified callee has no
     MIR body (`.external` or `.unsupported`), discharge the call only if the
     corresponding `TCBItem.assumedContract` or `TCBItem.unverifiedFn` entry is
     present in `c.tcb`.
- **Diamond CFG joins and state canonicalization (`execNormal_join`):** When
  two branches of a `Terminator.switchInt` reconverge at a join block, path
  states may differ in dead branch-local temporaries. Because Stage 2 maps
  `Stmt.storageDead l` to writing `MirVal.uninit` into local `l`, dead
  temporaries on both branches canonicalize to `MirVal.uninit`, allowing
  `execNormal_join` to merge the branches and verify the suffix from the join
  block once.

## Repository layout

Anneal's directory structure mirrors the trust boundary (`trusted/` vs.
`theory/`):

```text
anneal/
├── trusted/                        # Human-audited Trusted Computing Base (TCB)
│   ├── root-manifest.sha256        # SHA-256 pins for Cargo & Nix root manifests
│   ├── rustc-capture/              # Stage 1: rustc_driver MIR & spec extractor
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── main.rs             # GuardedFileLoader & rustc_driver entrypoint
│   │       ├── hook.rs             # Multi-config driver & MIR query hooks
│   │       ├── items.rs            # Crate item, ADT, const, & layout extraction
│   │       ├── extract.rs          # 1-to-1 MIR body & spec AST extraction
│   │       ├── ir.rs               # First-order intermediate capture structs
│   │       └── lean.rs             # Deterministic Mir.lean & Proof.lean emitter
│   ├── lean/                       # Stage 2: Trusted Lean foundation (tactic-free)
│   │   ├── foundation-lock.json    # SHA-256 pins for lean binary & Init.*
│   │   ├── Trusted.lean            # Root TCB prelude import
│   │   └── Trusted/
│   │       ├── Refinement.lean     # Sem, Abstracts, Compiles, VerificationResult
│   │       ├── StepResult.lean     # StepResult, Outcome, & bounded ExecSteps
│   │       ├── MirAst.lean         # Flat BodyId-indexed MIR AST & TCBItem
│   │       └── MirSemantics.lean   # Small-step MIR semantics & CrateTheorem
│   ├── audit/                      # CI-only .olean replay & boundary auditor
│   │   ├── src/                    # anneal-audit Rust binary & manifest checks
│   │   └── TrustedBoundary.lean    # Syntax allowlist & kernel DAG inspector
│   └── cargo-anneal/               # CLI orchestrator (cargo anneal)
└── theory/                         # Stage 3: Untrusted, kernel-checked proofs
    └── Anneal/
        ├── Refinement.lean         # Simulation & Obligation composition lemmas
        ├── StepResult.lean         # Fuel monotonicity & step composition lemmas
        ├── Lowering.lean           # In-place lowerBody & lowerBody_simulates
        └── MirLemmas.lean          # Compositional checker & symbolic execution
```

## Compiler integration and extraction lifecycle

Because Anneal's correctness promise applies to the Rust crate as compiled by
`rustc`, `trusted/rustc-capture/` hooks directly into `rustc`'s query and
codegen pipeline so that captured MIR reflects the exact semantics `rustc`
compiles.

### Why Anneal captures `Runtime(PostCleanup)` MIR with `-Z mir-preserve-ub`

`rustc` lowers source code through HIR, THIR, built MIR, borrow-checked
`Analysis` MIR, and finally **`Runtime(PostCleanup)` MIR** immediately before
monomorphization and code generation:

- **Explicit drops and control flow:** Implicit destructor calls (`Drop`),
  unwind edges, and state machines have already been elaborated into explicit
  basic blocks and terminators, so `trusted/lean/` does not need to re-implement
  drop elaboration or borrow checking.
- **Preserved Rust types and projections:** Unlike LLVM IR,
  `Runtime(PostCleanup)` MIR retains full Rust type definitions, ADTs, place
  projections, and pointer mutability metadata needed to detect Rust-level
  undefined behavior.
- **Preserving UB checks via `-Z mir-preserve-ub`:** In default builds,
  `rustc`'s `RemovePlaceMention` pass erases `StatementKind::PlaceMention`
  statements (such as `let _ = *ptr;`) before `Runtime(PostCleanup)`.
  `rustc-capture` injects `-Z mir-preserve-ub` into the compiler invocation so
  `PlaceMention` and other UB-bearing checks survive into `Runtime(PostCleanup)`
  and are checked by `Stmt.placeMention` in `Trusted/MirSemantics.lean`.

### Intercepting MIR before `Steal<Body>` consumption

During compilation, `rustc` stores intermediate MIR in `Steal<Body>` cells that
are consumed ("stolen") when transitioning from analysis to runtime MIR passes.
In `trusted/rustc-capture/src/hook.rs`, `rustc-capture` overrides the
`mir_drops_elaborated_and_const_checked` query provider to snapshot each local
function's post-drop-elaboration body before downstream passes steal it, and
then reads the final `Runtime(PostCleanup)` body (`tcx.optimized_mir(def_id)`)
inside `after_analysis`.

### Dual-configuration debug-assertion consistency (`CONFIGS`)

Code that is only safe when `debug_assert!` is active is unsound in release
builds. Conversely, ordinary Rust arithmetic (`+`, `-`, `*`) emits overflow
`TerminatorKind::Assert` checks when overflow checks are enabled. To verify
that functions do not rely on `debug_assert!` while modeling overflow checks
consistently, `rustc-capture` runs the compiler pipeline across two
configurations (`-C debug-assertions=on` vs. `-C debug-assertions=off`, with
`-C overflow-checks=on` and `-Z mir-preserve-ub` enabled in both) and checks
that every verified function's captured MIR is identical across both passes.

### Guarding against post-monomorphization errors (PMEs)

In `rustc`, `Runtime(PostCleanup)` MIR is constructed per generic function
before monomorphization completes. However, a generic function that passes type
checking can still fail during monomorphization if it evaluates a failing
`const { ... }` block, triggers an associated-constant panic, or instantiates a
type whose concrete size exceeds `isize::MAX`.

Anneal closes this post-monomorphization gap with a two-part defense across
Stage 1 and Stage 2:

1. **Collector execution and `MonoAdmitted`:** During Stage 1 capture,
   `rustc-capture` invokes `tcx.collect_and_partition_mono_items(())` and
   checks `tcx.dcx().has_errors()` so any monomorphization error reachable from
   concrete roots aborts capture immediately. Generic functions require either
   no generic parameters or an explicit `#[anneal::mono]` admission
   (`MonoAdmitted`).
2. **All-path constant and layout totality (`ConstsTotal`):** Even a dead branch
   such as `if false { let _ = MonoErr::<T>::TRIGGER; }` can trigger a PME in
   `rustc` before dead-branch pruning completes. Stage 1 captures both
   `Body::required_consts` and `Body::mentioned_items` from the pre-dead-block-
   elimination body snapshot (`mir_drops_elaborated_and_const_checked`), and
   `Trusted/MirSemantics.lean` requires `ConstsTotal`: for every valid
   monomorphized type-size assignment (`ValidTySizes`, where each type parameter
   size is at most `isize::MAX`), every mentioned item's layout must fit within
   `isize::MAX` and every required constant must evaluate cleanly to either a
   normal value or a clean panic unwind (`ConstSucceeds ∨ ConstUnwinds`, never
   `.failed`).

## Toolchain pinning and compiler upgrades

`rustc`'s internal `rustc_private` APIs change across compiler releases. Anneal
pins a single deterministic `rustc` toolchain in `rust-toolchain.toml` (and
`flake.lock`) and absorbs toolchain upgrades across the three stages according
to what changed:

1. **Internal `rustc_private` API changes (absorbed in Stage 1):** Compiler
   refactorings that rename internal queries or types without changing emitted
   MIR are handled entirely inside `trusted/rustc-capture/`, leaving
   `trusted/lean/` and `theory/` untouched.
2. **Minor MIR shape variations (absorbed in Stage 3 `lowerBody`):** Changes in
   how `rustc` emits `nop` statements or splits straight-line basic blocks are
   normalized away in place by `theory/Anneal/Lowering.lean` (`lowerBody` and
   `lowerBody_simulates`), keeping downstream verification lemmas stable without
   expanding `trusted/lean/`.
3. **New MIR constructs (staged in Stage 2 via `candidate:<feature>`):** When
   Anneal adds support for a new MIR construct, `Trusted/MirAst.lean` and
   `Trusted/MirSemantics.lean` receive an additive constructor and step rule
   under a `-- anneal-trust-tier: candidate:<feature>` directive until human
   auditing against the pinned Rust Reference and `rustc` source completes.
