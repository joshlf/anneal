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
   `vendor/lean-miri/` and enables a surgical opt-in flag (`deinitMovedPlace :
   Bool`) so that moving a MIR place deinitializes the source location at
   runtime, matching post-cleanup runtime MIR semantics.
2. **Anneal MIR syntax and semantics ($M_{\text{anneal}}$):**
   `Trusted.MirAst` represents MIR programs with structural types (`MirTy`)
   carried directly by value, and `Trusted.MirSemantics` defines a small-step
   operational semantics that shares its boundary input and output value types
   (`Query`, `Out`, `TerminalOut`) directly with the reference adapter.
3. **Canonical type codec and correspondence (`Trusted.Correspondence`):**
   A total encoder (`encodeProg`) interns structural `MirTy` values into a
   deduplicated type table (`RefProg.types`) indexed by `TyId := Nat`, and a
   total decoder (`decodeProg`) inverts `encodeProg` unconditionally (`∀ p,
   decodeProg (encodeProg p) = some p`). Over this codec,
   `anneal_corresponds_to_miri` proves forward simulation from
   $M_{\text{anneal}}$ to $M_{\text{ref}}$ via a bijective simulation invariant
   (`SimulationInv`), and `reachesResult_fault_iff_refReachesOutcome` proves
   that Undefined Behavior (`.undefined` vs. `.ub`) and unsupported constructs
   (`.unsupported` vs. `.blocked`) correspond in both directions.

---

## 1. Repository Layout, Two-Pass Audit, and Trust Boundary

Anneal separates the core semantics shipped in the downstream verification
archive (`trusted/lean/` and `theory/`) from the repository-only correspondence
proof against `vendor/lean-miri/` (`trusted/correspondence/` and
`correspondence/`):

```text
trusted/lean/                            Core TCB (Pass 1; shipped in omnibus-archive)
  Trusted.lean                             Umbrella module (-- anneal-trust-tier: vetted)
  Trusted/
    MirAst.lean                            Anneal MIR syntax (-- anneal-trust-tier: candidate:mir_ast)
    MirSemantics.lean                      Anneal small-step semantics (-- anneal-trust-tier: candidate:mir_semantics)

theory/                                  Core untrusted theory (Pass 1; shipped in omnibus-archive)
  Anneal.lean                              Umbrella module
  Anneal/
    MirWp.lean                             Fuel-bounded weakest precondition (wpProg, wpFaultProg)
                                           and M_anneal non-vacuity canaries (D1-D5)

vendor/lean-miri/                        Vendored lean-miri reference model (Pass 2)
  UPSTREAM_PIN.json                        Pinned commit, 608 file SHA-256s, 6 patched file
                                           SHA-256s, and 160 ExecutionMachine .olean SHA-256s
  Miri/
    MIR/...                                Reference MIR syntax (TyId-indexed)
    Interpreter/
      MachineHooks.lean                    MachineState + pendingMoveDeinit flag
      LocalAccess.lean                     Pure local operand helpers + deinitMovedPlace
      OperandMachine.lean                  Operand evaluation + immediate move deinit
      Place.lean                           copyRuntimePlaceNoValidate + indirect move deinit
      PlaceMachine.lean                    readImmediate + takePendingMoveDeinit wiring
      ExecutionMachine.lean                Top-level step engine (M_ref) + Config flag

trusted/correspondence/Trusted/          Correspondence TCB specification (Pass 2)
  Correspondence.lean                      Codec, MiriRefMachine hooks, RefWellFormed,
                                           RefBehavior, CorrespondenceClaim, and
                                           FaultEquivalenceClaim (-- anneal-trust-tier: candidate:mir_semantics)

correspondence/Anneal/                   Untrusted correspondence proof (Pass 2)
  MirCorrespondenceProof.lean              Bijective SimulationInv, step proofs, and M_ref
                                           correspondence canaries (D6-D9)

trusted/audit/                           Two-pass source + binary .olean auditor
  src/lib.rs                               Pass 1 (51-module core lock) + Pass 2
                                           (UPSTREAM_PIN.json + correspondence closure)
  TrustedBoundary.lean                     Syntactic preflight, constant-cone checks,
                                           statement-origin verification, and kernel replay
```

### 1.1 Physical Separation Between Pass 1 (Core Omnibus) and Pass 2 (Correspondence)

Anneal's Nix build (`omnibus-archive` in `flake.nix`) copies `trusted/lean/`
and `theory/` into `share/anneal/` inside `anneal-exocrate.tar.zst`, and
`anneal-audit` Pass 1 (`Checker::run`) verifies that every module under
`trusted/lean/` and `theory/` starts with `prelude` and imports only the 51
locked `Init.*` modules in `trusted/lean/foundation-lock.json`. By contrast,
`vendor/lean-miri/Miri/` (608 files total; 160 `Miri.*` modules in the
transitive import closure of `Miri.Interpreter.ExecutionMachine`) uses standard
Lean 4 module headers without `prelude`, transitively importing `Init.*` and
`Std.*` modules from the Lean 4.34.1 toolchain sysroot.

Placing `Trusted.Correspondence` and `Anneal.MirCorrespondenceProof` in
`trusted/correspondence/` and `correspondence/` preserves both invariants:

1. **Pass 1 (`Checker::run` on `trusted/lean/` and `theory/`):** Audits
   `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp` against the
   unmodified 51-module `trusted/lean/foundation-lock.json` and unmodified
   `allowedTrustedSyntaxKinds` / `allowedTheorySyntaxKinds` allowlists in
   `TrustedBoundary.lean`. Only `trusted/lean/` and `theory/` ship in
   `omnibus-archive`, keeping downstream per-crate verification completely
   independent of `vendor/lean-miri/`.
2. **Pass 2 (`Checker::run_correspondence` on `vendor/lean-miri/`,
   `trusted/correspondence/`, and `correspondence/`):** Runs in repository CI
   (`--require-correspondence`) to audit the correspondence claim against
   `vendor/lean-miri/`:
   - **Fail-closed `UPSTREAM_PIN.json` check:** Verifies that all 608 `.lean`
     files in `vendor/lean-miri/` are regular files (no symlinks or pre-existing
     `.olean`/`.ilean`/`.ir` files) matching their pinned SHA-256 digests: 602
     files match unmodified upstream `proofs-rs/lean-miri` at
     `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, and the 6 patched files match
     their pinned `patched_sha256` digests in `UPSTREAM_PIN.json`.
   - **160-module `ExecutionMachine` slice build and cache:** Compiles (or links
     from `--miri-cache-dir` after verifying each module's pinned `olean_sha256`
     in `UPSTREAM_PIN.json`) the 160 `Miri.*` modules in the transitive import
     closure of `Miri.Interpreter.ExecutionMachine` with
     `-DElab.async=false -Ddebug.skipKernelTC=false`.
   - **Syntactic preflight on `Trusted.Correspondence` and
     `Anneal.MirCorrespondenceProof`:** Enforces the unmodified
     `allowedTrustedSyntaxKinds` and `allowedTheorySyntaxKinds` allowlists,
     `prelude`, and explicit root-identifier checks on both modules.
   - **Constant-cone purity, statement-origin verification, and kernel replay:**
     Traverses the constant-level dependency graph (`declarationEdges`) from
     `Trusted.Correspondence` and `Anneal.MirCorrespondenceProof` across all 5
     module roles (`.foundation`, `.sysrootFoundation`, `.vendorMiri`,
     `.trusted tier`, and `.theory`). `TrustedBoundary.lean` verifies that no
     reachable constant is `unsafe` or `isPartial`, that no reachable
     `.vendorMiri` constant is `.opaqueInfo` (guaranteeing that none of the 24
     `partial def` JSON parser helpers in `Miri.Input.*` is reachable), that
     the only reachable axioms belong to `{propext, Classical.choice,
     Quot.sound}`, that `correspondence_claim_holds` and
     `fault_equivalence_claim_holds` prove the exact `Prop` constants defined in
     `Trusted.Correspondence`, and that `toKernelEnv.replay` replays every
     reachable `.vendorMiri` constant alongside `Trusted.Correspondence` and
     `Anneal.MirCorrespondenceProof` from scratch.

### 1.2 Compliance with `TrustedBoundary.lean` and `TrustTier` Discipline

Every `Trusted.*` and `Anneal.*` module satisfies `TrustedBoundary.lean` with
zero changes to `trusted/lean/foundation-lock.json` or the syntax/tactic
allowlists:

- **Trust-tier headers (`-- anneal-trust-tier:`):** `Trusted/MirAst.lean`
  carries `-- anneal-trust-tier: candidate:mir_ast`; `Trusted/MirSemantics.lean`
  and `Trusted/Correspondence.lean` carry `-- anneal-trust-tier:
  candidate:mir_semantics`; and `Trusted.lean` carries `-- anneal-trust-tier:
  vetted`. Because `Trusted.lean` is a pure umbrella module that declares zero
  constants, `checkTierReferences` (which inspects constant-level
  `declarationEdges`) permits `Trusted.lean` to import `Trusted.MirAst` and
  `Trusted.MirSemantics` while forbidding any `vetted` module from referencing
  `candidate:*` constants.
- **Tactic-free, `deriving`-free `Trusted.*` definitions:**
  `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and
  `Trusted/Correspondence.lean` start with `prelude`, import only locked modules
  from `foundation-lock.json` (`Init.NotationExtra`,
  `Init.Data.BitVec.BasicAux`, `Init.Data.Int.Basic`,
  `Init.Data.Nat.Div.Basic`, `Init.Data.Nat.Bitwise.Basic`, and
  `Init.Control.Except`), omit `deriving` clauses in favor of explicit
  structural `beq` functions, and mark recursive definitions `noncomputable def`
  so Lean 4.34.1 elaborates the identical pure kernel `.defnInfo` without
  emitting partial `._unsafe_rec` compiler helpers.
- **Allowlisted tactics in `theory/` and `correspondence/`:**
  `Anneal/MirWp.lean` and `Anneal/MirCorrespondenceProof.lean` use only the 30
  tactics in `allowedTheorySyntaxKinds` (such as `let ⟨a, b⟩ := h`, `cases`,
  `induction`, `dsimp`, `simp`, `rw`, `exact`, `apply`, and `decide`) and unfold
  multi-arm `Trusted.*` definitions via `dsimp only [Trusted.foo]` rather than
  `simp [Trusted.foo]` or `unfold Trusted.foo` (preventing
  `Lean.Meta.getEqnsFor?` from lazily emitting `Trusted.foo.eq_N` theorems into
  `theory/` `.olean`s).

---

## 2. Reference Model ($M_{\text{ref}}$) and Move Deinitialization

### 2.1 Vendored `lean-miri` Core

Anneal uses `lean-miri` (`Miri.Interpreter.ExecutionMachine.step`, pinned at
upstream `proofs-rs/lean-miri` commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, which targets `miri` commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `rustc` commit
`8144389c895da997dbdecaa635e41d6a50be6ffd` and compiles cleanly on
`leanprover/lean4:v4.34.1`) as $M_{\text{ref}}$. `lean-miri` is a mechanized
Lean 4 interpreter modeled line-by-line on `rustc_const_eval::interpret`. Each
invocation of `ExecutionMachine.step` takes a fuel parameter (`maxSubsteps :=
16` for internal sub-loops), a nondeterminism oracle (`choice : Choice`), and an
`ExecutionState`, and returns one of five outcomes:

- `.running nextState`: the statement or terminator stepped normally.
- `.returned`: the root frame executed `TerminatorKind.Return` and popped into
  the caller sentinel frame.
- `.exhausted .stepLimit`: the execution reached its configured step budget
  (`stepsExecuted ≥ limits.maxSteps`).
- `.ub err`: the execution triggered modeled Rust Undefined Behavior (such as
  reading uninitialized data, dividing by zero, overflowing an unchecked
  arithmetic operator, or accessing a dead local).
- `.blocked reason`: the execution encountered an unmodeled feature, missing
  hook, or malformed MIR invariant (such as an out-of-bounds basic-block index
  or an unsupported statement, rvalue, or terminator).

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
```

Every `MiriRefMachine` hook derives its layout answer purely by indexing into
`rp.types[tyId]?`:

- `MirTy.unit` maps to a 0-byte zero-sized layout (`Size.ZERO`, alignment 1,
  `FieldsShape.Arbitrary`).
- `MirTy.bool` maps to a 1-byte unsigned scalar layout with valid range
  `0..=1`.
- `MirTy.int width signed` maps to a scalar layout of size `width.byteSize`
  (`1`, `2`, `4`, `8`, or `16` bytes; `isize`/`usize` use 8 bytes on 64-bit
  targets) and signedness `signed`.
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

`initRefState` therefore initializes the reference stack with two frames
(`#[callerSentinelFrame, rootFrame]`):

1. `callerSentinelFrame` holds a single live destination slot (`local 0`) of the
   entry function's return type and sets `returnContinuation := none`.
2. `rootFrame` executes `rp.bodies[rp.entryDefId]` with `returnPlace := some
   (Place.fromLocal ⟨0⟩)` pointing into `callerSentinelFrame`.

When `rootFrame` executes `Return`, `lean-miri` validates and copies `_0` into
`callerSentinelFrame`'s slot `0`, pops `rootFrame`, and returns `.returned`.

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
`deinitMovedPlace : Bool := false` across 6 files in `vendor/lean-miri/Miri/`
(`MachineHooks.lean`, `LocalAccess.lean`, `OperandMachine.lean`, `Place.lean`,
`PlaceMachine.lean`, and `ExecutionMachine.lean`) and set `deinitMovedPlace :=
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
  (`PlaceMachine.readImmediate` and `Place.copyRuntimePlaceNoValidate`) read
  *after* `evalOperand` returns. (If `evalPlaceToOp` succeeds with `.immediate
  _` on a projected local `!place.projection.isEmpty`, meaning the local has no
  `.Deref` projection and every projection step is valid, `evalOperand`
  materializes the base local via `forceAllocation` and re-runs `evalPlaceToOp`
  to obtain `.indirect mplace` for the projected sub-place.) Rather than adding
  a field to `OpTy` (which would break 2-argument `⟨op, layout⟩` constructors
  across 174 files in `vendor/lean-miri/Miri/`), `evalOperand (.Move place)`
  sets `pendingMoveDeinit := true` on `MachineHooks.MachineState` (while
  `evalPlaceToOp` and non-`Move` arms of `evalOperand` reset
  `pendingMoveDeinit := false`):
  - Inside `PlaceMachine.readImmediate` (`BinaryOp`, `UnaryOp`, `SwitchInt`,
    `Assert`, `Cast`), the consumer atomically takes `pendingMoveDeinit`, runs
    upstream `Miri.Interpreter.readImmediate` (checking scalar layout, pointer
    alignment, borrow-tracker permissions, and `.uninit` bytes), and then writes
    `.uninit` to `⟨mplace, operand.layout⟩` via
    `writeImmediateToMplaceNoValidate`.
  - Inside `Place.copyRuntimePlaceNoValidate` (`Rvalue.Use`, `Aggregate`,
    `Repeat`, `WrapUnsafeBinder`), the consumer atomically takes
    `h.takePendingMoveDeinit` after `compatible` and `hasPadding` checks. In the
    `.immediate value` branch, it deinitializes `⟨mplace, source.layout⟩` via
    `h.writeMemoryNoValidate choice .uninit` *before* writing `value.value` to
    `dest` (preserving indirect self-moves `*_1 = move *_1`); in the `.place
    memory` branch (padded or memory-backed structs/arrays), it runs
    `copy.memoryCopy` (which already enforces `nonoverlapping = true`) and then
    deinitializes `⟨memory.mplace, source.layout⟩` via
    `h.writeMemoryNoValidate choice .uninit`, before `copyRuntimePlace` runs
    destination validity checks (`h.validate choice dest`).

---

## 3. MIR Representation (`Trusted.MirAst`) and Canonical Type Codec

### 3.1 Structural Types by Value in `Trusted.MirAst`

In `Trusted.MirAst`, MIR types (`MirTy`) are structural inductive values carried
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
and duplicate-index aliasing from `Trusted.MirAst` and `Trusted.MirSemantics`:
two types in $M_{\text{anneal}}$ are equal if and only if they are structurally
equal (`t₁ = t₂`). To satisfy `TrustedBoundary.lean`'s `deriving`-free syntax
allowlist in `trusted/`, `Trusted.MirAst` defines structural equality via pure
pattern-matching functions (`IntWidth.beq`, `Mutability.beq`, `MirTy.beq`).

Similarly, constant literals (`ConstLit`) represent only modeled constant shapes
(`.scalar (bits : BitVec 128)` and `.zeroSized`). When `anneal-rustc-capture`
encounters an unmodeled constant, statement, rvalue, or terminator, it lowers
the enclosing construct to `StatementKind.unsupported`, `Rvalue.unsupported`, or
`TerminatorKind.unsupported` so that unsupported features are rejected at clear
statement or expression boundaries rather than inside leaf literals.

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
   (returning `none` if any `TyId` is out of bounds).

### 3.3 Unconditional Anti-Laundering Guarantees

This codec design yields three unconditional theorems in
`Trusted.Correspondence`:

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

Sharing `Query` and `TerminalOut` across both $M_{\text{anneal}}$ and
$M_{\text{ref}}$ eliminates any output projection function $\pi :
\text{Out}_{\text{anneal}} \to \text{Out}_{\text{ref}}$ from the correspondence
theorem statement, preventing a constant or lossy projection from hiding
disagreements in return values or memory state.

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

1. `q.callerMem.allocations` is empty on Day 1 (non-empty initial caller memory
   returns `.error .unsupported`).
2. `p.bodies[p.entryDefId]?` exists, has at least one basic block, satisfies
   `body.argumentCount < body.locals.length`, has all `.storageLive` and
   `.storageDead` indices in bounds (`< body.locals.length`, matching
   `CallMachine.alwaysLiveVarsAndTemps`), and declares supported scalar or unit
   local types.
3. `q.args` has length `body.argumentCount` and each argument `v` satisfies
   `v.ty? = some paramTy` (including `ScalarVal.wf`: `v.bits.toNat <
   v.width.modulus`).

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
def Step (p : Program) (s : State) (res : StepResult State TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoice p s c ∧ evalStep p c s = res

inductive Reaches (p : Program) : State → State → Prop where
  | refl (s : State) : Reaches p s s
  | tail : Reaches p s₁ s₂ → Step p s₂ (.step s₃) → Reaches p s₁ s₃

def ReachesResult (p : Program) (q : Query)
    (res : StepResult State TerminalOut) : Prop :=
  match initState p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : State, Reaches p s₀ s ∧ Step p s res

def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

def Behavior (p : Program) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult p q (.done out)

def SatisfiesPost (p : Program) (q : Query) (post : TerminalOut → Prop) : Prop :=
  WellFormed p q ∧ ∀ out : TerminalOut, Behavior p q out → post out
```

`WellFormed p q` requires both that `initState p q` succeeds and every reachable
state has at least one admissible choice (`∃ c, ValidChoice p s c`, preventing a
vacuous choice predicate from making `WellFormed` hold on a stuck machine) and
that no reachable transition faults with either `.undefined` or `.unsupported`.

### 4.4 Core Operational Rules Matching `lean-miri`

To maintain a 1-to-1 step correspondence with `lean-miri` across all inputs—both
well-formed executions and faulting executions—`Trusted.MirSemantics` aligns its
operational checks with `lean-miri`'s evaluation order:

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

In `lean-miri`, `ExecutionMachine.step` checks `state.stepsExecuted <
limits.maxSteps` at the start of every step: if the budget is reached, it
returns `.exhausted .stepLimit`, and otherwise it executes one step and
increments `stepsExecuted := state.stepsExecuted + 1`.

To keep `Trusted.Correspondence` maximally auditable without modifying
intermediate `lean-miri` states between steps, `initRefState` takes `maxSteps :
Nat` as an explicit parameter (`stepsExecuted := 0, maxSteps := maxSteps`), and
`RefReaches` chains `RefStep` transitions completely unmodified:

```lean
inductive RefReaches (rp : RefProg) : RefState → RefState → Prop where
  | refl (rs : RefState) : RefReaches rp rs rs
  | tail : RefReaches rp rs₁ rs₂ → RefStep rp rs₂ (.running rs₃) → RefReaches rp rs₁ rs₃

def RefReachesOutcome (rp : RefProg) (q : Query) (maxSteps : Nat)
    (out : RefOutcome) : Prop :=
  match initRefState rp q maxSteps with
  | .error k => out = faultToRefOutcome k
  | .ok rs₀ => ∃ rs : RefState, RefReaches rp rs₀ rs ∧ RefStep rp rs out
```

`RefWellFormed` and `RefBehavior` then quantify over `maxSteps : Nat` according
to their polarity:

```lean
def RefWellFormed (rp : RefProg) (q : Query) : Prop :=
  ∀ maxSteps : Nat,
    (∃ rs₀ : RefState, initRefState rp q maxSteps = .ok rs₀ ∧
      ∀ rs : RefState, RefReaches rp rs₀ rs → ∃ c : Choice, ValidRefChoice rp rs c) ∧
    ¬ RefReachesOutcome rp q maxSteps .ub ∧
    ¬ RefReachesOutcome rp q maxSteps .blocked

def RefBehavior (rp : RefProg) (q : Query) (out : TerminalOut) : Prop :=
  ∃ maxSteps : Nat, RefReachesOutcome rp q maxSteps (.returned out)
```

- In `RefWellFormed rp q`, quantifying universally over `∀ maxSteps : Nat`
  asserts that no finite execution prefix of any length ever reaches `.ub` or
  `.blocked` (treating `.exhaustedStepLimit` as the step-budget horizon rather
  than a program fault).
- In `RefBehavior rp q out`, quantifying existentially over `∃ maxSteps : Nat`
  asserts that there exists a finite step budget large enough (specifically
  `maxSteps := n + 1` for an $n$-step trace in $M_{\text{anneal}}$) for
  `lean-miri` to run from `stepsExecuted = 0` to `.returned out`.

### 5.2 Correspondence and Bidirectional Fault-Equivalence Theorems

`Trusted.Correspondence` states—and `Anneal.MirCorrespondenceProof` proves with
zero `sorry`—both forward simulation for well-formed programs and exact
bidirectional fault equivalence:

```lean
theorem anneal_corresponds_to_miri (p : Program) (q : Query) :
    WellFormed p q →
      RefWellFormed (encodeProg p) q ∧
      ∀ out : TerminalOut, Behavior p q out → RefBehavior (encodeProg p) q out

theorem reachesResult_fault_iff_refReachesOutcome
    (p : Program) (q : Query) (k : FaultKind) :
    ReachesResult p q (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)
```

where `faultToRefOutcome .undefined = .ub` and `faultToRefOutcome .unsupported =
.blocked`.

### 5.3 Bijective Simulation Invariant (`SimulationInv`)

Because both $M_{\text{anneal}}$ and $M_{\text{ref}}$ deinitialize moved locals
in lockstep via `liveUninitSlot` and pre-cache local types via
`zipRefLocals`, the simulation relation `SimulationInv p s rs` in
`Anneal.MirCorrespondenceProof` requires no slack or ghost state:

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

def SimulationInv (p : Program) (s : State) (rs : RefState) : Prop :=
  ∃ f : FrameState, ∃ rf : RefFrameState,
    s.frames = [f] ∧
    rs.frames = [rf] ∧
    rs.callerMem = s.callerMem ∧
    FrameSimInv p f rf
```

(When linking against `vendor/lean-miri`'s `storageDeadDyn`, which clears the
cached layout on `.dead` slots and re-queries `rp.types` on `storageLiveDyn`,
`FrameSimInv` permits `cachedLayout ∈ {none, some ty}` on `.dead` slots while
requiring `cachedLayout = some ty` on all `.live` slots; projecting `.slot` is
identical.)

`SimulationInv` is an exact bijection between $M_{\text{anneal}}$ states and
$M_{\text{ref}}$ states at fixed step counters:

```lean
theorem state_unique_of_simulationInv
    (h₁ : SimulationInv p s₁ rs) (h₂ : SimulationInv p s₂ rs) : s₁ = s₂

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
(for proving `SatisfiesPost p q post` and `∃ out, Behavior p q out ∧ post out`
via `wellFormed_and_spec_of_wp`), and instantiating it with `onDone := fun _ =>
False` and `onFault := (· = expected)` yields `wpFaultProg` (for proving
negative fault canaries via `reaches_fault_and_exclusive_of_wpFault`).

`Anneal.MirWp` (Pass 1) and `Anneal.MirCorrespondenceProof` (Pass 2) include 11
kernel-checked non-vacuity canary theorems that exercise all three outcome poles
and runtime move semantics across both $M_{\text{anneal}}$ and $M_{\text{ref}}$:

| Canary theorem | Module (Audit Pass) | Tested MIR program | Verified outcome |
| :--- | :--- | :--- | :--- |
| `canary_positive_add_anneal` | `Anneal.MirWp` (Pass 1) | `_0 = copy _1 + copy _2; return` (`30u32 + 12u32`) | `WellFormed` and returns `42u32` |
| `canary_positive_empty_unit_fn` | `Anneal.MirWp` (Pass 1) | `fn empty() { return }` (`_0 : ()`) | `WellFormed` and returns `()` |
| `canary_negative_ub_div_zero_anneal` | `Anneal.MirWp` (Pass 1) | `_0 = copy _1 / const 0u32; return` | Reaches `.fault .undefined` (not `.unsupported`), `¬WellFormed` |
| `canary_negative_ub_signed_rem_overflow_i8` | `Anneal.MirWp` (Pass 1) | `_0 = copy _1 % copy _2; return` (`-128i8 % -1i8`) | Reaches `.fault .undefined` (not `.unsupported`), `¬WellFormed` |
| `canary_negative_unsupported_anneal` | `Anneal.MirWp` (Pass 1) | `StatementKind.unsupported; return` | Reaches `.fault .unsupported` (not `.undefined`), `¬WellFormed` |
| `canary_D6_use_after_move_ub` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_2 = move _1; _0 = copy _1; return` | Reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$ |
| `canary_D7a_binop_copy_then_move_ok` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_0 = copy _1 + move _1; return` (`42u32`) | `WellFormed`, `RefWellFormed`, and returns `84u32` in both |
| `canary_D7b_binop_move_then_copy_ub` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_0 = move _1 + copy _1; return` | Reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$ |
| `canary_D7c_binop_move_then_move_ub` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_0 = move _1 + move _1; return` | Reaches `.fault .undefined` and `.ub` in $M_{\text{ref}}$ |
| `canary_D8_self_move_ok` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_1 = move _1; _0 = copy _1; return` (`42u32`) | `WellFormed`, `RefWellFormed`, and returns `42u32` in both |
| `canary_D9_move_unit_zst_ok` | `Anneal.MirCorrespondenceProof` (Pass 2) | `_2 = move _1; _0 = copy _1; return` (`_1 : ()`) | `WellFormed`, `RefWellFormed`, and returns `()` in both |

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
  the destination local), whereas `ProjectionElem.Field` (`Place.lean:202–228`)
  can project over `.immediate (.scalar ..)` or `.immediate .uninit` only when
  the projected field has offset 0 and equal size (such as a 1-element
  newtype wrapper).

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
every construct that $M_{\text{anneal}}$ models (`WellFormed p q → RefWellFormed
(encodeProg p) q`), ensuring that `RefWellFormed` cannot vacuously excuse bugs
via `.blocked`. When Anneal later models a Rust feature (such as a compiler
intrinsic or inline assembly construct) that upstream `lean-miri` leaves
unimplemented:

1. **Preferred path (extend `MiriRefMachine` hooks):** `lean-miri` already
   delegates intrinsics (`evalIntrinsic`), foreign calls (`callExtraFn`), place
   projections (`evalPlaceProjectionExtra`), and pointer casts (`intToPtr`,
   `ptrToInt`) to its `Machine` typeclass. Implementing the corresponding hook
   in `MiriRefMachine` preserves `anneal_corresponds_to_miri` without changing
   its statement.
2. **Fallback path (explicit theorem update):** If a construct hits a hardcoded
   `.blocked` branch inside `lean-miri` that cannot be routed through `Machine`
   hooks or a small upstreamable patch, we will update the correspondence
   theorem statement in a dedicated, explicitly reviewed change as described in
   [`docs/mir-correspondence-strategy.md`](mir-correspondence-strategy.md).

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
inside `Trusted.Correspondence`. By contrast, the 6-file `deinitMovedPlace`
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
   breaks 2-argument anonymous constructor applications (`⟨op, layout⟩`) across
   174 files in `vendor/lean-miri/Miri/`. Recording `pendingMoveDeinit : Bool :=
   false` on `MachineHooks.MachineState` and `takePendingMoveDeinit : PlaceM S
   Bool := pure false` on `PlaceHooks` avoids touching `OpTy.mk` while compiling
   cleanly across all 53 reverse-dependent modules in the `ExecutionMachine`
   closure.

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
   If $M_{\text{anneal}}$ accidentally deinitializes local `j ≠ i` on `move _i`,
   or evaluates `BinOp(lhs, rhs)` right-to-left instead of left-to-right, any
   execution that reads the extra `.live none` local faults in
   $M_{\text{anneal}}$—making the premise `WellFormed p q` false and vacuously
   satisfying `anneal_corresponds_to_miri`.
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

#### Nominal `TyId` Indirection Inside `Trusted.MirAst`

We considered mirroring `lean-miri`'s `TyId := Nat` index table inside
`Trusted.MirAst` (`Program.types : List MirTy`). We rejected this because a
nominal `TyId` table inside $M_{\text{anneal}}$ introduces two classes of
representation artifacts:

1. Programs can contain out-of-bounds `TyId`s (`tyId ≥ p.types.length`),
   forcing every type lookup in `Trusted.MirSemantics` and `Anneal.MirWp` to
   handle missing-type faults.
2. A program's `types` table can list the same structural `MirTy` (such as
   `u32`) at two distinct indices (`TyId 0` and `TyId 1`). In `lean-miri`,
   `assertSameType` and `assertRvalueLayout` compare nominal `TyId`s (`0 ≠ 1`),
   whereas structural type checks compare `MirTy` values (`u32 = u32`), breaking
   correspondence unless every `Program` carries an extra canonical-table
   well-formedness side condition. Carrying `MirTy` by value in
   `Trusted.MirAst` and deduplicating during `encodeProg` eliminates both issues
   by construction.

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
`stepsExecuted` inside `RefStep` mutates the `ExecutionState` returned by
`ExecutionMachine.step` between steps. Quantifying over `maxSteps : Nat` in
`RefWellFormed` (`∀ maxSteps`) and `RefBehavior` (`∃ maxSteps`) allows
`RefReaches` to chain the exact states returned by `ExecutionMachine.step`
without modification.

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
