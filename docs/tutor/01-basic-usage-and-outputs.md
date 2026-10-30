# Chapter 1: Basic Tool Usage & Interpreting Outputs

[← Back to Tutor Overview](README.md) | [Next: Chapter 2 — Adding Specifications in Rust →](02-rust-specifications.md)

This chapter introduces Anneal's three core pipeline commands—`cargo anneal extract`,
`cargo anneal scaffold`, and `cargo anneal verify`—on a minimal safe Rust
function. You will learn how to read each command's CLI output block, inspect
the Lean 4 files generated inside `.anneal/generated/`, understand how
`VerificationResult` states contracts as `Partial` behavior refinements, and see
why an unannotated function that can panic on arithmetic overflow
(`advance_offset`) is still free of Undefined Behavior (`.defined = True`) yet
fails the default panic-free weakest-precondition check (`WP`).

---

## 1. Starting with a Minimal Function (`magic_version`)

This chapter runs its commands against the crate checked in at
[`examples/tutor-ch1/`](../../examples/tutor-ch1/); each later chapter has its
own crate (`examples/tutor-ch2/` through `examples/tutor-ch4/`, then
`examples/tutor/`), so you can either follow along by editing a copy of this
one or open the crate a chapter refers to directly. Its `Cargo.toml` defines the
`frame_tutor` crate (the empty `[workspace]` table keeps the crate independent
of the surrounding Anneal Cargo workspace):

<!-- tutor: file step=ch1-extract path=Cargo.toml -->
```toml
[package]
name = "frame_tutor"
version = "0.1.0"
edition = "2024"
publish = false

[workspace]
```

And `src/lib.rs` holds a single zero-argument function that returns the
protocol's current framing version:

<!-- tutor: file step=ch1-extract path=src/lib.rs -->
```rust
// Chapter 1 of the Anneal Tutor (docs/tutor/01-basic-usage-and-outputs.md)
// runs its commands against this crate. Section 6 asks you to add a second
// function below and watch verification reject it; Chapter 2 continues from
// the crate in examples/tutor-ch2/.

pub const fn magic_version() -> u32 {
    1
}
```

Even without annotations in `src/lib.rs` or proof files in `anneal/proofs/`,
Anneal can extract `magic_version`'s `Runtime(PostCleanup)` MIR, generate its
default `Partial` refinement obligation (`MirContractHolds`), and prove that
obligation in the Lean 4 kernel.

---

## 2. Step 1: Extracting `Runtime(PostCleanup)` MIR (`cargo anneal extract`)

Run `extract` using either **Flavour A** (inside an Anneal checkout, after
running `cargo build -p anneal-rustc-capture -p cargo-anneal` once) or
**Flavour B** (using an installed `cargo anneal` binary from outside the
checkout or inside the crate directory):

<!-- tutor: command step=ch1-extract -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor-ch1/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch1 && cargo anneal extract`):
cargo anneal extract --manifest-path examples/tutor-ch1/Cargo.toml
```

### Interpreting the Extract Report

`cargo anneal extract` invokes `anneal-rustc-capture` (`rustc -Zalways-encode-mir`)
on the target crate, serializes every local item's `Runtime(PostCleanup)` MIR
into `target/anneal/units/` (placed into `.anneal/generated/Mir/FrameTutor/<Item>.lean`
during scaffolding), writes `CaptureManifest.json`, and prints the **Extract
Report** (`Anneal Extract Summary:`):

<!-- tutor: report step=ch1-extract -->
```text
Anneal Extract Summary:
  Rust source files: 1
  Total MIR targets: 1
  Subject items: 1
  Companion items: requires: 0, ensures: 0, qualifiers: 0, external_spec: 0, model: 0, invariant: 0, unsafe_trait_impl: 0
  Subject mappings:
    frame_tutor::magic_version -> Mir.FrameTutor.magic_version
```

What each field means:
- **`Rust source files`**: The count of deduplicated crate source files
  (`src/lib.rs`) from which MIR bodies were extracted.
- **`Total MIR targets` vs. `Subject items` vs. `Companion items`**:
  Every compiled function produces a MIR body. Anneal classifies each body by
  its `ContractRole`:
  - **Subject items** (`ContractRole.subject`) are your crate's executable
    functions and methods that require verification (`frame_tutor::magic_version`).
  - **Companion items** are helper functions synthesized by `#[anneal_spec::*]`
    macros (`inline requires`, `inline ensures`, `qualifiers`, `external_spec`,
    `model`, `invariant`, and `unsafe_trait_impl`). Because `magic_version` has
    no macro annotations yet, all companion counts are `0`.
- **`Subject mappings` (`def_id -> Mir.<Crate>.<Item>`)**:
  Shows how each Rust definition path (`frame_tutor::magic_version`) maps to its
  generated Lean 4 MIR module (`Mir.FrameTutor.magic_version` at
  `.anneal/generated/Mir/FrameTutor/magic_version.lean`).

---

## 3. Step 2: Scaffolding Obligations and Verification Harnesses (`cargo anneal scaffold`)

Next, run `scaffold`:

<!-- tutor: command step=ch1-scaffold -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor-ch1/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch1 && cargo anneal scaffold`):
cargo anneal scaffold --manifest-path examples/tutor-ch1/Cargo.toml
```

### Interpreting the Scaffold Report

`cargo anneal scaffold` places the captured MIR modules and generates the
per-item `Obligations` and `Verify` Lean modules along with `.anneal/lakefile.toml`:

<!-- tutor: report step=ch1-scaffold -->
```text
Anneal Scaffold Summary:
  Generated (.anneal/generated/): Mir: 1, Obligations: 1, Verify: 1
  Durable (anneal/proofs/): created Specs: 0, preserved Specs: 0, created Proof: 0, preserved Proof: 0
```

What each line tells you:
- **`Generated (.anneal/generated/)`**:
  Reports the count of disposable machine-generated modules across the three
  layers: `Mir` (`1`), `Obligations` (`1`), and `Verify` (`1`). These files are
  regenerated on every run and must never be edited by hand.
- **`Durable (anneal/proofs/)`**:
  Reports how many files under `anneal/proofs/Specs/` and `anneal/proofs/Proof/`
  were newly created or preserved untouched. By default (without `--init-specs`
  or `--init-proofs`), `scaffold` creates `0` files under `anneal/proofs/` so
  your repository stays clean until an item actually needs a custom
  specification or proof.

---

## 4. Inspecting `.anneal/generated/` and the `Partial` Contract of `magic_version`

Let's inspect the three generated files for `frame_tutor::magic_version` to see
what theorem is stated and how `magic_version` verifies with zero files in
`anneal/proofs/`.

### 4.1 `.anneal/generated/Mir/FrameTutor/magic_version.lean`

This file is emitted by `anneal-rustc-capture` and imports only `Init.Core` and
`Trusted`:

<!-- tutor: file step=ch1-scaffold path=.anneal/generated/Mir/FrameTutor/magic_version.lean strip_module_doc -->
```lean
import Trusted

namespace Mir.FrameTutor.magic_version

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

-- TypeLayout[0]: size=4, align=4
def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil) }

-- bb0: _0 = const 1_u32; return
def body : CapturedMir :=
  {
    defPath := "frame_tutor::magic_version",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 4 })) }))), span := "src/lib.rs:7:5: 7:6" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:8:2: 8:2" }, isCleanup := false } List.nil),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

def defaultClaim : Claim :=
  { body := body, pre := fun _ => True, post := fun _ _ => True }

end Mir.FrameTutor.magic_version
```

Notice that `body` is a pure Lean 4 data structure (`CapturedMir`):
- `argCount := 0` and `localDecls` has a single slot `_0 : u32` (the return
  place).
- Basic block `0` assigns the 4-byte scalar constant `1`
  (`ConstScalar.int { bits := 1, sizeBytes := 4 }`) to `_0` and executes
  `TerminatorKind.return_`.
- `layouts` and `fnAbi` record the compiler's layout facts for `u32`, and
  `defaultClaim` pairs the body with the trivial `True` pre- and postconditions
  that the `Obligations` module below refines.

### 4.2 `.anneal/generated/Obligations/FrameTutor/magic_version.lean`

`cargo anneal scaffold` generates the specification obligation module, which
also imports only `Init.Core`, `Trusted`, and `Mir.FrameTutor.magic_version`:

<!-- tutor: file step=ch1-scaffold path=.anneal/generated/Obligations/FrameTutor/magic_version.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.magic_version

namespace Obligations.FrameTutor.magic_version

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `frame_tutor::magic_version` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  True

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `frame_tutor::magic_version` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  True

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::magic_version`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::magic_version`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Low-priority default `ItemSpec` instance for `frame_tutor::magic_version`.
    An authored normal-priority `ItemSpec` instance in `Specs.FrameTutor.magic_version`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "frame_tutor::magic_version" where
  pre := defaultPre
  post := defaultPost

/-- Low-priority default `StatefulItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "frame_tutor::magic_version" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `TotalItemSpec` instance for `frame_tutor::magic_version`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "frame_tutor::magic_version" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::magic_version" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::magic_version" where
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultSpec` for a safe function whose execution is defined
    (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain` while guarding
    `rustEnsures` and `extraPost` behind `rustRequires` and `extraPre` inside
    `.val` (`#125`). -/
@[instance_reducible]
         def refineSafeSpec
    (safetyDomain : List Value → Prop)
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::magic_version" where
  pre args := safetyDomain args
  post args ret :=
    And (rustRequires args) (extraPre args) →
      And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` for a safe stateful function whose execution
    is defined (`MirNoUB`, `.defined` of `Partial`) across `safetyDomain`
    while guarding `rustEnsures` and `extraPost` behind `rustRequires` and
    `extraPre` inside `.val` (`#125`). -/
@[instance_reducible]
         def refineSafeStatefulSpec
    (safetyDomain : List Value → Memory → Prop)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::magic_version" where
  pre args m := safetyDomain args m
  post args m0 ret m1 :=
    And (rustRequires args) (extraPre args m0) →
      And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Refine `defaultTotalSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineTotalSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    TotalItemSpec "frame_tutor::magic_version" where
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Specify program-to-program behavioral equivalence and total correctness
    against reference `specBody` while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineEquivSpec
    (specBody : CapturedMir)
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulEquivItemSpec "frame_tutor::magic_version" where
  specBody := specBody
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `frame_tutor::magic_version` synthesized from
    `ItemSpec "frame_tutor::magic_version"`. -/
def claim [spec : ItemSpec "frame_tutor::magic_version"] : Claim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical stateful verification claim for `frame_tutor::magic_version` synthesized
    from `StatefulItemSpec "frame_tutor::magic_version"`. -/
def statefulClaim [spec : StatefulItemSpec "frame_tutor::magic_version"] : StatefulClaim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical total-correctness verification claim for `frame_tutor::magic_version` synthesized
    from `TotalItemSpec "frame_tutor::magic_version"`. -/
def totalClaim [spec : TotalItemSpec "frame_tutor::magic_version"] : TotalClaim :=
  { body := Mir.FrameTutor.magic_version.body, pre := spec.pre, post := spec.post }

/-- Canonical program-to-program equivalence claim for `frame_tutor::magic_version` synthesized
    from `StatefulEquivItemSpec "frame_tutor::magic_version"`. -/
def equivClaim [spec : StatefulEquivItemSpec "frame_tutor::magic_version"] : StatefulEquivClaim :=
  { implBody := Mir.FrameTutor.magic_version.body, specBody := spec.specBody, pre := spec.pre, post := spec.post }

end Obligations.FrameTutor.magic_version
```

Because `magic_version` has no `#[anneal_spec::spec]` attributes, `defaultPre`
and `defaultPost` are both `True`.

Wait—does `defaultPost := True` mean `VerificationResult claim` is vacuous?
**No.** Look at how `Claim.holds` (`MirContractHolds`) is defined in
[`trusted/lean/Trusted/VerificationResult.lean`](../../trusted/lean/Trusted/VerificationResult.lean)
using `Partial`:

```lean
def MirExecPartial
    (body : CapturedMir)
    (args : List Value) :
    Partial (BehaviorSet (ExecPrefix MirObs Value)) where
  defined := MirNoUB.holds (MirSem ⟨body, args⟩)
  val := fun _ => MirSem ⟨body, args⟩

def MirContractSpec
    (safetyPre : List Value → Prop)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop)
    (args : List Value) :
    Partial (BehaviorSet (ExecPrefix MirObs Value)) where
  defined := safetyPre args
  val := fun _ pref =>
    And
      pref.outcome.isSafe
      (pre args →
        ∀ retVal : Value,
          pref.outcome = .terminal .normal retVal →
          post args retVal)

def MirContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre : List Value → Prop)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  Preorder.refines (MirExecPartial body) (MirContractSpec safetyPre pre post)

def MirContractHolds
    (body : CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafety body pre pre post
```

`MirContractHolds body pre post` states the Layer 1A `Partial` refinement
`Preorder.refines (MirExecPartial body) (MirContractSpec pre pre post)`.
By `instPreorderPartial` (and the equivalence theorem `mirContractHolds_iff` in
[`theory/Anneal/Rustc/V2026_06_01/Lower.lean`](../../theory/Anneal/Rustc/V2026_06_01/Lower.lean)),
for every `args : List Value` where `(MirContractSpec pre pre post args).defined`
(`pre args`) holds, a proof of `MirContractHolds` must supply a dependent pair:

1. **Definedness witness (`h₁ : (MirExecPartial body args).defined`)**:
   A proof of `MirNoUB.holds (MirSem ⟨body, args⟩)`, establishing that **every**
   reachable execution prefix `pref` satisfies `pref.outcome.isSafe`—meaning
   execution never hits `.fail .ub` (Undefined Behavior), `.fail .unsupported`
   (unmodeled MIR construct), or `.fail .outOfFuel`.
2. **Value refinement (`Preorder.refines ((MirExecPartial body args).val h₁) ((MirContractSpec pre pre post args).val h₂)`)**:
   A proof that every reachable prefix `pref` in `MirSem ⟨body, args⟩` satisfies
   `post args retVal` whenever `pref.outcome = .terminal .normal retVal`.

Even when `pre` and `post` are both `True`, proving `VerificationResult claim`
requires proving `(MirExecPartial magic_version.body args).defined` (`MirNoUB`)!

### 4.3 `.anneal/generated/Verify/FrameTutor/magic_version.lean`

Because no custom proof file exists at
`anneal/proofs/Proof/FrameTutor/magic_version.lean`, `cargo anneal scaffold`
emits a `defaultProof` instance in `Verify/FrameTutor/magic_version.lean`:

<!-- tutor: file step=ch1-scaffold path=.anneal/generated/Verify/FrameTutor/magic_version.lean strip_module_doc -->
```lean
-- @anneal-def-id: frame_tutor::magic_version
import Trusted
import Anneal
import Mir.FrameTutor.magic_version
import Obligations.FrameTutor.magic_version

namespace Verify.FrameTutor.magic_version

open Trusted.VerificationResult

/-- Low-priority fallback `ItemProof` instance attempting bounded
    `WP` discharge when no authored `Proof.FrameTutor.magic_version` module exists on
    disk. -/
instance (priority := low) defaultProof :
    ItemProof "frame_tutor::magic_version" Obligations.FrameTutor.magic_version.claim where
  verified :=
    Anneal.Rustc.V2026_06_01.SymbolicEval.verifyByWP Obligations.FrameTutor.magic_version.claim 64 (by
      intro _ _
      exact True.intro)

/-- Kernel-checked verification certificate for `frame_tutor::magic_version`. -/
theorem verified : VerificationResult Obligations.FrameTutor.magic_version.claim :=
  (inferInstance : ItemProof "frame_tutor::magic_version" Obligations.FrameTutor.magic_version.claim).verified

/-- Proposition verified by `Verify.FrameTutor.magic_version.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.FrameTutor.magic_version.claim

end Verify.FrameTutor.magic_version
```

Why does `defaultProof` succeed automatically for `magic_version`?
- `magic_version.body` takes zero arguments (`argCount := 0`), never reads any
  argument local (`_1..`), assigns `_0 := 1`, and returns `.ok (.scalar ⟨1, 4⟩)`
  in 2 steps.
- `WP (.ok (.scalar ⟨1, 4⟩)) (fun _ => True)` reduces definitionally in the
  Lean 4 kernel to `True`, which is discharged by `exact True.intro`.
- `verifyByWP` (`mirContractHolds_of_wp_bounded`) then lifts that bounded `WP`
  witness into a full `Partial` refinement proof of `MirContractHolds`.

---

## 5. Step 3: Running Kernel Verification & Audit (`cargo anneal verify`)

Now run `verify`:

<!-- tutor: command step=ch1-verify -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch1/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch1 && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor-ch1/Cargo.toml
```

### Interpreting the Verification Report

`cargo anneal verify` runs `extract`, `scaffold`, `lake build` on `.anneal/`,
and then invokes `TrustedBoundary.lean` (`verify-audit`) to replay the compiled
`.olean` files through the Lean 4 kernel and check the `TrustedBoundary` hygiene
rules:

<!-- tutor: report step=ch1-verify -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Totals: 1 unconditional, 0 conditional
  TrustedBoundary kernel replay: PASS
```

What each part of the Verification Report guarantees:
- **`Verify.FrameTutor.magic_version: UNCONDITIONAL` (`[UNCONDITIONAL]`)**:
  The theorem `Verify.FrameTutor.magic_version.verified` has type
  `VerificationResult Obligations.FrameTutor.magic_version.claim` and its
  transitive proof term depends on **zero** custom axioms (`Assumptions.*`,
  `sorryAx`, etc.).
- **`Totals: 1 unconditional, 0 conditional`**:
  Every subject item in `.anneal/manifest.json` is accounted for. If any
  subject item is missing a `Verify.<Crate>.<Item>.verified` theorem,
  verification fails immediately.
- **`TrustedBoundary kernel replay: PASS`**:
  `check_trusted.py` verified that:
  1. `lean --run trusted/audit/TrustedBoundary.lean` replayed the compiled
     `.olean` environment in the Lean 4 kernel (`Environment.replay`),
  2. No module in `Mir.*` or `Obligations.*` imports `Anneal.*` (so the statement
     of `claim` is expressed purely in `Trusted.*` types), and
  3. No `sorryAx`, `unsafe`, `partial`, or `native_decide` constants appear
     anywhere in the dependency cone of `Verify.FrameTutor.magic_version.verified`.

---

## 6. What Happens When a Safe Function Can Panic on Overflow? (`advance_offset`)

Now suppose we add a second safe function to `src/lib.rs` (in your own copy of
`examples/tutor-ch1/`; the comment at the top of the file marks the spot) that
advances a 1-byte header offset by 4 bytes, **without** any precondition:

<!-- tutor: file step=ch1-advance-offset-verify-fails path=src/lib.rs -->
```rust
// Chapter 1 of the Anneal Tutor (docs/tutor/01-basic-usage-and-outputs.md)
// runs its commands against this crate. Section 6 asks you to add a second
// function below and watch verification reject it; Chapter 2 continues from
// the crate in examples/tutor-ch2/.

pub const fn magic_version() -> u32 {
    1
}

pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}
```

What happens when we run `cargo anneal verify` now—and how does Anneal's
`Partial` model classify `offset + 4` when `offset >= 252`?

### 6.1 Defined Panic (`TerminationKind.panic`) vs. Undefined Behavior (`.fail .ub`)

In Rust's `Runtime(PostCleanup)` MIR, `offset + 4` on `u8` lowers to two basic
blocks:
1. `bb0` computes `_2 = AddWithOverflow(copy _1, const 4_u8)` and terminates
   with `assert(move (_2.1: bool) == false) -> [success: bb1, unwind: continue]`.
2. `bb1` extracts `_0 = move (_2.0: u8)` and returns.

When `offset` is a valid 1-byte `u8` scalar `.scalar { bits := b, sizeBytes := 1 }`
with `b ∈ [252, 255]`:
- `b + 4 ≥ 256` (`scalarModulus 1`), so the overflow flag `_2.1` is `true`
  (`.scalar ⟨1, 1⟩`).
- The MIR `assert(_2.1 == false)` terminator takes its failure branch and halts
  with `.terminal .panic` (`FuncResult.panic`), **not** `.fail .ub`!

In Rust, a checked arithmetic panic is **defined behavior**, not Undefined
Behavior. Consequently, in `Trusted.StepResult` and `Anneal.FuncProg`:
- `PrefixOutcome.isSafe` and `FuncResult.isSafe` evaluate to **`True`** on
  `.terminal .panic` and `.terminal .abort` (and **`False`** only on
  `.fail .ub`, `.fail .unsupported`, and `.fail .outOfFuel`).
- Therefore, `(MirExecPartial advance_offset.body [.scalar ⟨b, 1⟩]).defined`
  (`MirNoUB`) is **`True` for all 256 `u8` values** `b ∈ [0, 255]`!

### 6.2 Why `defaultProof` Still Fails: `WP` (Panic-Free) vs. `WPSafe` (Partial-Correctness Safety)

If `(MirExecPartial advance_offset.body [.scalar ⟨b, 1⟩]).defined` is `True` for
all 256 `u8` values, why does `Verify.FrameTutor.advance_offset.defaultProof`
fail to compile?

Because [`theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean`](../../theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean) provides **two**
weakest-precondition combinators (`verifyByWP` and `verifyByWPSafe`), and `defaultProof` uses
the stronger, panic-forbidding `verifyByWP`:

| `FuncResult α` Outcome | `(FuncResult.toPartial r).defined` (`r.isSafe`) | `WPSafe r post` (`verifyByWPSafe`) | `WP r post` (`verifyByWP`, used by `defaultProof`) |
| :--- | :--- | :--- | :--- |
| `.ok v` (normal return) | `True` | `post v` | `post v` |
| `.div` (divergence) | `True` | `True` | `True` |
| `.panic` (`TerminationKind.panic`) | `True` (defined unwinding) | **`True`** (`wpSafe_panic`) | **`False`** (`wp_panic`) |
| `.abort` (`TerminationKind.abort`) | `True` (defined process abort) | **`True`** (`wpSafe_abort`) | **`False`** (`wp_abort`) |
| `.fail k` (`.ub`, `.unsupported`, `.outOfFuel`) | `False` (`Partial.ub`) | `False` (`wpSafe_fail`) | `False` (`wp_fail`) |

Here is the difference between the two transformers:
- **`WP` (`verifyByWP`)** proves **normal return without panicking or aborting**
  (`NoPanicOrAbortSpec`). Because `defaultProof` runs `verifyByWP ... 64` with
  `pre := True`, it asks whether `advance_offset` returns normally without
  panicking for *all* `args : List Value`. That is false for two reasons:
  1. `defaultPre := True` does not restrict `args` to a 1-byte `u8` scalar
     (`WellTypedScalarArg1 1`), and
  2. Even for well-typed `u8` values, `offset ∈ [252, 255]` evaluates to
     `FuncResult.panic`, where `WP .panic _ = False`.
- **`WPSafe` (`verifyByWPSafe`)** proves **undefined-behavior freedom and
  partial functional correctness**: `.panic` and `.abort` evaluate to `True`
  (`wpSafe_panic`), while `.fail _` evaluates to `False`. As we will see at the
  beginning of [Chapter 2](02-rust-specifications.md) and in
  [Chapter 4](04-manual-proof-workflow.md), switching from `WP` to `WPSafe`
  (`verifyByWPSafe` or `verifyWellTypedSafeScalarArg1`) lets you prove that
  `advance_offset` is free of Undefined Behavior (`.defined = True`) across all
  256 `u8` inputs—either on its own (without adding any Rust `requires`/`ensures`
  contract) or paired with `refineSafeSpec` so in-contract inputs (`offset < 4`)
  also guarantee `*ret == offset + 4`.

### 6.3 Interpreting the Resulting Lake Error

Run `verify` again on the extended crate:

<!-- tutor: command step=ch1-advance-offset-verify-fails -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch1/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch1 && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor-ch1/Cargo.toml
```

When `cargo anneal verify` runs `lake build` on unannotated `advance_offset`,
`Verify/FrameTutor/advance_offset.lean` attempts to compile `defaultProof`
(`exact True.intro`), and Lean 4 rejects the proof with a type mismatch error,
after which `cargo anneal` reports the failed build and exits with status `1`:

<!-- tutor: errors step=ch1-advance-offset-verify-fails -->
```text
error: generated/Verify/FrameTutor/advance_offset.lean:27:6: Type mismatch
  True.intro
has type
  True
but is expected to have type
  Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym 64 Obligations.FrameTutor.advance_offset.claim.body
    (Trusted.Rustc.V2026_06_01.MirSemantics.initMachineState Obligations.FrameTutor.advance_offset.claim.body args✝)
    (Anneal.Rustc.V2026_06_01.SymbolicEval.mirNormalPost fun retVal x =>
      Obligations.FrameTutor.advance_offset.claim.post args✝ retVal)
error: build failed
cargo-anneal error: lake build failed with status exit status: 1 in examples/tutor-ch1/.anneal
```

How to read this error:
1. **Why `True.intro` failed**: `WP (runMirBounded 64 ... args✝) ...` did **not**
   reduce to `True` because `args✝` (`args : List Value`) is unconstrained—symbolic
   evaluation cannot step past `AddWithOverflow` and `assert` under panic-forbidding
   `WP` without knowing that `args` is a 1-byte `u8` scalar strictly less than
   `252`.
2. **What Anneal is telling you—and your two paths forward**: Because
   `advance_offset(offset: u8) -> u8` is a safe function that panics cleanly
   (`TerminationKind.panic`) on `offset >= 252` rather than triggering Undefined
   Behavior, there are **two ways** to resolve this failure depending on what you
   want to prove:
   - **Approach 1 — Switch to the weaker, panic-admitting `WPSafe` logic (UB-freedom only)**:
     Restrict `.defined` to concrete or well-typed `u8` inputs in Lean and
     discharge the obligation with `WPSafe` (`verifyByWPSafe`), proving that
     `advance_offset` is free of Undefined Behavior (`MirNoUB`) even on inputs
     like `offset = 255` that panic on overflow—without adding any `requires` or
     `ensures` clauses in Rust.
   - **Approach 2 — Add a functional specification in Rust (`#[anneal_spec::spec]`)**:
     Annotate `advance_offset` with `requires` and `ensures` (for example,
     `requires: offset < 4, ensures: |ref ret| *ret == offset + 4`) to prove
     when the function returns normally and what value it produces—either alone
     under `WP` or combined with `WPSafe` via `refineSafeSpec`.

In [Chapter 2](02-rust-specifications.md), we compare both approaches side by
side, add Rust specifications (`#[anneal_spec::spec]`) to `pin_magic`,
`total_frame_len`, and `advance_offset`, and examine how Anneal separates
**safety preconditions (`.defined`)** from **functional preconditions (`.val`)**
in `Obligations.<Crate>.<Item>`.
