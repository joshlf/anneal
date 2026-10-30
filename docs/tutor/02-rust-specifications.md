# Chapter 2: Adding Specifications in Rust

[← Chapter 1 — Basic Tool Usage & Interpreting Outputs](01-basic-usage-and-outputs.md) | [Back to Tutor Overview](README.md) | [Next: Chapter 3 — Explicit Assumptions & Incremental Adoption →](03-assumptions-and-incremental-adoption.md)

In [Chapter 1](01-basic-usage-and-outputs.md), we saw that `advance_offset(offset: u8) -> u8 { offset + 4 }`
cannot verify under `defaultProof`'s panic-forbidding `WP` across arbitrary
inputs because `offset + 4` panics when `offset >= 252`. Because a checked
arithmetic panic in Rust is defined behavior (`TerminationKind.panic`) rather
than Undefined Behavior, you have **two ways forward** depending on what you
want to prove:

1. **Approach 1 — Switch to the weaker, panic-admitting `WPSafe` logic (UB-freedom only)**:
   Constrain `.defined` in Lean to `u8` inputs (including panicking ones like
   `offset = 255`) and discharge the obligation with `WPSafe` (`verifyByWPSafe`),
   proving that `advance_offset` never triggers Undefined Behavior (`MirNoUB`)
   without adding any `requires` or `ensures` clauses in Rust.
2. **Approach 2 — Add a functional specification in Rust (`#[anneal_spec::spec]`)**:
   State what inputs `advance_offset` expects for normal return and what output
   it guarantees using the `anneal-spec` attribute crate (`#[anneal_spec::spec]`,
   `#[anneal_spec::model]`, `#[anneal_spec::invariant]`, and
   `#[anneal_spec::external_spec]`), and optionally combine both approaches via
   `refineSafeSpec`.

In this chapter, we first demonstrate Approach 1 directly on the unannotated
`advance_offset` from Chapter 1, then move to Approach 2 by adding Rust-level
specifications to `frame_tutor`, running `cargo anneal extract` and
`cargo anneal scaffold`, inspecting how Anneal translates Rust boolean contracts
into Lean 4 `Obligations` modules, and examining the foundational distinction
between **safety preconditions (`.defined`)** and **functional preconditions
(`.val`)** in `Partial`.

---

## 1. Two Approaches to Resolving a Panic-Free `WP` Failure

Recall from the end of [Chapter 1](01-basic-usage-and-outputs.md) why
`defaultProof` (`verifyByWP ... 64`) rejected unannotated
`pub fn advance_offset(offset: u8) -> u8 { offset + 4 }`:
1. `defaultPre := True` left the entry argument list `args : List Value`
   unconstrained (not even restricted to a 1-byte `u8` scalar), and
2. `defaultProof` used the panic-forbidding weakest-precondition transformer
   `WP` (`verifyByWP`), which maps `FuncResult.panic` (`offset >= 252`) to
   `False`.

Before reaching for Rust pre- and postconditions, ask what property you want
your verification certificate to establish:

| Goal | Which Logic & Specification to Use | What `VerificationResult` Proves |
| :--- | :--- | :--- |
| **Well-formedness / UB-freedom only** (admitting panics on overflow) | **Approach 1**: Keep `src/lib.rs` unannotated; restrict `pre` (`.defined`) to `u8` inputs in `Specs/` and prove with `WPSafe` (`verifyByWPSafe`). | Across the specified `u8` inputs (including overflowing inputs like `offset = 255`), `advance_offset` executes without Undefined Behavior (`MirNoUB`, `Language.WellFormedOn`), either returning normally or panicking cleanly. |
| **Functional correctness on in-domain inputs** (with or without `WPSafe` on out-of-domain inputs) | **Approach 2**: Annotate `advance_offset` with `#[anneal_spec::spec(requires: offset < 4, ensures: \|ref ret\| *ret == offset + 4)]` (paired with `defaultSpec` under `WP`, or with `refineSafeSpec` under `WPSafe`). | Whenever `offset < 4`, `advance_offset` returns `offset + 4` (`rustEnsures`); when paired with `refineSafeSpec` ([Section 5](#5-safety-preconditions-defined-vs-functional-preconditions-val) and [Chapter 4](04-manual-proof-workflow.md)), it *also* proves `MirNoUB` across panicking inputs. |

### 1.1 Approach 1 — Proving UB-Freedom with `WPSafe` (No Rust `#[spec]`)

Suppose your only goal for `advance_offset` in the Chapter 1 crate
([`examples/tutor-ch1/`](../../examples/tutor-ch1/) with `advance_offset`
appended to `src/lib.rs`) is to prove that it is well-formed (`MirNoUB`)—both on
a normal input (`offset = 2`) and on an overflowing input (`offset = 255`)—without
adding `anneal-spec` to `Cargo.toml` or writing `requires`/`ensures` annotations
in Rust.

First, create `anneal/proofs/Specs/FrameTutor/advance_offset.lean` to restrict
`.defined` (`pre`) to a two-case `u8` domain (`offset = 2` or `offset = 255`)
while keeping `post := defaultPost` (`True`):

<!-- tutor: file step=ch2-wpsafe-only path=anneal/proofs/Specs/FrameTutor/advance_offset.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Specs.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult

/-- Two-case safety domain covering both a non-overflowing input (`offset = 2`,
    which returns `6`) and an overflowing input (`offset = 255`, where
    `offset + 4` panics safely with `TerminationKind.panic` without triggering
    Undefined Behavior). -/
def advanceOffsetSafetyDomain (args : List Value) : Prop :=
  Or
    (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (args = List.cons (.scalar { bits := 255, sizeBytes := 1 }) List.nil)

instance : ItemSpec "frame_tutor::advance_offset" where
  pre := advanceOffsetSafetyDomain
  post := Obligations.FrameTutor.advance_offset.defaultPost

end Specs.FrameTutor.advance_offset
```

Notice two details in `Specs/FrameTutor/advance_offset.lean`:
1. **`advanceOffsetSafetyDomain` in `.defined`**:
   `advanceOffsetSafetyDomain` includes both `offset = 2` (`.scalar { bits := 2, sizeBytes := 1 }`)
   and the overflowing input `offset = 255` (`.scalar { bits := 255, sizeBytes := 1 }`).
   Under panic-forbidding `WP`, no proof could ever succeed when `offset = 255`
   is in `pre`, because `255 + 4` panics!
2. **`post := defaultPost` (`True`)**:
   Because `advance_offset` has no `#[anneal_spec::spec]` attributes in
   `src/lib.rs`, `Obligations.FrameTutor.advance_offset.defaultPost` is simply
   `fun _ _ => True`.

Next, create `anneal/proofs/Proof/FrameTutor/advance_offset.lean` to discharge
the claim using `verifyByWPSafe` instead of `defaultProof`'s `verifyByWP`:

<!-- tutor: file step=ch2-wpsafe-only path=anneal/proofs/Proof/FrameTutor/advance_offset.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.advance_offset
import Specs.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Proof.FrameTutor.advance_offset

open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.advance_offset

theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  verifyByWPSafe
    Obligations.FrameTutor.advance_offset.claim
    16
    (by
      intro args h_safe
      cases h_safe with
      | inl h2 =>
        subst h2
        exact True.intro
      | inr h255 =>
        subst h255
        exact True.intro)

end Proof.FrameTutor.advance_offset
```

Compare this directly with `defaultProof` from Chapter 1:
- In the `inl h2` branch (`offset = 2`), `runMirBounded 16` steps `2 + 4` to
  `.ok (.scalar ⟨6, 1⟩)`. Because `post` is `defaultPost` (`True`),
  `WPSafe (.ok _) (fun _ => True)` reduces definitionally to `True` and is
  discharged by `exact True.intro`.
- In the `inr h255` branch (`offset = 255`), `runMirBounded 16` overflows
  `255 + 4` and halts at the MIR `assert` terminator with `FuncResult.panic`.
  Whereas `WP .panic _` reduced to `False` in Chapter 1, `WPSafe .panic _`
  reduces definitionally to `True` (`wpSafe_panic`)—so `exact True.intro`
  discharges the panicking branch too!
  *(To quantify over all 256 `u8` values without listing cases by hand,
  `Anneal.Tactics` also provides `WellTypedScalarArg1 1`,
  `verifyWellTypedSafeScalarArg1`, and `dischargeSafeRustBoundedU8`; see
  [Chapter 4, Section 3.3](04-manual-proof-workflow.md#33-alternative-one-call-256-input-verification-dischargesaferustboundedu8-and-dischargerustboundedu8).)*

Run `cargo anneal verify` on that crate:

<!-- tutor: command step=ch2-wpsafe-only -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch1/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch1 && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor-ch1/Cargo.toml
```

Both `magic_version` and unannotated `advance_offset` verify as `UNCONDITIONAL`:

<!-- tutor: report step=ch2-wpsafe-only -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.advance_offset: UNCONDITIONAL
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Totals: 2 unconditional, 0 conditional
  TrustedBoundary kernel replay: PASS
```

### 1.2 Approach 2 — Adding Functional Pre/Postconditions (`#[anneal_spec::spec]`)

When is Approach 1 sufficient, and when do you need Approach 2?
- **Use Approach 1 (`WPSafe` without `#[spec]`)** when you are auditing safe
  functions for Undefined Behavior freedom (`MirNoUB`) and clean panics are an
  acceptable outcome that callers do not need to rule out logically.
- **Use Approach 2 (`#[anneal_spec::spec(requires: ..., ensures: ...)]`)** when
  you want to prove *when* a function returns normally without panicking and
  *what value* it produces (for example, that `advance_offset(offset)` returns
  `offset + 4` whenever `offset < 4`).
- **Combine both approaches (`#[anneal_spec::spec]` + `refineSafeSpec` + `WPSafe`)**
  when you want the best of both worlds: proving that a safe function is free of
  Undefined Behavior across panicking out-of-contract inputs (`.defined`) *and*
  satisfies its functional `requires`/`ensures` contract on in-contract inputs
  (`.val`). We examine how `refineSafeSpec` expresses this combination in
  [Section 5](#5-safety-preconditions-defined-vs-functional-preconditions-val)
  below and complete the combined proof in
  [Chapter 4, Section 3](04-manual-proof-workflow.md#3-specifying-and-discharging-advance_offset-with-refinesafespec-and-verifybywpsafe).

If you tried Approach 1 in your own copy of `examples/tutor-ch1/`, remove
`anneal/proofs/Specs/FrameTutor/advance_offset.lean` and
`anneal/proofs/Proof/FrameTutor/advance_offset.lean` before continuing, or
switch directly to [`examples/tutor-ch2/`](../../examples/tutor-ch2/), which is
the crate the rest of this chapter runs against.

---

## 2. Annotating `frame_tutor` with `anneal_spec` Attributes

This chapter's crate is checked in at [`examples/tutor-ch2/`](../../examples/tutor-ch2/);
it differs from Chapter 1's crate in exactly the two files shown next. First,
add `anneal-spec` to `Cargo.toml`:

<!-- tutor: file step=ch2-extract path=Cargo.toml -->
```toml
[package]
name = "frame_tutor"
version = "0.1.0"
edition = "2024"
publish = false

[workspace]

[dependencies]
anneal-spec = { path = "../../crates/anneal-spec" }
```

Now replace `src/lib.rs` with annotated functions and types. The glob import
`use anneal_spec::*;` is required: the attribute macros expand to code that
refers to the support module `anneal_spec::__`, and without the import
`cargo check` fails with ``cannot find module or crate `anodized` ``:

<!-- tutor: file step=ch2-extract path=src/lib.rs -->
```rust
use anneal_spec::*;

pub const fn magic_version() -> u32 {
    1
}

#[anneal_spec::spec(
    requires: magic == 7,
    ensures: |ref ret| *ret == 7,
)]
pub fn pin_magic(magic: u32) -> u32 {
    magic
}

#[anneal_spec::spec(
    requires: header_len == 1 && payload_len == 2,
    ensures: |ref ret| *ret == 3,
)]
pub fn total_frame_len(header_len: u8, payload_len: u8) -> u8 {
    header_len + payload_len
}

#[anneal_spec::spec(
    requires: offset < 4,
    ensures: |ref ret| *ret == offset + 4,
)]
pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}

#[anneal_spec::model]
pub const fn is_valid_version(v: u8) -> bool {
    v == 1
}

#[anneal_spec::invariant(self.0 <= 64)]
pub struct FrameLen(pub u8);
```

### How Each `anneal_spec` Attribute Works

1. **`#[anneal_spec::spec(requires: ..., ensures: |ref ret| ...)]`**:
   Built on `anodized`, `#[anneal_spec::spec]` synthesizes hidden companion
   functions in the same module:
   - `__anodized_fn_requires_<item>(...) -> bool` tagged with the custom diagnostic
     attribute `#[anneal::contract(role = "requires", target = "<item>")]`, and
   - `__anodized_fn_ensures_<item>(..., ret: &RetTy) -> bool` tagged with
     `#[anneal::contract(role = "ensures", target = "<item>")]`.
   Because these companion functions are ordinary Rust functions compiled by
   `rustc`, they go through full borrow checking, type checking, and MIR
   lowering alongside the subject function.
2. **`#[anneal_spec::model]`**:
   Marks a pure Rust specification helper (`pub const fn is_valid_version(v: u8) -> bool`)
   with `ContractRole.model`. The macro also emits a hidden marker constant
   `__ANNEAL_MODEL_is_valid_version` next to the helper, which is how
   `anneal-rustc-capture` recognizes the helper's role; both are captured as
   `model` records. `cargo anneal extract` captures the helper's MIR into
   `.anneal/generated/Mir/FrameTutor/is_valid_version.lean` so specifications
   can invoke it, without creating a standalone `Verify/FrameTutor/is_valid_version.lean`
   proof obligation.
3. **`#[anneal_spec::invariant(self.0 <= 64)]`**:
   Synthesizes a companion predicate method `FrameLen::__anneal_type_invariant_frame_len(&self) -> bool`
   tagged with `ContractRole.typeInvariant`. Its MIR is captured in
   `.anneal/generated/Mir/FrameTutor/FrameLen___anneal_type_invariant_frame_len.lean`
   and linked in `.anneal/manifest.json` so functions accepting or returning
   `FrameLen` can reference its structural invariant.
4. **`#[anneal_spec::external_spec]`**:
   When your crate calls a function defined in an external dependency (or `core` /
   `std`) that you cannot annotate directly, `#[anneal_spec::external_spec]`
   lets you attach `requires` and `ensures` clauses to an external path:
   ```rust
   #[anneal_spec::external_spec(
       target = "core::num::<impl u8>::wrapping_add",
       requires: self < 128 && rhs < 128,
       ensures: |ref ret| *ret == self + rhs,
   )]
   fn spec_u8_wrapping_add(self_: u8, rhs: u8) -> u8 {
       self_.wrapping_add(rhs)
   }
   ```
   `anneal-rustc-capture` records `ContractRole.externalSpec` with the target
   path in `.anneal/manifest.json` so interprocedural proofs can bind the
   external contract without modifying the upstream crate.

---

## 3. Re-Running `cargo anneal extract` and `cargo anneal scaffold`

Let's run `extract` and `scaffold` on the updated `frame_tutor` crate:

<!-- tutor: command step=ch2-extract,ch2-scaffold -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- extract --manifest-path examples/tutor-ch2/Cargo.toml
cargo run -p cargo-anneal -- scaffold --manifest-path examples/tutor-ch2/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or the same subcommands inside `examples/tutor-ch2/`):
cargo anneal extract --manifest-path examples/tutor-ch2/Cargo.toml
cargo anneal scaffold --manifest-path examples/tutor-ch2/Cargo.toml
```

### Updated Extract Report

Observe how the Extract Report now accounts for both subject items and companion
contract items (`requires: 3`, `ensures: 3`, and `qualifiers: 3`):

<!-- tutor: report step=ch2-extract -->
```text
Anneal Extract Summary:
  Rust source files: 1
  Total MIR targets: 16
  Subject items: 4
  Companion items: requires: 3, ensures: 3, qualifiers: 3, external_spec: 0, model: 2, invariant: 1, unsafe_trait_impl: 0
  Subject mappings:
    frame_tutor::advance_offset -> Mir.FrameTutor.advance_offset
    frame_tutor::magic_version -> Mir.FrameTutor.magic_version
    frame_tutor::pin_magic -> Mir.FrameTutor.pin_magic
    frame_tutor::total_frame_len -> Mir.FrameTutor.total_frame_len
```

Let's trace the 16 MIR targets captured by `anneal-rustc-capture`:
- **4 Subject items** (`Subject items: 4`):
  - `frame_tutor::magic_version` → `Mir.FrameTutor.magic_version`
  - `frame_tutor::pin_magic` → `Mir.FrameTutor.pin_magic`
  - `frame_tutor::total_frame_len` → `Mir.FrameTutor.total_frame_len`
  - `frame_tutor::advance_offset` → `Mir.FrameTutor.advance_offset`
- **3 Inline `requires` companions** (`requires: 3`):
  - `frame_tutor::__anodized_fn_requires_pin_magic` → `Mir.FrameTutor.__anodized_fn_requires_pin_magic`
  - `frame_tutor::__anodized_fn_requires_total_frame_len` → `Mir.FrameTutor.__anodized_fn_requires_total_frame_len`
  - `frame_tutor::__anodized_fn_requires_advance_offset` → `Mir.FrameTutor.__anodized_fn_requires_advance_offset`
- **3 Inline `ensures` companions** (`ensures: 3`):
  - `frame_tutor::__anodized_fn_ensures_pin_magic` → `Mir.FrameTutor.__anodized_fn_ensures_pin_magic`
  - `frame_tutor::__anodized_fn_ensures_total_frame_len` → `Mir.FrameTutor.__anodized_fn_ensures_total_frame_len`
  - `frame_tutor::__anodized_fn_ensures_advance_offset` → `Mir.FrameTutor.__anodized_fn_ensures_advance_offset`
- **3 Inline `qualifiers` companions** (`qualifiers: 3`):
  - `frame_tutor::__anodized_fn_qualifiers_pin_magic` → `Mir.FrameTutor.__anodized_fn_qualifiers_pin_magic`
  - `frame_tutor::__anodized_fn_qualifiers_total_frame_len` → `Mir.FrameTutor.__anodized_fn_qualifiers_total_frame_len`
  - `frame_tutor::__anodized_fn_qualifiers_advance_offset` → `Mir.FrameTutor.__anodized_fn_qualifiers_advance_offset`
- **2 `model` records** (`model: 2`):
  - `frame_tutor::is_valid_version` → `Mir.FrameTutor.is_valid_version`
  - `frame_tutor::__ANNEAL_MODEL_is_valid_version` → `Mir.FrameTutor.__ANNEAL_MODEL_is_valid_version`
    (the marker constant emitted by `#[anneal_spec::model]`)
- **1 `invariant` companion** (`invariant: 1`):
  - `frame_tutor::FrameLen::__anneal_type_invariant_frame_len` → `Mir.FrameTutor.FrameLen___anneal_type_invariant_frame_len`

### Updated Scaffold Report

<!-- tutor: report step=ch2-scaffold -->
```text
Anneal Scaffold Summary:
  Generated (.anneal/generated/): Mir: 16, Obligations: 4, Verify: 4
  Durable (anneal/proofs/): created Specs: 0, preserved Specs: 0, created Proof: 0, preserved Proof: 0
```

Notice that `.anneal/generated/Mir/` contains all 16 MIR modules (subjects +
companions), while `Obligations/` and `Verify/` contain 4 modules—one for each
subject item (`magic_version`, `pin_magic`, `total_frame_len`, and `advance_offset`).

---

## 4. Inspecting `Obligations/FrameTutor/pin_magic.lean`

Open `.anneal/generated/Obligations/FrameTutor/pin_magic.lean` to see how
`cargo anneal scaffold` links `pin_magic` to its companion `requires` and
`ensures` MIR bodies and generates the four specification-refinement
combinators:

<!-- tutor: file step=ch2-scaffold path=.anneal/generated/Obligations/FrameTutor/pin_magic.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.pin_magic
import Mir.FrameTutor.__anodized_fn_requires_pin_magic
import Mir.FrameTutor.__anodized_fn_ensures_pin_magic

namespace Obligations.FrameTutor.pin_magic

set_option linter.unusedVariables false

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.VerificationResult

/-- Default precondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `requires` companions for `frame_tutor::pin_magic` (or `True`
    when no companion contract is present). -/
def defaultPre (args : List Value) : Prop :=
  And (Trusted.Sequence.length args = Mir.FrameTutor.pin_magic.body.argCount) (MirBoolPredicateHolds Mir.FrameTutor.__anodized_fn_requires_pin_magic.body args)

/-- Default postcondition lowered automatically from Rust `#[spec]` /
    `#[external_spec]` `ensures` companions for `frame_tutor::pin_magic` (or `True`
    when no companion contract is present). -/
def defaultPost (args : List Value) (ret : Value) : Prop :=
  MirBoolPredicateHolds Mir.FrameTutor.__anodized_fn_ensures_pin_magic.body (List.append args (List.cons ret List.nil))

/-- Trusted `requires` predicate lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::pin_magic`. -/
abbrev rustRequires : List Value → Prop := defaultPre

/-- Trusted `ensures` relation lowered from companion `#[spec]` and
    `#[external_spec]` items for `frame_tutor::pin_magic`. -/
abbrev rustEnsures : List Value → Value → Prop := defaultPost

/-- Low-priority default `ItemSpec` instance for `frame_tutor::pin_magic`.
    An authored normal-priority `ItemSpec` instance in `Specs.FrameTutor.pin_magic`
    automatically overrides this instance via Lean typeclass
    synthesis. -/
instance (priority := low) defaultSpec : ItemSpec "frame_tutor::pin_magic" where
  pre := defaultPre
  post := defaultPost

/-- Low-priority default `StatefulItemSpec` instance for `frame_tutor::pin_magic`. -/
instance (priority := low) defaultStatefulSpec :
    StatefulItemSpec "frame_tutor::pin_magic" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Low-priority default `TotalItemSpec` instance for `frame_tutor::pin_magic`. -/
instance (priority := low) defaultTotalSpec :
    TotalItemSpec "frame_tutor::pin_magic" where
  pre := fun args _ => defaultPre args
  post := fun args _ ret _ => defaultPost args ret

/-- Refine `defaultSpec` by conjoining additional Lean `extraPre` and
    `extraPost` clauses while preserving `rustRequires` and `rustEnsures`. -/
@[instance_reducible]
         def refineSpec
    (extraPre : List Value → Prop)
    (extraPost : List Value → Value → Prop) :
    ItemSpec "frame_tutor::pin_magic" where
  pre args := And (rustRequires args) (extraPre args)
  post args ret := And (rustEnsures args ret) (extraPost args ret)

/-- Refine `defaultStatefulSpec` by conjoining additional stateful Lean
    `extraPre` and `extraPost` clauses while preserving `rustRequires` and
    `rustEnsures`. -/
@[instance_reducible]
         def refineStatefulSpec
    (extraPre : List Value → Memory → Prop)
    (extraPost : List Value → Memory → Value → Memory → Prop) :
    StatefulItemSpec "frame_tutor::pin_magic" where
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
    ItemSpec "frame_tutor::pin_magic" where
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
    StatefulItemSpec "frame_tutor::pin_magic" where
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
    TotalItemSpec "frame_tutor::pin_magic" where
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
    StatefulEquivItemSpec "frame_tutor::pin_magic" where
  specBody := specBody
  pre args m := And (rustRequires args) (extraPre args m)
  post args m0 ret m1 := And (rustEnsures args ret) (extraPost args m0 ret m1)

/-- Canonical verification claim for `frame_tutor::pin_magic` synthesized from
    `ItemSpec "frame_tutor::pin_magic"`. -/
def claim [spec : ItemSpec "frame_tutor::pin_magic"] : Claim :=
  { body := Mir.FrameTutor.pin_magic.body, pre := spec.pre, post := spec.post }

/-- Canonical stateful verification claim for `frame_tutor::pin_magic` synthesized
    from `StatefulItemSpec "frame_tutor::pin_magic"`. -/
def statefulClaim [spec : StatefulItemSpec "frame_tutor::pin_magic"] : StatefulClaim :=
  { body := Mir.FrameTutor.pin_magic.body, pre := spec.pre, post := spec.post }

/-- Canonical total-correctness verification claim for `frame_tutor::pin_magic` synthesized
    from `TotalItemSpec "frame_tutor::pin_magic"`. -/
def totalClaim [spec : TotalItemSpec "frame_tutor::pin_magic"] : TotalClaim :=
  { body := Mir.FrameTutor.pin_magic.body, pre := spec.pre, post := spec.post }

/-- Canonical program-to-program equivalence claim for `frame_tutor::pin_magic` synthesized
    from `StatefulEquivItemSpec "frame_tutor::pin_magic"`. -/
def equivClaim [spec : StatefulEquivItemSpec "frame_tutor::pin_magic"] : StatefulEquivClaim :=
  { implBody := Mir.FrameTutor.pin_magic.body, specBody := spec.specBody, pre := spec.pre, post := spec.post }

end Obligations.FrameTutor.pin_magic
```

### Understanding `defaultPre`, `defaultPost`, and `MirBoolPredicateHolds`

1. **`defaultPre` and `MirBoolPredicateHolds`**:
   `MirBoolPredicateHolds specBody args` (defined in
   [`trusted/lean/Trusted/VerificationResult.lean`](../../trusted/lean/Trusted/VerificationResult.lean))
   states that running the companion MIR body `__anodized_fn_requires_pin_magic.body`
   on `args` executes without Undefined Behavior (`MirNoUB`) and every normal
   return produces `.scalar { bits := 1, sizeBytes := 1 }` (`true`).
   If `args` is not a 1-element list containing a valid 4-byte `u32` scalar
   equal to `7`, `__anodized_fn_requires_pin_magic` either faults (falsifying
   `MirNoUB`) or returns `false` (`.scalar ⟨0, 1⟩`), so `defaultPre args` holds
   **if and only if** `args = [.scalar ⟨7, 4⟩]`.
2. **`defaultPost`**:
   Why does `anodized` generate `ensures: |ref ret| *ret == 7` with a
   by-reference parameter `ref ret` (`&u32`), yet `defaultPost` passes
   `List.append args (List.cons ret List.nil)` directly?
   In `Mir.FrameTutor.__anodized_fn_ensures_pin_magic.body`, the `ref ret`
   binding in the closure parameter pattern copies `ret` into a local and takes
   a reference to that local inside the companion body—so the companion
   function's ABI takes `(magic: u32, ret: u32)` by value (`append args [ret]`).
3. **`defaultSpec` (`priority := low`)**:
   Because `defaultSpec` is registered with `(priority := low)`, Lean 4 uses
   `defaultSpec` automatically whenever no `Specs/FrameTutor/pin_magic.lean`
   file is imported. If you define a normal-priority
   `instance : ItemSpec "frame_tutor::pin_magic"` in `Specs/FrameTutor/pin_magic.lean`,
   Lean 4's typeclass synthesis selects your custom instance instead—without
   modifying a single line in `.anneal/generated/`.

---

## 5. Safety Preconditions (`.defined`) vs. Functional Preconditions (`.val`)

Why does `Obligations.<Crate>.<Item>` generate **both** `refineSpec` /
`refineStatefulSpec` and `refineSafeSpec` / `refineSafeStatefulSpec`?

To see why, recall the Layer 1A `Partial` definitions from
[`trusted/lean/Trusted/Refinement.lean`](../../trusted/lean/Trusted/Refinement.lean):

```lean
def Partial.contract {Out : Type u}
    (safetyPre : Prop)
    (funcPre : Prop)
    (post : Out → Prop) :
    Partial (BehaviorSet Out) where
  defined := safetyPre
  val := fun _ out => funcPre → post out

def Language.WellFormedOn (L : Language) (safetyPre : L.Query → Prop) : L.Behavior :=
  fun q => {
    defined := safetyPre q
    val := fun _ _ => True
  }

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

def Language.ContractSpec (L : Language)
    (safetyPre : L.Query → Prop)
    (funcPre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => Partial.contract (safetyPre q) (funcPre q) (post q)
```

### 5.1 What Happens If You Put a Functional Precondition into `.defined`?

Consider our safe function `pub fn advance_offset(offset: u8) -> u8 { offset + 4 }`
with `#[anneal_spec::spec(requires: offset < 4, ensures: |ref ret| *ret == offset + 4)]`.

What does Rust's safety guarantee demand of a safe function `pub fn`?
- A safe function must be **free of Undefined Behavior (`MirNoUB`) across all
  well-typed inputs** (`offset ∈ [0, 255]`), corresponding to `L.WellFormed` on
  its well-typed input domain.
- When `offset < 4` holds (`funcPre`), `advance_offset` must return normally with
  `ret = offset + 4` (`post`).
- When `offset >= 4` (`¬ funcPre`), `advance_offset` is allowed to return a
  different value or panic (`offset >= 252` panics via `TerminationKind.panic`),
  **but it is still forbidden from triggering Undefined Behavior!**

Suppose instead that you place the functional precondition `offset < 4`
(`funcPre`) into `.defined` (`safetyPre := funcPre`, setting `funcPre := True`
inside `.val`). What does `L.ContractSpec funcPre (fun _ => True) post` say at an
out-of-contract input such as `offset = 255`?
- At `offset = 255`, `funcPre` is `False`, so `.defined` of the contract is
  `False`—which is `Partial.ub`!
- Because `Partial.ub` is the top element of `Partial` (`Partial.ub_top`), a
  specification with `.defined = False` at `offset = 255` **permits the function
  to exhibit Undefined Behavior at `offset = 255`**!
- Consequently, placing `offset < 4` into `.defined` only proves conditional
  well-formedness `L.WellFormedOn {offset < 4}` instead of unconditional safe-Rust
  `L.WellFormed` across all well-typed `u8` inputs.

This exact contrast is proved in [`theory/Anneal/Refinement.lean`](../../theory/Anneal/Refinement.lean)
and [`tests/refinement/ConcreteYDiagram.lean`](../../tests/refinement/ConcreteYDiagram.lean):

```lean
/-- Keeping `safetyPre := fun _ => True` and placing `funcPre` inside `.val`
    refines unconditional well-formedness (`L.WellFormed`). -/
theorem safe_contractSpec_preserves_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Preorder.refines (L.ContractSpec (fun _ => True) funcPre post) L.WellFormed :=
  Language.contractSpec_safe_refines_wellFormed funcPre post

/-- Placing a non-trivial functional precondition `funcPre` into `.defined`
    violates unconditional well-formedness (`L.WellFormed`) whenever there
    exists any query `q` with `¬ funcPre q`. -/
theorem misplaced_contractSpec_violates_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (q : L.Query) (h_not_pre : ¬ funcPre q) :
    ¬ Preorder.refines
        (L.ContractSpec funcPre (fun _ => True) post)
        L.WellFormed
```

### 5.2 Choosing Between the Four `Obligations` Combinators

`Obligations.<Crate>.<Item>` provides four combinators so you can express both
conditional-domain contracts and full safe-domain contracts:

| Combinator in `Obligations.<Item>` | `spec.pre` (`.defined` of `MirContractSpec`) | `spec.post` (`.val` of `MirContractSpec`) | When to Use |
| :--- | :--- | :--- | :--- |
| `refineSpec extraPre extraPost` | `rustRequires args ∧ extraPre args` | `rustEnsures args ret ∧ extraPost args ret` | When proving panic-free normal return (`WP`) restricted to inputs satisfying `rustRequires ∧ extraPre`. |
| `refineStatefulSpec extraPre extraPost` | `rustRequires args ∧ extraPre args m` | `rustEnsures args ret ∧ extraPost args m0 ret m1` | For `unsafe fn` (or stateful functions) whose `# Safety` memory and pointer validity preconditions (`extraPre`) genuinely gate `.defined` (`WellFormedOn`). |
| `refineSafeSpec safetyDomain extraPre extraPost` | `safetyDomain args` | `(rustRequires args ∧ extraPre args) → (rustEnsures args ret ∧ extraPost args ret)` | For **safe functions**: proves `MirNoUB` (`.defined`) across the broader `safetyDomain` (including out-of-contract inputs that panic safely under `WPSafe`) while guarding `rustEnsures ∧ extraPost` behind `rustRequires ∧ extraPre` inside `.val`. |
| `refineSafeStatefulSpec safetyDomain extraPre extraPost` | `safetyDomain args m` | `(rustRequires args ∧ extraPre args m0) → (rustEnsures args ret ∧ extraPost args m0 ret m1)` | Stateful counterpart of `refineSafeSpec` when a safe function reads or mutates `Memory` across `safetyDomain`. |

By `mirContractHoldsWithSafety_iff_mirContractHolds_imp` in
[`theory/Anneal/Rustc/V2026_06_01/Lower.lean`](../../theory/Anneal/Rustc/V2026_06_01/Lower.lean),
proving `VerificationResult claim` when `claim` uses
`refineSafeSpec safetyDomain extraPre extraPost` is logically equivalent (`↔`)
to proving:

```lean
MirContractHoldsWithSafety
  body
  safetyDomain
  (fun args => And (rustRequires args) (extraPre args))
  (fun args ret => And (rustEnsures args ret) (extraPost args ret))
```

which is `Preorder.refines (MirExecPartial body) (MirContractSpec safetyDomain (rustRequires ∧ extraPre) (rustEnsures ∧ extraPost))`!

---

## 6. Why `defaultProof` Does Not Discharge Non-Trivial `#[spec]` Contracts

If you run `cargo anneal verify` right now (before authoring proofs for
`pin_magic` and `advance_offset`), `Verify/FrameTutor/pin_magic.lean` will fail
to compile `defaultProof` (`exact True.intro`). Why?
- In `pin_magic`, `defaultPre args` is an assumption `h_pre : defaultPre args`
  in the context, and the goal is
  `WP (runMirBounded 64 pin_magic.body args) (fun ret => defaultPost args ret)`.
- Unlike `magic_version` (where `args` is unused and `defaultPost` is `True`),
  proving `defaultPost args ret` (`MirBoolPredicateHolds __anodized_fn_ensures_pin_magic.body (args ++ [ret])`)
  requires extracting `args = [.scalar ⟨7, 4⟩]` from `h_pre` (via
  `wpBoolOrExhausted_of_mirBoolPredicateHolds`) and stepping
  `__anodized_fn_ensures_pin_magic.body` via `mirBoolPredicateHolds_of_wp_bounded`.

Before we write the full proofs for `pin_magic` and `advance_offset` in
[Chapter 4](04-manual-proof-workflow.md), [Chapter 3](03-assumptions-and-incremental-adoption.md)
shows how to use **explicit scoped assumptions** (`Assumptions/FrameTutor/pin_magic.lean`)
so you can adopt Anneal incrementally across a codebase without proving every
function on day one.
