# Chapter 4: Completing a Manual Proof Workflow

[← Chapter 3 — Explicit Assumptions & Incremental Adoption](03-assumptions-and-incremental-adoption.md) | [Back to Tutor Overview](README.md) | [Next: Chapter 5 — Working with `unsafe` Code, Tree Borrows & Separation Logic →](05-verifying-unsafe-rust.md)

In [Chapter 3](03-assumptions-and-incremental-adoption.md), we verified
`frame_tutor` conditionally by placing an axiom in
`anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`. Now we will complete the
manual proof workflow:

1. Use `cargo anneal scaffold --init-specs --init-proofs` when you want starter
   templates under `anneal/proofs/`.
2. Replace the `pin_magic` assumption with a one-call kernel-checked proof using
   `dischargeRustEqU32` from `Anneal.Tactics`, and discharge the 2-argument
   conjunctive contract of `total_frame_len` using `dischargeRustEq2U8`.
3. Specify `advance_offset` (`requires: offset < 4, ensures: |ref ret| *ret == offset + 4`)
   in `Specs/FrameTutor/advance_offset.lean` using
   `Obligations.FrameTutor.advance_offset.refineSafeSpec`, discharge it in
   `Proof/FrameTutor/advance_offset.lean` using `verifyByWPSafe` alongside its
   `MirContractHoldsWithSafety` corollary (and compare with the one-call
   256-input `dischargeSafeRustBoundedU8` and 4-input `dischargeRustBoundedU8`
   combinators).
4. Delete `anneal/proofs/Assumptions/FrameTutor/pin_magic.lean` and run
   `cargo anneal verify` (with default `--disallow-assumptions`) so every item
   in `frame_tutor` verifies as `[UNCONDITIONAL]`.

---

## 1. Initializing Starter Templates (`--init-specs` and `--init-proofs`)

By default, `cargo anneal scaffold` writes only to `.anneal/generated/` and does
not create files in `anneal/proofs/`. When you are starting a manual proof or a
custom Lean specification and want starter boilerplate generated for you, pass
`--init-proofs` and/or `--init-specs`:

<!-- tutor: command step=ch4-init-templates -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- scaffold --init-specs --init-proofs --manifest-path examples/tutor-ch3/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch3 && cargo anneal scaffold --init-specs --init-proofs`):
cargo anneal scaffold --init-specs --init-proofs --manifest-path examples/tutor-ch3/Cargo.toml
```

Important safety guarantee:
- `cargo anneal scaffold --init-specs --init-proofs` **never overwrites** an
  existing file in `anneal/proofs/Specs/` or `anneal/proofs/Proof/`. If a file
  already exists, `scaffold` leaves it untouched and increments `preserved Specs`
  or `preserved Proof` in the Scaffold Report. Run on the Chapter 3 crate
  (`examples/tutor-ch3/`), where you would start writing proofs and where
  `Proof/FrameTutor/pin_magic.lean` already exists, the report reads:
  <!-- tutor: report step=ch4-init-templates -->
  ```text
  Anneal Scaffold Summary:
    Generated (.anneal/generated/): Mir: 5, Obligations: 2, Verify: 2
    Durable (anneal/proofs/): created Specs: 2, preserved Specs: 0, created Proof: 1, preserved Proof: 1
  ```
- Remember that `cargo anneal scaffold` only creates `Specs` or `Proof` files
  for items that do not verify trivially via `defaultProof` (or items you edit
  manually). If you do not need a custom `Specs/<Crate>/<Item>.lean` override
  for an item whose Rust `#[anneal_spec::spec]` attributes already state the
  full contract (like `pin_magic`), omit `--init-specs` so `defaultSpec` stays
  active. Delete any starter templates you do not intend to fill in before
  continuing; the rest of this chapter assumes only the files it lists exist.

---

## 2. Discharging `pin_magic` with `dischargeRustEqU32`

This chapter's crate is checked in at [`examples/tutor-ch4/`](../../examples/tutor-ch4/).
Starting from the Chapter 3 crate, it restores the four-item `src/lib.rs` from
[Chapter 2](02-rust-specifications.md) (Chapter 3 narrowed the crate to two
items), adds the proof and specification files shown in this chapter, and
deletes the assumption module. Recall `pin_magic`:

<!-- tutor: file step=ch4-verify path=src/lib.rs item=pin_magic -->
```rust
#[anneal_spec::spec(
    requires: magic == 7,
    ensures: |ref ret| *ret == 7,
)]
pub fn pin_magic(magic: u32) -> u32 {
    magic
}
```

Its generated obligation in `.anneal/generated/Obligations/FrameTutor/pin_magic.lean`
uses `defaultPre` (`length args = 1 ∧ MirBoolPredicateHolds __anodized_fn_requires_pin_magic.body args`)
and `defaultPost` (`MirBoolPredicateHolds __anodized_fn_ensures_pin_magic.body (args ++ [ret])`).

Because this pattern—an inline Rust `requires: x == targetBits` precondition paired
with a subject body and an inline `ensures` postcondition—is common across protocol
parsers and framing code, [`theory/Anneal/Rustc/V2026_06_01/SymReflect.lean`](../../theory/Anneal/Rustc/V2026_06_01/SymReflect.lean)
provides `dischargeRustEqU32` (along with `dischargeRustEqU8` and `dischargeRustEqUsize`).

Replace the contents of `anneal/proofs/Proof/FrameTutor/pin_magic.lean` with:

<!-- tutor: file step=ch4-verify path=anneal/proofs/Proof/FrameTutor/pin_magic.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  dischargeRustEqU32
    Obligations.FrameTutor.pin_magic.claim
    4
    64
    Mir.FrameTutor.__anodized_fn_requires_pin_magic.body
    Mir.FrameTutor.__anodized_fn_ensures_pin_magic.body
    7

end Proof.FrameTutor.pin_magic
```

### How `dischargeRustEqU32` Works Under the Hood

`dischargeRustEqU32` (an `abbrev` for width-parametric `dischargeRustEqScalar1 4`)
performs four kernel-checked steps automatically (using default tactic arguments
for width-mismatch rejection, symbolic branch inversion, and `rfl` evaluation):

1. **Inverts the lowered `requires` companion symbolically (`wpBoolOrExhaustedSym_of_mirBoolPredicateHolds`)**:
   Given `h_pre : c.pre args`, `extractRustScalarEq1 4` extracts
   `h_req : MirBoolPredicateHolds reqBody args` and evaluates
   `wpBoolOrExhaustedSym 4 reqBody args` using continuation-passing symbolic MIR
   evaluation (`evalMirBoolHoldSym` in `Anneal.Rustc.V2026_06_01.Lower`).
2. **Pins the 4-byte `u32` argument in $O(1)$ (`args = [.scalar ⟨7, 4⟩]`)**:
   Any non-scalar or non-4-byte argument causes `reqBody` to step to `.fail .ub`
   (contradicting `MirNoUB`), while a 4-byte scalar `.scalar ⟨x, 4⟩` reduces in
   WHNF to a symbolic `Nat.beq x 7` branch. Applying `eq_of_prop_branch_beq`
   inverts `Nat.beq x 7` in $O(1)$ (for arbitrary `u32` constants of any size,
   without Peano case-splitting on `x`) to obtain `x = 7` (`args = [.scalar ⟨7, 4⟩]`).
3. **Executes `pin_magic.body` (`verifyByWP c 64`)**:
   Substitutes `args = [.scalar ⟨7, 4⟩]` into `runMirBounded 64 pin_magic.body [.scalar ⟨7, 4⟩]`,
   which reduces by `rfl` to `.ok (.scalar ⟨7, 4⟩)`.
4. **Proves the lowered `ensures` companion (`mirBoolPredicateHolds_of_wp_bounded`)**:
   Evaluates `runMirBounded 64 ensBody [.scalar ⟨7, 4⟩, .scalar ⟨7, 4⟩]` by `rfl`
   to `.ok (.scalar ⟨1, 1⟩)`.

### 2.1 Discharging Multi-Argument Contracts (`total_frame_len` with `dischargeRustEq2U8`)

Now consider the 2-argument safe function `total_frame_len` in `src/lib.rs`:

<!-- tutor: file step=ch4-verify path=src/lib.rs item=total_frame_len -->
```rust
#[anneal_spec::spec(
    requires: header_len == 1 && payload_len == 2,
    ensures: |ref ret| *ret == 3,
)]
pub fn total_frame_len(header_len: u8, payload_len: u8) -> u8 {
    header_len + payload_len
}
```

Like `pin_magic`, `total_frame_len` states its full contract directly in Rust
via `#[anneal_spec::spec]`, so it needs no custom `Specs` override—its generated
`defaultSpec` in `.anneal/generated/Obligations/FrameTutor/total_frame_len.lean`
is already active. In `anneal/proofs/Proof/FrameTutor/total_frame_len.lean`,
we discharge `Obligations.FrameTutor.total_frame_len.claim` in one call using
`dischargeRustEq2U8`:

<!-- tutor: file step=ch4-verify path=anneal/proofs/Proof/FrameTutor/total_frame_len.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.total_frame_len
import Obligations.FrameTutor.total_frame_len

namespace Proof.FrameTutor.total_frame_len

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified : VerificationResult Obligations.FrameTutor.total_frame_len.claim :=
  dischargeRustEq2U8
    Obligations.FrameTutor.total_frame_len.claim
    16
    64
    Mir.FrameTutor.__anodized_fn_requires_total_frame_len.body
    Mir.FrameTutor.__anodized_fn_ensures_total_frame_len.body
    1
    2

end Proof.FrameTutor.total_frame_len
```

`dischargeRustEq2U8` generalizes `dischargeRustEqU8` to 2-argument `u8`
contracts: it inverts `MirBoolPredicateHolds __anodized_fn_requires_total_frame_len.body args`
across the short-circuiting MIR `SwitchInt` of `header_len == 1 && payload_len == 2`
to pin `args = [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩]`, executes `total_frame_len.body`
to `.ok (.scalar ⟨3, 1⟩)`, and discharges `__anodized_fn_ensures_total_frame_len.body`
by `rfl`.

---

## 3. Specifying and Discharging `advance_offset` with `refineSafeSpec` and `verifyByWPSafe`

Now consider `advance_offset` in `src/lib.rs`:

<!-- tutor: file step=ch4-verify path=src/lib.rs item=advance_offset -->
```rust
#[anneal_spec::spec(
    requires: offset < 4,
    ensures: |ref ret| *ret == offset + 4,
)]
pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}
```

As we learned in [Chapter 1](01-basic-usage-and-outputs.md) and
[Chapter 2](02-rust-specifications.md), `advance_offset` is a **safe** function
whose `requires: offset < 4` clause is a **functional precondition**:
- When `offset < 4` (for example, `offset = 2`), `advance_offset(2)` returns
  normally with `6`, satisfying `ensures: |ref ret| *ret == offset + 4`.
- When `offset >= 252` (for example, `offset = 255`), `255 + 4` overflows `u8`
  and halts via a defined Rust panic (`TerminationKind.panic`), which is **still
  free of Undefined Behavior** (`.defined = True`).

In [Chapter 2, Section 1](02-rust-specifications.md#1-two-approaches-to-resolving-a-panic-free-wp-failure),
we saw how Approach 1 used `WPSafe` (`verifyByWPSafe`) with
`post := defaultPost` (`True`) to prove UB-freedom (`MirNoUB`) alone without a
Rust `#[spec]` contract. Here, we **combine** Approach 1 and Approach 2: we use
`refineSafeSpec` and `verifyByWPSafe` so our proof establishes *both* `MirNoUB`
across panicking out-of-contract inputs (`.defined`) *and* the functional
`requires`/`ensures` contract on in-contract inputs (`.val`).

### 3.1 Separating `.defined` from `.val` in `Specs/FrameTutor/advance_offset.lean`

In `anneal/proofs/Specs/FrameTutor/advance_offset.lean`, we use
`Obligations.FrameTutor.advance_offset.refineSafeSpec` to separate the **safety
domain** (`advanceOffsetSafetyDomain`, which populates `.defined` of
`MirContractSpec`) from the **functional precondition** (`rustRequires` conjoined
with `offset = 2`, which guards `rustEnsures` and `ret = 6` inside `.val`):

<!-- tutor: file step=ch4-verify path=anneal/proofs/Specs/FrameTutor/advance_offset.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Specs.FrameTutor.advance_offset

open Trusted.MirSemantics
open Trusted.VerificationResult

/-- Two-case safety domain covering both an in-contract input (`offset = 2`,
    where `offset < 4` holds and `advance_offset` returns `6`) and an
    out-of-contract overflowing input (`offset = 255`, where `offset < 4` is
    false and `offset + 4` panics safely with `TerminationKind.panic`
    without triggering Undefined Behavior). -/
def advanceOffsetSafetyDomain (args : List Value) : Prop :=
  Or
    (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (args = List.cons (.scalar { bits := 255, sizeBytes := 1 }) List.nil)

instance : ItemSpec "frame_tutor::advance_offset" :=
  Obligations.FrameTutor.advance_offset.refineSafeSpec
    advanceOffsetSafetyDomain
    (fun args => args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil)
    (fun _ ret => ret = .scalar { bits := 6, sizeBytes := 1 })

end Specs.FrameTutor.advance_offset
```

Look closely at what this `ItemSpec` states:
- **`pre := advanceOffsetSafetyDomain`**:
  The `.defined` field of `MirContractSpec` includes **both** the in-contract
  input `offset = 2` (`Or.inl`) **and** the out-of-contract overflowing input
  `offset = 255` (`Or.inr`). Proving `VerificationResult` therefore proves
  `MirNoUB` across both inputs—demonstrating directly in the Lean 4 kernel that
  overflowing `offset + 4` at `offset = 255` is defined behavior (`MirNoUB`),
  not Undefined Behavior!
- **`post args ret := And (rustRequires args) (args = [.scalar ⟨2, 1⟩]) → And (rustEnsures args ret) (ret = .scalar ⟨6, 1⟩)`**:
  Inside `.val`, the normal-return postcondition (`*ret == offset + 4` and
  `ret = 6`) is guarded behind `rustRequires args ∧ args = [.scalar ⟨2, 1⟩]`.

### 3.2 Discharging `Proof/FrameTutor/advance_offset.lean` with `verifyByWPSafe` and `MirContractHoldsWithSafety`

Now open `anneal/proofs/Proof/FrameTutor/advance_offset.lean`:

<!-- tutor: file step=ch4-verify path=anneal/proofs/Proof/FrameTutor/advance_offset.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.advance_offset
import Specs.FrameTutor.advance_offset
import Obligations.FrameTutor.advance_offset

namespace Proof.FrameTutor.advance_offset

open Trusted.MirSemantics
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
        exact fun _ =>
          And.intro
            (mirBoolPredicateHolds_of_wp_bounded
              128
              Mir.FrameTutor.__anodized_fn_ensures_advance_offset.body
              (List.cons (.scalar { bits := 2, sizeBytes := 1 })
                (List.cons (.scalar { bits := 6, sizeBytes := 1 }) List.nil))
              rfl)
            rfl
      | inr h255 =>
        subst h255
        exact True.intro)

/-- Direct `MirContractHoldsWithSafety` corollary for `frame_tutor::advance_offset`:
    `MirExecPartial Mir.FrameTutor.advance_offset.body` refines `MirContractSpec`
    with `safetyPre := advanceOffsetSafetyDomain` (`.defined`) and the functional
    `rustRequires` / `rustEnsures` contract inside `.val` (`#125`). -/
theorem advance_offset_holds_with_safety :
    MirContractHoldsWithSafety
      Mir.FrameTutor.advance_offset.body
      advanceOffsetSafetyDomain
      (fun args =>
        And
          (Obligations.FrameTutor.advance_offset.rustRequires args)
          (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
      (fun args ret =>
        And
          (Obligations.FrameTutor.advance_offset.rustEnsures args ret)
          (ret = .scalar { bits := 6, sizeBytes := 1 })) :=
  (mirContractHoldsWithSafety_iff_mirContractHolds_imp
    Mir.FrameTutor.advance_offset.body
    advanceOffsetSafetyDomain
    (fun args =>
      And
        (Obligations.FrameTutor.advance_offset.rustRequires args)
        (args = List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
    (fun args ret =>
      And
        (Obligations.FrameTutor.advance_offset.rustEnsures args ret)
        (ret = .scalar { bits := 6, sizeBytes := 1 }))).2
    verified.proof

end Proof.FrameTutor.advance_offset
```

Trace how the two branches of `verifyByWPSafe` work:
1. **In-contract branch (`Or.inl h2`, `offset = 2`)**:
   `runMirBounded 16 advance_offset.body [.scalar ⟨2, 1⟩]` evaluates to
   `.ok (.scalar ⟨6, 1⟩)`. Under `WPSafe`, `.ok v` reduces to the postcondition
   implication, which is discharged by `mirBoolPredicateHolds_of_wp_bounded`
   (proving `rustEnsures`) and `rfl` (proving `ret = .scalar ⟨6, 1⟩`).
2. **Out-of-contract overflowing branch (`Or.inr h255`, `offset = 255`)**:
   `runMirBounded 16 advance_offset.body [.scalar ⟨255, 1⟩]` overflows `255 + 4`,
   fails the MIR `assert` terminator, and evaluates to `FuncResult.panic`.
   Because `WPSafe .panic post` is definitionally `True` (`wpSafe_panic`), the
   entire branch is discharged by `True.intro`!
3. **`advance_offset_holds_with_safety` (`MirContractHoldsWithSafety`)**:
   Applying `(mirContractHoldsWithSafety_iff_mirContractHolds_imp ...).2 verified.proof`
   unpacks `verified.proof` directly into
   `Preorder.refines (MirExecPartial advance_offset.body) (MirContractSpec advanceOffsetSafetyDomain (rustRequires ∧ offset = 2) (rustEnsures ∧ ret = 6))`.

### 3.3 Alternative: One-Call 256-Input Verification (`dischargeSafeRustBoundedU8` and `dischargeRustBoundedU8`)

When you want to prove a safe 1-argument `u8` function across **all 256
well-typed `u8` inputs** (`safetyDomain := WellTypedScalarArg1 1`) with zero
manual case splits, [`theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean`](../../theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean)
provides `verifyWellTypedSafeScalarArg1` (and `verifyWellTypedScalarArg1` when
proving panic-free contracts):

```lean
-- With `refineSafeSpec (WellTypedScalarArg1 1) (fun _ => True) (fun _ _ => True)`:
theorem verified : VerificationResult Obligations.FrameTutor.advance_offset.claim :=
  dischargeSafeRustBoundedU8
    Obligations.FrameTutor.advance_offset.claim
    16
    128
    Mir.FrameTutor.__anodized_fn_requires_advance_offset.body
    Mir.FrameTutor.__anodized_fn_ensures_advance_offset.body
    3
```

`dischargeSafeRustBoundedU8` combines `verifyWellTypedSafeScalarArg1` and
`wpSafe_imp_of_wpSafe_true` to prove `WPSafe` across all 256 `u8` values while
checking `rustEnsures` for every `offset ≤ 3` (`offset < 4`).

### 3.4 Why `Proof/<Crate>/<Item>.lean` Must `import Specs.<Crate>.<Item>`

Whenever `anneal/proofs/Specs/<Crate>/<Item>.lean` exists on disk,
**`anneal/proofs/Proof/<Crate>/<Item>.lean` must explicitly `import Specs.<Crate>.<Item>`**:

1. **Typeclass coherence across modules**:
   In `.anneal/generated/Obligations/<Crate>/<Item>.lean`, `claim` is parameterized
   by `[spec : ItemSpec "<def_id>"]`. `.anneal/generated/Verify/<Crate>/<Item>.lean`
   always imports `Specs.<Crate>.<Item>` when that file exists on disk, so in
   `Verify`, `Obligations.<Crate>.<Item>.claim` resolves `spec` to the
   normal-priority instance in `Specs.<Crate>.<Item>`.
   If `Proof.<Crate>.<Item>` forgets to `import Specs.<Crate>.<Item>`, then
   inside `Proof.<Crate>.<Item>`, `Obligations.<Crate>.<Item>.claim` would
   fall back to `defaultSpec` (`priority := low`), and `Verify` would fail with
   a type mismatch (`VerificationResult (@claim defaultSpec)` vs.
   `VerificationResult (@claim Specs.instItemSpec)`).
2. **Explicit enforcement by `cargo-anneal`**:
   As an additional safeguard, `cargo anneal agent-verify` checks that whenever
   `anneal/proofs/Specs/<Crate>/<Item>.lean` exists, `anneal/proofs/Proof/<Crate>/<Item>.lean`
   contains `import Specs.<Crate>.<Item>`.

---

## 4. Deleting the Assumption and Verifying Unconditionally

Now that `Proof/FrameTutor/pin_magic.lean`, `Proof/FrameTutor/total_frame_len.lean`,
and `Proof/FrameTutor/advance_offset.lean` contain complete kernel-checked
proofs, delete the temporary assumption module from Chapter 3 (in your copy of
the crate; `examples/tutor-ch4/` already omits it):

<!-- tutor: rm step=ch4-crate -->
```bash
rm anneal/proofs/Assumptions/FrameTutor/pin_magic.lean
```

And run `verify` (without `--allow-assumptions`):

<!-- tutor: command step=ch4-verify -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch4/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch4 && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor-ch4/Cargo.toml
```

### Unconditional Verification Report

<!-- tutor: report step=ch4-verify -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.advance_offset: UNCONDITIONAL
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Verify.FrameTutor.pin_magic: UNCONDITIONAL
  Verify.FrameTutor.total_frame_len: UNCONDITIONAL
  Totals: 4 unconditional, 0 conditional
  TrustedBoundary kernel replay: PASS
```

Every safe item in `frame_tutor` now verifies as `[UNCONDITIONAL]` (`UNCONDITIONAL`)
under `--disallow-assumptions`, and `TrustedBoundary` confirms that the `.olean`
environment replays cleanly in the Lean 4 kernel with zero custom axioms.

In [Chapter 5](05-verifying-unsafe-rust.md), we move from safe value-level
functions (where functional preconditions live in `.val` while `.defined` holds
even on panicking inputs) to **`unsafe` Rust**, where pointer validity and
Tree Borrows aliasing permissions populate `.defined` of
`MirStatefulExecPartial` and `MirStatefulContractSpec`.
