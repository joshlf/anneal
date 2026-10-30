# Chapter 3: Explicit Assumptions & Incremental Adoption

[← Chapter 2 — Adding Specifications in Rust](02-rust-specifications.md) | [Back to Tutor Overview](README.md) | [Next: Chapter 4 — Completing a Manual Proof Workflow →](04-manual-proof-workflow.md)

When adopting formal verification in an existing Rust crate, you rarely prove
every function at once. You may want to verify critical functions first while
deferring helper proofs, or you may need to state an assumption about an
external FFI function or hardware register.

In most proof assistants, developers reach for `sorry` (or `admit`) during
incremental adoption. However, `sorry` is dangerous in an automated verification
pipeline: it introduces a single undifferentiated `sorryAx` axiom into the
kernel environment, making it easy to lose track of *which* specific contract
is being assumed and impossible to distinguish a deliberately deferred boundary
from an unfinished proof tactic.

Anneal forbids `sorryAx` unconditionally and instead provides **scoped
assumption modules** under `anneal/proofs/Assumptions/<Crate>/<Item>.lean`.

---

## 1. Authoring a Scoped Assumption for `pin_magic`

Suppose our crate currently contains only `magic_version` and `pin_magic`, and
we want to verify the crate incrementally before writing the full proof of
`pin_magic` in [Chapter 4](04-manual-proof-workflow.md). This chapter's crate,
[`examples/tutor-ch3/`](../../examples/tutor-ch3/), narrows `src/lib.rs` to
those two items so the reports below stay small (Chapter 4 restores the four
safe functions from Chapter 2):

<!-- tutor: file step=ch3-verify-strict path=src/lib.rs -->
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
```

### 1.1 Declaring the Axiom in `anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`

Create `anneal/proofs/Assumptions/FrameTutor/pin_magic.lean`:

<!-- tutor: file step=ch3-verify-strict path=anneal/proofs/Assumptions/FrameTutor/pin_magic.lean -->
```lean
import Trusted
import Obligations.FrameTutor.pin_magic

namespace Assumptions.FrameTutor.pin_magic

open Trusted.VerificationResult

axiom assumed_pin_magic :
  VerificationResult Obligations.FrameTutor.pin_magic.claim

end Assumptions.FrameTutor.pin_magic
```

Notice two properties of this file:
1. Its module name begins with the `Assumptions.` prefix
   (`Assumptions.FrameTutor.pin_magic`). The `TrustedBoundary` kernel auditor
   only permits custom axioms declared inside the `Assumptions.*` namespace.
2. The axiom `assumed_pin_magic` states the exact certificate type
   `VerificationResult Obligations.FrameTutor.pin_magic.claim` (whose `.proof`
   field is the `Partial` refinement
   `Preorder.refines (MirExecPartial pin_magic.body) (MirContractSpec defaultPre defaultPre defaultPost)`).
   It cannot silently weaken the specification of `magic_version` or any other
   item in the crate.

### 1.2 Referencing the Assumption in `anneal/proofs/Proof/FrameTutor/pin_magic.lean`

Next, create `anneal/proofs/Proof/FrameTutor/pin_magic.lean` to discharge
`verified` using the scoped assumption:

<!-- tutor: file step=ch3-verify-strict path=anneal/proofs/Proof/FrameTutor/pin_magic.lean -->
```lean
import Trusted
import Obligations.FrameTutor.pin_magic
import Assumptions.FrameTutor.pin_magic

namespace Proof.FrameTutor.pin_magic

open Trusted.VerificationResult

theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  Assumptions.FrameTutor.pin_magic.assumed_pin_magic

end Proof.FrameTutor.pin_magic
```

When `cargo anneal scaffold` runs, it detects that both
`anneal/proofs/Assumptions/FrameTutor/pin_magic.lean` and
`anneal/proofs/Proof/FrameTutor/pin_magic.lean` exist on disk, adds `Assumptions`
and `Proof` to `.anneal/lakefile.toml`, and updates
`.anneal/generated/Verify/FrameTutor/pin_magic.lean` to delegate directly to
`Proof.FrameTutor.pin_magic.verified`:

<!-- tutor: file step=ch3-verify-strict path=.anneal/generated/Verify/FrameTutor/pin_magic.lean strip_module_doc -->
```lean
-- @anneal-def-id: frame_tutor::pin_magic
import Trusted
import Mir.FrameTutor.pin_magic
import Obligations.FrameTutor.pin_magic
import Assumptions.FrameTutor.pin_magic
import Proof.FrameTutor.pin_magic

namespace Verify.FrameTutor.pin_magic

open Trusted.VerificationResult

/-- Kernel-checked verification certificate for `frame_tutor::pin_magic`. -/
theorem verified : VerificationResult Obligations.FrameTutor.pin_magic.claim :=
  Proof.FrameTutor.pin_magic.verified

/-- Proposition verified by `Verify.FrameTutor.pin_magic.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := VerificationResult Obligations.FrameTutor.pin_magic.claim

end Verify.FrameTutor.pin_magic
```

---

## 2. Default Verification Rejects Assumptions (`--disallow-assumptions`)

Now run `verify` with its default flags:

<!-- tutor: command step=ch3-verify-strict -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor-ch3/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch3 && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor-ch3/Cargo.toml
```

Even though `lake build` compiles `Proof.FrameTutor.pin_magic` without error,
`cargo anneal verify` defaults to `--disallow-assumptions`. During the
`TrustedBoundary` `.olean` kernel audit, `trusted/audit/TrustedBoundary.lean`
traverses the transitive expression DAG of every `Verify.<Crate>.<Item>.verified`
theorem, finds `Assumptions.FrameTutor.pin_magic.assumed_pin_magic`, and fails
with a diagnostic naming the exact assumption (the `VERIFY_AUDIT_ITEM` line is
the audit's machine-readable verdict for the item it had already classified
before it reached `pin_magic`):

<!-- tutor: errors step=ch3-verify-strict -->
```text
cargo-anneal error: TrustedBoundary verify-audit failed in examples/tutor-ch3/.anneal (status exit status: 1):
VERIFY_AUDIT_ITEM	Verify.FrameTutor.magic_version	VerifiedUnconditional
policy:Verify.FrameTutor.pin_magic.verified depends on assumption axiom Assumptions.FrameTutor.pin_magic.assumed_pin_magic from Assumptions.FrameTutor.pin_magic (conditional verification requires allow_assumptions)
```

Why fail by default?
- A plain `cargo anneal verify` in CI is a strict gate: if it exits `0`, every
  subject item in the crate is verified **unconditionally** (`[UNCONDITIONAL]`)
  with zero user axioms.
- No developer or AI agent can slip an `axiom` into `Assumptions/` and pass a
  default `cargo anneal verify` run.

---

## 3. Enabling Conditional Verification (`cargo anneal verify --allow-assumptions`)

When you are actively migrating a crate or intentionally relying on a documented
`Assumptions.*` module, pass `--allow-assumptions`:

<!-- tutor: command step=ch3-verify-allow-assumptions -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --allow-assumptions --manifest-path examples/tutor-ch3/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor-ch3 && cargo anneal verify --allow-assumptions`):
cargo anneal verify --allow-assumptions --manifest-path examples/tutor-ch3/Cargo.toml
```

Now the audit succeeds and prints the **Verification Report** (`Anneal Verification Summary:`),
explicitly partitioning unconditional theorems from conditional ones and listing
every `Assumptions.*` axiom in each theorem's transitive dependency cone:

<!-- tutor: report step=ch3-verify-allow-assumptions -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Verify.FrameTutor.pin_magic: CONDITIONAL [Assumptions.FrameTutor.pin_magic.assumed_pin_magic]
  Totals: 1 unconditional, 1 conditional
  TrustedBoundary kernel replay: PASS
```

Notice how transparent this output is:
- `Verify.FrameTutor.magic_version` is `[UNCONDITIONAL]` (`UNCONDITIONAL`)—its
  proof does not touch `Assumptions.FrameTutor.pin_magic`.
- `Verify.FrameTutor.pin_magic` is `[CONDITIONAL (assumptions: Assumptions.FrameTutor.pin_magic.assumed_pin_magic)]`
  (`CONDITIONAL [Assumptions.FrameTutor.pin_magic.assumed_pin_magic]`)—any
  reviewer or downstream consumer sees the exact axiom name in the report.
- `Totals: 1 unconditional, 1 conditional` summarizes your incremental adoption
  progress across the crate.

---

## 4. What `--allow-assumptions` Still Forbids

Passing `--allow-assumptions` relaxes **only** the check on axioms declared
inside the `Assumptions.*` namespace. Every other `TrustedBoundary` and
`check_trusted.py` rule remains strictly enforced even when `--allow-assumptions`
is passed:

| Forbidden Construct | How `check_trusted.py` / `TrustedBoundary` Catches It |
| :--- | :--- |
| `sorry` / `admit` (`sorryAx`) | `TrustedBoundary.lean` rejects `sorryAx` anywhere in the transitive constant dependency cone of `Verify.<Crate>.<Item>.verified`, even under `--allow-assumptions`. |
| `axiom` outside `Assumptions.*` (e.g., in `Proof.*` or `Specs.*`) | Any `.axiomInfo` constant whose full Lean name does not begin with `Assumptions.` (and is not Lean's built-in `propext`, `Quot.sound`, or `Classical.choice`) is rejected immediately. |
| `unsafe` definitions or `partial` functions | Any `.opaqueInfo` (`partial def`) or `ConstantInfo.isUnsafe` constant in the dependency cone is rejected, preventing non-termination from masquerading as a proof of `False`. |
| `native_decide` (`Lean.ofReduceBool` / `Lean.trustCompiler`) | Rejected both syntactically (`FORBIDDEN_IDENT_RE`) and in the `.olean` kernel environment so unverified native code execution cannot bypass the Lean 4 kernel. |
| Weakening `Trusted.*` or polluting theorem statements with `Anneal.*` | `Mir.*` and `Obligations.*` are audited to ensure `Anneal.*` never appears in their import closures, and `Verify.<Item>.verified` must have the exact type `VerificationResult Obligations.<Item>.claim` (or `StatefulVerificationResult Obligations.<Item>.statefulClaim`). |

In [Chapter 4](04-manual-proof-workflow.md), we will replace
`Assumptions.FrameTutor.pin_magic` with a real kernel-checked proof, specify and
prove `advance_offset` using `refineSafeSpec` and `verifyByWPSafe` (along with
its `MirContractHoldsWithSafety` corollary), delete the assumption file, and
watch the entire crate verify as `[UNCONDITIONAL]`.
