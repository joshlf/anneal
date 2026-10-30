# Chapter 5: Working with `unsafe` Code, Tree Borrows & Separation Logic

[← Chapter 4 — Completing a Manual Proof Workflow](04-manual-proof-workflow.md) | [Back to Tutor Overview](README.md) | [Next: Chapter 6 — Guided Agentic Proof Workflow →](06-agentic-proof-workflow.md)

In Chapters 1 through 4, we verified safe Rust functions (`magic_version`,
`pin_magic`, `total_frame_len`, and `advance_offset`). For safe functions,
arithmetic overflow or domain violations trigger defined panics
(`TerminationKind.panic`), so `.defined` (`MirNoUB`) holds across well-typed
inputs while functional preconditions (`offset < 4`) guard normal-return
postconditions inside `.val`.

Real systems crates—protocol parsers, zero-copy deserializers, and memory
containers—also use `unsafe` Rust: raw pointer dereferences, reference retags,
byte-level transmutations, and `unsafe trait` / `unsafe impl` layout guarantees.
In this chapter, we examine how `Partial` models `# Safety` preconditions in
`.defined`, how `val : defined → B` enforces soundness at call sites, how
Anneal models memory and Tree Borrows aliasing, and how to verify
`read_version_ref`, `write_version_mut`, and `unsafe impl WireHeader for FrameLen`
in `frame_tutor` using `StatefulItemSpec`, `dischargeStatefulEq`, `Anneal.SepLogic`,
and `Anneal.BitValidity`.

---

## 1. `# Safety` Preconditions in `.defined` vs. Functional Preconditions in `.val`

Before inspecting memory layouts and Tree Borrows, compare `advance_offset` from
[Chapter 4](04-manual-proof-workflow.md) with `read_version_ref`:

```rust
// Chapter 4: Safe function with a functional precondition
#[anneal_spec::spec(
    requires: offset < 4,
    ensures: |ref ret| *ret == offset + 4,
)]
pub fn advance_offset(offset: u8) -> u8 {
    offset + 4
}

// Chapter 5: `unsafe` function with a `# Safety` precondition
/// # Safety
///
/// `hdr` must point to an initialized, readable byte in memory.
pub unsafe fn read_version_ref(hdr: &u8) -> u8 {
    *hdr
}
```

Why do their preconditions live in different fields of `Partial`?

### 1.1 `MirStatefulExecPartial` and `MirStatefulContractSpec`

In [`trusted/lean/Trusted/VerificationResult.lean`](../../trusted/lean/Trusted/VerificationResult.lean),
stateful MIR execution and stateful contracts are defined over
`Partial (BehaviorSet (Value × Memory))`:

```lean
def MirStatefulExecPartial
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory) :
    Partial (BehaviorSet (Value × Memory)) where
  defined :=
    MirNoUB.holds
      (ReachesPrefix
        MirMachine
        ⟨body, args⟩
        (initMachineStateWithMemory body args mem))
  val := fun _ out =>
    ReachesNormalReturn
      body
      (initMachineStateWithMemory body args mem)
      out.1
      out.2

def MirStatefulContractSpec
    (safetyPre : List Value → Memory → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value)
    (mem : Memory) :
    Partial (BehaviorSet (Value × Memory)) where
  defined := safetyPre args mem
  val := fun _ out => pre args mem → post args mem out.1 out.2

def MirStatefulContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre : List Value → Memory → Prop)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  Preorder.refines
    (MirStatefulExecPartial body)
    (MirStatefulContractSpec safetyPre pre post)

def MirStatefulContractHolds
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop) : Prop :=
  MirStatefulContractHoldsWithSafety body pre pre post
```

Compare how `advance_offset` and `read_version_ref` inhabit these structures:

| Aspect | Safe `advance_offset(offset: u8) -> u8` (Chapter 4) | `unsafe fn read_version_ref(hdr: &u8) -> u8` (Chapter 5) |
| :--- | :--- | :--- |
| **What happens outside the precondition?** | At `offset = 255`, `255 + 4` overflows and halts via `.terminal .panic` (`TerminationKind.panic`). Execution is **defined** (`MirNoUB` holds). | If `hdr` is dangling, misaligned, uninitialized (`.uninit`), or `.disabled` in Tree Borrows, evaluating `*hdr` faults with **`.fail .ub`** (`defined = False`, `Partial.ub`). |
| **Where the precondition belongs in `Partial`** | Inside **`.val`** (`refineSafeSpec`): `.defined` covers even out-of-contract panicking inputs (`offset = 255`), while `offset < 4` guards `ret == offset + 4` inside `.val`. | Inside **`.defined`** (`MirStatefulContractSpec pre pre post`): `defined := pre args mem` (`WellFormedOn pre`), because `MirNoUB` holds **only** when `hdr` points to an initialized, readable allocation in `mem`. |

### 1.2 How `val : defined → B` Enforces Soundness at Call Sites

Look at the type of `.val` on `MirStatefulContractSpec safetyPre pre post args mem`:

```lean
(MirStatefulContractSpec safetyPre pre post args mem).val :
  safetyPre args mem → BehaviorSet (Value × Memory)
```

Because `val` is a **dependent function** whose domain is
`(MirStatefulContractSpec ... args mem).defined` (`safetyPre args mem`), a caller
(or an interprocedural proof of a safe wrapper function that calls
`unsafe { read_version_ref(hdr) }`) **cannot extract the postcondition
`ret = 1_u8` from `.val` without first constructing a proof term
`h_safe : safetyPre args mem`!**

In other words, Lean's type system enforces Rust's `unsafe` soundness obligation
structurally:
- In Rust, the compiler requires an `unsafe { ... }` block around a call to
  `read_version_ref(hdr)` to remind the programmer to check its `# Safety`
  comment.
- In Anneal's `Partial` semantics, the `# Safety` comment is encoded as
  `.defined := safetyPre args mem`, and the dependent projection
  `val : defined → B` makes it a type error to use the return-value postcondition
  until `safetyPre args mem` (pointer alignment, bounds, initialization, and Tree
  Borrows read permission) has been discharged in the Lean 4 kernel.

---

## 2. How Anneal Models Memory, Layouts, and `unsafe` Obligations

Anneal divides its memory and aliasing reasoning across the audited semantic
kernel in [`trusted/lean/`](../../trusted/lean/) and the reusable proof theory
in [`theory/Anneal/`](../../theory/Anneal/):

### 2.1 Byte-Level Representation (`AbstractByte`, `encodeValueToBytes`, `decodeValueFromBytes`)

In [`trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Bytes.lean`](../../trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Bytes.lean)
and [`theory/Anneal/BitValidity.lean`](../../theory/Anneal/BitValidity.lean),
every byte in memory is represented by an explicit 3-state `AbstractByte`:

- `AbstractByte.uninit`: Uninitialized memory (such as padding bytes or freshly
  allocated stack slots). Reading `.uninit` into a scalar or integer type triggers
  immediate Undefined Behavior (`.ub`).
- `AbstractByte.init (b : Nat)`: An initialized concrete byte (`b < 256`).
- `AbstractByte.reloc (allocId : Nat) (byteIdx : Nat)`: A pointer-provenance
  fragment recording the `byteIdx`-th byte of a pointer to `allocId`.

Two core codec functions bridge structured MIR `Value`s and byte sequences
according to the compiler-extracted `LayoutTable`:
- `encodeValueToBytes fuel layouts ty val : Option (List AbstractByte)` encodes
  scalars (in target endianness), aggregates (inserting `.uninit` for padding
  gaps between fields), and enums (writing tags or niche encodings).
- `decodeValueFromBytes fuel layouts ty bytes : Option Value` checks bit-validity
  (including `ValidScalarRange` niches and initialization) and reconstructs the
  structured `Value`—powering `CastKind.transmute`, union field reads, and raw
  byte copies (`CopyNonOverlapping`).

### 2.2 Sub-Place Tree Borrows & Function-Entry Protectors (`Anneal.Memory`)

Anneal models pointer aliasing using **Tree Borrows** at sub-place and
byte-range granularity ([`trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean`](../../trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean)
and [`theory/Anneal/Memory.lean`](../../theory/Anneal/Memory.lean)):

- **Permission Lattice (`TreeBorrowPerm` / `AbstractPerm` / `BorrowPerm`)**:
  Every borrow tag in the borrow stack (`borrows : List BorrowEntry` / `BorrowStack`)
  carries one of four permissions:
  1. `.reserved`: Newly created mutable borrow (`&mut T`) before its first write
     (supports two-phase borrows).
  2. `.active`: Mutable borrow (`&mut T`) activated by a write.
  3. `.frozen`: Shared read-only borrow (`&T`).
  4. `.disabled`: Invalidated borrow tag; any subsequent read or write through a
     `.disabled` tag faults immediately with `.ub`.
- **Sub-Place and Byte-Range Non-Interference (`ByteRangePerm` / `accessBorrowByteRange`)**:
  Each `BorrowEntry` tracks `targetLocal`, `targetProjection` (e.g., `[.field 0]`),
  and its half-open byte range `[rangeOffset, rangeOffset + rangeLen)`.
  When code takes simultaneous mutable borrows of distinct struct fields
  (`let r0 = &mut hdr.src_port; let r1 = &mut hdr.dst_port;`), writing through
  `r0` updates `r0` to `.active` while leaving `r1` untouched
  (`disjoint_byte_range_non_interference`).
- **Function-Entry Lifetime Protectors (`ProtectorSet` / `ProtectedTags` / `activeProtectors`)**:
  When a reference argument enters a function (`RetagKind.fnEntry`), the machine
  attaches a protector ID (`protector := .some protId`) and adds `protId` to
  `memory.activeProtectors`. While that protector is active, any conflicting
  foreign write to an overlapping byte range is immediate Undefined Behavior
  (`protector_forbids_conflicting_foreign_write`), even if the protected
  reference is never dereferenced again inside the function.

### 2.3 `unsafe` Rust Proof Obligations (`Anneal.UnsafeObligations`)

[`theory/Anneal/UnsafeObligations.lean`](../../theory/Anneal/UnsafeObligations.lean)
packages the safety side conditions that populate `.defined` for `unsafe`
operations into composable predicates over `PtrVal`, `TypeLayout`, and `Memory`:

| Predicate in `Anneal.UnsafeObligations` | What It Requires |
| :--- | :--- |
| `PtrAligned ptr layout` | `ptr.offsetBytes % layout.align.bytes = 0` (`layout.align.bytes > 0`). |
| `PtrInBounds ptr layout allocLen` | `ptr.offsetBytes + layout.size.bytes ≤ allocLen`. |
| `RangeInitialized bytes offset size` | Every byte in `bytes[offset .. offset + size]` is `AbstractByte.init b` (`b < 256`). |
| `ValidBytePattern layouts ty bytes offset` | The slice at `offset` decodes via `decodeValueFromBytes` to a valid `Value` of type `ty`. |
| `RefDerefSafe layouts ty ptr allocLen borrows` | Combines non-disabled borrow permission (`permAllowsRead`), alignment, and in-bounds checks for `&T` / `&mut T` dereferences (`evalOperand_copy_deref_eq` / `evalPlaceWrite_deref_eq`). |
| `RawPtrReadSafe` / `RawPtrWriteSafe` | Alignment, bounds, and byte-validity / write-permission requirements for `*const T` and `*mut T`. |
| `CopyNonOverlappingSafe` | Source and destination alignment, bounds, and non-overlapping byte intervals (`ptrRangesDisjoint`) for `core::intrinsics::copy_nonoverlapping`. |
| `TransmuteSafe layouts srcTy dstTy srcVal` | Equi-sized layouts and valid byte decoding (`transmuteViaBytes = .ok dstVal`). |

### 2.4 Partial-Heap Separation Logic (`Anneal.SepLogic`)

When reasoning modularly about functions that touch only a small slice of
memory, [`theory/Anneal/SepLogic.lean`](../../theory/Anneal/SepLogic.lean)
provides a partial-heap separation logic (`HeapFrag` and `HeapPred := HeapFrag → Prop`):

- **Points-to & Borrow Assertions**:
  - `PointsToSep ptr sz v`: Asserts ownership of the singleton local/allocation
    slot pointed to by `ptr` containing initialized value `v`.
  - `BorrowTokenSep tag entry`: Asserts ownership of the Tree Borrows permission
    token `entry` for provenance `tag`.
- **Separating Conjunction (`sepConj` / `P ∗ Q`) and Magic Wand (`sepWand`)**:
  Splits a `HeapFrag` into disjoint local/allocation slots and disjoint borrow
  tags (`HeapFrag.Disjoint h₁ h₂`).
- **Disjoint Frame Rule (`wp_frame_disjoint`)**:
  Proves that any computation whose footprint is disjoint from a frame heap
  `h_frame` preserves every assertion `R h_frame` across execution without
  re-verifying the frame.

---

## 3. Verifying `read_version_ref` in `frame_tutor`

From here on the crate is the complete companion crate checked in at
[`examples/tutor/`](../../examples/tutor/), which extends Chapter 4's crate with
the three `unsafe` items below, their `Specs` overrides, and their proofs. Now
let's verify `read_version_ref` in `examples/tutor/src/lib.rs`:

<!-- tutor: file step=ch5-verify path=src/lib.rs item=read_version_ref docs -->
```rust
/// Reads the version byte pointed to by `hdr`.
///
/// Unlike safe `advance_offset` (which panics safely without Undefined
/// Behavior on out-of-contract inputs), `read_version_ref` is `unsafe fn`: its
/// pointer-validity precondition lives in `.defined` of
/// `MirStatefulContractSpec` via `StatefulItemSpec`.
///
/// # Safety
///
/// `hdr` must point to an initialized, readable byte in memory.
pub unsafe fn read_version_ref(hdr: &u8) -> u8 {
    *hdr
}
```

### 3.1 Why `read_version_ref` Needs a `StatefulItemSpec`

In `Mir.FrameTutor.read_version_ref.body`, the function takes one argument
`_1 : &u8` (`hdr`) and executes `_0 = copy (*_1)` followed by `return`.

What happens when `evalOperand` evaluates `*_1` (`ProjectionElem.deref`)?
In `Trusted.Rustc.V2026_06_01.MirSemantics.Places`:
1. It reads local `_1`, expecting a pointer value `.ptr ptrVal sz` where
   `ptrVal = { allocId, offsetBytes, tag }` and `sz = 1` (1 byte for `u8`).
2. It looks up `ptrVal.tag` in `mem.borrows` (`lookupBorrow mem.borrows ptrVal.tag`)
   or, for an entry-point reference pointing into an external/global allocation
   (`lookupBorrow mem.borrows ptrVal.tag = .none`), looks up `ptrVal.allocId` in
   `mem.globals` (`lookupGlobalAlloc mem.globals ptrVal.allocId`) and reads
   `sz = 1` initialized byte at `ptrVal.offsetBytes`.

Because stateless claims (`ItemSpec` / `Claim`) initialize execution with
`emptyMemory` (`globals := .nil, borrows := .nil`), dereferencing `hdr` in an
empty memory state immediately faults with `.fail .ub`
(`(MirExecPartial read_version_ref.body args).defined = False`)! To specify the
memory state in which `hdr` is dereferenceable, we use
`StatefulItemSpec "frame_tutor::read_version_ref"` and
`StatefulVerificationResult Obligations.FrameTutor.read_version_ref.statefulClaim`.

### 3.2 Writing `anneal/proofs/Specs/FrameTutor/read_version_ref.lean`

Inspect `examples/tutor/anneal/proofs/Specs/FrameTutor/read_version_ref.lean`:

<!-- tutor: file step=ch5-verify path=anneal/proofs/Specs/FrameTutor/read_version_ref.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.read_version_ref
import Obligations.FrameTutor.read_version_ref

namespace Specs.FrameTutor.read_version_ref

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

def versionAlloc : CapturedAllocation where
  allocId := 1
  bytes := List.cons (.some (UInt8.ofNat 1)) List.nil
  relocations := List.nil
  align := { bytes := 1 }
  mutability := .not

def versionMem : Memory :=
  { emptyMemory with
    globals := List.cons versionAlloc List.nil }

instance : StatefulItemSpec "frame_tutor::read_version_ref" where
  pre args mem :=
    And
      (args = List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1) List.nil)
      (mem = versionMem)
  post _ _ ret _ :=
    ret = .scalar { bits := 1, sizeBytes := 1 }

end Specs.FrameTutor.read_version_ref
```

Let's examine how this `StatefulItemSpec` populates `MirStatefulContractSpec`:
- **Safety Precondition in `.defined` (`pre args mem`)**:
  - `args` is a 1-element argument list containing the pointer
    `.ptr { allocId := 1, offsetBytes := 0 } 1` (pointing to byte offset `0` of
    allocation `1` with pointee size `1` byte).
  - `mem` is `versionMem`, which holds an immutable 1-byte allocation
    `versionAlloc` at `allocId := 1` initialized to byte `1`
    (`.some (UInt8.ofNat 1) :: .nil`).
- **Postcondition in `.val` (`post _ _ ret _`)**:
  - Given a proof that `pre args mem` holds, every normal return produces the
    1-byte `u8` scalar `1` (`ret = .scalar { bits := 1, sizeBytes := 1 }`).

### 3.3 Writing `anneal/proofs/Proof/FrameTutor/read_version_ref.lean`

Now inspect `examples/tutor/anneal/proofs/Proof/FrameTutor/read_version_ref.lean`,
which discharges `StatefulVerificationResult` using `dischargeStatefulEq` from
`Anneal.Tactics`:

<!-- tutor: file step=ch5-verify path=anneal/proofs/Proof/FrameTutor/read_version_ref.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.read_version_ref
import Specs.FrameTutor.read_version_ref
import Obligations.FrameTutor.read_version_ref

namespace Proof.FrameTutor.read_version_ref

open Trusted.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.read_version_ref

theorem verified :
    StatefulVerificationResult
      Obligations.FrameTutor.read_version_ref.statefulClaim :=
  dischargeStatefulEq
    Obligations.FrameTutor.read_version_ref.statefulClaim
    16
    (List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1) List.nil)
    versionMem
    (fun _ _ h_pre => h_pre)
    rfl

end Proof.FrameTutor.read_version_ref
```

### How `dischargeStatefulEq` Discharges `StatefulVerificationResult`

Look at the signature of `dischargeStatefulEq` in
[`theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean`](../../theory/Anneal/Rustc/V2026_06_01/SymbolicEval.lean):

```lean
theorem dischargeStatefulEq
    (c : StatefulClaim)
    (fuel : Nat)
    (expectedArgs : List Value)
    (expectedMem : Memory)
    (hPre : ∀ (args : List Value) (mem : Memory),
      c.pre args mem → args = expectedArgs ∧ mem = expectedMem)
    (hEval :
      WP (runMirStatefulBounded fuel c.body expectedArgs expectedMem)
        (fun (p : Value × Memory) =>
          c.post expectedArgs expectedMem p.fst p.snd)) :
    StatefulVerificationResult c
```

1. `hPre` (`fun _ _ h_pre => h_pre`) extracts both
   `args = [.ptr { allocId := 1, offsetBytes := 0 } 1]` and `mem = versionMem`
   from `(MirStatefulContractSpec ... args mem).defined`.
2. `dischargeStatefulEq` substitutes both equalities into
   `WP (runMirStatefulBounded 16 read_version_ref.body expectedArgs expectedMem) ...`.
3. The Lean 4 kernel evaluates `runMirStatefulBounded 16` to
   `.ok (.scalar { bits := 1, sizeBytes := 1 }, versionMem)`, and `rfl` proves
   both `(MirStatefulExecPartial read_version_ref.body args mem).defined`
   (`MirNoUB`) and `.val` refinement (`ret = .scalar { bits := 1, sizeBytes := 1 }`)!

When `cargo anneal scaffold` runs, it detects that
`Proof/FrameTutor/read_version_ref.lean` proves a `StatefulVerificationResult`
and generates `.anneal/generated/Verify/FrameTutor/read_version_ref.lean`:

<!-- tutor: file step=ch5-verify path=.anneal/generated/Verify/FrameTutor/read_version_ref.lean strip_module_doc -->
```lean
-- @anneal-def-id: frame_tutor::read_version_ref
import Trusted
import Mir.FrameTutor.read_version_ref
import Obligations.FrameTutor.read_version_ref
import Specs.FrameTutor.read_version_ref
import Proof.FrameTutor.read_version_ref

namespace Verify.FrameTutor.read_version_ref

open Trusted.VerificationResult

/-- Kernel-checked stateful verification certificate for `frame_tutor::read_version_ref`. -/
theorem verified : StatefulVerificationResult Obligations.FrameTutor.read_version_ref.statefulClaim :=
  Proof.FrameTutor.read_version_ref.verified

/-- Proposition verified by `Verify.FrameTutor.read_version_ref.verified` for whole-crate rollup. -/
abbrev Certificate : Prop := StatefulVerificationResult Obligations.FrameTutor.read_version_ref.statefulClaim

end Verify.FrameTutor.read_version_ref
```

---

## 4. Verifying Mutable Reference Writes & Tree Borrows Ownership (`write_version_mut`)

Now let's verify a mutable reference write in `examples/tutor/src/lib.rs`:

<!-- tutor: file step=ch5-verify path=src/lib.rs item=write_version_mut docs -->
```rust
/// Overwrites the protocol version byte in place through a mutable
/// reference and returns the stored version byte.
///
/// Demonstrates stateful `unsafe` verification (`StatefulItemSpec` +
/// `dischargeStatefulEq`) over an `.active` Tree Borrows `BorrowEntry` and
/// `Anneal.SepLogic` (`BorrowTokenSep`).
///
/// # Safety
///
/// `hdr` must point to a writable, uniquely borrowed byte in memory under an
/// `.active` Tree Borrows permission.
pub unsafe fn write_version_mut(hdr: &mut u8, ver: u8) -> u8 {
    *hdr = ver;
    *hdr
}
```

Unlike `read_version_ref` (which only reads `*hdr`), `write_version_mut` writes
`*hdr = ver` (`PlaceElem.deref` on the left-hand side of `StatementKind.assign`)
and then reads back `*hdr` into `_0`. In `Trusted.Rustc.V2026_06_01.MirSemantics.Places`,
a dereference write through pointer provenance tag `t` requires an `.active` (or
`.reserved`) `BorrowEntry` in `mem.borrows` covering `[rangeOffset, rangeOffset + rangeLen)`.

### 4.1 Writing `anneal/proofs/Specs/FrameTutor/write_version_mut.lean`

Inspect `examples/tutor/anneal/proofs/Specs/FrameTutor/write_version_mut.lean`:

<!-- tutor: file step=ch5-verify path=anneal/proofs/Specs/FrameTutor/write_version_mut.lean strip_module_doc -->
```lean
import Trusted
import Mir.FrameTutor.write_version_mut
import Obligations.FrameTutor.write_version_mut

namespace Specs.FrameTutor.write_version_mut

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

def writeVersionBorrow : BorrowEntry where
  tag := 1
  perm := .active
  targetLocal := 2
  targetProjection := List.nil
  protector := .some 1
  rangeOffset := 0
  rangeLen := 1

def writeVersionMem : Memory :=
  { emptyMemory with
    borrows := List.cons writeVersionBorrow List.nil
    nextTag := 2
    activeProtectors := List.cons 1 List.nil
    nextProtector := 2 }

instance : StatefulItemSpec "frame_tutor::write_version_mut" where
  pre args mem :=
    And
      (args =
        List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1)
          (List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
      (mem = writeVersionMem)
  post _ _ ret mem' :=
    And
      (ret = .scalar { bits := 2, sizeBytes := 1 })
      (mem' = writeVersionMem)

end Specs.FrameTutor.write_version_mut
```

Notice what `writeVersionBorrow` and `writeVersionMem` model:
- `writeVersionBorrow` gives provenance tag `1` `.active` Tree Borrows
  permission over the 1-byte range `[0, 1)` of `targetLocal := 2`, protected by
  function-entry lifetime protector `.some 1` (`activeProtectors := [1]`).
- `pre args mem` populates `.defined` of `MirStatefulContractSpec` with `hdr` at
  tag `1`, `ver = 2_u8`, and `mem = writeVersionMem`.
- `post _ _ ret mem'` asserts inside `.val` that `write_version_mut` returns the
  newly written byte `2_u8` and preserves the `.active` borrow entry in `mem'`.

### 4.2 Writing `anneal/proofs/Proof/FrameTutor/write_version_mut.lean`

Inspect `examples/tutor/anneal/proofs/Proof/FrameTutor/write_version_mut.lean`,
which discharges `StatefulVerificationResult` via `dischargeStatefulEq` and
pairs the theorem with a partial-heap separation logic ownership witness
(`BorrowTokenSep` from `Anneal.SepLogic`):

<!-- tutor: file step=ch5-verify path=anneal/proofs/Proof/FrameTutor/write_version_mut.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.write_version_mut
import Specs.FrameTutor.write_version_mut
import Obligations.FrameTutor.write_version_mut

namespace Proof.FrameTutor.write_version_mut

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Memory
open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Specs.FrameTutor.write_version_mut

theorem verified :
    StatefulVerificationResult
      Obligations.FrameTutor.write_version_mut.statefulClaim :=
  dischargeStatefulEq
    Obligations.FrameTutor.write_version_mut.statefulClaim
    16
    (List.cons (.ptr { allocId := 1, offsetBytes := 0 } 1)
      (List.cons (.scalar { bits := 2, sizeBytes := 1 }) List.nil))
    writeVersionMem
    (fun _ _ h_pre => h_pre)
    ⟨rfl, rfl⟩

def writeVersionRawPtr : RawPtrVal where
  allocId := 2
  offset := 0
  tag := 1

def writeVersionPartialHeap : PartialHeap where
  state := writeVersionMem
  footprint := { addrs := List.nil, tags := List.cons 1 List.nil }

theorem writeVersion_borrowToken :
    BorrowToken writeVersionRawPtr .active writeVersionPartialHeap :=
  ⟨⟨writeVersionBorrow, rfl, rfl, rfl⟩, rfl⟩

end Proof.FrameTutor.write_version_mut
```

---

## 5. Verifying `unsafe trait` and `unsafe impl` Layout Contracts (`WireHeader` for `FrameLen`)

Beyond pointer dereferences, Rust crates such as `zerocopy` rely on
`unsafe trait` and `unsafe impl` declarations (`Unaligned`, `FromZeros`,
`FromBytes`, `IntoBytes`, `TryFromBytes`) whose soundness depends on compiler
type layouts.

Anneal supports trait-level safety contracts through two attributes in
`anneal-spec` and the byte-validity layout theory in
[`theory/Anneal/BitValidity.lean`](../../theory/Anneal/BitValidity.lean). In
`examples/tutor/src/lib.rs`, `frame_tutor` declares the `WireHeader` unsafe
marker trait and implements it for `FrameLen(u8)`:

<!-- tutor: file step=ch5-verify path=src/lib.rs items="WireHeader,unsafe impl WireHeader for FrameLen" -->
```rust
#[anneal_spec::unsafe_trait]
pub unsafe trait WireHeader {}

#[anneal_spec::unsafe_impl(true)]
unsafe impl WireHeader for FrameLen {}
```

`anneal-rustc-capture` synthesizes the companion subject item
`frame_tutor::__anneal_unsafe_impl_WireHeader_for_FrameLen` (`ContractRole.unsafeTraitImpl`)
and extracts `FrameLen`'s 1-byte, 1-aligned `TypeLayout`. In
`examples/tutor/anneal/proofs/Proof/FrameTutor/__anneal_unsafe_impl_WireHeader_for_FrameLen.lean`,
we discharge `VerificationResult` via `verifyByWP` and prove all four
`Anneal.BitValidity` layout predicates (`IsUnaligned`, `IsFromBytes`,
`IsIntoBytes`, and `IsFromZeros`) for `FrameLen`:

<!-- tutor: file step=ch5-verify path=anneal/proofs/Proof/FrameTutor/__anneal_unsafe_impl_WireHeader_for_FrameLen.lean strip_module_doc -->
```lean
import Trusted
import Anneal
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Mir.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen
import Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen

namespace Proof.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.BitValidity
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval

theorem verified :
    VerificationResult
      Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen.claim :=
  verifyByWP
    Obligations.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen.claim
    8
    (fun _ _ => True.intro)

@[reducible]
def frameLenLayoutTable : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries :=
    {
      size := { bytes := 1 }
      align := { bytes := 1 }
      backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 })
      fields := .arbitrary ({ bytes := 0 } :: .nil) (0 :: .nil)
      variants := .single 0
      isUninhabited := false
    } ::
    .nil
}

@[reducible]
def frameLenTy : Ty := {
  kind := .adt "frame_tutor::FrameLen" (.uint .u8 :: .nil)
  layoutIdx := 0
}

theorem frameLen_isUnaligned :
    IsUnaligned frameLenLayoutTable frameLenTy :=
  checkUnaligned_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isFromBytes :
    IsFromBytes frameLenLayoutTable frameLenTy :=
  checkFromBytes_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isIntoBytes :
    IsIntoBytes frameLenLayoutTable frameLenTy :=
  checkIntoBytes_sound frameLenLayoutTable frameLenTy rfl

theorem frameLen_isFromZeros :
    IsFromZeros frameLenLayoutTable frameLenTy :=
  checkFromZeros_sound frameLenLayoutTable frameLenTy rfl

end Proof.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen
```

Because `TypeLayout` is extracted directly from `rustc`'s layout engine into
`.anneal/generated/Mir/`, the decidable layout certificate checkers in
`Anneal.BitValidity` (`checkUnaligned_sound`, `checkFromBytes_sound`,
`checkIntoBytes_sound`, and `checkFromZeros_sound`) discharge each layout
invariant in a single `rfl` step in the Lean 4 kernel.

---

## 6. Verifying the Complete Crate

With the three `unsafe` items, their `Specs` overrides, and their proofs in
place alongside the safe functions from Chapter 4, run `verify` once more:

<!-- tutor: command step=ch5-verify -->
```bash
# Flavour A — Inside an Anneal checkout:
cargo run -p cargo-anneal -- verify --manifest-path examples/tutor/Cargo.toml

# Flavour B — Using installed `cargo anneal` (or `cd examples/tutor && cargo anneal verify`):
cargo anneal verify --manifest-path examples/tutor/Cargo.toml
```

All seven subject items now verify unconditionally:

<!-- tutor: report step=ch5-verify -->
```text
Anneal Verification Summary:
  Verify.FrameTutor.__anneal_unsafe_impl_WireHeader_for_FrameLen: UNCONDITIONAL
  Verify.FrameTutor.advance_offset: UNCONDITIONAL
  Verify.FrameTutor.magic_version: UNCONDITIONAL
  Verify.FrameTutor.pin_magic: UNCONDITIONAL
  Verify.FrameTutor.read_version_ref: UNCONDITIONAL
  Verify.FrameTutor.total_frame_len: UNCONDITIONAL
  Verify.FrameTutor.write_version_mut: UNCONDITIONAL
  Totals: 7 unconditional, 0 conditional
  TrustedBoundary kernel replay: PASS
```

In [Chapter 6](06-agentic-proof-workflow.md), we bring all 7 subject items in
`frame_tutor` together and walk through the **Guided Agentic Proof Workflow**
(`lock-specs`, `agent-context`, `anneal-prove`, and `agent-verify`).
