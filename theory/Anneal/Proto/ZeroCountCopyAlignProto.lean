/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted

/-!
# Prototype: zero-count / zero-byte `copy_nonoverlapping` alignment and null guard

Track-P prototype (`ws-proto-tcb-zero-count-copy-align-and-null-guard`, never
merged) for the paired TCB fix `ws-tcb-zero-count-copy-align-and-null-guard`.

## The bug

`Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingWithCount`
(`Statements.lean:3538-3550`, byte-identical in `V2026_08_01`) returns
`MirStepNode.step (advanceStmt s locals₃)` whenever `countBits = 0`, *before*
inspecting `srcVal` / `dstVal`. It therefore accepts null, misaligned, and even
non-pointer (`u32` scalar) operands, all of which Rust (`core::ptr::copy_nonoverlapping`
"must be properly aligned even when the copied size is `0`") and `lean-miri`
(`Intrinsics.copyWith`, which runs `checkAlign` on both pointers before the
zero-length `memCopy`) reject. Conversely, a ZST copy with `count > 0`
(`copy_nonoverlapping::<()>(dangling, dangling, 5)`, zero bytes) falls into the
`countBits ≠ 0` branch and spuriously faults on provenance-free dangling
pointers. Separately, the statement-level `evalCopyNonOverlapping` never checks
`countSc.sizeBytes = ptrBytes` (the terminator-level `evalCopyNonOverlappingCall`
does), and neither path checks `countSc.bits < 2^(8·ptrBytes)`.

## The prototype fix (hardened in B1)

* `resolveCopyElemLayout` uses a self-contained, target-pointer-width-aware
  (`layoutPointerBytes`, handling both 32-bit and 64-bit targets) and
  `ptrLayout.fieldLayouts`-aware resolver (`copyTySizeAndAlign?`, with zero
  dependency on `Terminators.lean` so the exact same code drops directly into
  `V2026_08_01/Statements.lean`):
  - statically non-pointer operands (`u32`, `u64`, etc.) and unsized pointees
    (`[u8]`, `str`, `dyn Trait`, `extern type`, or arrays/tuples containing one)
    yield `.ub`;
  - conflicting or unresolved pointees and non-power-of-two alignments yield
    fail-closed `.unsupported`;
  - authoritative `ptrLayout.fieldLayouts = [ptLayoutIdx]` entries resolve
    pointer-only ADT parameters even when no local in `localDecls` has type `T`
    and even when `ptLayoutIdx = 0`.
* `evalCopyNonOverlappingWithCountProto` checks `count * elemSize ≤ isize::MAX`
  first and then gates the **zero-byte** fast path on `totalBytes = 0`
  (covering both `count = 0` and ZST `elemSize = 0`, including aligned ZSTs
  such as `[u64; 0]`). Non-zero-byte copies with a resolved, non-overflowing
  layout, and every `count ≠ 0` copy whose layout is `.unsupported`, are
  delegated *unchanged* to the legacy `evalCopyNonOverlappingWithCount`.
  On `count = 0` with `.unsupported` layout, malformed pointer values (`.unit`,
  wrong width, etc.) still fault `.ub` before falling back to `.unsupported`.
* The zero-byte fragment validates each pointer through a `ZeroPtrView`
  (`malformed` / `unresolvedAddr` / `resolved addr alignKnowledge`) and a
  policy-parametric decision `ZeroPtrView.decide`:
  - `ZeroCountNullPolicy.rejectNull` (default): additionally rejects address `0`
    (mod `2^(8·ptrBytes)`, so wrapped addresses are caught);
  - `ZeroCountNullPolicy.allowRawIntrinsicNull`: exactly `lean-miri`'s raw
    `Intrinsics.copyWith` (and Rust 1.98 `core::ptr::copy_nonoverlapping`, whose
    `# Safety` clause adds "or that number must be 0" and whose `ub_checks`
    passes `zero_size := count == 0 || size == 0`).
* `stackBorrowAlignKnown` checks `entry.allocDead` (preventing frame-depth-reuse
  unsoundness when a returned callee's dead borrow collides with a new frame's
  `LocalDecl`), honors `placeTy.layoutIdx` and `rootDecl.ty.layoutIdx` at the
  target pointer width, fails closed on unlaid-out root containers, checks
  `(placeOff + p.offsetBytes) % elemAlign = 0` (catching `.downcast` offsets and
  over-aligned `align > 65536` structs), and passes the real `rootValOpt` to
  `checkTargetPlaceAlignWalk`.
* On success the step is a pure no-op: `MirStepNode.step (advanceStmt s locals₃)`
  (no slot read/write, no Tree Borrows access, no overlap check).
-/

namespace Anneal.Proto.ZeroCountCopyAlign

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Policies, outcomes, and helper predicates -/

/-- Null-pointer policy for zero-byte `copy_nonoverlapping`.

* `rejectNull` (default): address `0` is `.ub` even for zero bytes. This is a
  conservative (sound-for-verification) strengthening matching Anneal's Rust MIR
  evaluator (`crates/anneal-mir/src/lower/rvalue.rs:12808`) and pre-relaxation
  `core::ptr` validity (`library/core/src/ptr/mod.rs:19-21`), retained so that
  `.runtimeOptimized` MIR (where `-C debug-assertions=no` strips inline
  `ub_checks`) cannot accept null pointers on zero-byte copies.
* `allowRawIntrinsicNull`: the raw `lean-miri` `Intrinsics.copyWith` semantics
  (`checkAndDerefPtr` returns `.ok none` for size `0` without resolving the
  address), which coincides with Rust 1.98 `core::ptr::copy_nonoverlapping`
  (`library/core/src/ptr/mod.rs:455-457,542-545`: "or that number must be 0"
  and `maybe_is_aligned_and_not_null(ptr, align, zero_size)`). -/
inductive ZeroCountNullPolicy : Type where
  | rejectNull
  | allowRawIntrinsicNull
  deriving DecidableEq, Repr

/-- Three-valued fail-closed outcome of a zero-byte check. -/
inductive ZeroCheck : Type where
  | ok
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Left-biased sequential composition (models check order: the first failing
check determines the outcome). -/
@[reducible]
def ZeroCheck.andThen : ZeroCheck → ZeroCheck → ZeroCheck
  | .ok, r => r
  | .ub, _ => .ub
  | .unsupported, _ => .unsupported

/-- Map a `ZeroCheck` to the corresponding no-op MIR step. -/
@[reducible]
def ZeroCheck.toStep (s : MachineState) (locals₃ : List LocalSlot) : ZeroCheck → MirStepNode
  | .ok => MirStepNode.step (advanceStmt s locals₃)
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/-- Whether `addr` denotes the null address on a `ptrBytes`-byte target
(`addr ≡ 0 (mod 2^(8·ptrBytes))`, so a canonical address that wraps to `0` is
null too). -/
@[reducible]
def isNullAddr (ptrBytes addr : Nat) : Bool :=
  Nat.beq (Nat.mod addr (scalarModulus ptrBytes)) 0

/-- `isize::MAX` on a `ptrBytes`-byte target. -/
@[reducible]
def isizeMaxBytes (ptrBytes : Nat) : Nat :=
  Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1

/-- Whether `n` is a positive power of two (Rust's `Align` invariant), via the
`Trusted` helper `Align.isPowerOfTwoBytes`. -/
@[reducible]
def isPowTwoAlign (n : Nat) : Bool :=
  Align.isPowerOfTwoBytes { bytes := n }

/-- Whether `v` has the runtime shape of a well-formed thin pointer of byte
width `ptrBytes` (`.ptr _ ptrBytes`, or `.scalar ⟨bits, ptrBytes⟩` with
`bits < 2^(8·ptrBytes)`). -/
@[reducible]
def isThinPtrValue (ptrBytes : Nat) : Value → Bool
  | .ptr _ sz => Nat.beq sz ptrBytes
  | .scalar sc =>
    Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits (scalarModulus ptrBytes))
  | _ => false

/-! ## 2. Self-contained, target-width-aware & `fieldLayouts`-aware layout helpers

These helpers depend only on `Layout`, `State`, `Bytes`, and `Places` (and
**not** on `Terminators`), so the exact same definitions drop into both
`V2026_06_01/MirSemantics/Statements.lean` and
`V2026_08_01/MirSemantics/Statements.lean` without relocating anything out of
`V2026_08_01/MirSemantics/Terminators.lean`. They also respect
`layoutPointerBytes layouts` (32-bit & 64-bit targets) and preserve
`ptrLayout.fieldLayouts` / `Ty.layoutIdx`. -/

/-- Fuel-bounded list check matching `anyUnsizedRigidTy`. -/
@[reducible]
def copyAnyUnsizedRigidTy (pred : RigidTy → Bool) : List RigidTy → Bool
  | .nil => false
  | k :: rest =>
    match pred k with
    | true => true
    | false => copyAnyUnsizedRigidTy pred rest

/-- Self-contained unsized-type check (proved equal to `Trusted`'s
`isUnsizedRigidTy` below; does not depend on `V2026_08_01/Terminators.lean`). -/
@[reducible]
def copyIsUnsizedRigidTy : Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    match ty with
    | .slice _ => true
    | .str => true
    | .dynamic _ => true
    | .foreign _ => true
    | .array elemTy _ => copyIsUnsizedRigidTy fuel' elemTy
    | .tuple ks => copyAnyUnsizedRigidTy (copyIsUnsizedRigidTy fuel') ks
    | _ => false

/-- Round `bytes` up to a multiple of `alignBytes` (self-contained mirror of
`roundUpToAlign`). -/
@[reducible]
def copyRoundUpToAlign (bytes alignBytes : Nat) : Nat :=
  match Nat.beq (Nat.mod bytes alignBytes) 0 with
  | true => bytes
  | false => Nat.add bytes (Nat.sub alignBytes (Nat.mod bytes alignBytes))

/-- Scan `localDecls` for a sized declaration whose `RigidTy` structurally matches
`ty` and whose `TypeLayout` has a positive power-of-two alignment. -/
@[reducible]
def copyFindDeclLayout?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option TypeLayout :=
  match copyIsUnsizedRigidTy 8 ty with
  | true => .none
  | false =>
    let rec go : List LocalDecl → Option TypeLayout
      | .nil => .none
      | decl :: rest =>
        match rigidTyEq decl.ty.kind ty with
        | false => go rest
        | true =>
          match LayoutTable.lookup layouts decl.ty.layoutIdx with
          | .some l => .some l
          | .none => go rest
    go localDecls

/-- Fold `(size, align)` over tuple field kinds: returns `(sumOfFieldSizes,
maxFieldAlign)` or `.none` if any field fails to resolve. -/
@[reducible]
def copyTupleFieldsSizeAndAlign
    (recKind : RigidTy → Option (Nat × Nat)) :
    List RigidTy → Option (Nat × Nat)
  | .nil => .some (0, 1)
  | k :: rest =>
    match recKind k, copyTupleFieldsSizeAndAlign recKind rest with
    | .some (sz, al), .some (restSz, restAl) =>
      let maxAl :=
        match Nat.ble al restAl with
        | true => restAl
        | false => al
      .some (Nat.add sz restSz, maxAl)
    | _, _ => .none

/-- Extract validated `(size, align)` from a `TypeLayout`, rejecting
non-power-of-two alignments (including `0`). -/
@[reducible]
def validatedLayoutSizeAlign? (l : TypeLayout) : Option (Nat × Nat) :=
  match isPowTwoAlign l.align.bytes with
  | true => .some (l.size.bytes, l.align.bytes)
  | false => .none

/-- Whether `ptrBytes` is a target width (`4` or `8`) on which the ABI
alignment of `u16`/`i16`/`f16` (`2`), `u32`/`i32`/`f32`/`char` (`4`), and
pointer-width types (`ptrBytes`) is uniform across all Rust targets. On 16-bit
targets (AVR, MSP430) these may be 1-aligned. -/
@[reducible]
def copyTargetWidthUniform (ptrBytes : Nat) : Bool :=
  Bool.or (Nat.beq ptrBytes 4) (Nat.beq ptrBytes 8)

/-- Whether `ptrBytes = 8`, the only width on which `Trusted`'s structural
alignment of 8-byte and 16-byte primitives (`u64`/`i64`/`f64` → `8`, `u128`/`i128`/`f128`
→ `16`) is assumed. On 32-bit targets these vary (`align_of::<u64>()` is `4` on
`i686` but `8` on `armv7`), so claiming them would over-estimate the alignment of
a backing **place** and accept misaligned higher-aligned elements (A1). -/
@[reducible]
def copyTarget64 (ptrBytes : Nat) : Bool :=
  Nat.beq ptrBytes 8

/-- Target-pointer-width-aware `(elemSize, elemAlign)` resolution for a sized
`RigidTy`. Unlike `intrinsicRigidTy{ByteSize,Align}`, pointer-width-dependent
types (`usize`, `isize`, `*const T`, `*mut T`, `&T`, `&mut T`, `fn(...)`) use
`ptrBytes := layoutPointerBytes layouts` (4 on 32-bit, 8 on 64-bit), and wide
pointers to `[T]` / `str` / `dyn Trait` have size `2 * ptrBytes` and align
`ptrBytes`. -/
@[reducible]
def copyRigidTySizeAndAlignAux
    (ptrBytes : Nat) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Nat → RigidTy → Option (Nat × Nat)
  | .zero, _ => .none
  | .succ fuel', ty =>
    match copyIsUnsizedRigidTy 8 ty with
    | true => .none
    | false =>
      match ty with
      | .bool => .some (1, 1)
      | .char =>
        match copyTargetWidthUniform ptrBytes with
        | true => .some (4, 4)
        | false => .none
      | .never => .some (0, 1)
      | .fnDef _ _ => .some (0, 1)
      | .tuple .nil => .some (0, 1)
      | .uint .u8 | .int .i8 => .some (1, 1)
      | .uint .u16 | .int .i16 | .float .f16 =>
        match copyTargetWidthUniform ptrBytes with
        | true => .some (2, 2)
        | false => .none
      | .uint .u32 | .int .i32 | .float .f32 =>
        match copyTargetWidthUniform ptrBytes with
        | true => .some (4, 4)
        | false => .none
      | .uint .u64 | .int .i64 | .float .f64 =>
        match copyTarget64 ptrBytes with
        | true => .some (8, 8)
        | false => .none
      | .uint .u128 | .int .i128 | .float .f128 =>
        match copyTarget64 ptrBytes with
        | true => .some (16, 16)
        | false => .none
      | .uint .usize | .int .isize | .fnPtr _ _ _ _ =>
        match copyTargetWidthUniform ptrBytes with
        | true => .some (ptrBytes, ptrBytes)
        | false => .none
      | .rawPtr _ pt | .ref _ pt =>
        match copyFindDeclLayout? localDecls layouts ty with
        | .some l => validatedLayoutSizeAlign? l
        | .none =>
          match copyTargetWidthUniform ptrBytes with
          | false => .none
          | true =>
            match pt with
            | .slice _ | .str | .dynamic _ => .some (Nat.mul 2 ptrBytes, ptrBytes)
            | _ => .some (ptrBytes, ptrBytes)
      | .array elemKind n =>
        match copyFindDeclLayout? localDecls layouts elemKind with
        | .some l =>
          match validatedLayoutSizeAlign? l with
          | .some (eSz, eAl) => .some (Nat.mul eSz n, eAl)
          | .none => .none
        | .none =>
          match copyFindDeclLayout? localDecls layouts ty with
          | .some l => validatedLayoutSizeAlign? l
          | .none =>
            match copyRigidTySizeAndAlignAux ptrBytes localDecls layouts fuel' elemKind with
            | .some (eSz, eAl) => .some (Nat.mul eSz n, eAl)
            | .none => .none
      | .tuple ks =>
        match copyFindDeclLayout? localDecls layouts ty with
        | .some l => validatedLayoutSizeAlign? l
        | .none =>
          match copyTupleFieldsSizeAndAlign
              (copyRigidTySizeAndAlignAux ptrBytes localDecls layouts fuel') ks with
          | .some (rawSz, maxAl) =>
            match isPowTwoAlign maxAl with
            | true => .some (copyRoundUpToAlign rawSz maxAl, maxAl)
            | false => .none
          | .none => .none
      | _ =>
        match copyFindDeclLayout? localDecls layouts ty with
        | .some l => validatedLayoutSizeAlign? l
        | .none => .none

/-- Self-contained copy of `V2026_06_01`'s `layoutValidForResolvedAdt`
(`Places.lean:3470`), which does **not** exist in `V2026_08_01` (only
`layoutValidForAdt`, `Places.lean:3427`, does). Using this copy keeps the TCB
patch portable to both snapshots (A1; machine-checked by the port audit in
`ZeroCountCopyAlignProtoTests.lean`). -/
@[reducible]
def copyLayoutValidForResolvedAdt (layoutIdx : Nat) (l : TypeLayout) : Bool :=
  match layoutValidForAdt l with
  | true => true
  | false =>
    match Nat.beq layoutIdx 0, l.isUninhabited, l.fields, l.variants with
    | false, false, .primitive, .single _ => true
    | _, _, _, _ => false

theorem copyLayoutValidForResolvedAdt_eq (layoutIdx : Nat) (l : TypeLayout) :
    copyLayoutValidForResolvedAdt layoutIdx l = layoutValidForResolvedAdt layoutIdx l := rfl

/-- Whether `l : TypeLayout` can be trusted directly from `ty.layoutIdx` (when
`ty.layoutIdx` is non-zero and in bounds of `layouts`, avoiding synthetic
`layoutIdx := 0` aliasing `entries[0]`). -/
@[reducible]
def directTyLayout? (layouts : LayoutTable) (ty : Ty) : Option TypeLayout :=
  match isUnresolvedLayoutIdx layouts ty.layoutIdx with
  | true => .none
  | false =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .none => .none
    | .some l =>
      let ok : Bool :=
        match ty.kind with
        | .adt _ _ | .closure _ _ => copyLayoutValidForResolvedAdt ty.layoutIdx l
        | .tuple ks => layoutMatchesAggregateVariant l 0 (length ks)
        | .array _ n =>
          match l.fields with
          | .array _ count => Nat.beq count n
          | _ => false
        | _ =>
          match l.fields with
          | .primitive => true
          | _ => false
      match ok with
      | true => .some l
      | false => .none

/-- Resolve validated `(sizeBytes, alignBytes)` for a `Ty` (with optional
authoritative `TypeLayout` extracted directly from `ptrLayout.fieldLayouts`):
1. Unsized types always return `.none` (caller classifies unsized as `.ub`).
2. An authoritative `authLayoutOpt` (from `ptrLayout.fieldLayouts`) is used
   directly, validating `isPowTwoAlign` — resolving pointer-only ADT parameters
   even when no local has type `T` and even when `ptLayoutIdx = 0`.
3. A validated non-zero `ty.layoutIdx` (`directTyLayout?`) is used next, so
   nested struct fields resolved by `placeTyResolved` also retain their layout.
4. Otherwise falls back to target-pointer-width-aware
   `copyRigidTySizeAndAlignAux (layoutPointerBytes layouts) localDecls layouts 8`. -/
def copyTySizeAndAlign?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty)
    (authLayoutOpt : Option TypeLayout := .none) :
    Option (Nat × Nat) :=
  match copyIsUnsizedRigidTy 8 ty.kind with
  | true => .none
  | false =>
    match authLayoutOpt with
    | .some l => validatedLayoutSizeAlign? l
    | .none =>
      match directTyLayout? layouts ty with
      | .some l => validatedLayoutSizeAlign? l
      | .none =>
        copyRigidTySizeAndAlignAux (layoutPointerBytes layouts) localDecls layouts 8 ty.kind

/-- Resolve the validated ABI alignment of `ty` (preserving `ty.layoutIdx` and
target pointer width). -/
@[reducible]
def copyTyAlign?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option Nat :=
  match copyTySizeAndAlign? localDecls layouts ty with
  | .some (_, al) => .some al
  | .none => .none

/-! ## 3. Pointer views and the policy-parametric decision -/

/-- Abstract view of one `copy_nonoverlapping` pointer operand on the zero-byte
fragment. -/
inductive ZeroPtrView : Type where
  /-- Not a thin pointer of the target width (`.unit`, `.aggregate`, `.uninit`,
      wrong-width or out-of-range `.scalar`, wrong-width `.ptr`): `.ub`. -/
  | malformed
  /-- Provenance pointer whose canonical address is unresolvable
      (`borrowPlaceByteOffset? = none` or dead projected borrow): fail closed. -/
  | unresolvedAddr
  /-- Canonical address `addr` with alignment knowledge `aligned`:
      `some true` (aligned), `some false` (misaligned), `none` (unknown, e.g.
      under-aligned backing allocation or dead allocation with `elemAlign > 1`). -/
  | resolved (addr : Nat) (aligned : Option Bool)
  deriving DecidableEq, Repr

/-- Policy-parametric zero-byte decision for one pointer view. Check order:
shape (`.ub`), address resolution (`.unsupported`), null under `.rejectNull`
(`.ub`), then alignment (`.ub` if misaligned, `.unsupported` if unknown). -/
@[reducible]
def ZeroPtrView.decide (policy : ZeroCountNullPolicy) (ptrBytes : Nat) :
    ZeroPtrView → ZeroCheck
  | .malformed => .ub
  | .unresolvedAddr => .unsupported
  | .resolved addr aligned =>
    match policy, isNullAddr ptrBytes addr with
    | .rejectNull, true => .ub
    | _, _ =>
      match aligned with
      | .some true => .ok
      | .some false => .ub
      | .none => .unsupported

/-- Alignment knowledge for a provenance pointer `p` whose tag resolves to the
stack `BorrowEntry` `entry` at resolved sub-place offset `placeOff` (mirrors
`Terminators.writeBytesAction:3823-3845`, hardened in B1):

1. `elemAlign ≤ 1`: trivially aligned.
2. `entry.allocDead = true`: fail closed (`none`) so a dead borrow from a
   returned callee can never accidentally read the `LocalDecl` of a different
   function that later reuses `entry.targetFrameDepth`!
3. Resolve the target frame's `(decls, lays)` at `entry.targetFrameDepth`
   (`frameLocalDeclsAndLayoutsAtDepth`: active frame or saved caller frame),
   `rootDecl`, and `placeTy` (`placeTyResolved`).
4. Resolve `placeAlign := copyTyAlign? decls lays placeTy` (preserving
   `placeTy.layoutIdx` and target pointer width). If `placeAlign` is unknown or
   not a nonzero multiple of `elemAlign`, return `none` (`.unsupported`: the
   canonical `65536`-byte virtual page base is not a real alignment guarantee,
   so `&raw mut u8_local as *mut u64` must not pass).
5. Resolve `rootAlign := copyTyAlign? decls lays rootDecl.ty`:
   - unknown `rootAlign` → fail closed `none` (never assume aligned when root
     container alignment is unknown);
   - `rootAlign` not a multiple of `elemAlign` (e.g. a `u64` field inside a
     `#[repr(packed)]` struct of align `1`) → `some false` (`.ub`);
   - otherwise aligned iff `(placeOff + p.offsetBytes) % elemAlign = 0` (catches
     `.downcast` offsets and works above the `65536`-byte virtual page size for
     `#[repr(align(131072))]`), `p.offsetBytes % elemAlign = 0`, and
     `checkTargetPlaceAlignWalk` (passed the real `rootValOpt`) accepts. -/
def stackBorrowAlignKnown
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (p : ProvenancePtr)
    (entry : BorrowEntry)
    (placeOff : Nat) :
    Option Bool :=
  match Nat.ble elemAlign 1 with
  | true => .some true
  | false =>
    match entry.allocDead with
    | true => .none
    | false =>
      match
        frameLocalDeclsAndLayoutsAtDepth s.memory.callStack localDecls layouts
          entry.targetFrameDepth
      with
      | .none => .none
      | .some (decls, lays) =>
        match get? decls entry.targetLocal with
        | .none => .none
        | .some rootDecl =>
          match
            placeTyResolved decls lays
              { local_ := entry.targetLocal, projection := entry.targetProjection }
          with
          | .none => .none
          | .some placeTy =>
            match copyTyAlign? decls lays placeTy with
            | .none => .none
            | .some placeAlign =>
              match
                Bool.and (Bool.not (Nat.beq placeAlign 0))
                  (Nat.beq (Nat.mod placeAlign elemAlign) 0)
              with
              | false => .none
              | true =>
                match copyTyAlign? decls lays rootDecl.ty with
                | .none => .none
                | .some rootAlign =>
                  match
                    Bool.and (Bool.not (Nat.beq rootAlign 0))
                      (Nat.beq (Nat.mod rootAlign elemAlign) 0)
                  with
                  | false => .some false
                  | true =>
                    let rootValOpt : Option Value :=
                      match
                        readFrameLocalSlot s.frame.locals s.memory.callStack
                          s.memory.callerLocals entry.targetFrameDepth entry.targetLocal
                      with
                      | .some (.init v) => .some v
                      | _ => .none
                    .some
                      (Bool.and
                        (Nat.beq (Nat.mod (Nat.add placeOff p.offsetBytes) elemAlign) 0)
                        (Bool.and (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)
                          (checkTargetPlaceAlignWalk decls lays elemAlign p.offsetBytes
                            (.some rootDecl.ty) rootValOpt .none entry.targetProjection)))

/-- Alignment knowledge for a provenance pointer into the global allocation
`g`: the base is guaranteed `g.align.bytes`-aligned only when `g.align.bytes`
is a valid power of two and a multiple of `elemAlign`. -/
@[reducible]
def globalAllocAlignKnown (g : CapturedAllocation) (elemAlign : Nat) (p : ProvenancePtr) :
    Option Bool :=
  match Nat.ble elemAlign 1 with
  | true => .some true
  | false =>
    match
      Bool.and (isPowTwoAlign g.align.bytes)
        (Nat.beq (Nat.mod g.align.bytes elemAlign) 0)
    with
    | false => .none
    | true => .some (Nat.beq (Nat.mod p.offsetBytes elemAlign) 0)

/-- Alignment knowledge for a function pointer or an unbacked synthetic
`ProvenancePtr`: a misaligned offset is `.ub`; otherwise unknown base alignment
is fail-closed whenever `elemAlign > 1`. -/
@[reducible]
def unbackedAlignKnown (elemAlign : Nat) (p : ProvenancePtr) : Option Bool :=
  match Nat.beq (Nat.mod p.offsetBytes elemAlign) 0 with
  | false => .some false
  | true =>
    match Nat.ble elemAlign 1 with
    | true => .some true
    | false => .none

/-- Compute the `ZeroPtrView` of one evaluated pointer operand `v`. -/
def zeroPtrView
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat) :
    Value → ZeroPtrView
  | .scalar sc =>
    let ptrBytes := layoutPointerBytes layouts
    match
      Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits (scalarModulus ptrBytes))
    with
    | false => .malformed
    | true => .resolved sc.bits (.some (Nat.beq (Nat.mod sc.bits elemAlign) 0))
  | .ptr p sz =>
    let ptrBytes := layoutPointerBytes layouts
    match Nat.beq sz ptrBytes with
    | false => .malformed
    | true =>
      match lookupBorrow s.memory.borrows p.tag with
      | .some entry =>
        let placeOffOpt : Option Nat :=
          match entry.allocDead with
          | true =>
            match normalizeSubsliceProjections
                (stripTransparentProjections entry.targetProjection) with
            | .nil => .some 0
            | _ :: _ => .none
          | false =>
            borrowPlaceByteOffset? s.frame.locals s.memory.callerLocals localDecls layouts entry
              s.memory.callStack
        match placeOffOpt with
        | .none => .unresolvedAddr
        | .some placeOff =>
          let localPage := Nat.add (stackLocalAddrPageBase ptrBytes) entry.targetLocal
          let addr := Nat.add (Nat.add (Nat.mul localPage 65536) placeOff) p.offsetBytes
          .resolved addr (stackBorrowAlignKnown s localDecls layouts elemAlign p entry placeOff)
      | .none =>
        let addr := Nat.add (Nat.mul p.allocId 65536) p.offsetBytes
        match lookupGlobalAlloc s.memory.globals p.allocId with
        | .some g => .resolved addr (globalAllocAlignKnown g elemAlign p)
        | .none =>
          match lookupFnPtr s.memory.fnPtrs p.allocId with
          | .some _ => .resolved addr (unbackedAlignKnown elemAlign p)
          | .none => .resolved addr (unbackedAlignKnown elemAlign p)
  -- `.unit`, `.aggregate`, and (in `V2026_06_01` only) `.uninit`: a wildcard keeps
  -- the definition portable to `V2026_08_01`, whose `Value` has no `.uninit`.
  | _ => .malformed

/-- Zero-byte check of one pointer operand (the six corner cases). -/
@[reducible]
def checkZeroCountCopyPtr
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (v : Value) :
    ZeroCheck :=
  ZeroPtrView.decide policy (layoutPointerBytes layouts) (zeroPtrView s localDecls layouts elemAlign v)

/-- Zero-byte precheck of both operands in `Intrinsics.copyWith` order: **both**
pointer reads (`toPointer`, i.e. the thin-pointer shape check) precede **any**
alignment check, so a malformed `dst` is `.ub` even when `src`'s alignment is
unknown (A1; B1 returned `.unsupported` there); then `src` before `dst`. -/
@[reducible]
def zeroByteCopyPrecheck
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (srcVal dstVal : Value) :
    ZeroCheck :=
  match
    Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal)
  with
  | false => .ub
  | true =>
    ZeroCheck.andThen
      (checkZeroCountCopyPtr policy s localDecls layouts elemAlign srcVal)
      (checkZeroCountCopyPtr policy s localDecls layouts elemAlign dstVal)

/-! ## 4. Element layout resolution -/

/-- Outcome of classifying a single pointer operand's static type:
* `unknown`: no static type available (e.g. missing `localDecls`);
* `nonPtr`: statically known to be a non-pointer type (e.g. `u32`, `u64`, `bool`);
* `pointee ty authLayoutOpt`: pointer/ref operand with pointee `ty` and optional
  authoritative `TypeLayout` from `ptrLayout.fieldLayouts`. -/
inductive OperandPointeeLookup : Type where
  | unknown
  | nonPtr
  | pointee (ty : Ty) (authLayoutOpt : Option TypeLayout)

/-- Whether a non-pointer (`pointeeTyOf = none`) static operand kind is
**definitely** not a raw pointer: scalars, aggregates, `!`, function items /
pointers, closures. Unnormalized `.alias` / `.param` types, non-`Box` ADTs,
`dyn` and `extern` types are *not* classified (they stay `.unknown`, so a
statically unknown operand never triggers a spurious `.ub`, and a non-zero
count is delegated to the legacy evaluator unchanged). -/
@[reducible]
def copyKindDefinitelyNonPtr : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .never | .str => true
  | .tuple _ | .array _ _ | .slice _ => true
  | .fnDef _ _ | .fnPtr _ _ _ _ | .closure _ _ => true
  | _ => false

/-- Classify a `copy_nonoverlapping` pointer operand, retaining any
authoritative `TypeLayout` recorded in `ptrLayout.fieldLayouts` (even when
`ptLayoutIdx = 0` and no local has the pointee type). -/
@[reducible]
def operandPointeeLookup
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    OperandPointeeLookup :=
  match operandTy localDecls layouts op with
  | .none => .unknown
  | .some ptrTy =>
    match pointeeTyOf ptrTy with
    | .none =>
      match copyKindDefinitelyNonPtr ptrTy.kind with
      | true => .nonPtr
      | false => .unknown
    | .some pt =>
      match LayoutTable.lookup layouts ptrTy.layoutIdx with
      | .some ptrLayout =>
        let isPtrRepr :=
          match ptrLayout.backendRepr with
          | .scalar (.initialized (.pointer _) _) => true
          | .scalar (.union (.pointer _)) => true
          | .scalarPair (.initialized (.pointer _) _) _ => true
          | .scalarPair (.union (.pointer _)) _ => true
          | _ => false
        match isPtrRepr, ptrLayout.fieldLayouts with
        | true, ptLayoutIdx :: .nil =>
          .pointee { kind := pt.kind, layoutIdx := ptLayoutIdx }
            (LayoutTable.lookup layouts ptLayoutIdx)
        | _, _ => .pointee pt .none
      | .none => .pointee pt .none

/-- Outcome of resolving the common pointee `T` of a `copy_nonoverlapping`. -/
inductive CopyElemLayout : Type where
  | ok (elemSize elemAlign : Nat)
  | ub
  | unsupported
  deriving DecidableEq, Repr

/-- Resolve one pointee `(ty, authLayoutOpt)` into `CopyElemLayout`:
unsized pointees are `.ub`, resolved sized pointees with power-of-two alignment
are `.ok elemSize elemAlign`, and everything else fails closed `.unsupported`. -/
@[reducible]
def resolveSinglePointeeLayout
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty)
    (authLayoutOpt : Option TypeLayout) :
    CopyElemLayout :=
  match copyIsUnsizedRigidTy 8 ty.kind with
  | true => .ub
  | false =>
    match copyTySizeAndAlign? localDecls layouts ty authLayoutOpt with
    | .some (elemSize, elemAlign) =>
      match isPowTwoAlign elemAlign with
      | true => .ok elemSize elemAlign
      | false => .unsupported
    | .none => .unsupported

/-- Resolve `(elemSize, elemAlign)` for `copy_nonoverlapping::<T>(src, dst, _)`:
* statically non-pointer `src` or `dst` (`copyKindDefinitelyNonPtr`) → `.ub`
  (catches `bdCopyZeroScalars` and `copy_nonoverlapping(ptr, 8_u64, 0)` even with
  `localDecls = []`); unnormalized `.alias` / `.param` / non-`Box` ADT operand
  types are `.unknown` (A1), never `.ub`;
* both operands have pointees:
  - if `copyPointeeSizesConflict` → `.unsupported`;
  - if both are unsized and `rigidTyEq` → `.ub`;
  - if `rigidTyEq`: resolve both; if one side has an authoritative layout and
    they disagree → `.unsupported`, else return the resolved layout;
  - if not `rigidTyEq`: require both to resolve to `.ok` with equal
    `(elemSize, elemAlign)`, else `.unsupported`;
* one operand known, one `.unknown` (missing decl) → resolve the known one;
* both `.unknown` → `.unsupported`. -/
def resolveCopyElemLayout
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (src dst : Operand) :
    CopyElemLayout :=
  match operandPointeeLookup localDecls layouts src, operandPointeeLookup localDecls layouts dst with
  | .nonPtr, _ => .ub
  | _, .nonPtr => .ub
  | .unknown, .unknown => .unsupported
  | .pointee sp sAuth, .unknown => resolveSinglePointeeLayout localDecls layouts sp sAuth
  | .unknown, .pointee dp dAuth => resolveSinglePointeeLayout localDecls layouts dp dAuth
  | .pointee sp sAuth, .pointee dp dAuth =>
    match copyPointeeSizesConflict localDecls layouts (.some sp) (.some dp) with
    | true => .unsupported
    | false =>
      match rigidTyEq sp.kind dp.kind with
      | true =>
        let rS := resolveSinglePointeeLayout localDecls layouts sp sAuth
        let rD := resolveSinglePointeeLayout localDecls layouts dp dAuth
        match rS, rD with
        | .ok sSz sAl, .ok dSz dAl =>
          match Bool.and (Nat.beq sSz dSz) (Nat.beq sAl dAl) with
          | true => .ok sSz sAl
          | false => .unsupported
        | .ok sSz sAl, .unsupported => .ok sSz sAl
        | .unsupported, .ok dSz dAl => .ok dSz dAl
        | .ub, _ => .ub
        | _, .ub => .ub
        | .unsupported, .unsupported => .unsupported
      | false =>
        match
          resolveSinglePointeeLayout localDecls layouts sp sAuth,
          resolveSinglePointeeLayout localDecls layouts dp dAuth
        with
        | .ok sSz sAl, .ok dSz dAl =>
          match Bool.and (Nat.beq sSz dSz) (Nat.beq sAl dAl) with
          | true => .ok sSz sAl
          | false => .unsupported
        | _, _ => .unsupported

/-! ## 5. Prototype evaluators -/

/-- Zero-byte `copy_nonoverlapping` (after layout resolution and the overflow
check): validate both pointers and, on success, step as a pure no-op. -/
@[reducible]
def evalCopyNonOverlappingZeroCountProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (elemAlign : Nat)
    (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  ZeroCheck.toStep s locals₃
    (zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal)

/-- Legacy non-zero-byte path behind a pointer-**width** gate (A1). The legacy
`evalCopyNonOverlappingWithCount` ignores the `sizeBytes` field of `.ptr p sz`
on `count > 0` (kernel-checked: `.ptr p 1` / `.ptr p 99` on a 64-bit target
still perform the copy, `nonzero_wrong_width_ptr_legacy_copies`), so a
malformed pointer value is rejected `.ub` here before delegation; every
well-formed thin pointer value is delegated unchanged. -/
@[reducible]
def evalCopyNonOverlappingWithCountNonZeroGated
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match
    Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal)
  with
  | false => MirStepNode.fail .ub
  | true =>
    evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits locals₃

/-- Prototype replacement for `evalCopyNonOverlappingWithCount`. -/
def evalCopyNonOverlappingWithCountProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes layouts
  match resolveCopyElemLayout localDecls layouts src dst with
  | .ok elemSize elemAlign =>
    match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) with
    | false => MirStepNode.fail .ub
    | true =>
      match Nat.beq (Nat.mul countBits elemSize) 0 with
      | true =>
        evalCopyNonOverlappingZeroCountProto policy s localDecls layouts elemAlign srcVal dstVal
          locals₃
      | false =>
        evalCopyNonOverlappingWithCountNonZeroGated s src dst localDecls layouts srcVal dstVal
          countBits locals₃
  | .ub => MirStepNode.fail .ub
  | .unsupported =>
    match Nat.beq countBits 0 with
    | true =>
      match Bool.and (isThinPtrValue ptrBytes srcVal) (isThinPtrValue ptrBytes dstVal) with
      | false => MirStepNode.fail .ub
      | true => MirStepNode.unsupported
    | false =>
      evalCopyNonOverlappingWithCountNonZeroGated s src dst localDecls layouts srcVal dstVal
        countBits locals₃

/-- Whether `countSc` is a well-formed `usize` on a `ptrBytes`-byte target. -/
@[reducible]
def countScalarWellFormed (ptrBytes : Nat) (countSc : ScalarInt) : Bool :=
  Bool.and (Nat.beq countSc.sizeBytes ptrBytes) (Nat.blt countSc.bits (scalarModulus ptrBytes))

/-- Prototype replacement for statement-level `evalCopyNonOverlapping`, adding
the missing `countSc.sizeBytes = ptrBytes ∧ countSc.bits < 2^(8·ptrBytes)`
check. -/
def evalCopyNonOverlappingProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls s.memory.callStack
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok srcVal locals₁ =>
    match
      evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals localDecls s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok dstVal locals₂ =>
      match
        evalOperand locals₂ count s.memory.borrows s.memory.globals layouts
          s.memory.callerLocals localDecls s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        match countScalarWellFormed (layoutPointerBytes layouts) countSc with
        | false => MirStepNode.fail .ub
        | true =>
          evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
            countSc.bits locals₃
      | .ok _ _ => MirStepNode.fail .ub

/-- Prototype replacement for `Terminators.evalCopyNonOverlappingCall`: the
only change is calling `evalCopyNonOverlappingWithCountProto` (and checking the
count range); i.e. the terminator path inherits the statement fix
automatically once `evalCopyNonOverlappingWithCount` is patched. -/
def evalCopyNonOverlappingCallProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    MirStepNode :=
  match argOps, argVals with
  | srcOp :: dstOp :: _ :: .nil, srcVal :: dstVal :: .scalar countSc :: .nil =>
    match countScalarWellFormed (layoutPointerBytes bodyLayouts) countSc with
    | false => MirStepNode.fail .ub
    | true =>
      finishMemIntrinsicCall s
        (evalCopyNonOverlappingWithCountProto policy s srcOp dstOp bodyLocalDecls bodyLayouts
          srcVal dstVal countSc.bits locals')
        destination targetBb
  | _, _ => MirStepNode.fail .ub

/-- Prototype `evalStmt`: only `copy_nonoverlapping` is rerouted. -/
def evalStmtProto
    (policy : ZeroCountNullPolicy)
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlappingProto policy s src dst count localDecls layouts
  | _ => evalStmt s stmt localDecls layouts

/-- The `copy_nonoverlapping` statement (operands and active body) that
`stepMirFn body s` would execute next, if any (`none` for a `.other` phase, a
missing block, a terminator position, or any other statement kind). -/
def nextCopyNonOverlapping? (body : CapturedMir) (s : MachineState) :
    Option (Operand × Operand × Operand × CapturedMir) :=
  match (s.memory.activeCallee.getD body).phase with
  | .other _ => none
  | _ =>
    match get? (s.memory.activeCallee.getD body).basicBlocks s.frame.blockIdx with
    | none => none
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | none => none
      | some stmt =>
        match stmt.kind with
        | .intrinsic (.copyNonOverlapping src dst count) =>
          some (src, dst, count, s.memory.activeCallee.getD body)
        | _ => none

/-- Prototype `stepMirFn`: reroutes exactly the next `copy_nonoverlapping`
statement through `evalCopyNonOverlappingProto` and is `Machine.stepMirFn`
otherwise (so it executes every other statement and terminator identically). -/
def stepMirFnProto (policy : ZeroCountNullPolicy) (body : CapturedMir) (s : MachineState) :
    MirStepNode :=
  match nextCopyNonOverlapping? body s with
  | some (src, dst, count, cb) =>
    evalCopyNonOverlappingProto policy s src dst count cb.localDecls cb.layouts
  | none => stepMirFn body s

/-! ## 6. Structural theorems (blast radius, helper invariants, address exactness) -/

theorem ble_true_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  Nat.ble_eq_true_of_le h

theorem ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hh : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hh) (Nat.not_le.mpr h)

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hh : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hh) h

theorem blt_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

theorem fail_ne_step (k : Trusted.Effect.FailureKind) (s : MachineState) :
    MirStepNode.fail k ≠ MirStepNode.step s := by
  intro h
  simp only [MirStepNode.fail, MirStepNode.step] at h
  cases h

theorem unsupported_ne_step (s : MachineState) :
    MirStepNode.unsupported ≠ MirStepNode.step s :=
  fail_ne_step _ s

theorem step_inj {s s' : MachineState} (h : MirStepNode.step s = MirStepNode.step s') :
    s = s' := by
  simp only [MirStepNode.step] at h
  injection h with h1
  injection h1

/-- Our self-contained `copyIsUnsizedRigidTy` agrees everywhere with `Trusted`'s
`isUnsizedRigidTy` (while avoiding any dependency on `V2026_08_01/Terminators.lean`). -/
theorem copyAnyUnsizedRigidTy_eq {p q : RigidTy → Bool} (h : ∀ k, p k = q k) :
    ∀ ks, copyAnyUnsizedRigidTy p ks = anyUnsizedRigidTy q ks
  | .nil => rfl
  | k :: rest => by
    unfold copyAnyUnsizedRigidTy anyUnsizedRigidTy
    rw [h k]
    cases q k with
    | true => rfl
    | false => exact copyAnyUnsizedRigidTy_eq h rest

theorem copyIsUnsizedRigidTy_eq :
    ∀ (fuel : Nat) (ty : RigidTy), copyIsUnsizedRigidTy fuel ty = isUnsizedRigidTy fuel ty
  | .zero, _ => rfl
  | .succ fuel', ty => by
    cases ty with
    | array elem _ => exact copyIsUnsizedRigidTy_eq fuel' elem
    | tuple ks => exact copyAnyUnsizedRigidTy_eq (copyIsUnsizedRigidTy_eq fuel') ks
    | _ => rfl

/-- Any positive power of two satisfies `1 ≤ n`. -/
theorem isPowTwoAlign_pos {n : Nat} (h : isPowTwoAlign n = true) : 1 ≤ n := by
  cases n with
  | zero => cases h
  | succ k => exact Nat.succ_le_succ (Nat.zero_le k)

private theorem resolveSinglePointeeLayout_align_pow2
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ty : Ty)
    (authLayoutOpt : Option TypeLayout) (elemSize elemAlign : Nat)
    (h : resolveSinglePointeeLayout localDecls layouts ty authLayoutOpt =
      .ok elemSize elemAlign) :
    isPowTwoAlign elemAlign = true ∧ 1 ≤ elemAlign := by
  unfold resolveSinglePointeeLayout at h
  cases hu : copyIsUnsizedRigidTy 8 ty.kind <;> rw [hu] at h
  · dsimp only at h
    cases hs : copyTySizeAndAlign? localDecls layouts ty authLayoutOpt with
    | none => rw [hs] at h; cases h
    | some pair =>
      rcases pair with ⟨sz, al⟩
      rw [hs] at h
      dsimp only at h
      cases hp : isPowTwoAlign al <;> rw [hp] at h
      · cases h
      · cases h
        exact ⟨hp, isPowTwoAlign_pos hp⟩
  · cases h

/-- Whenever `resolveCopyElemLayout` succeeds with `.ok elemSize elemAlign`,
`elemAlign` is a valid positive power of two (`1 ≤ elemAlign`, so `Nat.mod _ elemAlign`
is never a degenerate mod-0). -/
theorem resolveCopyElemLayout_align_pow2
    (localDecls : List LocalDecl) (layouts : LayoutTable) (src dst : Operand)
    (elemSize elemAlign : Nat)
    (h : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign) :
    isPowTwoAlign elemAlign = true ∧ 1 ≤ elemAlign := by
  unfold resolveCopyElemLayout at h
  cases hS : operandPointeeLookup localDecls layouts src <;>
    cases hD : operandPointeeLookup localDecls layouts dst <;>
    rw [hS, hD] at h <;> dsimp only at h
  · cases h
  · cases h
  · exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ h
  · cases h
  · cases h
  · cases h
  · exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ h
  · cases h
  · rename_i sp sAuth dp dAuth
    cases hc : copyPointeeSizesConflict localDecls layouts (.some sp) (.some dp) <;>
      rw [hc] at h <;> dsimp only at h
    · cases heq : rigidTyEq sp.kind dp.kind <;> rw [heq] at h <;> dsimp only at h
      · cases hRS : resolveSinglePointeeLayout localDecls layouts sp sAuth with
        | ub => rw [hRS] at h; cases h
        | unsupported => rw [hRS] at h; cases h
        | ok sSz sAl =>
          cases hRD : resolveSinglePointeeLayout localDecls layouts dp dAuth with
          | ub => rw [hRS, hRD] at h; cases h
          | unsupported => rw [hRS, hRD] at h; cases h
          | ok dSz dAl =>
            rw [hRS, hRD] at h; dsimp only at h
            cases hEq : Bool.and (Nat.beq sSz dSz) (Nat.beq sAl dAl) <;> rw [hEq] at h
            · cases h
            · cases h
              exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ hRS
      · cases hRS : resolveSinglePointeeLayout localDecls layouts sp sAuth with
        | ub => rw [hRS] at h; cases h
        | unsupported =>
          cases hRD : resolveSinglePointeeLayout localDecls layouts dp dAuth with
          | ub => rw [hRS, hRD] at h; cases h
          | unsupported => rw [hRS, hRD] at h; cases h
          | ok dSz dAl =>
            rw [hRS, hRD] at h; cases h
            exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ hRD
        | ok sSz sAl =>
          cases hRD : resolveSinglePointeeLayout localDecls layouts dp dAuth with
          | ub => rw [hRS, hRD] at h; cases h
          | unsupported =>
            rw [hRS, hRD] at h; cases h
            exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ hRS
          | ok dSz dAl =>
            rw [hRS, hRD] at h; dsimp only at h
            cases hEq : Bool.and (Nat.beq sSz dSz) (Nat.beq sAl dAl) <;> rw [hEq] at h
            · cases h
            · cases h
              exact resolveSinglePointeeLayout_align_pow2 _ _ _ _ _ _ hRS
    · cases h

/-- For a live stack borrow (`entry.allocDead = false`), the canonical address
recorded in `zeroPtrView` agrees identically with `Trusted`'s `ptrAddress?`. -/
theorem zeroPtrView_stack_live_addr_eq_ptrAddress?
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign : Nat) (p : ProvenancePtr) (entry : BorrowEntry)
    (hlookup : lookupBorrow s.memory.borrows p.tag = .some entry)
    (hlive : entry.allocDead = false) :
    match
      ptrAddress? s.frame.locals s.memory.borrows s.memory.callerLocals localDecls layouts
        (layoutPointerBytes layouts) p s.memory.callStack
    with
    | .none =>
      zeroPtrView s localDecls layouts elemAlign (.ptr p (layoutPointerBytes layouts)) =
        .unresolvedAddr
    | .some addr =>
      ∃ aligned,
        zeroPtrView s localDecls layouts elemAlign (.ptr p (layoutPointerBytes layouts)) =
          .resolved addr aligned := by
  unfold ptrAddress? borrowBaseAddress? zeroPtrView
  dsimp only
  rw [hlookup, Nat.beq_refl]
  dsimp only
  rw [hlive]
  dsimp only
  cases hOff : borrowPlaceByteOffset? s.frame.locals s.memory.callerLocals localDecls layouts entry
      s.memory.callStack with
  | none => rfl
  | some placeOff => exact ⟨_, rfl⟩

/-- `evalStmtProto` coincides with `evalStmt` on every non-`copy_nonoverlapping`
statement. -/
theorem evalStmtProto_eq_of_not_copy
    (policy : ZeroCountNullPolicy) (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : ∀ src dst count, stmt.kind ≠ .intrinsic (.copyNonOverlapping src dst count)) :
    evalStmtProto policy s stmt localDecls layouts = evalStmt s stmt localDecls layouts := by
  unfold evalStmtProto
  split
  · rename_i src dst count hk
    exact absurd hk (h src dst count)
  · rfl

/-- `stepMirFnProto` coincides with `stepMirFn` whenever the next step is not
a `copy_nonoverlapping` statement. -/
theorem stepMirFnProto_eq_of_not_copy
    (policy : ZeroCountNullPolicy) (body : CapturedMir) (s : MachineState)
    (h : nextCopyNonOverlapping? body s = none) :
    stepMirFnProto policy body s = stepMirFn body s := by
  unfold stepMirFnProto
  rw [h]

/-- When the next step is a `copy_nonoverlapping`, the legacy `stepMirFn`
executes exactly the legacy `evalCopyNonOverlapping` on the same operands, and
`stepMirFnProto` its prototype replacement. -/
theorem stepMirFn_eq_of_copy
    (body : CapturedMir) (s : MachineState) (src dst count : Operand) (cb : CapturedMir)
    (h : nextCopyNonOverlapping? body s = some (src, dst, count, cb)) :
    stepMirFn body s = evalCopyNonOverlapping s src dst count cb.localDecls cb.layouts := by
  unfold nextCopyNonOverlapping? at h
  unfold stepMirFn
  dsimp only
  split at h
  · cases h
  · rename_i hph
    split at h
    · cases h
    · rename_i bb hbb
      split at h
      · cases h
      · rename_i stmt hstmt
        split at h
        · rename_i s0 d0 c0 hk
          cases h
          split
          · rename_i nm hnm
            exact absurd hnm (hph nm)
          · rw [hbb]
            dsimp only
            rw [hstmt]
            dsimp only
            unfold evalStmt
            rw [hk]
        · cases h

/-- Non-zero-byte copies with a resolved, non-overflowing layout are delegated
unchanged to the legacy `evalCopyNonOverlappingWithCount`. -/
theorem evalCopyNonOverlappingWithCountProto_nonzero
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hfit : countBits * elemSize ≤ isizeMaxBytes (layoutPointerBytes layouts))
    (hnz : countBits * elemSize ≠ 0)
    (hthin : Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal) = true) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃ := by
  have hfit' : Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes (layoutPointerBytes layouts)) =
      true := ble_true_of_le hfit
  have hnz' : Nat.beq (Nat.mul countBits elemSize) 0 = false := beq_false_of_ne hnz
  unfold evalCopyNonOverlappingWithCountProto
  rw [hl]
  dsimp only
  rw [hfit', hnz']
  unfold evalCopyNonOverlappingWithCountNonZeroGated
  rw [hthin]

/-- Non-zero-count copies whose layout is `.unsupported` are delegated unchanged
to the legacy evaluator (preserving e.g. `L5_ControlAndCalls` sub-case (d) and
`UnsafeObligations.evalCopyNonOverlapping_one_of_obligations`). -/
theorem evalCopyNonOverlappingWithCountProto_unresolved_nonzero_count
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .unsupported)
    (hc : countBits ≠ 0)
    (hthin : Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal) = true) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal countBits
        locals₃ := by
  unfold evalCopyNonOverlappingWithCountProto
  rw [hl]
  dsimp only
  rw [beq_false_of_ne hc]
  unfold evalCopyNonOverlappingWithCountNonZeroGated
  rw [hthin]

/-- **Width gate (A1)**: a malformed (non-thin or wrong-width) pointer value is
`.ub` for every count, never delegated to the width-blind legacy body. -/
theorem evalCopyNonOverlappingWithCountProto_malformed_ub
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (hbad : Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal) = false) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.fail .ub := by
  have hview : ∀ (elemAlign : Nat),
      zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal = .ub := by
    intro elemAlign
    unfold zeroByteCopyPrecheck
    rw [hbad]
  unfold evalCopyNonOverlappingWithCountProto
  cases hl : resolveCopyElemLayout localDecls layouts src dst with
  | ub => rfl
  | unsupported =>
    dsimp only
    cases Nat.beq countBits 0
    · unfold evalCopyNonOverlappingWithCountNonZeroGated; rw [hbad]
    · dsimp only; rw [hbad]
  | ok sz al =>
    dsimp only
    cases Nat.ble (Nat.mul countBits sz) (isizeMaxBytes (layoutPointerBytes layouts))
    · rfl
    · dsimp only
      cases Nat.beq (Nat.mul countBits sz) 0
      · unfold evalCopyNonOverlappingWithCountNonZeroGated; rw [hbad]
      · dsimp only
        unfold evalCopyNonOverlappingZeroCountProto
        rw [hview al]

/-- The zero-byte fragment (`count * elemSize = 0`) is exactly the precheck
followed by a pure no-op step. -/
theorem evalCopyNonOverlappingWithCountProto_zero
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      ZeroCheck.toStep s locals₃
        (zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  unfold evalCopyNonOverlappingWithCountProto
  rw [hl]
  dsimp only
  rw [hz', ble_true_of_le (Nat.zero_le _)]

/-- Unresolved / unsized / non-pointer pointees on a zero-count copy fail closed
(and malformed pointer values still fault `.ub` even when the pointee layout is
`.unsupported`). -/
theorem evalCopyNonOverlappingWithCountProto_zero_count_unresolved
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    (resolveCopyElemLayout localDecls layouts src dst = .unsupported →
      isThinPtrValue (layoutPointerBytes layouts) srcVal = true →
      isThinPtrValue (layoutPointerBytes layouts) dstVal = true →
      evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal 0
        locals₃ = MirStepNode.unsupported) ∧
    (resolveCopyElemLayout localDecls layouts src dst = .unsupported →
      (isThinPtrValue (layoutPointerBytes layouts) srcVal = false ∨
        isThinPtrValue (layoutPointerBytes layouts) dstVal = false) →
      evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal 0
        locals₃ = MirStepNode.fail .ub) ∧
    (resolveCopyElemLayout localDecls layouts src dst = .ub →
      ∀ countBits,
      evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.fail .ub) := by
  refine ⟨fun hl hs hd => ?_, fun hl hbad => ?_, fun hl countBits => ?_⟩
  · unfold evalCopyNonOverlappingWithCountProto
    rw [hl]
    dsimp only
    rw [hs, hd]
    rfl
  · unfold evalCopyNonOverlappingWithCountProto
    rw [hl]
    dsimp only
    rcases hbad with hs | hd
    · rw [hs]; rfl
    · cases isThinPtrValue (layoutPointerBytes layouts) srcVal <;> rw [hd] <;> rfl
  · unfold evalCopyNonOverlappingWithCountProto
    rw [hl]

/-! ## 7. Null-policy refinement (lifted all the way to `stepMirFnProto`) -/

/-- Per-view refinement: `.rejectNull` is never more permissive than
`.allowRawIntrinsicNull`, and they differ only on a null address, where
`.rejectNull` reports `.ub`. -/
theorem ZeroPtrView.decide_refines (ptrBytes : Nat) (v : ZeroPtrView) :
    (ZeroPtrView.decide .rejectNull ptrBytes v = .ok →
      ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes v = .ok) ∧
    (ZeroPtrView.decide .rejectNull ptrBytes v ≠
        ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes v →
      ZeroPtrView.decide .rejectNull ptrBytes v = .ub ∧
        ∃ addr al, v = .resolved addr al ∧ isNullAddr ptrBytes addr = true) := by
  cases v with
  | malformed => exact ⟨id, fun h => absurd rfl h⟩
  | unresolvedAddr => exact ⟨id, fun h => absurd rfl h⟩
  | resolved addr al =>
    cases hn : isNullAddr ptrBytes addr
    · have e : ZeroPtrView.decide .rejectNull ptrBytes (.resolved addr al) =
          ZeroPtrView.decide .allowRawIntrinsicNull ptrBytes (.resolved addr al) := by
        simp only [ZeroPtrView.decide, hn]
      exact ⟨fun h => by rw [← e]; exact h, fun h => absurd e h⟩
    · have e : ZeroPtrView.decide .rejectNull ptrBytes (.resolved addr al) = .ub := by
        simp only [ZeroPtrView.decide, hn]
      exact ⟨fun h => (by rw [e] at h; cases h), fun _ => ⟨e, addr, al, rfl, hn⟩⟩

/-- `.rejectNull` ⊑ `.allowRawIntrinsicNull` on the two-pointer precheck. -/
theorem zeroByteCopyPrecheck_refines
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign : Nat) (srcVal dstVal : Value)
    (h : zeroByteCopyPrecheck .rejectNull s localDecls layouts elemAlign srcVal dstVal = .ok) :
    zeroByteCopyPrecheck .allowRawIntrinsicNull s localDecls layouts elemAlign srcVal dstVal =
      .ok := by
  unfold zeroByteCopyPrecheck checkZeroCountCopyPtr at *
  cases hg : Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal) <;> rw [hg] at h
  · cases h
  dsimp only at h ⊢
  generalize zeroPtrView s localDecls layouts elemAlign srcVal = vs at *
  generalize zeroPtrView s localDecls layouts elemAlign dstVal = vd at *
  generalize layoutPointerBytes layouts = pb at *
  cases hs : ZeroPtrView.decide .rejectNull pb vs <;> rw [hs] at h
  · rw [(ZeroPtrView.decide_refines pb vs).1 hs]
    exact (ZeroPtrView.decide_refines pb vd).1 h
  · cases h
  · cases h

/-- End-to-end policy difference on `zeroByteCopyPrecheck`: the two policies
differ only when `srcVal` or `dstVal` resolves to a null address, in which case
`.rejectNull` returns `.ub`. -/
theorem zeroByteCopyPrecheck_policy_difference
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign : Nat) (srcVal dstVal : Value)
    (hne : zeroByteCopyPrecheck .rejectNull s localDecls layouts elemAlign srcVal dstVal ≠
      zeroByteCopyPrecheck .allowRawIntrinsicNull s localDecls layouts elemAlign srcVal dstVal) :
    zeroByteCopyPrecheck .rejectNull s localDecls layouts elemAlign srcVal dstVal = .ub ∧
      ((∃ addr al, zeroPtrView s localDecls layouts elemAlign srcVal = .resolved addr al ∧
          isNullAddr (layoutPointerBytes layouts) addr = true) ∨
        (∃ addr al, zeroPtrView s localDecls layouts elemAlign dstVal = .resolved addr al ∧
          isNullAddr (layoutPointerBytes layouts) addr = true)) := by
  unfold zeroByteCopyPrecheck checkZeroCountCopyPtr at *
  cases hg : Bool.and (isThinPtrValue (layoutPointerBytes layouts) srcVal)
      (isThinPtrValue (layoutPointerBytes layouts) dstVal) <;> rw [hg] at hne
  · exact absurd rfl hne
  dsimp only at hne ⊢
  generalize zeroPtrView s localDecls layouts elemAlign srcVal = vs at *
  generalize zeroPtrView s localDecls layouts elemAlign dstVal = vd at *
  generalize layoutPointerBytes layouts = pb at *
  by_cases hs : ZeroPtrView.decide .rejectNull pb vs =
      ZeroPtrView.decide .allowRawIntrinsicNull pb vs
  · rw [hs] at hne ⊢
    cases hsr : ZeroPtrView.decide .allowRawIntrinsicNull pb vs with
    | ok =>
      rw [hsr] at hne
      have hd := (ZeroPtrView.decide_refines pb vd).2 hne
      exact ⟨hd.1, Or.inr hd.2⟩
    | ub => rw [hsr] at hne; exact absurd rfl hne
    | unsupported => rw [hsr] at hne; exact absurd rfl hne
  · have hsr := (ZeroPtrView.decide_refines pb vs).2 hs
    rw [hsr.1]
    exact ⟨rfl, Or.inl hsr.2⟩

/-- **Soundness refinement** (`WithCount`): whenever the default `.rejectNull`
prototype steps to `s'`, so does `.allowRawIntrinsicNull`, to the same post-state. -/
theorem evalCopyNonOverlappingWithCountProto_rejectNull_refines
    (s s' : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (h : evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts srcVal
        dstVal countBits locals₃ = MirStepNode.step s') :
    evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst localDecls layouts
        srcVal dstVal countBits locals₃ = MirStepNode.step s' := by
  unfold evalCopyNonOverlappingWithCountProto at *
  cases hl : resolveCopyElemLayout localDecls layouts src dst with
  | ub => rw [hl] at h; exact h
  | unsupported => rw [hl] at h; exact h
  | ok sz al =>
    rw [hl] at h
    dsimp only at h ⊢
    cases hb : Nat.ble (Nat.mul countBits sz) (isizeMaxBytes (layoutPointerBytes layouts)) <;>
      rw [hb] at h
    · exact h
    · cases hz : Nat.beq (Nat.mul countBits sz) 0 <;> rw [hz] at h
      · exact h
      · unfold evalCopyNonOverlappingZeroCountProto at *
        cases hp : zeroByteCopyPrecheck .rejectNull s localDecls layouts al srcVal dstVal <;>
          rw [hp] at h
        · rw [zeroByteCopyPrecheck_refines _ _ _ _ _ _ hp]
          exact h
        · exact absurd h (fail_ne_step _ _)
        · exact absurd h (unsupported_ne_step _)

/-- End-to-end policy difference directly on `evalCopyNonOverlappingWithCountProto`:
whenever `.rejectNull` and `.allowRawIntrinsicNull` disagree, `.rejectNull`
faults with `.ub` and at least one operand resolved to address `≡ 0`. -/
theorem evalCopyNonOverlappingWithCountProto_policy_difference
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits : Nat) (locals₃ : List LocalSlot)
    (hne : evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts srcVal
        dstVal countBits locals₃ ≠
      evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst localDecls layouts
        srcVal dstVal countBits locals₃) :
    evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.fail .ub ∧
      ∃ elemSize elemAlign,
        resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign ∧
        countBits * elemSize = 0 ∧
        ((∃ addr al, zeroPtrView s localDecls layouts elemAlign srcVal = .resolved addr al ∧
            isNullAddr (layoutPointerBytes layouts) addr = true) ∨
          (∃ addr al, zeroPtrView s localDecls layouts elemAlign dstVal = .resolved addr al ∧
            isNullAddr (layoutPointerBytes layouts) addr = true)) := by
  unfold evalCopyNonOverlappingWithCountProto at *
  cases hl : resolveCopyElemLayout localDecls layouts src dst with
  | ub => rw [hl] at hne; exact absurd rfl hne
  | unsupported => rw [hl] at hne; exact absurd rfl hne
  | ok sz al =>
    rw [hl] at hne
    dsimp only at hne ⊢
    cases hb : Nat.ble (Nat.mul countBits sz) (isizeMaxBytes (layoutPointerBytes layouts)) <;>
      rw [hb] at hne
    · exact absurd rfl hne
    · cases hz : Nat.beq (Nat.mul countBits sz) 0 <;> rw [hz] at hne
      · exact absurd rfl hne
      · have hnePre :
            zeroByteCopyPrecheck .rejectNull s localDecls layouts al srcVal dstVal ≠
              zeroByteCopyPrecheck .allowRawIntrinsicNull s localDecls layouts al srcVal dstVal :=
          fun heq => hne (congrArg (ZeroCheck.toStep s locals₃) heq)
        have hdiff := zeroByteCopyPrecheck_policy_difference s localDecls layouts al srcVal dstVal
          hnePre
        refine ⟨?_, sz, al, rfl, Nat.eq_of_beq_eq_true hz, hdiff.2⟩
        unfold evalCopyNonOverlappingZeroCountProto
        rw [hdiff.1]

/-- **Soundness refinement** lifted to statement-level `evalCopyNonOverlappingProto`. -/
theorem evalCopyNonOverlappingProto_rejectNull_refines
    (s s' : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : evalCopyNonOverlappingProto .rejectNull s src dst count localDecls layouts =
        MirStepNode.step s') :
    evalCopyNonOverlappingProto .allowRawIntrinsicNull s src dst count localDecls layouts =
      MirStepNode.step s' := by
  unfold evalCopyNonOverlappingProto at *
  cases h1 : evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals localDecls s.memory.callStack with
  | ub => rw [h1] at h; exact h
  | unsupported => rw [h1] at h; exact h
  | ok srcVal l1 =>
    rw [h1] at h; dsimp only at h ⊢
    cases h2 : evalOperand l1 dst s.memory.borrows s.memory.globals layouts
        s.memory.callerLocals localDecls s.memory.callStack with
    | ub => rw [h2] at h; exact h
    | unsupported => rw [h2] at h; exact h
    | ok dstVal l2 =>
      rw [h2] at h; dsimp only at h ⊢
      cases h3 : evalOperand l2 count s.memory.borrows s.memory.globals layouts
          s.memory.callerLocals localDecls s.memory.callStack with
      | ub => rw [h3] at h; exact h
      | unsupported => rw [h3] at h; exact h
      | ok cntVal l3 =>
        rw [h3] at h
        cases cntVal with
        | scalar countSc =>
          dsimp only at h ⊢
          cases hwf : countScalarWellFormed (layoutPointerBytes layouts) countSc <;>
            rw [hwf] at h <;> dsimp only at h ⊢
          · exact h
          · exact evalCopyNonOverlappingWithCountProto_rejectNull_refines _ _ _ _ _ _ _ _ _ _ h
        | ptr _ _ => exact h
        | unit => exact h
        | aggregate _ _ => exact h
        | uninit => exact h

/-- **Soundness refinement** lifted to `evalStmtProto`. -/
theorem evalStmtProto_rejectNull_refines
    (s s' : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h : evalStmtProto .rejectNull s stmt localDecls layouts = MirStepNode.step s') :
    evalStmtProto .allowRawIntrinsicNull s stmt localDecls layouts = MirStepNode.step s' := by
  unfold evalStmtProto at *
  cases hk : stmt.kind with
  | intrinsic intr =>
    rw [hk] at h
    cases intr with
    | assume _ => exact h
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlappingProto_rejectNull_refines s s' src dst count localDecls layouts h
  | assign _ _ => rw [hk] at h; exact h
  | setDiscriminant _ _ => rw [hk] at h; exact h
  | deinit _ => rw [hk] at h; exact h
  | storageLive _ => rw [hk] at h; exact h
  | storageDead _ => rw [hk] at h; exact h
  | retag _ _ => rw [hk] at h; exact h
  | placeMention _ => rw [hk] at h; exact h
  | nop => rw [hk] at h; exact h
  | coverage => rw [hk] at h; exact h
  | constEvalCounter => rw [hk] at h; exact h
  | backwardIncompatibleDropHint _ => rw [hk] at h; exact h

/-- **Soundness refinement** lifted all the way to `stepMirFnProto`. -/
theorem stepMirFnProto_rejectNull_refines
    (body : CapturedMir) (s s' : MachineState)
    (h : stepMirFnProto .rejectNull body s = MirStepNode.step s') :
    stepMirFnProto .allowRawIntrinsicNull body s = MirStepNode.step s' := by
  unfold stepMirFnProto at *
  cases hn : nextCopyNonOverlapping? body s <;> rw [hn] at h <;> dsimp only at h ⊢
  · exact h
  · rename_i q
    rcases q with ⟨src, dst, count, cb⟩
    exact evalCopyNonOverlappingProto_rejectNull_refines s s' src dst count cb.localDecls cb.layouts
      h

/-- **Soundness refinement** lifted to terminator-level `evalCopyNonOverlappingCallProto`. -/
theorem evalCopyNonOverlappingCallProto_rejectNull_refines
    (s s' : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (h : evalCopyNonOverlappingCallProto .rejectNull s bodyLocalDecls bodyLayouts argOps argVals
        locals' destination targetBb = MirStepNode.step s') :
    evalCopyNonOverlappingCallProto .allowRawIntrinsicNull s bodyLocalDecls bodyLayouts argOps
        argVals locals' destination targetBb = MirStepNode.step s' := by
  unfold evalCopyNonOverlappingCallProto at *
  split at h
  · rename_i srcOp dstOp cntOp srcVal dstVal countSc
    cases hwf : countScalarWellFormed (layoutPointerBytes bodyLayouts) countSc <;>
      rw [hwf] at h <;> dsimp only at h ⊢
    · exact h
    · cases hStep : evalCopyNonOverlappingWithCountProto .rejectNull s srcOp dstOp
          bodyLocalDecls bodyLayouts srcVal dstVal countSc.bits locals' with
      | tau res =>
        cases res with
        | running sMid =>
          have hMid := evalCopyNonOverlappingWithCountProto_rejectNull_refines
            s sMid srcOp dstOp bodyLocalDecls bodyLayouts srcVal dstVal
            countSc.bits locals' hStep
          rw [hStep] at h
          rw [hMid]
          exact h
        | halted _ => rw [hStep] at h; unfold finishMemIntrinsicCall at h; cases h
        | faulted _ => rw [hStep] at h; unfold finishMemIntrinsicCall at h; cases h
      | vis _ _ => rw [hStep] at h; unfold finishMemIntrinsicCall at h; cases h
      | ret _ => rw [hStep] at h; unfold finishMemIntrinsicCall at h; cases h
  · exact absurd h (fail_ne_step _ _)

/-- On the zero-byte fragment, a successful prototype step is the pure no-op
`advanceStmt s locals₃` (memory and locals untouched; no Tree Borrows access). -/
theorem evalCopyNonOverlappingWithCountProto_zero_noop
    (policy : ZeroCountNullPolicy) (s s' : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (h : evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.step s') :
    s' = advanceStmt s locals₃ ∧ s'.memory = s.memory := by
  rw [evalCopyNonOverlappingWithCountProto_zero policy s src dst localDecls layouts srcVal dstVal
    countBits elemSize elemAlign locals₃ hl hz] at h
  cases hp : zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal <;>
    rw [hp] at h
  · have := step_inj h
    subst this
    exact ⟨rfl, rfl⟩
  · exact absurd h (fail_ne_step _ _)
  · exact absurd h (unsupported_ne_step _)

/-! ## 8. Standalone reference models (`lean-miri` and `core::ptr`) and end-to-end bridge

Resolved-integer abstractions of the check order of
`lean-miri/vendor/Miri/Interpreter/Intrinsics.lean:143-158` (`copyWith`) with
`Miri/Memory/Access.lean:134-153` (`checkAndDerefPtr`: size `0` returns
`.ok none` before any provenance resolution, so address `0` is accepted) and
of Rust's `core::ptr::copy_nonoverlapping` (`ub_checks` precondition followed by
the intrinsic), **directly bridged** to `evalCopyNonOverlappingWithCountProto`. -/

/-- Outcome of the reference models. -/
inductive RefCopyOutcome : Type where
  | ub
  | noop
  | access (bytes : Nat)
  deriving DecidableEq, Repr

/-- Map a zero-byte or overflow `Option RefCopyOutcome` to the corresponding
`MirStepNode` (`none` → `.unsupported`, `some .ub` → `.fail .ub`,
`some .noop` → `.step (advanceStmt s locals₃)`). -/
@[reducible]
def refOutcomeToStep (s : MachineState) (locals₃ : List LocalSlot) :
    Option RefCopyOutcome → MirStepNode
  | .some .noop => MirStepNode.step (advanceStmt s locals₃)
  | .some .ub => MirStepNode.fail .ub
  | .some (.access _) => MirStepNode.unsupported
  | .none => MirStepNode.unsupported

/-- `lean-miri` `Intrinsics.copyWith` on resolved addresses: (1) count read,
(2) `computeSizeInBytes` against `isize::MAX`, (3) `checkAlign source`,
(4) `checkAlign dest`, (5) `memCopy` (zero bytes: `checkAndDerefPtr` returns
`none`, no resolution, no null check). -/
@[reducible]
def miriCopyWithRef (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) :
    RefCopyOutcome :=
  match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) with
  | false => .ub
  | true =>
    match Nat.beq (Nat.mod srcAddr elemAlign) 0 with
    | false => .ub
    | true =>
      match Nat.beq (Nat.mod dstAddr elemAlign) 0 with
      | false => .ub
      | true =>
        match Nat.beq (Nat.mul countBits elemSize) 0 with
        | true => .noop
        | false => .access (Nat.mul countBits elemSize)

/-- `core::ptr::ub_checks::maybe_is_aligned_and_not_null(ptr, align, is_zst)`.
`zeroSizeWaivesNull = true` is the Rust 1.98 definition
(`maybe_is_aligned(ptr, align) && (is_zst || !ptr.is_null())`);
`zeroSizeWaivesNull = false` is the strict (pre-relaxation) contract that
`.rejectNull` implements. -/
@[reducible]
def ubChecksAlignedAndNotNull
    (zeroSizeWaivesNull : Bool) (ptrBytes addr align : Nat) (isZst : Bool) : Bool :=
  Bool.and (Nat.beq (Nat.mod addr align) 0)
    (Bool.or (Bool.and isZst zeroSizeWaivesNull) (Bool.not (isNullAddr ptrBytes addr)))

/-- `core::ptr::copy_nonoverlapping` = `ub_checks` precondition (with
`zero_size := count == 0 || size == 0`) followed by the intrinsic
(`miriCopyWithRef`). The overlap precondition is vacuous for zero bytes and is
not modelled. -/
@[reducible]
def corePtrCopyRef
    (zeroSizeWaivesNull : Bool) (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) :
    RefCopyOutcome :=
  match
    Bool.and
      (ubChecksAlignedAndNotNull zeroSizeWaivesNull ptrBytes srcAddr elemAlign
        (Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0)))
      (ubChecksAlignedAndNotNull zeroSizeWaivesNull ptrBytes dstAddr elemAlign
        (Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0)))
  with
  | false => .ub
  | true => miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr

/-- Whether a view is `malformed` (failed thin-pointer shape check). -/
@[reducible]
def ZeroPtrView.isMalformed : ZeroPtrView → Bool
  | .malformed => true
  | _ => false

/-- Two-view zero-byte decision in `Intrinsics.copyWith` order: both pointer
reads (shape) first, then `src` / `dst` null+alignment. -/
@[reducible]
def zeroViewsDecide (policy : ZeroCountNullPolicy) (ptrBytes : Nat) (srcV dstV : ZeroPtrView) :
    ZeroCheck :=
  match Bool.or srcV.isMalformed dstV.isMalformed with
  | true => .ub
  | false =>
    ZeroCheck.andThen (ZeroPtrView.decide policy ptrBytes srcV)
      (ZeroPtrView.decide policy ptrBytes dstV)

/-- `isThinPtrValue` is exactly "the view is not malformed" (for every
`elemAlign`). -/
theorem isThinPtrValue_eq_not_malformed (s : MachineState) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (elemAlign : Nat) (v : Value) :
    isThinPtrValue (layoutPointerBytes layouts) v =
      !(zeroPtrView s localDecls layouts elemAlign v).isMalformed := by
  cases v with
  | scalar sc =>
    unfold isThinPtrValue zeroPtrView
    dsimp only
    cases Bool.and (Nat.beq sc.sizeBytes (layoutPointerBytes layouts))
      (Nat.blt sc.bits (scalarModulus (layoutPointerBytes layouts))) <;> rfl
  | ptr p sz =>
    unfold isThinPtrValue zeroPtrView
    dsimp only
    cases Nat.beq sz (layoutPointerBytes layouts)
    · rfl
    · dsimp only
      split
      · split <;> rfl
      · split <;> (try split) <;> rfl
  | unit => rfl
  | aggregate _ _ => rfl
  | uninit => rfl

/-- `zeroByteCopyPrecheck` factors through the two views. -/
theorem zeroByteCopyPrecheck_eq_views (policy : ZeroCountNullPolicy) (s : MachineState)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (elemAlign : Nat)
    (srcVal dstVal : Value) :
    zeroByteCopyPrecheck policy s localDecls layouts elemAlign srcVal dstVal =
      zeroViewsDecide policy (layoutPointerBytes layouts)
        (zeroPtrView s localDecls layouts elemAlign srcVal)
        (zeroPtrView s localDecls layouts elemAlign dstVal) := by
  unfold zeroByteCopyPrecheck zeroViewsDecide checkZeroCountCopyPtr
  rw [isThinPtrValue_eq_not_malformed s localDecls layouts elemAlign srcVal,
    isThinPtrValue_eq_not_malformed s localDecls layouts elemAlign dstVal]
  cases (zeroPtrView s localDecls layouts elemAlign srcVal).isMalformed <;>
    cases (zeroPtrView s localDecls layouts elemAlign dstVal).isMalformed <;> rfl

/-- The prototype's zero-byte & overflow decision on views, as a reference
outcome (`none` = fail-closed `.unsupported`). Non-zero-byte copies that do not
overflow are outside the fragment (`access`). -/
@[reducible]
def protoFragment (policy : ZeroCountNullPolicy) (ptrBytes countBits elemSize : Nat)
    (srcV dstV : ZeroPtrView) : Option RefCopyOutcome :=
  match Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) with
  | false => .some .ub
  | true =>
    match Nat.beq (Nat.mul countBits elemSize) 0 with
    | false => .some (.access (Nat.mul countBits elemSize))
    | true =>
      match zeroViewsDecide policy ptrBytes srcV dstV with
      | .ok => .some .noop
      | .ub => .some .ub
      | .unsupported => .none

/-- Address-exact view (alignment knowledge = actual address alignment), as
produced for every dangling `.scalar` pointer and as Miri computes it. -/
@[reducible]
def exactView (elemAlign addr : Nat) : ZeroPtrView :=
  .resolved addr (.some (Nat.beq (Nat.mod addr elemAlign) 0))

/-- `.scalar` dangling pointers produce exactly the address-exact view. -/
theorem zeroPtrView_scalar
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign bits : Nat)
    (hlt : bits < scalarModulus (layoutPointerBytes layouts)) :
    zeroPtrView s localDecls layouts elemAlign (.scalar ⟨bits, layoutPointerBytes layouts⟩) =
      exactView elemAlign bits := by
  unfold zeroPtrView
  dsimp only
  rw [Nat.beq_refl, blt_true_of_lt hlt]
  rfl

/-- **Direct bridge from `evalCopyNonOverlappingWithCountProto` to
`protoFragment`** on the entire zero-byte and overflow fragment (connecting the
actual prototype evaluator to the standalone reference theorems below). -/
theorem evalCopyNonOverlappingWithCountProto_eq_protoFragment
    (policy : ZeroCountNullPolicy) (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hfrag : countBits * elemSize = 0 ∨
      isizeMaxBytes (layoutPointerBytes layouts) < countBits * elemSize) :
    evalCopyNonOverlappingWithCountProto policy s src dst localDecls layouts srcVal dstVal
        countBits locals₃ =
      refOutcomeToStep s locals₃
        (protoFragment policy (layoutPointerBytes layouts) countBits elemSize
          (zeroPtrView s localDecls layouts elemAlign srcVal)
          (zeroPtrView s localDecls layouts elemAlign dstVal)) := by
  unfold evalCopyNonOverlappingWithCountProto protoFragment
  rw [hl]
  dsimp only
  rcases hfrag with hz | hov
  · have hz' : Nat.mul countBits elemSize = 0 := hz
    rw [hz', ble_true_of_le (Nat.zero_le _)]
    dsimp only [evalCopyNonOverlappingZeroCountProto]
    rw [zeroByteCopyPrecheck_eq_views]
    cases zeroViewsDecide policy (layoutPointerBytes layouts)
        (zeroPtrView s localDecls layouts elemAlign srcVal)
        (zeroPtrView s localDecls layouts elemAlign dstVal) <;> rfl
  · have hov' : Nat.ble (Nat.mul countBits elemSize)
        (isizeMaxBytes (layoutPointerBytes layouts)) = false := ble_false_of_lt hov
    rw [hov']

/-- The zero-byte fragment (`count * elemSize = 0`) of `protoFragment`. -/
theorem protoFragment_zero (policy : ZeroCountNullPolicy) (ptrBytes countBits elemSize : Nat)
    (srcV dstV : ZeroPtrView) (hz : countBits * elemSize = 0) :
    protoFragment policy ptrBytes countBits elemSize srcV dstV =
      match zeroViewsDecide policy ptrBytes srcV dstV with
      | .ok => .some .noop
      | .ub => .some .ub
      | .unsupported => .none := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  unfold protoFragment
  rw [hz', ble_true_of_le (Nat.zero_le _)]

/-- **Equivalence 1** (`.allowRawIntrinsicNull` ≡ `lean-miri`
`Intrinsics.copyWith`) on the resolved zero-byte fragment. -/
theorem protoFragment_allowRaw_eq_miri
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_zero _ _ _ _ _ _ hz]
  unfold miriCopyWithRef
  rw [hz', ble_true_of_le (Nat.zero_le _)]
  unfold exactView
  cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    rfl

/-- **Equivalence 2** (`.allowRawIntrinsicNull` ≡ Rust 1.98
`core::ptr::copy_nonoverlapping`, i.e. `ub_checks` with the zero-size null
waiver, followed by the intrinsic) on the resolved zero-byte fragment. -/
theorem protoFragment_allowRaw_eq_corePtr
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (corePtrCopyRef true ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hzs : Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0) = true := by
    cases countBits with
    | zero => rfl
    | succ c =>
      cases elemSize with
      | zero => cases Nat.beq (c + 1) 0 <;> rfl
      | succ e => exact absurd hz (Nat.mul_ne_zero (Nat.succ_ne_zero c) (Nat.succ_ne_zero e))
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_allowRaw_eq_miri _ _ _ _ _ _ hz]
  unfold corePtrCopyRef ubChecksAlignedAndNotNull miriCopyWithRef
  rw [hzs, hz', ble_true_of_le (Nat.zero_le _)]
  cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    rfl

/-- **Equivalence 3** (`.rejectNull` ≡ strict `core::ptr::copy_nonoverlapping`
contract, `ub_checks` without the zero-size null waiver, followed by the
intrinsic) on the resolved zero-byte fragment, including null rejection for
`u8` / `()` (`elemAlign = 1`). -/
theorem protoFragment_rejectNull_eq_corePtrStrict
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0) :
    protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) =
      .some (corePtrCopyRef false ptrBytes countBits elemSize elemAlign srcAddr dstAddr) := by
  have hz' : Nat.mul countBits elemSize = 0 := hz
  rw [protoFragment_zero _ _ _ _ _ _ hz]
  unfold corePtrCopyRef ubChecksAlignedAndNotNull miriCopyWithRef exactView zeroViewsDecide
    ZeroPtrView.isMalformed ZeroPtrView.decide
  rw [hz', ble_true_of_le (Nat.zero_le _)]
  dsimp only
  cases isNullAddr ptrBytes srcAddr <;> cases isNullAddr ptrBytes dstAddr <;>
    cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    cases Bool.or (Nat.beq countBits 0) (Nat.beq elemSize 0) <;> rfl

/-- **End-to-end Equivalence 1 on `evalCopyNonOverlappingWithCountProto`**:
for any well-formed `.scalar` pointer pair (`NonNull::dangling()`, null,
misaligned, on either 32-bit or 64-bit targets) with resolved layout and
`countBits * elemSize = 0`, `.allowRawIntrinsicNull` matches `miriCopyWithRef`
identically. -/
theorem evalCopyNonOverlappingWithCountProto_scalar_allowRaw_eq_miri
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcBits dstBits countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (hsLt : srcBits < scalarModulus (layoutPointerBytes layouts))
    (hdLt : dstBits < scalarModulus (layoutPointerBytes layouts)) :
    evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst localDecls layouts
        (.scalar ⟨srcBits, layoutPointerBytes layouts⟩)
        (.scalar ⟨dstBits, layoutPointerBytes layouts⟩) countBits locals₃ =
      refOutcomeToStep s locals₃
        (.some (miriCopyWithRef (layoutPointerBytes layouts) countBits elemSize elemAlign
          srcBits dstBits)) := by
  rw [evalCopyNonOverlappingWithCountProto_eq_protoFragment .allowRawIntrinsicNull s src dst
      localDecls layouts _ _ countBits elemSize elemAlign locals₃ hl (Or.inl hz),
    zeroPtrView_scalar s localDecls layouts elemAlign srcBits hsLt,
    zeroPtrView_scalar s localDecls layouts elemAlign dstBits hdLt,
    protoFragment_allowRaw_eq_miri _ _ _ _ _ _ hz]

/-- **End-to-end Equivalence 2 on `evalCopyNonOverlappingWithCountProto`**:
`.allowRawIntrinsicNull` matches Rust 1.98 `core::ptr::copy_nonoverlapping` on
all well-formed `.scalar` zero-byte inputs. -/
theorem evalCopyNonOverlappingWithCountProto_scalar_allowRaw_eq_corePtr
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcBits dstBits countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (hsLt : srcBits < scalarModulus (layoutPointerBytes layouts))
    (hdLt : dstBits < scalarModulus (layoutPointerBytes layouts)) :
    evalCopyNonOverlappingWithCountProto .allowRawIntrinsicNull s src dst localDecls layouts
        (.scalar ⟨srcBits, layoutPointerBytes layouts⟩)
        (.scalar ⟨dstBits, layoutPointerBytes layouts⟩) countBits locals₃ =
      refOutcomeToStep s locals₃
        (.some (corePtrCopyRef true (layoutPointerBytes layouts) countBits elemSize elemAlign
          srcBits dstBits)) := by
  rw [evalCopyNonOverlappingWithCountProto_eq_protoFragment .allowRawIntrinsicNull s src dst
      localDecls layouts _ _ countBits elemSize elemAlign locals₃ hl (Or.inl hz),
    zeroPtrView_scalar s localDecls layouts elemAlign srcBits hsLt,
    zeroPtrView_scalar s localDecls layouts elemAlign dstBits hdLt,
    protoFragment_allowRaw_eq_corePtr _ _ _ _ _ _ hz]

/-- **End-to-end Equivalence 3 on `evalCopyNonOverlappingWithCountProto`**:
`.rejectNull` matches the strict `core::ptr::copy_nonoverlapping` contract on
all well-formed `.scalar` zero-byte inputs (including null rejection on `u8`/`()`). -/
theorem evalCopyNonOverlappingWithCountProto_scalar_rejectNull_eq_corePtrStrict
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcBits dstBits countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (hsLt : srcBits < scalarModulus (layoutPointerBytes layouts))
    (hdLt : dstBits < scalarModulus (layoutPointerBytes layouts)) :
    evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts
        (.scalar ⟨srcBits, layoutPointerBytes layouts⟩)
        (.scalar ⟨dstBits, layoutPointerBytes layouts⟩) countBits locals₃ =
      refOutcomeToStep s locals₃
        (.some (corePtrCopyRef false (layoutPointerBytes layouts) countBits elemSize elemAlign
          srcBits dstBits)) := by
  rw [evalCopyNonOverlappingWithCountProto_eq_protoFragment .rejectNull s src dst
      localDecls layouts _ _ countBits elemSize elemAlign locals₃ hl (Or.inl hz),
    zeroPtrView_scalar s localDecls layouts elemAlign srcBits hsLt,
    zeroPtrView_scalar s localDecls layouts elemAlign dstBits hdLt,
    protoFragment_rejectNull_eq_corePtrStrict _ _ _ _ _ _ hz]

/-- **End-to-end Soundness Refinement against `lean-miri`**: whenever
`evalCopyNonOverlappingWithCountProto .rejectNull` steps on resolved `.scalar`
zero-byte inputs, `miriCopyWithRef` also steps as `.noop`. -/
theorem evalCopyNonOverlappingWithCountProto_scalar_rejectNull_refines_miri
    (s s' : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcBits dstBits countBits elemSize elemAlign : Nat) (locals₃ : List LocalSlot)
    (hl : resolveCopyElemLayout localDecls layouts src dst = .ok elemSize elemAlign)
    (hz : countBits * elemSize = 0)
    (hsLt : srcBits < scalarModulus (layoutPointerBytes layouts))
    (hdLt : dstBits < scalarModulus (layoutPointerBytes layouts))
    (hstep : evalCopyNonOverlappingWithCountProto .rejectNull s src dst localDecls layouts
        (.scalar ⟨srcBits, layoutPointerBytes layouts⟩)
        (.scalar ⟨dstBits, layoutPointerBytes layouts⟩) countBits locals₃ = MirStepNode.step s') :
    miriCopyWithRef (layoutPointerBytes layouts) countBits elemSize elemAlign srcBits dstBits =
        .noop ∧
      s' = advanceStmt s locals₃ := by
  have hraw := evalCopyNonOverlappingWithCountProto_rejectNull_refines s s' src dst localDecls
    layouts _ _ countBits locals₃ hstep
  rw [evalCopyNonOverlappingWithCountProto_scalar_allowRaw_eq_miri s src dst localDecls layouts
      srcBits dstBits countBits elemSize elemAlign locals₃ hl hz hsLt hdLt] at hraw
  cases hm : miriCopyWithRef (layoutPointerBytes layouts) countBits elemSize elemAlign
      srcBits dstBits with
  | noop =>
    rw [hm] at hraw
    exact ⟨rfl, (step_inj hraw).symm⟩
  | ub =>
    rw [hm] at hraw
    exact absurd hraw (fail_ne_step _ _)
  | access n =>
    rw [hm] at hraw
    exact absurd hraw (unsupported_ne_step _)

/-- **Overflow agreement**: when `count * elemSize > isize::MAX`, the prototype
and `lean-miri` both report `.ub` (for every view / address). -/
theorem protoFragment_overflow_eq_miri
    (policy : ZeroCountNullPolicy)
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat) (srcV dstV : ZeroPtrView)
    (hov : isizeMaxBytes ptrBytes < countBits * elemSize) :
    protoFragment policy ptrBytes countBits elemSize srcV dstV = .some .ub ∧
      miriCopyWithRef ptrBytes countBits elemSize elemAlign srcAddr dstAddr = .ub := by
  have hb : Nat.ble (Nat.mul countBits elemSize) (isizeMaxBytes ptrBytes) = false :=
    ble_false_of_lt hov
  unfold protoFragment miriCopyWithRef
  rw [hb]
  exact ⟨rfl, rfl⟩

/-- **Sole difference** between the two policies on the resolved zero-byte
fragment: an address `≡ 0`, where `.rejectNull` reports `.ub` and
`lean-miri` / Rust 1.98 accept. -/
theorem protoFragment_policy_difference
    (ptrBytes countBits elemSize elemAlign srcAddr dstAddr : Nat)
    (hz : countBits * elemSize = 0)
    (hne : protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) ≠
      protoFragment .allowRawIntrinsicNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr)) :
    protoFragment .rejectNull ptrBytes countBits elemSize
        (exactView elemAlign srcAddr) (exactView elemAlign dstAddr) = .some .ub ∧
      (isNullAddr ptrBytes srcAddr = true ∨ isNullAddr ptrBytes dstAddr = true) := by
  revert hne
  rw [protoFragment_zero _ _ _ _ _ _ hz, protoFragment_zero _ _ _ _ _ _ hz]
  unfold exactView zeroViewsDecide ZeroPtrView.isMalformed
  cases hs : isNullAddr ptrBytes srcAddr <;> cases hd : isNullAddr ptrBytes dstAddr <;>
    cases Nat.beq (Nat.mod srcAddr elemAlign) 0 <;> cases Nat.beq (Nat.mod dstAddr elemAlign) 0 <;>
    simp [ZeroPtrView.decide, hs, hd, ZeroCheck.andThen]

end Anneal.Proto.ZeroCountCopyAlign
