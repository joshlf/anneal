/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted
import Anneal.MirFuelFree
import Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
# Track P Prototype: Multi-Element Subplace `copy_nonoverlapping`, `tailCall` Unwind & Caller-Referent Isolation, and `opaqueCast` Root Dispatch

This prototype module (`ws-proto-tcb-copy-subplace-and-tailcall-opaquecast`)
mechanizes and kernel-certifies off `unstable` all four TCB ground-semantics
repairs slated for paired Track A workstream
`ws-tcb-copy-subplace-and-tailcall-opaquecast-correspondence`:

1. **Bug 1 — Multi-Element Subplace `copy_nonoverlapping` (`RawPtrOffsetMutator:wrong_value:MirDiffTag.normalScalar`)**:
   - Peels trailing `.constantIndex` array-element projections into element
     offsets over the enclosing `.aggregate 0` array container when `n > 1` or
     `ptrElemOffset > 0` (`peelArrayElementProjForMultiCopy`,
     `resolveArraySliceEndpoint?`), converts pointer byte offsets to element
     indices via `resolvePtrElemOffset?`, writes updated array slices back to
     the peeled parent projection `{ local_ := dstEntry.targetLocal, projection := dstParentProj }`,
     scopes Tree Borrows read/write transitions and active-protector conflict
     checks to the accessed `.subslice` window, and closes the `copyViaBytes`
     silent-truncation hole by requiring `length bs == n * elemBytes`.
   - Kernel-certifies (`by rfl`) both Campaign #14
     (`pass_transmute_u32_byte_array_le__b0_c6`: `19 -> 112`) and Campaign #15
     (`pass_enum_discriminant_valid__b2_c9`: `70 -> 4`) against live Miri.

2. **Bug 2 — `DIV-LM-TAILCALL-NOUNWIND-UNWIND` (`Terminators.lean:846`)**:
   - Rewrites the top `SavedCallerFrame.returnUnwind` on `Memory.callStack` to
     `.unreachable` when a `TerminatorKind.tailCall` enters a callee with
     `calleeBody.fnAbi.canUnwind = false` (or a non-unwinding call-site ABI),
     matching Miri's `initStackFrame` (`Call.lean:261-264`) and preserving
     multi-hop unwind narrowing monotonicity across arbitrarily many subsequent
     tail calls.

3. **Bug 3 — `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW` (`State.lean`, `Places.lean`, `Terminators.lean`)**:
   - Distinguishes external caller-owned referents in `Memory.callerLocals` from
     frame-owned locals across root `TerminatorKind.tailCall` transitions so a
     tail callee with more locals than the root caller never shadows
     `callerLocals` on dereference reads, dereference writes, reborrows, local
     writes/deallocations, or multi-hop tail-call teardowns.

4. **Bug 4 — `DIV-TR-OPAQUECAST-ROOT-DISPATCH` (`Places.lean`, `Statements.lean`, `Terminators.lean`)**:
   - Strips leading `ProjectionElem.opaqueCast` projections before root-vs-projected
     (`[]` vs `proj :: rest`) dispatch in `evalOperand (.move)`,
     `writePlaceValue`, `uninitFieldWriteShell?`, `evalStmt (.assign / .deinit / .setDiscriminant)`,
     `writeReturnDestination`, and `TerminatorKind.drop`, while preserving
     fail-closed `.unsupported` on ill-formed `.opaqueCast _ :: .deref :: _`
     paths and preserving type-switched validity checks.
-/

namespace Anneal.TcbCopySubplaceAndTailCallPrototype

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-! ## 1. Bug 4: `ProjectionElem.opaqueCast` Root-vs-Projected Dispatch Normalization -/

/--
Strip leading `ProjectionElem.opaqueCast` elements from a projection path before
root-vs-projected (`[]` vs `proj :: rest`) dispatch.

Note that `.deref` is NOT stripped and a leading `.opaqueCast` before `.deref`
(`.opaqueCast t :: .deref :: rest`) reduces to `.deref :: rest` under
`stripLeadingOpaqueCast`, so callers that dispatch `.deref` on the raw head
`place.projection` keep rejecting ill-formed `.opaqueCast _ :: .deref :: _` with
`.unsupported` while treating a pure `.opaqueCast` chain (`stripLeadingOpaqueCast p = []`)
as a root-local access.
-/
@[reducible]
def stripLeadingOpaqueCast : List ProjectionElem → List ProjectionElem
  | .opaqueCast _ :: rest => stripLeadingOpaqueCast rest
  | projs => projs

/--
Erase all `ProjectionElem.opaqueCast` elements at any depth of a projection path.
-/
@[reducible]
def eraseAllOpaqueCast : List ProjectionElem → List ProjectionElem
  | .nil => .nil
  | .opaqueCast _ :: rest => eraseAllOpaqueCast rest
  | elem :: rest => elem :: eraseAllOpaqueCast rest

@[simp]
theorem stripLeadingOpaqueCast_nil :
    stripLeadingOpaqueCast .nil = .nil := rfl

@[simp]
theorem stripLeadingOpaqueCast_cons_opaqueCast (t : Ty) (rest : List ProjectionElem) :
    stripLeadingOpaqueCast (.opaqueCast t :: rest) = stripLeadingOpaqueCast rest := rfl

@[simp]
theorem eraseAllOpaqueCast_nil :
    eraseAllOpaqueCast .nil = .nil := rfl

@[simp]
theorem eraseAllOpaqueCast_cons_opaqueCast (t : Ty) (rest : List ProjectionElem) :
    eraseAllOpaqueCast (.opaqueCast t :: rest) = eraseAllOpaqueCast rest := rfl

theorem stripTransparentProjections_stripLeadingOpaqueCast :
    ∀ p : List ProjectionElem,
      stripTransparentProjections (stripLeadingOpaqueCast p) =
        stripTransparentProjections p
  | .nil => rfl
  | .opaqueCast _ :: rest =>
    stripTransparentProjections_stripLeadingOpaqueCast rest
  | .deref :: _ => rfl
  | .field _ _ :: _ => rfl
  | .index _ :: _ => rfl
  | .constantIndex _ _ _ :: _ => rfl
  | .subslice _ _ _ :: _ => rfl
  | .downcast _ _ :: _ => rfl
  | .unwrapUnsafeBinder _ :: _ => rfl

theorem stripTransparentProjections_eraseAllOpaqueCast :
    ∀ p : List ProjectionElem,
      stripTransparentProjections (eraseAllOpaqueCast p) =
        stripTransparentProjections p
  | .nil => rfl
  | .opaqueCast _ :: rest =>
    stripTransparentProjections_eraseAllOpaqueCast rest
  | .deref :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .field _ _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .index _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .constantIndex _ _ _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .subslice _ _ _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .downcast _ _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]
  | .unwrapUnsafeBinder _ :: rest => by
    simp only [stripTransparentProjections,
      stripTransparentProjections_eraseAllOpaqueCast rest]

theorem projectionsOverlap_eraseAllOpaqueCast_left
    (p q : List ProjectionElem) :
    projectionsOverlap (eraseAllOpaqueCast p) q = projectionsOverlap p q := by
  unfold projectionsOverlap
  rw [stripTransparentProjections_eraseAllOpaqueCast]

theorem projectionsOverlap_eraseAllOpaqueCast_right
    (p q : List ProjectionElem) :
    projectionsOverlap p (eraseAllOpaqueCast q) = projectionsOverlap p q := by
  unfold projectionsOverlap
  rw [stripTransparentProjections_eraseAllOpaqueCast]

theorem readProjectedValue_stripLeadingOpaqueCast (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v : Value),
      readProjectedValue locals v (stripLeadingOpaqueCast p) =
        readProjectedValue locals v p
  | .nil, _ => rfl
  | .opaqueCast ty :: rest, v => by
    rw [stripLeadingOpaqueCast_cons_opaqueCast]
    have hStep : readProjectedValue locals v (.opaqueCast ty :: rest) =
        readProjectedValue locals v rest := by
      cases v <;> rfl
    rw [hStep]
    exact readProjectedValue_stripLeadingOpaqueCast locals rest v
  | .deref :: _, _ => rfl
  | .field _ _ :: _, _ => rfl
  | .index _ :: _, _ => rfl
  | .constantIndex _ _ _ :: _, _ => rfl
  | .subslice _ _ _ :: _, _ => rfl
  | .downcast _ _ :: _, _ => rfl
  | .unwrapUnsafeBinder _ :: _, _ => rfl

theorem writeProjectedValue_stripLeadingOpaqueCast (locals : List LocalSlot) :
    ∀ (p : List ProjectionElem) (v nv : Value),
      writeProjectedValue locals v (stripLeadingOpaqueCast p) nv =
        writeProjectedValue locals v p nv
  | .nil, _, _ => rfl
  | .opaqueCast ty :: rest, v, nv => by
    rw [stripLeadingOpaqueCast_cons_opaqueCast]
    have hStep : writeProjectedValue locals v (.opaqueCast ty :: rest) nv =
        writeProjectedValue locals v rest nv := by
      cases v <;> rfl
    rw [hStep]
    exact writeProjectedValue_stripLeadingOpaqueCast locals rest v nv
  | .deref :: _, _, _ => rfl
  | .field _ _ :: _, _, _ => rfl
  | .index _ :: _, _, _ => rfl
  | .constantIndex _ _ _ :: _, _, _ => rfl
  | .subslice _ _ _ :: _, _, _ => rfl
  | .downcast _ _ :: _, _, _ => rfl
  | .unwrapUnsafeBinder _ :: _, _, _ => rfl

/--
Repaired `uninitFieldWriteShell?`: strips leading `.opaqueCast` projections
before matching on `.field fieldIdx fieldTy :: rest'`, so `(_l as T).f = rv` on
a live `.uninit` struct, union, or tuple local materializes the exact same
aggregate shell as `_l.f = rv`.
-/
def uninitFieldWriteShellProto?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem := .nil) :
    Option Value :=
  match stripLeadingOpaqueCast (proj :: rest) with
  | .field fieldIdx fieldTy :: rest' =>
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) rest'
  | _ => .none

@[simp]
theorem uninitFieldWriteShellProto?_opaqueCast
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (t : Ty)
    (proj : ProjectionElem)
    (rest : List ProjectionElem) :
    uninitFieldWriteShellProto? localDecls layouts loc (.opaqueCast t) (proj :: rest) =
      uninitFieldWriteShellProto? localDecls layouts loc proj rest := rfl

@[simp]
theorem uninitFieldWriteShellProto?_field
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rest : List ProjectionElem) :
    uninitFieldWriteShellProto? localDecls layouts loc (.field fieldIdx fieldTy) rest =
      uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) rest := rfl

/-! ## 2. Bug 3: Root Caller-Owned Referent Isolation (`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`) -/

/--
Sentinel frame-depth tag (`65535`) used to distinguish external caller-owned
referent borrows backed by `Memory.callerLocals` from stack-frame-owned borrows
at depth `0 .. length callStack` inside `Trusted.BorrowEntry` (without modifying
`trusted/lean/Trusted/.../State.lean` during Track P prototyping).

In paired Track A workstream `ws-tcb-copy-subplace-and-tailcall-opaquecast-correspondence`,
this corresponds 1-to-1 to `BorrowEntry.isCallerReferent : Bool := false` (see
`ProtoBorrowEntry` and `protoBorrowEntry_iso` below).
-/
@[reducible]
def callerReferentFrameDepth : Nat := 255

/--
Explicit TCB target representation of `BorrowEntry` with a dedicated
`isCallerReferent : Bool := false` origin flag.
-/
structure ProtoBorrowEntry : Type where
  tag : Nat
  targetLocal : LocalIdx
  targetProjection : List ProjectionElem
  perm : TreeBorrowPerm
  rangeOffset : Nat := 0
  rangeLen : Nat := 0
  protector : Option Nat := .none
  parentTag : Option Nat := .none
  targetFrameDepth : Nat := 0
  allocDead : Bool := false
  /-- `true` when `targetLocal` indexes `Memory.callerLocals` (external caller
      referent of the modular root) rather than a stack frame's `frame.locals`. -/
  isCallerReferent : Bool := false

/-- Convert a `ProtoBorrowEntry` into a `Trusted.BorrowEntry` using `callerReferentFrameDepth`. -/
@[reducible]
def ProtoBorrowEntry.toBorrowEntry (e : ProtoBorrowEntry) : BorrowEntry :=
  { tag := e.tag
    targetLocal := e.targetLocal
    targetProjection := e.targetProjection
    perm := e.perm
    rangeOffset := e.rangeOffset
    rangeLen := e.rangeLen
    protector := e.protector
    parentTag := e.parentTag
    targetFrameDepth :=
      match e.isCallerReferent with
      | true => callerReferentFrameDepth
      | false => e.targetFrameDepth
    allocDead := e.allocDead }

/-- Recover a `ProtoBorrowEntry` from a `Trusted.BorrowEntry`. -/
@[reducible]
def ProtoBorrowEntry.ofBorrowEntry (e : BorrowEntry) : ProtoBorrowEntry :=
  let isCr := Nat.beq e.targetFrameDepth callerReferentFrameDepth
  { tag := e.tag
    targetLocal := e.targetLocal
    targetProjection := e.targetProjection
    perm := e.perm
    rangeOffset := e.rangeOffset
    rangeLen := e.rangeLen
    protector := e.protector
    parentTag := e.parentTag
    targetFrameDepth :=
      match isCr with
      | true => 0
      | false => e.targetFrameDepth
    allocDead := e.allocDead
    isCallerReferent := isCr }

theorem ProtoBorrowEntry.ofBorrowEntry_toBorrowEntry
    (e : ProtoBorrowEntry)
    (hDepth : e.isCallerReferent = true → e.targetFrameDepth = 0)
    (hNotSentinel : e.isCallerReferent = false →
      Nat.beq e.targetFrameDepth callerReferentFrameDepth = false) :
    ProtoBorrowEntry.ofBorrowEntry e.toBorrowEntry = e := by
  cases e with
  | mk tag targetLocal targetProjection perm rangeOffset rangeLen protector
      parentTag targetFrameDepth allocDead isCallerReferent =>
    cases isCallerReferent with
    | false =>
      have hNS : Nat.beq targetFrameDepth callerReferentFrameDepth = false :=
        hNotSentinel rfl
      simp [ProtoBorrowEntry.ofBorrowEntry, hNS]
    | true =>
      have hD : targetFrameDepth = 0 := hDepth rfl
      subst hD
      rfl

/--
Test whether a `BorrowEntry` targets an external caller-owned referent in
`Memory.callerLocals`.
-/
@[reducible]
def isCallerReferentBorrow (entry : BorrowEntry) : Bool :=
  Nat.beq entry.targetFrameDepth callerReferentFrameDepth

@[simp]
theorem isCallerReferentBorrow_zero
    (tag : Nat) (targetLocal : LocalIdx) (targetProjection : List ProjectionElem)
    (perm : TreeBorrowPerm) (rangeOffset rangeLen : Nat)
    (protector parentTag : Option Nat) (allocDead : Bool) :
    isCallerReferentBorrow
      { tag := tag, targetLocal := targetLocal, targetProjection := targetProjection,
        perm := perm, rangeOffset := rangeOffset, rangeLen := rangeLen,
        protector := protector, parentTag := parentTag,
        targetFrameDepth := 0, allocDead := allocDead } = false := rfl

theorem isCallerReferentBorrow_sentinel
    (tag : Nat) (targetLocal : LocalIdx) (targetProjection : List ProjectionElem)
    (perm : TreeBorrowPerm) (rangeOffset rangeLen : Nat)
    (protector parentTag : Option Nat) (allocDead : Bool) :
    isCallerReferentBorrow
      { tag := tag, targetLocal := targetLocal, targetProjection := targetProjection,
        perm := perm, rangeOffset := rangeOffset, rangeLen := rangeLen,
        protector := protector, parentTag := parentTag,
        targetFrameDepth := callerReferentFrameDepth, allocDead := allocDead } = true := by
  exact Nat.beq_refl callerReferentFrameDepth

/--
Stamp root caller-owned referent borrows (`targetFrameDepth == 0` and
`targetLocal >= rootLocalCount` with `allocDead == false`) with
`callerReferentFrameDepth` so that replacing the root frame on a root
`TerminatorKind.tailCall` by a wider callee never shadows `Memory.callerLocals`.
-/
@[reducible]
def promoteRootCallerReferentBorrows
    (borrows : List BorrowEntry)
    (rootLocalCount : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    let promote :=
      Bool.and
        (Bool.not entry.allocDead)
        (Bool.and
          (Nat.beq entry.targetFrameDepth 0)
          (Nat.ble rootLocalCount entry.targetLocal))
    match promote with
    | true =>
      { entry with targetFrameDepth := callerReferentFrameDepth } ::
        promoteRootCallerReferentBorrows rest rootLocalCount
    | false =>
      entry :: promoteRootCallerReferentBorrows rest rootLocalCount

/--
Repaired `activeFrameSlot?`: checks `Nat.beq d (length callStack)` even when
`callStack = .nil`, so caller-owned referents (`d = callerReferentFrameDepth`)
never resolve to the active frame's `locals` even after a root `tailCall` into a
wider callee.
-/
@[reducible]
def activeFrameSlotProto?
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (d loc : Nat) :
    Option LocalSlot :=
  match Nat.beq d (length callStack) with
  | true => get? locals loc
  | false => .none

/--
Repaired `foreignFrameSlot?`: resolves caller-owned referents
(`d == callerReferentFrameDepth` or root-depth fallback) directly to
`get? callerLocals loc` regardless of how many locals the current root frame or
suspended depth-`0` frame has.
-/
@[reducible]
def foreignFrameSlotProto?
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option LocalSlot :=
  match Nat.beq d callerReferentFrameDepth with
  | true => get? callerLocals loc
  | false =>
    match callStack with
    | .nil => get? callerLocals loc
    | _ :: _ =>
      match savedFrameAtDepth? callStack d with
      | .some sf =>
        match get? sf.frame.locals loc with
        | .some slot => .some slot
        | .none =>
          match d with
          | .zero => get? callerLocals loc
          | .succ _ => .none
      | .none => .none

/--
Repaired `foreignFrameTarget?`: routes `d == callerReferentFrameDepth` directly
to `.some (.callerReferent callerLocals)` even when a suspended frame at depth
`0` has more locals than `loc`.
-/
@[reducible]
def foreignFrameTargetProto?
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option ForeignFrameTarget :=
  match Nat.beq d callerReferentFrameDepth with
  | true => .some (.callerReferent callerLocals)
  | false => foreignFrameTarget? callStack callerLocals d loc

/--
Repaired `readFrameLocalSlot` using `activeFrameSlotProto?` and
`foreignFrameSlotProto?`.
-/
@[reducible]
def readFrameLocalSlotProto
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat) :
    Option LocalSlot :=
  match activeFrameSlotProto? locals callStack d loc with
  | .some slot => .some slot
  | .none => foreignFrameSlotProto? callStack callerLocals d loc

/--
Repaired `writeFrameLocalSlot` using `activeFrameSlotProto?` and
`foreignFrameTargetProto?`.
-/
@[reducible]
def writeFrameLocalSlotProto
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (d loc : Nat)
    (slot : LocalSlot) :
    Option (List LocalSlot × List SavedCallerFrame × List LocalSlot) :=
  match activeFrameSlotProto? locals callStack d loc with
  | .some _ =>
    match set? locals loc slot with
    | .some locals' => .some (locals', callStack, callerLocals)
    | .none => .none
  | .none =>
    match foreignFrameTargetProto? callStack callerLocals d loc with
    | .some (.savedFrame idx frameLocals) =>
      match set? frameLocals loc slot, get? callStack idx with
      | .some frameLocals', .some sf =>
        match set? callStack idx { sf with frame := { sf.frame with locals := frameLocals' } } with
        | .some callStack' => .some (locals, callStack', callerLocals)
        | .none => .none
      | _, _ => .none
    | .some (.callerReferent referents) =>
      match set? referents loc slot with
      | .some referents' => .some (locals, callStack, referents')
      | .none => .none
    | .none => .none

/--
Repaired `disableFrameBorrows`:
- Disables and marks `allocDead := true` every borrow of the torn-down frame's
  own locals (`entry.targetFrameDepth == depth && entry.targetLocal < nLocals`),
- At the root frame (`depth == 0`), stamps surviving external caller-owned
  referent borrows (`entry.targetFrameDepth == 0 && entry.targetLocal >= nLocals && !entry.allocDead`)
  with `targetFrameDepth := callerReferentFrameDepth` so they are never shadowed
  or disabled by any subsequent wider tail-callee frame!
-/
def disableFrameBorrowsProto
    (borrows : List BorrowEntry)
    (depth nLocals : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match
      Bool.and
        (Nat.beq entry.targetFrameDepth depth)
        (Nat.blt entry.targetLocal nLocals)
    with
    | true =>
      { entry with perm := .disabled, allocDead := true } ::
        disableFrameBorrowsProto rest depth nLocals
    | false =>
      let promoteCallerReferent :=
        Bool.and
          (Bool.not entry.allocDead)
          (Bool.and
            (Nat.beq depth 0)
            (Nat.beq entry.targetFrameDepth 0))
      match promoteCallerReferent with
      | true =>
        { entry with targetFrameDepth := callerReferentFrameDepth } ::
          disableFrameBorrowsProto rest depth nLocals
      | false =>
        entry :: disableFrameBorrowsProto rest depth nLocals

/--
Repaired `disableFramesAbove`: when unwinding pops frames above `depth`,
preserves caller-owned referents (`targetFrameDepth == callerReferentFrameDepth`),
which live in the external caller of the modular root (`depth < 0`) rather than
above `depth`.
-/
def disableFramesAboveProto
    (borrows : List BorrowEntry)
    (depth : Nat) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match
      Bool.and
        (Bool.not (Nat.beq entry.targetFrameDepth callerReferentFrameDepth))
        (Nat.blt depth entry.targetFrameDepth)
    with
    | true =>
      { entry with perm := .disabled, allocDead := true } ::
        disableFramesAboveProto rest depth
    | false =>
      entry :: disableFramesAboveProto rest depth

/-! ## 3. Bug 1: Multi-Element Subplace `copy_nonoverlapping` (`peelArrayElementProjForMultiCopy`) -/

/--
If `proj` ends with `.constantIndex offset minLen fromEnd`, split `proj` into
`(initProj, offset, minLen, fromEnd)`; otherwise return `.none`.
-/
@[reducible]
def splitLastConstantIndexWithFromEnd? :
    List ProjectionElem → Option (List ProjectionElem × Nat × Nat × Bool)
  | .nil => .none
  | .constantIndex offset minLen fromEnd :: .nil =>
    .some (.nil, offset, minLen, fromEnd)
  | elem :: rest =>
    match splitLastConstantIndexWithFromEnd? rest with
    | .some (initProj, offset, minLen, fromEnd) =>
      .some (elem :: initProj, offset, minLen, fromEnd)
    | .none => .none

/--
Peel a trailing forward `.constantIndex idx minLen false` projection into
`(parentProj, ptrElemOffset + idx)` when copying multiple elements (`n > 1`) or
starting at a non-zero element offset (`ptrElemOffset > 0`).

When `n <= 1` and `ptrElemOffset == 0`, returns `(proj, 0)` unchanged so single-element
direct copies (`evalCopySingleDirect`) keep their exact subplace projection.
-/
@[reducible]
def peelArrayElementProjForMultiCopy
    (proj : List ProjectionElem)
    (ptrElemOffset : Nat)
    (n : Nat) :
    List ProjectionElem × Nat :=
  match Bool.or (Nat.blt 1 n) (Nat.blt 0 ptrElemOffset) with
  | false => (proj, ptrElemOffset)
  | true =>
    let normProj := normalizeSubsliceProjections (stripTransparentProjections proj)
    match splitLastConstantIndex? normProj with
    | .some (parentProj, idx, _) => (parentProj, Nat.add ptrElemOffset idx)
    | .none => (proj, ptrElemOffset)

@[simp]
theorem peelArrayElementProjForMultiCopy_single_zero (proj : List ProjectionElem) :
    peelArrayElementProjForMultiCopy proj 0 1 = (proj, 0) := rfl

@[simp]
theorem peelArrayElementProjForMultiCopy_zero_count_zero_off (proj : List ProjectionElem) :
    peelArrayElementProjForMultiCopy proj 0 0 = (proj, 0) := rfl

theorem peelArrayElementProjForMultiCopy_topLevel_constantIndex
    (idx minLen ptrElemOffset k : Nat) :
    peelArrayElementProjForMultiCopy [.constantIndex idx minLen false] ptrElemOffset (k + 2) =
      ([], Nat.add ptrElemOffset idx) := by
  have hlt : Nat.blt 1 (k + 2) = true := by
    change Nat.ble 2 (k + 2) = true
    exact Nat.ble_eq.mpr (Nat.le_add_left 2 k)
  simp [peelArrayElementProjForMultiCopy, hlt, stripTransparentProjections,
    normalizeSubsliceProjections, normalizeSubsliceProjectionsAux, splitLastConstantIndex?]

theorem peelArrayElementProjForMultiCopy_field_constantIndex
    (fIdx : FieldIdx) (fTy : Ty) (idx minLen ptrElemOffset k : Nat) :
    peelArrayElementProjForMultiCopy
        [.field fIdx fTy, .constantIndex idx minLen false] ptrElemOffset (k + 2) =
      ([.field fIdx fTy], Nat.add ptrElemOffset idx) := by
  have hlt : Nat.blt 1 (k + 2) = true := by
    change Nat.ble 2 (k + 2) = true
    exact Nat.ble_eq.mpr (Nat.le_add_left 2 k)
  simp [peelArrayElementProjForMultiCopy, hlt, stripTransparentProjections,
    normalizeSubsliceProjections, normalizeSubsliceProjectionsAux, splitLastConstantIndex?]

/--
Convert a raw pointer byte offset `offsetBytes` (`ProvenancePtr.offsetBytes`)
into an element index for `copy_nonoverlapping`:
- `0` always maps to `.some 0`.
- When `pointeeTyOpt` has a resolved positive byte size `elemSz`
  (`rigidTyByteSize layouts pt = .some elemSz`), divides `offsetBytes` evenly by
  `elemSz` via `byteOffsetToElemIdx?` (returning `.none` on misaligned byte
  offsets or non-zero offsets on zero-sized pointee types).
- When `pointeeTyOpt` is `.none` (untyped unit tests with `localDecls = []`),
  interprets `offsetBytes` directly as the element offset.
-/
@[reducible]
def resolvePtrElemOffset?
    (offsetBytes : Nat)
    (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) :
    Option Nat :=
  match Nat.beq offsetBytes 0 with
  | true => .some 0
  | false =>
    match pointeeTyOpt with
    | .some pt =>
      match rigidTyByteSize layouts pt with
      | .some elemSz => byteOffsetToElemIdx? offsetBytes elemSz
      | .none => .some offsetBytes
    | .none => .some offsetBytes

/--
Resolve a `copy_nonoverlapping` source or destination borrow endpoint into an
enclosing array slice `(containerProj, elemStartIdx, elems)`:
1. Resolves dynamic `.index` projections in `entry.targetProjection` against
   `locals₃`, strips transparent projections, and normalizes `.subslice` chains.
2. Converts `ptr.offsetBytes` into `ptrElemOffset` via `resolvePtrElemOffset?`.
3. When the normalized projection ends in `.constantIndex offset minLen fromEnd`
   and the parent projection `parentProj` evaluates to `.ok (.aggregate 0 outerElems)`:
   - Checks whether the unpeeled projection itself is an inner array matching
     `pointeeTyOpt` (`preferInner`, e.g. a 2D array row cast to an element
     pointer without `.subslice`),
   - Otherwise validates `minLen <= length outerElems` and `fromEnd` bounds
     (`offset <= length outerElems` when `fromEnd = false`;
      `1 <= offset <= length outerElems` when `fromEnd = true`), computes
     `baseIdx := if fromEnd then length outerElems - offset else offset`, and
     returns `.some (parentProj, ptrElemOffset + baseIdx, outerElems)`.
4. When the normalized projection does not end in `.constantIndex`, checks if
   `readProjectedValue locals₃ rootVal normProj` yields `.ok (.aggregate 0 elems)`
   and returns `.some (normProj, ptrElemOffset, elems)`.
-/
@[reducible]
def resolveArraySliceEndpoint?
    (locals₃ : List LocalSlot)
    (rootVal : Value)
    (targetProjection : List ProjectionElem)
    (offsetBytes : Nat)
    (n : Nat)
    (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) :
    Option (List ProjectionElem × Nat × List Value) :=
  match resolvePtrElemOffset? offsetBytes pointeeTyOpt layouts with
  | .none => .none
  | .some ptrElemOffset =>
    let resolvedProj :=
      match resolveBorrowProjectionElems locals₃ targetProjection with
      | .some rp => rp
      | .none => targetProjection
    let normProj :=
      normalizeSubsliceProjections (stripTransparentProjections resolvedProj)
    match splitLastConstantIndexWithFromEnd? normProj with
    | .some (parentProj, offset, minLen, fromEnd) =>
      match readProjectedValue locals₃ rootVal parentProj with
      | .ok (.aggregate 0 outerElems) =>
        let len := length outerElems
        let baseIdxOpt : Option Nat :=
          match fromEnd with
          | false =>
            match Bool.and (Nat.ble minLen len) (Nat.ble offset len) with
            | true => .some offset
            | false => .none
          | true =>
            match
              Bool.and
                (Nat.ble minLen len)
                (Bool.and (Nat.ble 1 offset) (Nat.ble offset len))
            with
            | true => .some (Nat.sub len offset)
            | false => .none
        let expSzOpt : Option Nat :=
          match pointeeTyOpt with
          | .some pt => rigidTyByteSize layouts pt
          | .none => .none
        let preferInner : Bool :=
          match readProjectedValue locals₃ rootVal normProj with
          | .ok (.aggregate 0 innerElems) =>
            match expSzOpt with
            | .some expSz =>
              let outerStride := inferElemListByteStride outerElems
              let innerStride := inferElemListByteStride innerElems
              Bool.and
                (Bool.not (Nat.beq outerStride expSz))
                (Bool.and
                  (Nat.beq innerStride expSz)
                  (Nat.ble (Nat.add ptrElemOffset n) (length innerElems)))
            | .none => false
          | _ => false
        match preferInner with
        | true =>
          match readProjectedValue locals₃ rootVal normProj with
          | .ok (.aggregate 0 innerElems) =>
            .some (normProj, ptrElemOffset, innerElems)
          | _ => .none
        | false =>
          match baseIdxOpt with
          | .some baseIdx =>
            .some (parentProj, Nat.add ptrElemOffset baseIdx, outerElems)
          | .none => .none
      | _ => .none
    | .none =>
      match readProjectedValue locals₃ rootVal normProj with
      | .ok (.aggregate 0 elems) => .some (normProj, ptrElemOffset, elems)
      | _ => .none

/--
Tree Borrows read-then-write check and permission transition for a `copy_nonoverlapping`
operating at effective source projection `srcEffProj` and effective destination
projection `dstEffProj` (e.g. `parentProj ++ [.subslice start (start + n) false]`
for a multi-element array slice copy).
-/
def borrowsAfterCopyAtProj
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (srcEffProj dstEffProj : List ProjectionElem) :
    Option (List BorrowEntry) :=
  let readUB : Bool :=
    match borrows with
    | b₁ :: b₂ :: restBorrows =>
      let allBorrows := b₁ :: b₂ :: restBorrows
      hasTreeReadUB
        allBorrows
        allBorrows
        activeProtectors
        srcEntry.targetLocal
        (.some srcPtr.tag)
        srcEffProj
        srcEntry.rangeOffset
        srcEntry.rangeLen
        srcEntry.targetFrameDepth
    | _ => false
  match readUB with
  | true => .none
  | false =>
    let borrowsAfterRead : List BorrowEntry :=
      match borrows with
      | .nil => .nil
      | single :: .nil =>
        updateBorrowPermOnReadAtProj
          (single :: .nil)
          single
          srcEntry.targetLocal
          (.some srcPtr.tag)
          srcEffProj
          srcEntry.rangeOffset
          srcEntry.rangeLen
          activeProtectors
          srcEntry.targetFrameDepth :: .nil
      | b₁ :: b₂ :: restBorrows =>
        let allBorrows := b₁ :: b₂ :: restBorrows
        freezeTreeBorrowsOnReadAtProj
          allBorrows
          allBorrows
          srcEntry.targetLocal
          (.some srcPtr.tag)
          srcEffProj
          srcEntry.rangeOffset
          srcEntry.rangeLen
          activeProtectors
          srcEntry.targetFrameDepth
    let dstWriteTreeUB : Bool :=
      match borrowsAfterRead with
      | .nil => false
      | single :: .nil =>
        match lookupBorrow (single :: .nil) dstPtr.tag with
        | .some dEntryAfter =>
          match dEntryAfter.perm with
          | .frozen | .disabled => true
          | _ => false
        | .none => true
      | b₁ :: b₂ :: restBorrows =>
        let allBorrows := b₁ :: b₂ :: restBorrows
        match lookupBorrow allBorrows dstPtr.tag with
        | .some dEntryAfter =>
          match dEntryAfter.perm with
          | .frozen | .disabled => true
          | _ => treeBorrowAncestorsChildAccessUB .write allBorrows dEntryAfter.parentTag
        | .none => true
    match dstWriteTreeUB with
    | true => .none
    | false =>
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          match borrowsAfterRead with
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            hasProtectedTreeWriteConflict
              allBorrows
              allBorrows
              activeProtectors
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEffProj
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
          | _ =>
            hasProtectedWriteConflict
              borrowsAfterRead
              activeProtectors
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEffProj
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
      match protConflict with
      | true => .none
      | false =>
        let borrows' : List BorrowEntry :=
          match borrowsAfterRead with
          | .nil => .nil
          | single :: .nil =>
            let b := single :: .nil
            match dstEffProj with
            | .nil =>
              match Nat.beq dstEntry.rangeLen 0 with
              | true =>
                invalidateConflictingBorrows
                  b
                  dstEntry.targetLocal
                  (.some dstPtr.tag)
                  dstEntry.targetFrameDepth
              | false =>
                invalidateConflictingBorrowsAtProj
                  b
                  dstEntry.targetLocal
                  (.some dstPtr.tag)
                  .nil
                  dstEntry.rangeOffset
                  dstEntry.rangeLen
                  dstEntry.targetFrameDepth
            | pHead :: pTail =>
              invalidateConflictingBorrowsAtProj
                b
                dstEntry.targetLocal
                (.some dstPtr.tag)
                (pHead :: pTail)
                dstEntry.rangeOffset
                dstEntry.rangeLen
                dstEntry.targetFrameDepth
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            invalidateTreeBorrowsAtProj
              allBorrows
              allBorrows
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEffProj
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
        .some borrows'

/--
Write `newVal` to `dstPlace` (the peeled parent array place or subplace) in the
owning frame (`locals₃`, `s.memory.callStack`, or `s.memory.callerLocals`) and
invalidate conflicting Tree Borrows tags at `dstInvalProj` (checking active
protectors when `s.memory.activeProtectors` is non-empty).
-/
def commitCopyDstPlaceWriteProto
    (s : MachineState)
    (dstPlace : Place)
    (dstEntry : BorrowEntry)
    (dstTag : Nat)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (dstInvalProjOpt : Option (List ProjectionElem) := .none) :
    MirStepNode :=
  let effProj :=
    match dstInvalProjOpt with
    | .some p => p
    | .none => dstPlace.projection
  let protConflict : Bool :=
    match s.memory.activeProtectors with
    | .nil => false
    | _ :: _ =>
      hasProtectedWriteConflict
        s.memory.borrows
        s.memory.activeProtectors
        dstEntry.targetLocal
        (.some dstTag)
        effProj
        dstEntry.rangeOffset
        dstEntry.rangeLen
        dstEntry.targetFrameDepth
  match protConflict with
  | true => MirStepNode.fail .ub
  | false =>
    let computeBorrows (depth : Nat) : List BorrowEntry :=
      match effProj with
      | .nil =>
        invalidateConflictingBorrows
          s.memory.borrows
          dstEntry.targetLocal
          (.some dstTag)
          depth
      | pHead :: pTail =>
        invalidateConflictingBorrowsAtProj
          s.memory.borrows
          dstEntry.targetLocal
          (.some dstTag)
          (pHead :: pTail)
          dstEntry.rangeOffset
          dstEntry.rangeLen
          depth
    match isCallerReferentBorrow dstEntry with
    | false =>
      match
        writePlaceValue
          locals₃
          s.memory.borrows
          dstPlace
          newVal
          localDecls
          layouts
          s.memory.callStack
      with
      | .ok locals₄ =>
        let borrows' := computeBorrows (length s.memory.callStack)
        MirStepNode.step
          (advanceStmt s locals₄ { s.memory with borrows := borrows' })
      | .unsupported => MirStepNode.unsupported
      | .ub =>
        match get? locals₃ dstPlace.local_ with
        | .some _ => MirStepNode.fail .ub
        | .none =>
          let callerIdx :=
            match get? s.memory.callerLocals dstPlace.local_ with
            | .some _ => dstPlace.local_
            | .none => Nat.sub dstPlace.local_ (length locals₃)
          let callerWriteRes : PlaceWriteResult :=
            match dstPlace.projection with
            | .nil =>
              match get? s.memory.callerLocals callerIdx with
              | .some .dead => .ub
              | .some _ =>
                match set? s.memory.callerLocals callerIdx (.init newVal) with
                | .some callerLocals' => .ok callerLocals'
                | .none => .ub
              | .none => .ub
            | .deref :: _ => .ub
            | proj :: rest =>
              match get? s.memory.callerLocals callerIdx with
              | .some (.init rootVal) =>
                match writeProjectedValue locals₃ rootVal (proj :: rest) newVal with
                | .ok rootVal' =>
                  match set? s.memory.callerLocals callerIdx (.init rootVal') with
                  | .some callerLocals' => .ok callerLocals'
                  | .none => .ub
                | .ub => .ub
                | .unsupported => .unsupported
              | _ => .ub
          match callerWriteRes with
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
          | .ok callerLocals' =>
            let borrows' := computeBorrows 0
            MirStepNode.step
              (advanceStmt s locals₃
                { s.memory with borrows := borrows', callerLocals := callerLocals' })
    | true =>
      let callerIdx := dstPlace.local_
      let callerWriteRes : PlaceWriteResult :=
        match dstPlace.projection with
        | .nil =>
          match get? s.memory.callerLocals callerIdx with
          | .some .dead => .ub
          | .some _ =>
            match set? s.memory.callerLocals callerIdx (.init newVal) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | .deref :: _ => .ub
        | proj :: rest =>
          match get? s.memory.callerLocals callerIdx with
          | .some (.init rootVal) =>
            match writeProjectedValue locals₃ rootVal (proj :: rest) newVal with
            | .ok rootVal' =>
              match set? s.memory.callerLocals callerIdx (.init rootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
      match callerWriteRes with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callerLocals' =>
        let borrows' := computeBorrows callerReferentFrameDepth
        MirStepNode.step
          (advanceStmt s locals₃
            { s.memory with borrows := borrows', callerLocals := callerLocals' })

/--
Resolve the root slot of `entry` across `locals₃` and `s.memory.callerLocals`,
respecting `isCallerReferentBorrow entry`.
-/
@[reducible]
def resolveCopyEndpointRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (entry : BorrowEntry) :
    Option LocalSlot :=
  match isCallerReferentBorrow entry with
  | true => get? s.memory.callerLocals entry.targetLocal
  | false =>
    match get? locals₃ entry.targetLocal with
    | .some slot => .some slot
    | .none =>
      match get? s.memory.callerLocals entry.targetLocal with
      | .some slot => .some slot
      | .none =>
        get? s.memory.callerLocals (Nat.sub entry.targetLocal (length locals₃))

/--
Repaired `evalCopySingleDirect` that respects `isCallerReferentBorrow` on both
`srcEntry` and `dstEntry` while remaining definitionally identical to
`Trusted.evalCopySingleDirect` when neither entry is marked with
`callerReferentFrameDepth`.
-/
def evalCopySingleDirectProto
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match
    Bool.or
      (isCallerReferentBorrow srcEntry)
      (isCallerReferentBorrow dstEntry)
  with
  | false =>
    evalCopySingleDirect
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃
  | true =>
    let overlaps :=
      match Nat.beq srcPtr.tag dstPtr.tag with
      | true => true
      | false =>
        match
          Bool.and
            (Nat.beq srcEntry.targetFrameDepth dstEntry.targetFrameDepth)
            (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
        with
        | false => false
        | true =>
          projectionsOverlap
            srcEntry.targetProjection
            dstEntry.targetProjection
    match overlaps with
    | true => MirStepNode.fail .ub
    | false =>
      match resolveCopyEndpointRootSlot s locals₃ srcEntry with
      | .some (.init srcRootVal) =>
        match readProjectedValue locals₃ srcRootVal srcEntry.targetProjection with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok copiedVal =>
          let dstPlace : Place := {
            local_ := dstEntry.targetLocal
            projection := dstEntry.targetProjection
          }
          let convertedOpt : Option Value :=
            match
              operandPointeeTy localDecls layouts src,
              operandPointeeTy localDecls layouts dst
            with
            | .some srcPt, .some dstPt =>
              match sameRigidTyShape srcPt.kind dstPt.kind with
              | true => .some copiedVal
              | false =>
                match rigidTyByteSize layouts srcPt, rigidTyByteSize layouts dstPt with
                | .some sSz, .some dSz =>
                  match Nat.beq sSz dSz with
                  | false => .none
                  | true =>
                    match encodeValueToBytes defaultCodecFuel layouts srcPt copiedVal with
                    | .some bs => decodeValueFromBytes defaultCodecFuel layouts dstPt bs
                    | .none => .none
                | _, _ => .some copiedVal
            | _, _ => .some copiedVal
          match convertedOpt with
          | .none => MirStepNode.fail .ub
          | .some finalVal =>
            commitCopyDstPlaceWriteProto
              s dstPlace dstEntry dstPtr.tag locals₃ finalVal localDecls layouts
      | _ => MirStepNode.fail .ub

/--
Determine the required total byte length `n * elemBytes` for a `copyViaBytes`
fallback when `n > 1`:
- Uses `operandPointeeTy localDecls layouts src` (or `dst`) when available.
- When `localDecls` is empty and `srcSubVal` is a non-aggregate scalar or
  pointer (`Value.scalar sc` or `Value.ptr _ sz`), each element has size
  `sc.sizeBytes` / `sz`, so `n` elements require `n * elemBytes` bytes (preventing
  a single scalar from ever satisfying `n > 1`!).
-/
@[reducible]
def expectedMultiCopyBytes?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (src dst : Operand)
    (srcSubVal : Value)
    (n : Nat) :
    Option Nat :=
  let staticElemBytesOpt : Option Nat :=
    match operandPointeeTy localDecls layouts src with
    | .some pt => rigidTyByteSize layouts pt
    | .none =>
      match operandPointeeTy localDecls layouts dst with
      | .some pt => rigidTyByteSize layouts pt
      | .none => .none
  match staticElemBytesOpt with
  | .some elemSz => .some (Nat.mul n elemSz)
  | .none =>
    match srcSubVal with
    | .scalar sc => .some (Nat.mul n sc.sizeBytes)
    | .ptr _ sz => .some (Nat.mul n sz)
    | .unit => .some 0
    | .aggregate 0 (elem :: _) =>
      match inferValueByteSizeAux 8 elem with
      | .some elemSz => .some (Nat.mul n elemSz)
      | .none => .none
    | _ => .none

/--
Repaired `evalCopyNonOverlappingPermOk`:
1. Delegates single-element zero-offset copies (`n == 1 && srcStart == 0 && dstStart == 0`)
   to `evalCopySingleDirectProto`.
2. Peels trailing `.constantIndex` projections on `srcEntry.targetProjection`
   and `dstEntry.targetProjection` via `resolveArraySliceEndpoint?` so
   multi-element copies (`copy_nonoverlapping(&raw const arr[i], &raw mut dst[j], n)`)
   read and write `n` elements of the enclosing `.aggregate 0` array container
   and write back to `{ local_ := dstEntry.targetLocal, projection := dstParentProj }`.
3. Checks bounds (`srcStart + n <= length srcElems` and `dstStart + n <= length dstElems`)
   and non-overlap (`sameContainer -> srcStart + n <= dstStart || dstStart + n <= srcStart`),
   allowing disjoint slices of the same array while faulting with `.ub` on
   overlapping slices or out-of-bounds element counts.
4. Enforces `length bs == expectedCopyBytes` in `copyViaBytes` so `n > 1` on a
   scalar subplace always faults with `MirStepNode.fail .ub` instead of silently
   copying 1 element.
-/
def evalCopyNonOverlappingPermOkProto
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let n := countBits
  match Nat.beq n 0 with
  | true => MirStepNode.step (advanceStmt s locals₃)
  | false =>
    let srcStartRaw := srcPtr.offsetBytes
    let dstStartRaw := dstPtr.offsetBytes
    let srcUnionOpt :=
      resolveUnionEndpoint? localDecls layouts locals₃ srcEntry
    let dstUnionOpt :=
      resolveUnionEndpoint? localDecls layouts locals₃ dstEntry
    let hasUnionEndpoint :=
      match srcUnionOpt, dstUnionOpt with
      | .none, .none => false
      | _, _ => true
    match hasUnionEndpoint with
    | true =>
      evalCopyUnionBytes
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃
    | false =>
      let isSingleDirect :=
        Bool.and
          (Nat.beq n 1)
          (Bool.and (Nat.beq srcStartRaw 0) (Nat.beq dstStartRaw 0))
      match isSingleDirect with
      | true =>
        evalCopySingleDirectProto
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃
      | false =>
        let srcRootSlot := resolveCopyEndpointRootSlot s locals₃ srcEntry
        let dstRootSlot := resolveCopyEndpointRootSlot s locals₃ dstEntry
        match srcRootSlot, dstRootSlot with
        | .some (.init srcRootVal), .some (.init dstRootVal) =>
          let srcPtOpt := operandPointeeTy localDecls layouts src
          let dstPtOpt := operandPointeeTy localDecls layouts dst
          let effSrcPtOpt :=
            match srcPtOpt with
            | .some pt => .some pt
            | .none => dstPtOpt
          let effDstPtOpt :=
            match dstPtOpt with
            | .some pt => .some pt
            | .none => srcPtOpt
          let srcSliceEndOpt :=
            resolveArraySliceEndpoint?
              locals₃ srcRootVal srcEntry.targetProjection srcStartRaw n effSrcPtOpt layouts
          let dstSliceEndOpt :=
            resolveArraySliceEndpoint?
              locals₃ dstRootVal dstEntry.targetProjection dstStartRaw n effDstPtOpt layouts
          let dstRawPlace : Place := {
            local_ := dstEntry.targetLocal
            projection := dstEntry.targetProjection
          }
          let dstLocalPlaceTy : Option Ty :=
            match isCallerReferentBorrow dstEntry, get? locals₃ dstRawPlace.local_ with
            | false, .some _ => placeTy localDecls layouts dstRawPlace
            | _, _ => .none
          let dstIsAdt : Bool :=
            match dstLocalPlaceTy with
            | .some { kind := .adt _ _, .. } => true
            | _ => false
          let copyViaBytes
              (srcSubVal dstSubVal : Value)
              (effSrcStart effDstStart : Nat)
              (effDstPlace : Place)
              (effDstLocalPlaceTy : Option Ty)
              (effDstIsAdt : Bool) :
              MirStepNode :=
            let overlaps :=
              match Nat.beq srcPtr.tag dstPtr.tag with
              | true => true
              | false =>
                match
                  Bool.and
                    (Nat.beq srcEntry.targetFrameDepth dstEntry.targetFrameDepth)
                    (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                with
                | false => false
                | true =>
                  projectionsOverlap
                    srcEntry.targetProjection
                    effDstPlace.projection
            match overlaps with
            | true => MirStepNode.fail .ub
            | false =>
              let srcSliceVal : Option Value :=
                match srcSubVal with
                | .aggregate 0 srcElems =>
                  match Nat.ble (Nat.add effSrcStart n) (length srcElems) with
                  | true =>
                    .some (.aggregate 0 (takeValues n (dropValues effSrcStart srcElems)))
                  | false =>
                    match Bool.and (Nat.beq effSrcStart 0) (Nat.beq n 1) with
                    | true => .some srcSubVal
                    | false => .none
                | _ =>
                  match Nat.beq effSrcStart 0 with
                  | true => .some srcSubVal
                  | false => .none
              let dstTargetTyOpt : Option Ty :=
                match effDstLocalPlaceTy with
                | .some t => .some t
                | .none => effDstPtOpt
              match srcSliceVal with
              | .none => MirStepNode.fail .ub
              | .some sVal =>
                match encodeUntypedValueToBytes defaultCodecFuel sVal with
                | .none => MirStepNode.unsupported
                | .some bs =>
                  let byteCountMatches : Bool :=
                    match expectedMultiCopyBytes? localDecls layouts src dst srcSubVal n with
                    | .some expBytes => Nat.beq (length bs) expBytes
                    | .none => true
                  match byteCountMatches with
                  | false => MirStepNode.fail .ub
                  | true =>
                    let writeDstVal (newVal : Value) : MirStepNode :=
                      commitCopyDstPlaceWriteProto
                        s effDstPlace dstEntry dstPtr.tag locals₃ newVal localDecls layouts
                    let spliceBytesToDstArray : Option Value :=
                      match Bool.not effDstIsAdt, dstSubVal with
                      | true, .aggregate 0 dstElems =>
                        match Nat.ble (Nat.add effDstStart (length bs)) (length dstElems) with
                        | false => .none
                        | true =>
                          match
                            decodeArrayChunksWith
                              (fun chunk =>
                                decodeValueFromBytes
                                  defaultCodecFuel
                                  layouts
                                  { kind := .uint .u8, layoutIdx := 0 }
                                  chunk)
                              1
                              (length bs)
                              bs
                          with
                          | .some copiedBytes =>
                            .some (.aggregate 0 (spliceValues copiedBytes effDstStart dstElems))
                          | .none => .none
                      | _, _ => .none
                    let preferSplicedArray : Bool :=
                      match effDstLocalPlaceTy, dstSubVal with
                      | .none, .aggregate 0 _ => true
                      | _, _ => false
                    match preferSplicedArray, spliceBytesToDstArray with
                    | true, .some splicedVal => writeDstVal splicedVal
                    | _, _ =>
                      match dstTargetTyOpt with
                      | .some dstPt =>
                        match rigidTyByteSize layouts dstPt with
                        | .some dstBytes =>
                          match Nat.beq (length bs) dstBytes with
                          | true =>
                            match decodeValueFromBytes defaultCodecFuel layouts dstPt bs with
                            | .some decodedVal => writeDstVal decodedVal
                            | .none =>
                              match spliceBytesToDstArray with
                              | .some splicedVal => writeDstVal splicedVal
                              | .none => MirStepNode.fail .ub
                          | false =>
                            match spliceBytesToDstArray with
                            | .some splicedVal => writeDstVal splicedVal
                            | .none => MirStepNode.fail .ub
                        | .none =>
                          match spliceBytesToDstArray with
                          | .some splicedVal => writeDstVal splicedVal
                          | .none => MirStepNode.unsupported
                      | .none =>
                        match spliceBytesToDstArray with
                        | .some splicedVal => writeDstVal splicedVal
                        | .none => MirStepNode.fail .ub
          match srcSliceEndOpt, dstSliceEndOpt with
          | .some (srcParentProj, srcStart, srcElems),
            .some (dstParentProj, dstStart, dstElems) =>
            let dstParentPlace : Place := {
              local_ := dstEntry.targetLocal
              projection := dstParentProj
            }
            let dstParentTy : Option Ty :=
              match isCallerReferentBorrow dstEntry, get? locals₃ dstParentPlace.local_ with
              | false, .some _ => placeTy localDecls layouts dstParentPlace
              | _, _ => .none
            let dstParentIsAdt : Bool :=
              match dstParentTy with
              | .some { kind := .adt _ _, .. } => true
              | _ => false
            let inBounds :=
              Bool.and
                (Bool.not dstParentIsAdt)
                (Bool.and
                  (Nat.ble (Nat.add srcStart n) (length srcElems))
                  (Nat.ble (Nat.add dstStart n) (length dstElems)))
            match inBounds with
            | false =>
              match
                Bool.and
                  (Nat.beq dstStart 0)
                  (Nat.ble (Nat.add srcStart n) (length srcElems))
              with
              | true =>
                copyViaBytes
                  (.aggregate 0 srcElems)
                  (.aggregate 0 dstElems)
                  srcStart
                  dstStart
                  dstParentPlace
                  dstParentTy
                  dstParentIsAdt
              | false => MirStepNode.fail .ub
            | true =>
              let sameContainer :=
                Bool.and
                  (Nat.beq srcEntry.targetFrameDepth dstEntry.targetFrameDepth)
                  (Bool.and
                    (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                    (projectionsOverlap srcParentProj dstParentProj))
              let disjoint :=
                match sameContainer with
                | false => Bool.not (Nat.beq srcPtr.tag dstPtr.tag)
                | true =>
                  Bool.or
                    (Nat.ble (Nat.add srcStart n) dstStart)
                    (Nat.ble (Nat.add dstStart n) srcStart)
              match disjoint with
              | false => MirStepNode.fail .ub
              | true =>
                let copiedSlice := takeValues n (dropValues srcStart srcElems)
                let dstElems' := spliceValues copiedSlice dstStart dstElems
                let dstSliceInvalProj :=
                  match dstParentProj, Nat.beq dstStart 0 && Nat.beq n (length dstElems) with
                  | .nil, true => .nil
                  | _, _ =>
                    normalizeSubsliceProjections
                      (appendProjections
                        dstParentProj
                        (.subslice dstStart (Nat.add dstStart n) false :: .nil))
                commitCopyDstPlaceWriteProto
                  s
                  dstParentPlace
                  dstEntry
                  dstPtr.tag
                  locals₃
                  (.aggregate 0 dstElems')
                  localDecls
                  layouts
                  (.some dstSliceInvalProj)
          | .some (_, srcStart, srcElems), .none =>
            match readProjectedValue locals₃ dstRootVal dstEntry.targetProjection with
            | .ok dstSubVal =>
              copyViaBytes
                (.aggregate 0 srcElems)
                dstSubVal
                srcStart
                dstStartRaw
                dstRawPlace
                dstLocalPlaceTy
                dstIsAdt
            | .ub =>
              match Nat.beq dstStartRaw 0 with
              | true =>
                copyViaBytes
                  (.aggregate 0 srcElems)
                  .unit
                  srcStart
                  0
                  dstRawPlace
                  dstLocalPlaceTy
                  dstIsAdt
              | false => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
          | .none, .some (dstParentProj, dstStart, dstElems) =>
            let dstParentPlace : Place := {
              local_ := dstEntry.targetLocal
              projection := dstParentProj
            }
            let dstParentTy : Option Ty :=
              match isCallerReferentBorrow dstEntry, get? locals₃ dstParentPlace.local_ with
              | false, .some _ => placeTy localDecls layouts dstParentPlace
              | _, _ => .none
            let dstParentIsAdt : Bool :=
              match dstParentTy with
              | .some { kind := .adt _ _, .. } => true
              | _ => false
            match readProjectedValue locals₃ srcRootVal srcEntry.targetProjection with
            | .ok srcSubVal =>
              copyViaBytes
                srcSubVal
                (.aggregate 0 dstElems)
                srcStartRaw
                dstStart
                dstParentPlace
                dstParentTy
                dstParentIsAdt
            | _ => MirStepNode.fail .ub
          | .none, .none =>
            match
              readProjectedValue locals₃ srcRootVal srcEntry.targetProjection,
              readProjectedValue locals₃ dstRootVal dstEntry.targetProjection
            with
            | .ok srcSubVal, .ok dstSubVal =>
              copyViaBytes
                srcSubVal
                dstSubVal
                srcStartRaw
                dstStartRaw
                dstRawPlace
                dstLocalPlaceTy
                dstIsAdt
            | .ok srcSubVal, .ub =>
              match Nat.beq dstStartRaw 0 with
              | true =>
                copyViaBytes
                  srcSubVal
                  .unit
                  srcStartRaw
                  0
                  dstRawPlace
                  dstLocalPlaceTy
                  dstIsAdt
              | false => MirStepNode.fail .ub
            | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub

/--
Check whether `srcEntry` and `dstEntry` both target the active frame (or root
`callerLocals` when `callStack` is empty).
-/
def copyEntriesTargetActiveFrameProto
    (callStack : List SavedCallerFrame)
    (srcEntry dstEntry : BorrowEntry) :
    Bool :=
  match callStack with
  | .nil => true
  | _ :: _ =>
    Bool.and
      (Nat.beq srcEntry.targetFrameDepth (length callStack))
      (Nat.beq dstEntry.targetFrameDepth (length callStack))

/--
Repaired `evalCopyNonOverlappingWithCount` delegating to
`evalCopyNonOverlappingPermOkProto`.
-/
def evalCopyNonOverlappingWithCountProto
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match Nat.beq countBits 0 with
  | true => MirStepNode.step (advanceStmt s locals₃)
  | false =>
    match srcVal, dstVal with
    | .ptr srcPtr _, .ptr dstPtr _ =>
      match
        lookupBorrow s.memory.borrows srcPtr.tag,
        lookupBorrow s.memory.borrows dstPtr.tag
      with
      | .some srcEntry, .some dstEntry =>
        match srcEntry.perm, dstEntry.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ =>
          match copyEntriesTargetActiveFrameProto s.memory.callStack srcEntry dstEntry with
          | false =>
            evalForeignFrameCopySingleDirect
              s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
          | true =>
            evalCopyNonOverlappingPermOkProto
              s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
      | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub

/--
Repaired `evalCopyNonOverlapping` delegating to
`evalCopyNonOverlappingWithCountProto`.
-/
def evalCopyNonOverlappingProto
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperand
      s.frame.locals
      src
      s.memory.borrows
      s.memory.globals
      layouts
      s.memory.callerLocals
      localDecls
      s.memory.callStack
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok srcVal locals₁ =>
    match
      evalOperand
        locals₁
        dst
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
        localDecls
        s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok dstVal locals₂ =>
      match
        evalOperand
          locals₂
          count
          s.memory.borrows
          s.memory.globals
          layouts
          s.memory.callerLocals
          localDecls
          s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        evalCopyNonOverlappingWithCountProto
          s
          src
          dst
          localDecls
          layouts
          srcVal
          dstVal
          countSc.bits
          locals₃
      | .ok _ _ => MirStepNode.fail .ub

/-! ## 4. Repaired Place Read, Operand, Rvalue, Place Write, and Statement Evaluation -/

/--
Dereference read helper for a pointer whose `BorrowEntry` has
`isCallerReferentBorrow entry = true` (targeting `callerLocals[entry.targetLocal]`
even when `entry.targetLocal < length locals`).
-/
def evalCallerReferentDerefRead
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (_pointeeTyOpt : Option Ty := .none)
    (accessedTyOpt : Option Ty := .none) :
    PlaceReadResult :=
  match entry.perm with
  | .disabled => .ub
  | _ =>
    match get? callerLocals entry.targetLocal with
    | .some (.init targetRootVal) =>
      match
        needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes
      with
      | false =>
        let fullProj :=
          match entry.targetProjection with
          | .nil => restProj
          | ph :: pt => ph :: appendProjections pt restProj
        match readProjectedValue locals targetRootVal fullProj with
        | .ok fieldVal =>
          match localDecls with
          | .nil => .ok fieldVal locals
          | _ :: _ =>
            match validateValueForTy? layouts accessedTyOpt fieldVal with
            | true => .ok fieldVal locals
            | false => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | true =>
        match
          resolveStackThinPtrTargetProj?
            locals
            targetRootVal
            entry
            ptrVal
            restProj
        with
        | .none => .ub
        | .some fullProj =>
          match readProjectedValue locals targetRootVal fullProj with
          | .ok fieldVal =>
            match localDecls with
            | .nil => .ok fieldVal locals
            | _ :: _ =>
              match validateValueForTy? layouts accessedTyOpt fieldVal with
              | true => .ok fieldVal locals
              | false => .ub
          | .ub => .ub
          | .unsupported => .unsupported
    | _ => .ub

/--
Check whether `p` is a dereferencing place `⟨ptrLoc, .deref :: restProj⟩` whose
pointer in `locals` resolves to a caller-owned referent borrow
(`isCallerReferentBorrow entry = true`).
-/
@[reducible]
def derefLookupCallerReferent?
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (p : Place) :
    Option (ProvenancePtr × BorrowEntry × List ProjectionElem) :=
  match p.projection with
  | .deref :: restProj =>
    match get? locals p.local_ with
    | .some (.init (.ptr ptrVal _)) =>
      match lookupBorrow borrows ptrVal.tag with
      | .some entry =>
        match isCallerReferentBorrow entry with
        | true => .some (ptrVal, entry, restProj)
        | false => .none
      | .none => .none
    | _ => .none
  | _ => .none

/--
Repaired `evalPlaceRead`:
- Routes dereferences of caller-owned referents (`isCallerReferentBorrow entry = true`)
  directly to `callerLocals[entry.targetLocal]` instead of `locals[entry.targetLocal]`.
- Strips leading `.opaqueCast` projections before root-vs-projected (`[]` vs `proj :: rest`)
  dispatch while keeping `placeTy` / `placeTyResolved` on the original `Place` `p`.
-/
def evalPlaceReadProto
    (locals : List LocalSlot)
    (p : Place)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) :
    PlaceReadResult :=
  match derefLookupCallerReferent? locals borrows p with
  | .some (ptrVal, entry, restProj) =>
    let accessedTyOpt := placeTyResolved localDecls layouts p
    let pointeeTyOpt :=
      placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
    evalCallerReferentDerefRead
      locals callerLocals entry ptrVal restProj localDecls layouts pointeeTyOpt accessedTyOpt
  | .none =>
    match p.projection with
    | .deref :: _ =>
      evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack
    | _ =>
      match stripLeadingOpaqueCast p.projection with
      | .nil =>
        match get? locals p.local_ with
        | .some (.init rootVal) =>
          match validateValueForTy? layouts (placeTy localDecls layouts p) rootVal with
          | true => .ok rootVal locals
          | false => .ub
        | .some .uninit => .ub
        | .some .dead => .ub
        | .none => .ub
      | _ :: _ =>
        evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack

/--
Repaired `evalOperand`:
- Strips leading `.opaqueCast` projections on `Operand.move p` before
  root-vs-projected dispatch so `move (_l as T)` de-initializes `_l` to `.uninit`
  just like `move _l`.
- Routes dereferences of caller-owned referents (`isCallerReferentBorrow entry = true`)
  directly to `callerLocals[entry.targetLocal]`.
-/
def evalOperandProto
    (locals : List LocalSlot)
    (op : Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) :
    PlaceReadResult :=
  match op with
  | .constant _ =>
    evalOperand locals op borrows globals layouts callerLocals localDecls callStack
  | .copy p =>
    match derefLookupCallerReferent? locals borrows p with
    | .some (ptrVal, entry, restProj) =>
      let accessedTyOpt := placeTyResolved localDecls layouts p
      let pointeeTyOpt :=
        placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
      evalCallerReferentDerefRead
        locals callerLocals entry ptrVal restProj localDecls layouts pointeeTyOpt accessedTyOpt
    | .none =>
      evalOperand locals (.copy p) borrows globals layouts callerLocals localDecls callStack
  | .move p =>
    match derefLookupCallerReferent? locals borrows p with
    | .some (ptrVal, entry, restProj) =>
      let accessedTyOpt := placeTyResolved localDecls layouts p
      let pointeeTyOpt :=
        placeTyResolved localDecls layouts { local_ := p.local_, projection := .deref :: .nil }
      evalCallerReferentDerefRead
        locals callerLocals entry ptrVal restProj localDecls layouts pointeeTyOpt accessedTyOpt
    | .none =>
      match p.projection with
      | .deref :: _ =>
        evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack
      | _ =>
        match stripLeadingOpaqueCast p.projection with
        | .nil =>
          let tyValid :=
            match localDecls with
            | .nil => true
            | _ :: _ =>
              match get? locals p.local_ with
              | .some (.init v) =>
                validateValueForTy? layouts (placeTy localDecls layouts p) v
              | _ => true
          match tyValid with
          | false => .ub
          | true =>
            match get? locals p.local_ with
            | .some (.init v) =>
              match set? locals p.local_ .uninit with
              | .some locals' => .ok v locals'
              | .none => .ub
            | .some .uninit => .ub
            | .some .dead => .ub
            | .none => .ub
        | _ :: _ =>
          evalOperand locals (.move p) borrows globals layouts callerLocals localDecls callStack

/--
Evaluate a list of `Operand`s left-to-right using `evalOperandProto`.
-/
def evalOperandsProto
    (locals : List LocalSlot)
    (ops : List Operand)
    (borrows : List BorrowEntry := .nil)
    (globals : List CapturedAllocation := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callerLocals : List LocalSlot := .nil)
    (localDecls : List LocalDecl := .nil)
    (callStack : List SavedCallerFrame := .nil) :
    OperandsEvalResult :=
  match ops with
  | .nil => .ok .nil locals
  | op :: rest =>
    match evalOperandProto locals op borrows globals layouts callerLocals localDecls callStack with
    | .ok val locals' =>
      match evalOperandsProto locals' rest borrows globals layouts callerLocals localDecls callStack with
      | .ok vals locals'' => .ok (val :: vals) locals''
      | .ub => .ub
      | .unsupported => .unsupported
    | .ub => .ub
    | .unsupported => .unsupported

/--
Repaired `writePlaceValue`:
- Strips leading `.opaqueCast` projections before root-vs-projected (`[]` vs `proj :: rest`)
  dispatch so `writePlaceValue` on `⟨l, [.opaqueCast t]⟩` initializes an `.uninit`
  local `l` just like `⟨l, []⟩` (while still validating `val` against
  `placeTy localDecls layouts dst` when `localDecls` is non-empty, and still
  returning `.unsupported` on `.opaqueCast _ :: .deref :: _`).
- Returns `.ub` when dereferencing a caller-owned referent (`isCallerReferentBorrow entry = true`)
  so caller-local dereference writes fall through cleanly to `foreignFrameDerefWriteProto`
  instead of overwriting `locals[entry.targetLocal]`.
-/
def writePlaceValueProto
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callStack : List SavedCallerFrame := .nil) :
    PlaceWriteResult :=
  match derefLookupCallerReferent? locals borrows dst with
  | .some _ => .ub
  | .none =>
    match dst.projection with
    | .deref :: _ =>
      writePlaceValue locals borrows dst val localDecls layouts callStack
    | _ =>
      match stripLeadingOpaqueCast dst.projection with
      | .nil =>
        let tyValid :=
          match localDecls with
          | .nil => true
          | _ :: _ => validateValueForTy? layouts (placeTy localDecls layouts dst) val
        match tyValid with
        | false => .ub
        | true =>
          match get? locals dst.local_ with
          | .some .dead => .ub
          | .some _ =>
            match set? locals dst.local_ (.init val) with
            | .some locals' => .ok locals'
            | .none => .ub
          | .none => .ub
      | _ :: _ =>
        writePlaceValue locals borrows dst val localDecls layouts callStack

/--
Repaired `evalPlaceWrite` using `writePlaceValueProto`.
-/
def evalPlaceWriteProto
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (val : Value)
    (activeProtectors : List Nat := .nil)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (callStack : List SavedCallerFrame := .nil) :
    PlaceWriteResult :=
  match derefLookupCallerReferent? locals borrows dst with
  | .some _ => .ub
  | .none =>
    match activeProtectors with
    | .nil => writePlaceValueProto locals borrows dst val localDecls layouts callStack
    | protHead :: protTail =>
      let prots := protHead :: protTail
      match dst.projection with
      | .deref :: _ =>
        evalPlaceWrite locals borrows dst val prots localDecls layouts callStack
      | _ =>
        match stripLeadingOpaqueCast dst.projection with
        | .nil =>
          match
            hasProtectedWriteConflict
              borrows prots dst.local_ .none .nil 0 0 (length callStack)
          with
          | true => .ub
          | false => writePlaceValueProto locals borrows dst val localDecls layouts callStack
        | proj :: rest =>
          let resolvedProj :=
            match resolveBorrowProjectionElems locals (proj :: rest) with
            | .some rp => rp
            | .none => proj :: rest
          match
            hasProtectedWriteConflict
              borrows prots dst.local_ .none resolvedProj 0 0 (length callStack)
          with
          | true => .ub
          | false => writePlaceValueProto locals borrows dst val localDecls layouts callStack

/--
Dereference write helper for a pointer whose `BorrowEntry` has
`isCallerReferentBorrow entry = true` (targeting `callerLocals[entry.targetLocal]`
even when `entry.targetLocal < length frameLocals` and `callStack = .nil`).
-/
def evalCallerReferentDerefWrite
    (frameLocals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (borrows : List BorrowEntry)
    (entry : BorrowEntry)
    (ptrVal : ProvenancePtr)
    (restProj : List ProjectionElem)
    (val : Value)
    (activeProtectors : List Nat := .nil) :
    PlaceWriteResult :=
  match entry.perm with
  | .frozen | .disabled => .ub
  | _ =>
    let fullProjOpt : Option (List ProjectionElem) :=
      match needsThinPtrElemResolution entry.targetProjection ptrVal.offsetBytes with
      | false =>
        .some
          (match entry.targetProjection with
           | .nil => restProj
           | ph :: pt => ph :: appendProjections pt restProj)
      | true =>
        match get? callerLocals entry.targetLocal with
        | .some (.init targetRootVal) =>
          resolveStackThinPtrTargetProj? frameLocals targetRootVal entry ptrVal restProj
        | _ => .none
    match fullProjOpt with
    | .none => .ub
    | .some fullProj =>
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          hasProtectedWriteConflict
            borrows
            activeProtectors
            entry.targetLocal
            (.some ptrVal.tag)
            fullProj
            entry.rangeOffset
            entry.rangeLen
            entry.targetFrameDepth
      match protConflict with
      | true => .ub
      | false =>
        match fullProj with
        | .nil =>
          match get? callerLocals entry.targetLocal with
          | .some .dead => .ub
          | .some _ =>
            match set? callerLocals entry.targetLocal (.init val) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | pHead :: pTail =>
          match get? callerLocals entry.targetLocal with
          | .some (.init targetRootVal) =>
            match writeProjectedValue frameLocals targetRootVal (pHead :: pTail) val with
            | .ok targetRootVal' =>
              match set? callerLocals entry.targetLocal (.init targetRootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub

/--
Repaired `foreignFrameDerefWrite` that routes caller-owned referents
(`isCallerReferentBorrow entry = true`) to `mem₁.callerLocals` even when
`mem₁.callStack` is empty and `entry.targetLocal < length locals₁`.
-/
def foreignFrameDerefWriteProto
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (dst : Place)
    (restProj : List ProjectionElem)
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    FrameWriteResult :=
  match get? locals₁ dst.local_ with
  | .some (.init ptrOrFatVal) =>
    match extractDerefPtrVal? ptrOrFatVal with
    | .some ptrVal =>
      match lookupBorrow mem₁.borrows ptrVal.tag with
      | .some entry =>
        match activeFrameSlotProto? locals₁ mem₁.callStack entry.targetFrameDepth entry.targetLocal with
        | .some _ => .ub
        | .none =>
          match
            foreignFrameTargetProto?
              mem₁.callStack
              mem₁.callerLocals
              entry.targetFrameDepth
              entry.targetLocal
          with
          | .none => .ub
          | .some target =>
            let writeRes : PlaceWriteResult :=
              match isCallerReferentBorrow entry with
              | true =>
                evalCallerReferentDerefWrite
                  locals₁
                  target.locals
                  mem₁.borrows
                  entry
                  ptrVal
                  restProj
                  val
                  mem₁.activeProtectors
              | false =>
                let (writeDecls, writeLayouts) :=
                  match target with
                  | .savedFrame _ _ => (localDecls, layouts)
                  | .callerReferent _ => (.nil, emptyLayoutTable)
                evalCallerPlaceWrite
                  locals₁
                  target.locals
                  mem₁.borrows
                  dst
                  val
                  mem₁.activeProtectors
                  writeDecls
                  writeLayouts
                  mem₁.callStack
            match writeRes with
            | .ok targetLocals' =>
              let (targetDecls, targetLayouts) :=
                match isCallerReferentBorrow entry with
                | true => (.nil, layouts)
                | false =>
                  foreignFrameDeclsAndLayouts
                    mem₁.callStack
                    layouts
                    entry.targetFrameDepth
                    entry.targetLocal
              match
                Bool.or
                  (derefWriteTreeUB locals₁ mem₁.borrows dst)
                  (derefWriteUnionProtectorUB
                    targetDecls
                    targetLayouts
                    locals₁
                    mem₁.borrows
                    mem₁.activeProtectors
                    dst
                    restProj
                    mem₁.callStack)
              with
              | true => .ub
              | false =>
                let borrows' :=
                  match targetDecls with
                  | .nil =>
                    invalidateDerefWriteBorrows
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callerLocals
                      mem₁.callStack
                  | _ :: _ =>
                    invalidateDerefWriteBorrowsWithLayouts
                      targetDecls
                      targetLayouts
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callStack
                match commitForeignFrameLocals mem₁ target targetLocals' with
                | .some mem₂ => .ok locals₁ { mem₂ with borrows := borrows' }
                | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
      | .none => .ub
    | .none => .ub
  | _ => .ub

/--
Repaired `evalRvalue`:
- Uses `evalOperandProto` for `Rvalue.use`.
- Propagates `callerReferentFrameDepth` (`isCallerReferentBorrow`) across child
  reborrows (`Rvalue.ref` and `Rvalue.rawPtr` on `.deref :: restProj`) and resolves
  the referent root value from `mem.callerLocals[parentEntry.targetLocal]` even
  when `parentEntry.targetLocal < length locals`.
-/
def evalRvalueProto
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory := emptyMemory)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  match rv with
  | .use op =>
    match
      evalOperandProto
        locals
        op
        mem.borrows
        mem.globals
        layouts
        mem.callerLocals
        localDecls
        mem.callStack
    with
    | .ok v locals' => .ok v locals' mem
    | .ub => .ub
    | .unsupported => .unsupported
  | .ref borrowKind place =>
    match derefLookupCallerReferent? locals mem.borrows place with
    | .some (parentPtr, parentEntry, restProj) =>
      let perm :=
        match borrowKind with
        | .shared => sharedBorrowPerm localDecls layouts place
        | .mut _ => mutableBorrowPerm localDecls layouts place
      let ptrBytes := layoutPointerBytes layouts
      match parentEntry.perm, borrowKind with
      | .disabled, _ => .ub
      | .frozen, .mut _ => .ub
      | _, _ =>
        match resolveBorrowProjectionElems locals restProj with
        | .none => .ub
        | .some resolvedRest =>
          match get? mem.callerLocals parentEntry.targetLocal with
          | .some (.init targetRootVal) =>
            let rawFull :=
              match parentEntry.targetProjection with
              | .nil => resolvedRest
              | ph :: pt => ph :: appendProjections pt resolvedRest
            match readProjectedValue locals targetRootVal rawFull with
            | .ok _ =>
              let tag := mem.nextTag
              let entry : BorrowEntry := {
                tag := tag
                targetLocal := parentEntry.targetLocal
                targetFrameDepth := parentEntry.targetFrameDepth
                allocDead := parentEntry.allocDead
                targetProjection := rawFull
                perm := perm
                rangeOffset := parentEntry.rangeOffset
                rangeLen := parentEntry.rangeLen
                parentTag := .some parentPtr.tag
              }
              let mem' := {
                mem with
                borrows := entry :: mem.borrows
                nextTag := Nat.add tag 1
              }
              .ok (.ptr { allocId := tag, offsetBytes := parentPtr.offsetBytes } ptrBytes) locals mem'
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
    | .none =>
      evalRvalue locals (.ref borrowKind place) mem localDecls layouts
  | .rawPtr mutability place =>
    match derefLookupCallerReferent? locals mem.borrows place with
    | .some (parentPtr, parentEntry, restProj) =>
      let ptrBytes := layoutPointerBytes layouts
      let cleanRest := stripTransparentProjections restProj
      match cleanRest with
      | .nil => .ok (.ptr parentPtr ptrBytes) locals mem
      | _ :: _ =>
        match resolveBorrowProjectionElems locals restProj with
        | .none => .ub
        | .some resolvedRest =>
          let rawFull :=
            match parentEntry.targetProjection with
            | .nil => resolvedRest
            | ph :: pt => ph :: appendProjections pt resolvedRest
          let tag := mem.nextTag
          let entry : BorrowEntry := {
            tag := tag
            targetLocal := parentEntry.targetLocal
            targetFrameDepth := parentEntry.targetFrameDepth
            allocDead := parentEntry.allocDead
            targetProjection := rawFull
            perm := parentEntry.perm
            rangeOffset := parentEntry.rangeOffset
            rangeLen := parentEntry.rangeLen
            parentTag := .some parentPtr.tag
          }
          let mem' := {
            mem with
            borrows := entry :: mem.borrows
            nextTag := Nat.add tag 1
          }
          .ok (.ptr { allocId := tag, offsetBytes := parentPtr.offsetBytes } ptrBytes) locals mem'
    | .none =>
      evalRvalue locals (.rawPtr mutability place) mem localDecls layouts
  | _ =>
    evalRvalue locals rv mem localDecls layouts

/--
Repaired `evalStmt` combining:
- Bug 1: `evalCopyNonOverlappingProto` on `StatementKind.intrinsic (.copyNonOverlapping ...)`,
- Bug 3: `foreignFrameDerefWriteProto` / `evalRvalueProto` / `evalOperandProto`
  for caller-owned referents after root tail calls,
- Bug 4: `stripLeadingOpaqueCast` before root-vs-projected dispatch in
  `StatementKind.assign`, `StatementKind.deinit`, and `StatementKind.setDiscriminant`,
  plus `uninitFieldWriteShellProto?` for `(_l as T).f = rv` on `.uninit` locals.
-/
def evalStmtProto
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlappingProto s src dst count localDecls layouts
  | .deinit p =>
    match stripLeadingOpaqueCast p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | proj :: rest =>
      match get? s.frame.locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue s.frame.locals rootVal (proj :: rest) with
        | .ok _ => MirStepNode.step (advanceStmt s s.frame.locals)
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | _ => MirStepNode.fail .ub
  | .setDiscriminant p variantIdx =>
    match p.projection with
    | .deref :: _ =>
      evalStmt s stmt localDecls layouts
    | _ =>
      match stripLeadingOpaqueCast p.projection with
      | .nil =>
        evalStmt s ⟨.setDiscriminant ⟨p.local_, .nil⟩ variantIdx, stmt.span⟩ localDecls layouts
      | _ :: _ =>
        evalStmt s stmt localDecls layouts
  | .assign dst rv =>
    match evalRvalueProto s.frame.locals rv s.memory localDecls layouts with
    | .ok val locals₁ mem₁ =>
      match dst.projection with
      | .deref :: restProj =>
        match
          evalPlaceWriteProto
            locals₁
            mem₁.borrows
            dst
            val
            mem₁.activeProtectors
            localDecls
            layouts
            mem₁.callStack
        with
        | .ok locals₂ =>
          match
            Bool.or
              (derefWriteTreeUB locals₁ mem₁.borrows dst)
              (derefWriteUnionProtectorUB
                localDecls
                layouts
                locals₁
                mem₁.borrows
                mem₁.activeProtectors
                dst
                restProj
                mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateDerefWriteBorrowsWithLayouts
                localDecls
                layouts
                locals₁
                mem₁.borrows
                dst
                restProj
                mem₁.callStack
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .ub =>
          match foreignFrameDerefWriteProto locals₁ mem₁ dst restProj val localDecls layouts with
          | .ok locals₂ mem₂ => MirStepNode.step (advanceStmt s locals₂ mem₂)
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | .unsupported => MirStepNode.unsupported
      | _ =>
        match stripLeadingOpaqueCast dst.projection with
        | .nil =>
          match get? locals₁ dst.local_ with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? locals₁ dst.local_ (.init val) with
            | .some locals₂ =>
              match mem₁.activeProtectors with
              | .nil =>
                let borrows' :=
                  invalidateConflictingBorrows
                    mem₁.borrows dst.local_ .none (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | protHead :: protTail =>
                match
                  hasProtectedWriteConflict
                    mem₁.borrows
                    (protHead :: protTail)
                    dst.local_
                    .none
                    .nil
                    0
                    0
                    (length mem₁.callStack)
                with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateConflictingBorrows
                      mem₁.borrows dst.local_ .none (length mem₁.callStack)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub
        | proj :: rest =>
          match get? locals₁ dst.local_ with
          | .some (.init rootVal) =>
            match
              writeProjectedForLocal
                locals₁
                localDecls
                layouts
                dst.local_
                (ensureNestedFieldShells rootVal dst.projection)
                dst.projection
                val
            with
            | .ok rootVal' =>
              match set? locals₁ dst.local_ (.init rootVal') with
              | .some locals₂ =>
                let resolvedLocalProj :=
                  resolveBorrowWriteLocalProj
                    localDecls
                    layouts
                    locals₁
                    dst.local_
                    dst.projection
                match mem₁.activeProtectors with
                | .nil =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
                | protHead :: protTail =>
                  match
                    hasProtectedWriteConflict
                      mem₁.borrows
                      (protHead :: protTail)
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  with
                  | true => MirStepNode.fail .ub
                  | false =>
                    let borrows' :=
                      invalidateConflictingBorrowsAtProj
                        mem₁.borrows
                        dst.local_
                        .none
                        resolvedLocalProj
                        0
                        0
                        (length mem₁.callStack)
                    MirStepNode.step
                      (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | .none => MirStepNode.fail .ub
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
          | .some .uninit =>
            match uninitFieldWriteShellProto? localDecls layouts dst.local_ proj rest with
            | .some rootVal =>
              match
                writeProjectedForLocal
                  locals₁
                  localDecls
                  layouts
                  dst.local_
                  rootVal
                  dst.projection
                  val
              with
              | .ok rootVal' =>
                match set? locals₁ dst.local_ (.init rootVal') with
                | .some locals₂ =>
                  let resolvedLocalProj :=
                    resolveBorrowWriteLocalProj
                      localDecls
                      layouts
                      locals₁
                      dst.local_
                      dst.projection
                  match mem₁.activeProtectors with
                  | .nil =>
                    let borrows' :=
                      invalidateConflictingBorrowsAtProj
                        mem₁.borrows
                        dst.local_
                        .none
                        resolvedLocalProj
                        0
                        0
                        (length mem₁.callStack)
                    MirStepNode.step
                      (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
                  | protHead :: protTail =>
                    match
                      hasProtectedWriteConflict
                        mem₁.borrows
                        (protHead :: protTail)
                        dst.local_
                        .none
                        resolvedLocalProj
                        0
                        0
                        (length mem₁.callStack)
                    with
                    | true => MirStepNode.fail .ub
                    | false =>
                      let borrows' :=
                        invalidateConflictingBorrowsAtProj
                          mem₁.borrows
                          dst.local_
                          .none
                          resolvedLocalProj
                          0
                          0
                          (length mem₁.callStack)
                      MirStepNode.step
                        (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
                | .none => MirStepNode.fail .ub
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
            | .none => MirStepNode.fail .ub
          | .some .dead => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | _ => evalStmt s stmt localDecls layouts

/-! ## 5. Bug 2 & Bug 3: Repaired `TerminatorKind.tailCall` (`enterTailCalleeFrameProto`, `evalTailCallTerminatorProto`, `evalTerminatorProto`) -/

/--
Narrow the inherited caller frame's `returnUnwind` on `callStack` to
`.unreachable` when a `TerminatorKind.tailCall` enters a callee that cannot
unwind (`canUnwind = false`), matching Miri's `initStackFrame`
(`lean-miri/vendor/Miri/Interpreter/Call.lean:261-264`).
-/
@[reducible]
def narrowCallStackForTailCallee
    (callStack : List SavedCallerFrame)
    (canUnwind : Bool) :
    List SavedCallerFrame :=
  match callStack, canUnwind with
  | caller :: rest, false =>
    { caller with returnUnwind := .unreachable } :: rest
  | cs, _ => cs

@[simp]
theorem narrowCallStackForTailCallee_true (callStack : List SavedCallerFrame) :
    narrowCallStackForTailCallee callStack true = callStack := by
  cases callStack <;> rfl

@[simp]
theorem narrowCallStackForTailCallee_nil (canUnwind : Bool) :
    narrowCallStackForTailCallee .nil canUnwind = .nil := by
  cases canUnwind <;> rfl

@[simp]
theorem narrowCallStackForTailCallee_cons_false
    (caller : SavedCallerFrame) (rest : List SavedCallerFrame) :
    narrowCallStackForTailCallee (caller :: rest) false =
      { caller with returnUnwind := .unreachable } :: rest := rfl

@[simp]
theorem narrowCallStackForTailCallee_length
    (callStack : List SavedCallerFrame) (canUnwind : Bool) :
    length (narrowCallStackForTailCallee callStack canUnwind) = length callStack := by
  cases callStack <;> cases canUnwind <;> rfl

/--
Multi-hop monotonicity of `narrowCallStackForTailCallee`: once a tail call with
`canUnwind = false` narrows the top `SavedCallerFrame.returnUnwind` to
`.unreachable`, any subsequent tail call (even with `canUnwind₂ = true`) keeps
`returnUnwind = .unreachable`.
-/
theorem narrowCallStackForTailCallee_idempotent_after_false
    (callStack : List SavedCallerFrame) (canUnwind₂ : Bool) :
    narrowCallStackForTailCallee
      (narrowCallStackForTailCallee callStack false)
      canUnwind₂ =
    narrowCallStackForTailCallee callStack false := by
  cases callStack with
  | nil => cases canUnwind₂ <;> rfl
  | cons caller rest => cases canUnwind₂ <;> rfl

/--
Repaired `enterTailCalleeFrame`:
- Enters `calleeBody` at `bb0[0]` with `initLocals calleeBody argVals` without
  pushing onto `mem.callStack`,
- Narrows the top `SavedCallerFrame.returnUnwind` on `mem.callStack` to
  `.unreachable` when `calleeBody.fnAbi.canUnwind == false`
  (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).
-/
@[simp]
def enterTailCalleeFrameProto
    (mem : Memory)
    (calleeBody : CapturedMir)
    (argVals : List Value) :
    MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals calleeBody argVals
    }
    memory := {
      mem with
      callStack := narrowCallStackForTailCallee mem.callStack calleeBody.fnAbi.canUnwind
      activeCallee := .some calleeBody
    }
  }

/--
Repaired frame-teardown memory transition for `TerminatorKind.tailCall`:
applies `disableFrameBorrowsProto` at `(length s.memory.callStack, length s.frame.locals)`,
which disables the popped tail-caller's own locals while promoting any surviving
root caller-owned referents (`depth == 0, targetLocal >= nLocals`) to
`callerReferentFrameDepth` (`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`).
-/
@[reducible]
def frameTeardownMemProto (s : MachineState) : Memory :=
  { s.memory with
    borrows :=
      disableFrameBorrowsProto
        s.memory.borrows
        (length s.memory.callStack)
        (length s.frame.locals) }

/--
Repaired `unwindFromCallStack` using `disableFramesAboveProto` so caller-owned
referents (`callerReferentFrameDepth`) remain live when an inner frame catches an
unwind via `.cleanup cleanupBb`.
-/
@[simp]
def unwindFromCallStackProto : List SavedCallerFrame → Memory → MirExecState
  | .nil, _ => .halted .panic
  | caller :: restStack, memAfter =>
    let memCaller : Memory := {
      memAfter with
      callStack := restStack
      activeCallee := .some caller.callerBody
      activeProtectors := restoreCallerProtectors caller
    }
    match caller.returnUnwind with
    | .unreachable => .faulted .ub
    | .terminate => .halted .abort
    | .continue_ => unwindFromCallStackProto restStack memCaller
    | .cleanup cleanupBb =>
      .running {
        frame := {
          caller.frame with
          blockIdx := cleanupBb
          stmtIdx := 0
        }
        memory := {
          memCaller with
          borrows := disableFramesAboveProto memCaller.borrows (length restStack)
        }
      }

/--
Repaired `resumeExternalTailCall` using `unwindFromCallStackProto`.
-/
def resumeExternalTailCallProto (ans : MirCallAns) : MirExecState :=
  match ans with
  | .returned retVal memAfter =>
    resumeExternalTailCall (.returned retVal memAfter)
  | .panicked memAfter =>
    unwindFromCallStackProto memAfter.callStack memAfter
  | .aborted => .halted .abort

/--
Repaired `evalTailCallTerminator`:
- Evaluates `func` and `argOps` via `evalOperandsProto`,
- Checks `hasFrameDeallocProtectorConflict`,
- Tears down the tail-caller frame via `disableFrameBorrowsProto` (preserving and
  isolating root caller-owned referents via `callerReferentFrameDepth`),
- Enters `calleeBody` via `enterTailCalleeFrameProto` (narrowing `returnUnwind`
  to `.unreachable` when `calleeBody.fnAbi.canUnwind = false`).
-/
def evalTailCallTerminatorProto
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (currentBody : Option CapturedMir) :
    MirStepNode :=
  let bodyLocalDecls := bodyLocalDeclsOf currentBody
  let bodyLayouts : LayoutTable :=
    match currentBody with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  match
    resolveCallTarget
      s
      func
      (length argOps)
      bodyLocalDecls
      bodyLayouts
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok target localsAfterFunc =>
    match
      evalOperandsProto
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        bodyLayouts
        s.memory.callerLocals
        bodyLocalDecls
        s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok argVals _ =>
      let depth := length s.memory.callStack
      let nLocals := length s.frame.locals
      match
        hasFrameDeallocProtectorConflict
          s.memory.borrows
          s.memory.activeProtectors
          depth
          nLocals
      with
      | true => MirStepNode.fail .ub
      | false =>
        let memAfterTeardown : Memory :=
          { s.memory with borrows := disableFrameBorrowsProto s.memory.borrows depth nLocals }
        match
          lookupCallee
            s.memory.callees
            bodyLayouts
            target.defPath
            target.typeArgs
            s.memory.traitImpls
        with
        | .some calleeBody =>
          match checkCalleeTargetCompatible target calleeBody (length argVals) with
          | false => MirStepNode.fail .ub
          | true =>
            MirStepNode.step (enterTailCalleeFrameProto memAfterTeardown calleeBody argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath
              typeArgs := target.typeArgs
              args := argVals
              memory := memAfterTeardown }
            resumeExternalTailCallProto

/--
Repaired `evalTerminator`:
- Dispatches `.tailCall` to `evalTailCallTerminatorProto`,
- Dispatches `.unwindResume` to `unwindFromCallStackProto`,
- Strips leading `.opaqueCast` in `.drop` before root-vs-projected dispatch.
-/
def evalTerminatorProto
    (s : MachineState)
    (term : Terminator)
    (currentBody : Option CapturedMir := .none) :
    MirStepNode :=
  match term.kind with
  | .tailCall func argOps =>
    evalTailCallTerminatorProto s func argOps currentBody
  | .unwindResume =>
    match unwindFromCallStackProto s.memory.callStack s.memory with
    | .running nextState => MirStepNode.step nextState
    | .halted out => MirStepNode.retOutcome out
    | .faulted fk => MirStepNode.fail fk
  | .drop place target _ =>
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some slot =>
      match stripLeadingOpaqueCast place.projection with
      | .nil =>
        match set? s.frame.locals place.local_ .uninit with
        | .some locals' =>
          MirStepNode.step {
            s with
            frame := { blockIdx := target, stmtIdx := 0, locals := locals' }
          }
        | .none => MirStepNode.fail .ub
      | _ :: _ =>
        match slot with
        | .init rootVal =>
          match readProjectedValue s.frame.locals rootVal place.projection with
          | .ok _ =>
            MirStepNode.step {
              s with
              frame := { s.frame with blockIdx := target, stmtIdx := 0 }
            }
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub
  | _ => evalTerminator s term currentBody

/-! ## 6. Unified Prototype Step Evaluator & Bounded Differential Runner -/

/--
Initialize `MachineState` for `body` with incoming `args` and `mem`, promoting
any initial caller-owned referent borrows (`targetFrameDepth == 0` and
`targetLocal >= length body.localDecls`) to `callerReferentFrameDepth`.
-/
def initMachineStateWithMemoryProto
    (body : CapturedMir) (args : List Value) (mem : Memory) : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := initLocals body args
    }
    memory := {
      mem with
      borrows := promoteRootCallerReferentBorrows mem.borrows (length body.localDecls)
    }
  }

/--
One-step prototype MIR coalgebra transition from an active `MachineState`.
-/
def stepMirFnProto (body : CapturedMir) (s : MachineState) : MirStepNode :=
  let currentBody := s.memory.activeCallee.getD body
  match currentBody.phase with
  | .other _ => MirStepNode.unsupported
  | _ =>
    match get? currentBody.basicBlocks s.frame.blockIdx with
    | none => MirStepNode.fail .ub
    | some bb =>
      match get? bb.statements s.frame.stmtIdx with
      | some stmt => evalStmtProto s stmt currentBody.localDecls currentBody.layouts
      | none =>
        if s.frame.stmtIdx == length bb.statements then
          evalTerminatorProto s bb.terminator (some currentBody)
        else
          MirStepNode.fail .ub

/-- Total `ITreeF` coalgebra step over `MirExecState` using `stepMirFnProto`. -/
def stepMirStateProto (body : CapturedMir) : MirExecState → MirStepNode
  | .running s => stepMirFnProto body s
  | .halted out => .ret out
  | .faulted fk => MirStepNode.fail fk

/-- One coalgebra step on `MirExecState` under `stepMirStateProto`. -/
def execStepProto (body : CapturedMir) (s : MirExecState) : Option MirExecState :=
  match stepMirStateProto body s with
  | .ret out => some (.halted out)
  | .tau s' => some s'
  | .vis (.inl (.fail k)) _ => some (.faulted k)
  | .vis (.inr (.inl _)) k => some (k PUnit.unit)
  | .vis (.inr (.inr _)) _ => none

/-- `n` coalgebra steps under `execStepProto`. -/
def execNProto (body : CapturedMir) : Nat → MirExecState → Option MirExecState
  | 0, s => some s
  | n + 1, s => (execStepProto body s).bind (execNProto body n)

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps under
`stepMirStateProto`, classifying the terminal outcome into a `MirDiffVerdict`.
-/
def evalMirDiffExecBoundedProto
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : MirDiffVerdict :=
  match fuel with
  | 0 => .outOfFuel
  | fuel' + 1 =>
    match stepMirStateProto body st with
    | .ret (.normal (retVal, mem)) => .normal retVal mem
    | .ret .panic => .panic
    | .ret .abort => .abort
    | .tau st' => evalMirDiffExecBoundedProto fuel' body st'
    | .vis (.inl (.fail .ub)) _ => .ub
    | .vis (.inl (.fail .unsupported)) _ => .unsupported
    | .vis (.inl (.fail .outOfFuel)) _ => .outOfFuel
    | .vis (.inr (.inl _)) k => evalMirDiffExecBoundedProto fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ => .externalCall req.defPath

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps under
`stepMirStateProto` and return its `MirDiffVerdict`.
-/
def evalMirDiffBoundedProto
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffVerdict :=
  evalMirDiffExecBoundedProto fuel body (.running s)

/--
Evaluate `body` starting from `s : MachineState` for up to `fuel` steps under
`stepMirStateProto` and return its decidable `MirDiffTag`.
-/
def evalMirDiffTagBoundedProto
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : MirDiffTag :=
  (evalMirDiffBoundedProto fuel body s).toTagWithBody body

/--
Evaluate `body` from `st : MirExecState` for up to `fuel` steps under
`stepMirStateProto` and return `(MirDiffTag, span)`.
-/
def probeMirDiffExecBoundedProto
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    MirDiffTag × String :=
  match fuel with
  | 0 => (.outOfFuel, activeMirSpan body st)
  | fuel' + 1 =>
    match stepMirStateProto body st with
    | .ret (.normal (retVal, mem)) =>
      ((MirDiffVerdict.normal retVal mem).toTagWithBody body, "none")
    | .ret .panic => (.panic, activeMirSpan body st)
    | .ret .abort => (.abort, activeMirSpan body st)
    | .tau st' => probeMirDiffExecBoundedProto fuel' body st'
    | .vis (.inl (.fail .ub)) _ => (.ub, activeMirSpan body st)
    | .vis (.inl (.fail .unsupported)) _ => (.unsupported, activeMirSpan body st)
    | .vis (.inl (.fail .outOfFuel)) _ => (.outOfFuel, activeMirSpan body st)
    | .vis (.inr (.inl _)) k =>
      probeMirDiffExecBoundedProto fuel' body (k PUnit.unit)
    | .vis (.inr (.inr (.call req))) _ =>
      (.externalCall req.defPath, activeMirSpan body st)


/-! ## 7. Campaign #14 & #15 Minimized Miri Divergence Witnesses (`by rfl`) -/

/--
Synthetic stand-in for the `core::fmt::Arguments` constructor `defPath`,
matching `MiriOracleConfirm.lean` in Campaign #14 and Campaign #15.
-/
def fmtArgumentsCtorStub (defPath : String) : CapturedMir :=
  { defPath := defPath
    phase := MirPhaseTag.runtimePostCleanup
    role := ContractRole.model
    argCount := 1
    localDecls :=
      [{ mutability := Mutability.mut, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none },
       { mutability := Mutability.not, ty := { kind := RigidTy.ref Mutability.not RigidTy.str, layoutIdx := 0 }, debugName := Option.none }]
    basicBlocks :=
      [{ statements :=
           [{ kind := StatementKind.assign { local_ := 0, projection := [] }
                (Rvalue.use (Operand.copy { local_ := 1, projection := [] })),
              span := "<dummy>" }]
         terminator := { kind := TerminatorKind.return_, span := "<dummy>" }
         isCleanup := false }]
    fnAbi :=
      { args := [{ layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }]
        ret := { layout := { size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }, mode := AbiPassMode.pair }
        conv := CallConv.rust
        canUnwind := false }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries :=
          [{ size := { bytes := 16 }, align := { bytes := 8 }, backendRepr := BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 }) (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 }), fields := FieldsShape.arbitrary [{ bytes := 0 }, { bytes := 8 }] [0, 1], variants := VariantsShape.single 0, isUninhabited := false }] }
    allocations := [] }

/-- Linked `core::fmt::Arguments` constructors for `miri-difftest` modules. -/
def linkedCallees : List CapturedMir :=
  [fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::from_str_nonconst",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'a>::new_const",
   fmtArgumentsCtorStub "core::fmt::Arguments::<'_>::new_const"]

namespace Campaign14_pass_transmute_u32_byte_array_le__b0_c6

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 1 } 4), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 2 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 1 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 (List.cons 4 List.nil)) } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 4 } 2), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 1 List.nil) } List.nil))))))))) }

def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_transmute_u32_byte_array_le__b0_c6",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "word") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 2 }, debugName := (Option.some "bytes") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_ptr_26165") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u8) (List.cons RigidTy.bool List.nil))), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 6 }, debugName := (Option.some "__cp_src") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 6 }, debugName := (Option.some "__cp_dst") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 8 }, debugName := (Option.some "__src_p") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 8 }, debugName := (Option.some "__dst_p") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := (Option.some "__miri_ptr_26165") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, debugName := Option.none } List.nil)))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 7), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 10), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 11), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 17), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 20), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 27), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 30), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:183:9: 183:13" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 67305985, sizeBytes := 4 })) }))), span := "src/lib.rs:183:21: 183:32" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:184:9: 184:14" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:184:45: 184:49" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 1, projection := List.nil }))), span := "src/lib.rs:184:45: 184:49" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.move { local_ := 3, projection := List.nil }) { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 2 })), span := "src/lib.rs:184:35: 184:50" } (List.cons { kind := (StatementKind.storageDead 3), span := "src/lib.rs:184:49: 184:50" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:185:9: 185:32" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:185:39: 185:47" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:185:45: 185:46" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:185:45: 185:46" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 6, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 8 })) }))), span := "src/lib.rs:185:39: 185:47" } List.nil))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 7, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:185:39: 185:47" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := (List.cons (ProjectionElem.index 6) List.nil) }))), span := "src/lib.rs:185:39: 185:47" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:185:50: 185:58" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:185:56: 185:57" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 8 })) }))), span := "src/lib.rs:185:56: 185:57" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 8 })) }))), span := "src/lib.rs:185:50: 185:58" } List.nil))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 10, projection := List.nil }) true 2 UnwindAction.continue_), span := "src/lib.rs:185:50: 185:58" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := (List.cons (ProjectionElem.index 9) List.nil) }))), span := "src/lib.rs:185:50: 185:58" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.binaryOp BinOp.addWithOverflow (Operand.copy { local_ := 5, projection := List.nil }) (Operand.copy { local_ := 8, projection := List.nil }))), span := "src/lib.rs:185:39: 185:58" } List.nil)), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 11, projection := (List.cons (ProjectionElem.field 1 { kind := RigidTy.bool, layoutIdx := 4 }) List.nil) }) false 3 UnwindAction.continue_), span := "src/lib.rs:185:39: 185:58" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.use (Operand.move { local_ := 11, projection := (List.cons (ProjectionElem.field 0 { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }) List.nil) }))), span := "src/lib.rs:185:39: 185:58" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:185:57: 185:58" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:185:57: 185:58" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:185:58: 185:59" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:185:58: 185:59" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:186:9: 186:17" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 22, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 99, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:186:30: 186:44" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:187:9: 187:21" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 1 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:187:34: 187:46" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:188:5: 192:6" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:189:13: 189:20" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:189:55: 189:56" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:189:55: 189:56" } (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 16, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:189:46: 189:57" } List.nil)))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 17, projection := List.nil }) true 4 UnwindAction.continue_), span := "src/lib.rs:189:46: 189:57" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 12, projection := (List.cons (ProjectionElem.index 16) List.nil) })), span := "src/lib.rs:189:35: 189:57" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:189:57: 189:58" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:190:13: 190:20" } (List.cons { kind := (StatementKind.storageLive 19), span := "src/lib.rs:190:51: 190:52" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:190:51: 190:52" } (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 19, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:190:42: 190:53" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 20, projection := List.nil }) true 5 UnwindAction.continue_), span := "src/lib.rs:190:42: 190:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.rawPtr Mutability.mut { local_ := 13, projection := (List.cons (ProjectionElem.index 19) List.nil) })), span := "src/lib.rs:190:33: 190:53" } (List.cons { kind := (StatementKind.storageDead 19), span := "src/lib.rs:190:53: 190:54" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:191:9: 191:54" } (List.cons { kind := (StatementKind.storageLive 22), span := "src/lib.rs:191:29: 191:36" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 15, projection := List.nil }))), span := "src/lib.rs:191:29: 191:36" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:191:38: 191:45" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 18, projection := List.nil }))), span := "src/lib.rs:191:38: 191:45" } (List.cons { kind := (StatementKind.intrinsic (NonDivergingIntrinsic.copyNonOverlapping (Operand.move { local_ := 22, projection := List.nil }) (Operand.move { local_ := 23, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:191:9: 191:54" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:191:53: 191:54" } (List.cons { kind := (StatementKind.storageDead 22), span := "src/lib.rs:191:53: 191:54" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:191:54: 191:55" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 7 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:188:5: 192:6" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:192:5: 192:6" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:192:5: 192:6" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:192:5: 192:6" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:193:9: 193:25" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:193:33: 193:44" } (List.cons { kind := (StatementKind.storageLive 26), span := "src/lib.rs:193:42: 193:43" } (List.cons { kind := (StatementKind.assign { local_ := 26, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:193:42: 193:43" } (List.cons { kind := (StatementKind.assign { local_ := 27, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 26, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:193:33: 193:44" } List.nil)))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 27, projection := List.nil }) true 6 UnwindAction.continue_), span := "src/lib.rs:193:33: 193:44" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := (List.cons (ProjectionElem.index 26) List.nil) }))), span := "src/lib.rs:193:33: 193:44" } (List.cons { kind := (StatementKind.storageLive 28), span := "src/lib.rs:193:47: 193:58" } (List.cons { kind := (StatementKind.storageLive 29), span := "src/lib.rs:193:56: 193:57" } (List.cons { kind := (StatementKind.assign { local_ := 29, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 8 })) }))), span := "src/lib.rs:193:56: 193:57" } (List.cons { kind := (StatementKind.assign { local_ := 30, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 29, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:193:47: 193:58" } List.nil))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 30, projection := List.nil }) true 7 UnwindAction.continue_), span := "src/lib.rs:193:47: 193:58" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 28, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 13, projection := (List.cons (ProjectionElem.index 29) List.nil) }))), span := "src/lib.rs:193:47: 193:58" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 25, projection := List.nil }) (Operand.move { local_ := 28, projection := List.nil }))), span := "src/lib.rs:193:33: 193:58" } (List.cons { kind := (StatementKind.storageDead 28), span := "src/lib.rs:193:57: 193:58" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:193:57: 193:58" } (List.cons { kind := (StatementKind.storageDead 29), span := "src/lib.rs:193:58: 193:59" } (List.cons { kind := (StatementKind.storageDead 26), span := "src/lib.rs:193:58: 193:59" } (List.cons { kind := (StatementKind.storageLive 31), span := "src/lib.rs:194:5: 194:28" } (List.cons { kind := (StatementKind.assign { local_ := 31, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 4, projection := List.nil }))), span := "src/lib.rs:194:5: 194:28" } (List.cons { kind := (StatementKind.storageLive 32), span := "src/lib.rs:194:31: 194:55" } (List.cons { kind := (StatementKind.storageLive 33), span := "src/lib.rs:194:32: 197:48" } (List.cons { kind := (StatementKind.assign { local_ := 33, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 24, projection := List.nil }))), span := "src/lib.rs:194:32: 194:48" } (List.cons { kind := (StatementKind.assign { local_ := 32, projection := List.nil } (Rvalue.cast CastKind.intToInt (Operand.move { local_ := 33, projection := List.nil }) { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 })), span := "src/lib.rs:194:31: 194:55" } (List.cons { kind := (StatementKind.storageDead 33), span := "src/lib.rs:194:54: 194:55" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 31, projection := List.nil }) (Operand.move { local_ := 32, projection := List.nil }))), span := "src/lib.rs:194:5: 194:55" } (List.cons { kind := (StatementKind.storageDead 32), span := "src/lib.rs:194:54: 194:55" } (List.cons { kind := (StatementKind.storageDead 31), span := "src/lib.rs:194:54: 194:55" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:195:1: 195:2" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:195:1: 195:2" } (List.cons { kind := (StatementKind.storageDead 12), span := "src/lib.rs:195:1: 195:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:195:1: 195:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:195:1: 195:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:195:1: 195:2" } List.nil)))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:195:2: 195:2" }, isCleanup := false } List.nil)))))))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

/--
Baseline unpatched `Trusted` behavior on Campaign #14's minimized witness:
returns `19` (`5 ^ 22`) because `copy_nonoverlapping` overwrites `_13` with a
single scalar `22` instead of `[22, 99]`.
-/
theorem unpatched_tag_pass_transmute_u32_byte_array_le__b0_c6 :
    evalMirDiffTagBounded 512 body
      (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 19 1 := by
  rfl

/--
Repaired prototype behavior on Campaign #14's minimized witness:
returns `112` (`5 ^ (22 ^ 99) = 5 ^ 117 = 112`), matching live Miri (`MIRI_PASS:scalar:112:1`).
-/
theorem confirm_repaired_tag_pass_transmute_u32_byte_array_le__b0_c6 :
    evalMirDiffTagBoundedProto 512 body
      (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 112 1 := by
  rfl

/--
Repaired prototype probe on Campaign #14's minimized witness:
returns `((MirDiffTag.normalScalar 112 1), "none")`.
-/
theorem confirm_repaired_probe_pass_transmute_u32_byte_array_le__b0_c6 :
    probeMirDiffExecBoundedProto 512 body
      (.running (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees)) =
      (MirDiffTag.normalScalar 112 1, "none") := by
  rfl

end Campaign14_pass_transmute_u32_byte_array_le__b0_c6

namespace Campaign15_pass_enum_discriminant_valid__b2_c9

def layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } List.nil) (List.cons 0 List.nil)), variants := (VariantsShape.multiple (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 2 }) 0 (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) (List.cons (FieldsShape.arbitrary List.nil List.nil) List.nil)))), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 4 } 2), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 2 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } List.nil)))))))) }

def body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_enum_discriminant_valid__b2_c9",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 1 }, debugName := (Option.some "tag") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_ptr_46656") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 3 }, debugName := (Option.some "__cp_src") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.array (RigidTy.uint UintTy.u32) 2), layoutIdx := 3 }, debugName := (Option.some "__cp_dst") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := (Option.some "__src_p") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := (Option.some "__dst_p") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 5 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, debugName := (Option.some "__miri_ptr_46656") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, debugName := Option.none } List.nil)))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 3), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 9), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 12), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 19), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 22), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:183:9: 183:12" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.cast CastKind.transmute (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 1 })) }) { kind := (RigidTy.adt "miri_diff_corpus::ColorTag" List.nil), layoutIdx := 1 })), span := "src/lib.rs:183:34: 183:48" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:184:9: 184:32" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.discriminant { local_ := 1, projection := List.nil })), span := "src/lib.rs:184:45: 184:48" } List.nil))))))))), terminator := { kind := (TerminatorKind.switchInt (Operand.move { local_ := 3, projection := List.nil }) { branches := (List.cons (0, 4) (List.cons (1, 3) (List.cons (2, 2) List.nil))), otherwise := 1 }), span := "src/lib.rs:184:39: 184:48" }, isCleanup := false } (List.cons { statements := List.nil, terminator := { kind := TerminatorKind.unreachable, span := "src/lib.rs:184:45: 184:48" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 30, sizeBytes := 1 })) }))), span := "src/lib.rs:187:27: 187:29" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:187:27: 187:29" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 20, sizeBytes := 1 })) }))), span := "src/lib.rs:186:28: 186:30" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:186:28: 186:30" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 }, val := (ConstValue.scalar (ConstScalar.int { bits := 10, sizeBytes := 1 })) }))), span := "src/lib.rs:185:26: 185:28" } List.nil), terminator := { kind := (TerminatorKind.goto 5), span := "src/lib.rs:185:26: 185:28" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:189:9: 189:17" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 88, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 66, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:189:30: 189:44" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:190:9: 190:21" } (List.cons { kind := (StatementKind.assign { local_ := 5, projection := List.nil } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 2 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 4 })) }) List.nil)))), span := "src/lib.rs:190:34: 190:46" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:191:5: 195:6" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:192:13: 192:20" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:192:55: 192:56" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:192:55: 192:56" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 8, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:192:46: 192:57" } List.nil))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 9, projection := List.nil }) true 6 UnwindAction.continue_), span := "src/lib.rs:192:46: 192:57" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 4, projection := (List.cons (ProjectionElem.index 8) List.nil) })), span := "src/lib.rs:192:35: 192:57" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:192:57: 192:58" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:193:13: 193:20" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:193:51: 193:52" } (List.cons { kind := (StatementKind.assign { local_ := 11, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:193:51: 193:52" } (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 11, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:193:42: 193:53" } List.nil)))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 12, projection := List.nil }) true 7 UnwindAction.continue_), span := "src/lib.rs:193:42: 193:53" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.rawPtr Mutability.mut { local_ := 5, projection := (List.cons (ProjectionElem.index 11) List.nil) })), span := "src/lib.rs:193:33: 193:53" } (List.cons { kind := (StatementKind.storageDead 11), span := "src/lib.rs:193:53: 193:54" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:194:9: 194:54" } (List.cons { kind := (StatementKind.storageLive 14), span := "src/lib.rs:194:29: 194:36" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 7, projection := List.nil }))), span := "src/lib.rs:194:29: 194:36" } (List.cons { kind := (StatementKind.storageLive 15), span := "src/lib.rs:194:38: 194:45" } (List.cons { kind := (StatementKind.assign { local_ := 15, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 10, projection := List.nil }))), span := "src/lib.rs:194:38: 194:45" } (List.cons { kind := (StatementKind.intrinsic (NonDivergingIntrinsic.copyNonOverlapping (Operand.move { local_ := 14, projection := List.nil }) (Operand.move { local_ := 15, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:194:9: 194:54" } (List.cons { kind := (StatementKind.storageDead 15), span := "src/lib.rs:194:53: 194:54" } (List.cons { kind := (StatementKind.storageDead 14), span := "src/lib.rs:194:53: 194:54" } (List.cons { kind := (StatementKind.storageDead 13), span := "src/lib.rs:194:54: 194:55" } (List.cons { kind := (StatementKind.assign { local_ := 6, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 4 }, val := ConstValue.zeroSized }))), span := "src/lib.rs:191:5: 195:6" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:195:5: 195:6" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:195:5: 195:6" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:195:5: 195:6" } (List.cons { kind := (StatementKind.storageLive 16), span := "src/lib.rs:196:9: 196:25" } (List.cons { kind := (StatementKind.storageLive 17), span := "src/lib.rs:196:33: 196:44" } (List.cons { kind := (StatementKind.storageLive 18), span := "src/lib.rs:196:42: 196:43" } (List.cons { kind := (StatementKind.assign { local_ := 18, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:196:42: 196:43" } (List.cons { kind := (StatementKind.assign { local_ := 19, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 18, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:196:33: 196:44" } List.nil)))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 19, projection := List.nil }) true 8 UnwindAction.continue_), span := "src/lib.rs:196:33: 196:44" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 17, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := (List.cons (ProjectionElem.index 18) List.nil) }))), span := "src/lib.rs:196:33: 196:44" } (List.cons { kind := (StatementKind.storageLive 20), span := "src/lib.rs:196:47: 196:58" } (List.cons { kind := (StatementKind.storageLive 21), span := "src/lib.rs:196:56: 196:57" } (List.cons { kind := (StatementKind.assign { local_ := 21, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 8 })) }))), span := "src/lib.rs:196:56: 196:57" } (List.cons { kind := (StatementKind.assign { local_ := 22, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 21, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 6 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 8 })) }))), span := "src/lib.rs:196:47: 196:58" } List.nil))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 22, projection := List.nil }) true 9 UnwindAction.continue_), span := "src/lib.rs:196:47: 196:58" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 20, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 5, projection := (List.cons (ProjectionElem.index 21) List.nil) }))), span := "src/lib.rs:196:47: 196:58" } (List.cons { kind := (StatementKind.assign { local_ := 16, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 17, projection := List.nil }) (Operand.move { local_ := 20, projection := List.nil }))), span := "src/lib.rs:196:33: 196:58" } (List.cons { kind := (StatementKind.storageDead 20), span := "src/lib.rs:196:57: 196:58" } (List.cons { kind := (StatementKind.storageDead 17), span := "src/lib.rs:196:57: 196:58" } (List.cons { kind := (StatementKind.storageDead 21), span := "src/lib.rs:196:58: 196:59" } (List.cons { kind := (StatementKind.storageDead 18), span := "src/lib.rs:196:58: 196:59" } (List.cons { kind := (StatementKind.storageLive 23), span := "src/lib.rs:197:5: 197:28" } (List.cons { kind := (StatementKind.assign { local_ := 23, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 2, projection := List.nil }))), span := "src/lib.rs:197:5: 197:28" } (List.cons { kind := (StatementKind.storageLive 24), span := "src/lib.rs:197:31: 197:55" } (List.cons { kind := (StatementKind.storageLive 25), span := "src/lib.rs:197:32: 197:48" } (List.cons { kind := (StatementKind.assign { local_ := 25, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 16, projection := List.nil }))), span := "src/lib.rs:197:32: 197:48" } (List.cons { kind := (StatementKind.assign { local_ := 24, projection := List.nil } (Rvalue.cast CastKind.intToInt (Operand.move { local_ := 25, projection := List.nil }) { kind := (RigidTy.uint UintTy.u8), layoutIdx := 0 })), span := "src/lib.rs:197:31: 197:55" } (List.cons { kind := (StatementKind.storageDead 25), span := "src/lib.rs:197:54: 197:55" } (List.cons { kind := (StatementKind.assign { local_ := 0, projection := List.nil } (Rvalue.binaryOp BinOp.bitXor (Operand.move { local_ := 23, projection := List.nil }) (Operand.move { local_ := 24, projection := List.nil }))), span := "src/lib.rs:197:5: 197:55" } (List.cons { kind := (StatementKind.storageDead 24), span := "src/lib.rs:197:54: 197:55" } (List.cons { kind := (StatementKind.storageDead 23), span := "src/lib.rs:197:54: 197:55" } (List.cons { kind := (StatementKind.storageDead 16), span := "src/lib.rs:198:1: 198:2" } (List.cons { kind := (StatementKind.storageDead 5), span := "src/lib.rs:198:1: 198:2" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:198:1: 198:2" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:198:1: 198:2" } (List.cons { kind := (StatementKind.storageDead 1), span := "src/lib.rs:198:1: 198:2" } List.nil))))))))))))))))))))), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:198:2: 198:2" }, isCleanup := false } List.nil)))))))))),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := layouts,
    allocations := List.nil
  }

/--
Baseline unpatched `Trusted` behavior on Campaign #15's minimized witness:
returns `70` (`30 ^ 88`) because `copy_nonoverlapping` overwrites `_5` with a
single scalar `88` instead of `[88, 66]`.
-/
theorem unpatched_tag_pass_enum_discriminant_valid__b2_c9 :
    evalMirDiffTagBounded 512 body
      (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 70 1 := by
  rfl

/--
Repaired prototype behavior on Campaign #15's minimized witness:
returns `4` (`30 ^ (88 ^ 66) = 30 ^ 26 = 4`), matching live Miri (`MIRI_PASS:scalar:4:1`).
-/
theorem confirm_repaired_tag_pass_enum_discriminant_valid__b2_c9 :
    evalMirDiffTagBoundedProto 512 body
      (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees) =
      MirDiffTag.normalScalar 4 1 := by
  rfl

/--
Repaired prototype probe on Campaign #15's minimized witness:
returns `((MirDiffTag.normalScalar 4 1), "none")`.
-/
theorem confirm_repaired_probe_pass_enum_discriminant_valid__b2_c9 :
    probeMirDiffExecBoundedProto 512 body
      (.running (initMachineStateWithMemoryAndCallees body [] emptyMemory linkedCallees)) =
      (MirDiffTag.normalScalar 4 1, "none") := by
  rfl

end Campaign15_pass_enum_discriminant_valid__b2_c9

/-! ## 8. Universal Characterization & Simulation Theorems for Bug 1 -/

/--
Zero-count `copy_nonoverlapping` (`countBits == 0`) advances the statement
counter without reading or mutating any memory slots.
-/
@[simp]
theorem evalCopyNonOverlappingPermOkProto_zero
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingPermOkProto
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry 0 locals₃ =
    MirStepNode.step (advanceStmt s locals₃) := rfl

@[simp]
theorem evalCopyNonOverlappingWithCountProto_zero
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCountProto
      s src dst localDecls layouts srcVal dstVal 0 locals₃ =
    MirStepNode.step (advanceStmt s locals₃) := rfl

/--
Single-element zero-offset `copy_nonoverlapping` (`countBits == 1`,
`srcPtr.offsetBytes == 0`, `dstPtr.offsetBytes == 0`) delegates directly to
`evalCopySingleDirectProto`.
-/
theorem evalCopyNonOverlappingPermOkProto_singleDirect_eq
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot)
    (hSrcOff : srcPtr.offsetBytes = 0)
    (hDstOff : dstPtr.offsetBytes = 0)
    (hNoUnionSrc : resolveUnionEndpoint? localDecls layouts locals₃ srcEntry = .none)
    (hNoUnionDst : resolveUnionEndpoint? localDecls layouts locals₃ dstEntry = .none) :
    evalCopyNonOverlappingPermOkProto
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry 1 locals₃ =
    evalCopySingleDirectProto
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ := by
  unfold evalCopyNonOverlappingPermOkProto
  simp [hSrcOff, hDstOff, hNoUnionSrc, hNoUnionDst]

/--
Helper lemma: `resolveArraySliceEndpoint?` on an array subplace
`[.constantIndex idx minLen false]` with zero pointer offset and no static
pointee layout resolves to `.some ([], idx, elems)`.
-/
theorem resolveArraySliceEndpoint?_constantIndex_zeroOff
    (locals₃ : List LocalSlot)
    (elems : List Value)
    (idx minLen n : Nat)
    (hMinBounds : Nat.ble minLen (length elems) = true)
    (hIdxBounds : Nat.ble idx (length elems) = true) :
    resolveArraySliceEndpoint?
      locals₃ (.aggregate 0 elems) [.constantIndex idx minLen false] 0 n .none emptyLayoutTable =
    .some (.nil, idx, elems) := by
  unfold resolveArraySliceEndpoint?
  have hZeroAdd : Nat.add 0 idx = idx := Nat.zero_add idx
  simp only [stripTransparentProjections,
    normalizeSubsliceProjections, normalizeSubsliceProjectionsAux,
    splitLastConstantIndexWithFromEnd?, readProjectedValue,
    hMinBounds, hIdxBounds, Bool.true_and, hZeroAdd]
  cases get? elems idx with
  | none => rfl
  | some elemVal =>
    cases elemVal with
    | aggregate vIdx _ => cases vIdx <;> rfl
    | _ => rfl

/--
Universal multi-element subplace slice copy characterization:
For any two distinct local array slots `srcLoc ≠ dstLoc` holding `.aggregate 0 srcElems`
and `.aggregate 0 dstElems`, when `srcEntry` targets `{ local_ := srcLoc, projection := [.constantIndex srcIdx minS false] }`
and `dstEntry` targets `{ local_ := dstLoc, projection := [.constantIndex dstIdx minD false] }`
with zero pointer offsets, `n ≥ 2` (`Nat.beq n 0 = false`, `Nat.beq n 1 = false`),
and in-bounds slices (`srcIdx + n ≤ length srcElems` and `dstIdx + n ≤ length dstElems`),
`evalCopyNonOverlappingPermOkProto` writes
`.aggregate 0 (spliceValues (takeValues n (dropValues srcIdx srcElems)) dstIdx dstElems)`
back to the parent array local `dstLoc` (`projection := []`).
-/
theorem evalCopyNonOverlappingPermOkProto_subplace_constantIndex_slice
    (s : MachineState)
    (src dst : Operand)
    (srcTag dstTag srcLoc dstLoc srcIdx minS dstIdx minD n : Nat)
    (srcPerm dstPerm : TreeBorrowPerm)
    (srcElems dstElems : List Value)
    (locals₃ : List LocalSlot)
    (hCountPos : Nat.beq n 0 = false)
    (hNotSingle : Nat.beq n 1 = false)
    (hDistinctTag : Nat.beq srcTag dstTag = false)
    (hDistinctLoc : Nat.beq srcLoc dstLoc = false)
    (_hCallStackNil : s.memory.callStack = .nil)
    (hSrcPt : operandPointeeTy .nil emptyLayoutTable src = .none)
    (hDstPt : operandPointeeTy .nil emptyLayoutTable dst = .none)
    (hSrcSlot : get? locals₃ srcLoc = .some (.init (.aggregate 0 srcElems)))
    (hDstSlot : get? locals₃ dstLoc = .some (.init (.aggregate 0 dstElems)))
    (hSrcSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 srcElems) [.constantIndex srcIdx minS false] 0 n .none emptyLayoutTable =
      .some (.nil, srcIdx, srcElems))
    (hDstSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 dstElems) [.constantIndex dstIdx minD false] 0 n .none emptyLayoutTable =
      .some (.nil, dstIdx, dstElems))
    (hSrcBounds : Nat.ble (Nat.add srcIdx n) (length srcElems) = true)
    (hDstBounds : Nat.ble (Nat.add dstIdx n) (length dstElems) = true) :
    let srcPtr : ProvenancePtr := { allocId := srcTag, offsetBytes := 0 }
    let dstPtr : ProvenancePtr := { allocId := dstTag, offsetBytes := 0 }
    let srcEntry : BorrowEntry := {
      tag := srcTag
      targetLocal := srcLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex srcIdx minS false]
      perm := srcPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := dstTag
      targetLocal := dstLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex dstIdx minD false]
      perm := dstPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let copiedSlice := takeValues n (dropValues srcIdx srcElems)
    let dstElems' := spliceValues copiedSlice dstIdx dstElems
    let dstSliceInvalProj :=
      match Nat.beq dstIdx 0 && Nat.beq n (length dstElems) with
      | true => .nil
      | false =>
        normalizeSubsliceProjections [.subslice dstIdx (Nat.add dstIdx n) false]
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    commitCopyDstPlaceWriteProto
      s
      { local_ := dstLoc, projection := .nil }
      dstEntry
      dstTag
      locals₃
      (.aggregate 0 dstElems')
      .nil
      emptyLayoutTable
      (.some dstSliceInvalProj) := by
  intro srcPtr dstPtr srcEntry dstEntry copiedSlice dstElems' dstSliceInvalProj
  unfold evalCopyNonOverlappingPermOkProto
  have hSrcRoot :
      resolveCopyEndpointRootSlot s locals₃ srcEntry =
        .some (.init (.aggregate 0 srcElems)) := by
    simp [resolveCopyEndpointRootSlot, srcEntry, hSrcSlot]
  have hDstRoot :
      resolveCopyEndpointRootSlot s locals₃ dstEntry =
        .some (.init (.aggregate 0 dstElems)) := by
    simp [resolveCopyEndpointRootSlot, dstEntry, hDstSlot]
  have hPlaceTyNil : ∀ p, placeTy .nil emptyLayoutTable p = .none := by
    intro p
    simp [placeTy, get?]
  have hTagEq : srcPtr.tag = srcTag := rfl
  have hDstTagEq : dstPtr.tag = dstTag := rfl
  cases hFull : (Nat.beq dstIdx 0 && Nat.beq n (length dstElems)) <;>
    simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
      hSrcRoot, hDstRoot, hSrcPt, hDstPt, hSrcSlice, hDstSlice,
      srcEntry, dstEntry, isCallerReferentBorrow_zero, hDstSlot,
      hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
      Nat.beq_refl, hDistinctLoc, hTagEq, hDstTagEq, hDistinctTag,
      copiedSlice, dstElems', dstSliceInvalProj, appendProjections, hFull]

/--
Out-of-bounds multi-element subplace copy (`srcIdx + n > length srcElems`)
always faults with `MirStepNode.fail .ub`.
-/
theorem evalCopyNonOverlappingPermOkProto_subplace_src_oob_ub
    (s : MachineState)
    (src dst : Operand)
    (srcTag dstTag srcLoc dstLoc srcIdx minS dstIdx minD n : Nat)
    (srcPerm dstPerm : TreeBorrowPerm)
    (srcElems dstElems : List Value)
    (locals₃ : List LocalSlot)
    (hCountPos : Nat.beq n 0 = false)
    (hNotSingle : Nat.beq n 1 = false)
    (_hCallStackNil : s.memory.callStack = .nil)
    (hSrcPt : operandPointeeTy .nil emptyLayoutTable src = .none)
    (hDstPt : operandPointeeTy .nil emptyLayoutTable dst = .none)
    (hSrcSlot : get? locals₃ srcLoc = .some (.init (.aggregate 0 srcElems)))
    (hDstSlot : get? locals₃ dstLoc = .some (.init (.aggregate 0 dstElems)))
    (hSrcSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 srcElems) [.constantIndex srcIdx minS false] 0 n .none emptyLayoutTable =
      .some (.nil, srcIdx, srcElems))
    (hDstSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 dstElems) [.constantIndex dstIdx minD false] 0 n .none emptyLayoutTable =
      .some (.nil, dstIdx, dstElems))
    (hSrcOob : Nat.ble (Nat.add srcIdx n) (length srcElems) = false) :
    let srcPtr : ProvenancePtr := { allocId := srcTag, offsetBytes := 0 }
    let dstPtr : ProvenancePtr := { allocId := dstTag, offsetBytes := 0 }
    let srcEntry : BorrowEntry := {
      tag := srcTag
      targetLocal := srcLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex srcIdx minS false]
      perm := srcPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := dstTag
      targetLocal := dstLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex dstIdx minD false]
      perm := dstPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    MirStepNode.fail .ub := by
  intro srcPtr dstPtr srcEntry dstEntry
  unfold evalCopyNonOverlappingPermOkProto
  have hSrcRoot :
      resolveCopyEndpointRootSlot s locals₃ srcEntry =
        .some (.init (.aggregate 0 srcElems)) := by
    simp [resolveCopyEndpointRootSlot, srcEntry, hSrcSlot]
  have hDstRoot :
      resolveCopyEndpointRootSlot s locals₃ dstEntry =
        .some (.init (.aggregate 0 dstElems)) := by
    simp [resolveCopyEndpointRootSlot, dstEntry, hDstSlot]
  have hPlaceTyNil : ∀ p, placeTy .nil emptyLayoutTable p = .none := by
    intro p
    simp [placeTy, get?]
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hSrcRoot, hDstRoot, hSrcPt, hDstPt, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, isCallerReferentBorrow_zero, hDstSlot,
    hPlaceTyNil, Bool.not_false, hSrcOob, Bool.and_false]

/--
Overlapping multi-element subplace copy within the same array container
(`srcLoc == dstLoc`, `srcParentProj == dstParentProj`, and the index intervals
`[srcIdx, srcIdx + n)` and `[dstIdx, dstIdx + n)` overlap) always faults with
`MirStepNode.fail .ub`.
-/
theorem evalCopyNonOverlappingPermOkProto_sameArray_overlap_ub
    (s : MachineState)
    (src dst : Operand)
    (srcTag dstTag arrLoc srcIdx minS dstIdx minD n : Nat)
    (srcPerm dstPerm : TreeBorrowPerm)
    (arrElems : List Value)
    (locals₃ : List LocalSlot)
    (hCountPos : Nat.beq n 0 = false)
    (hNotSingle : Nat.beq n 1 = false)
    (_hCallStackNil : s.memory.callStack = .nil)
    (hSrcPt : operandPointeeTy .nil emptyLayoutTable src = .none)
    (hDstPt : operandPointeeTy .nil emptyLayoutTable dst = .none)
    (hArrSlot : get? locals₃ arrLoc = .some (.init (.aggregate 0 arrElems)))
    (hSrcSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 arrElems) [.constantIndex srcIdx minS false] 0 n .none emptyLayoutTable =
      .some (.nil, srcIdx, arrElems))
    (hDstSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 arrElems) [.constantIndex dstIdx minD false] 0 n .none emptyLayoutTable =
      .some (.nil, dstIdx, arrElems))
    (hSrcBounds : Nat.ble (Nat.add srcIdx n) (length arrElems) = true)
    (hDstBounds : Nat.ble (Nat.add dstIdx n) (length arrElems) = true)
    (hOverlap1 : Nat.ble (Nat.add srcIdx n) dstIdx = false)
    (hOverlap2 : Nat.ble (Nat.add dstIdx n) srcIdx = false) :
    let srcPtr : ProvenancePtr := { allocId := srcTag, offsetBytes := 0 }
    let dstPtr : ProvenancePtr := { allocId := dstTag, offsetBytes := 0 }
    let srcEntry : BorrowEntry := {
      tag := srcTag
      targetLocal := arrLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex srcIdx minS false]
      perm := srcPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := dstTag
      targetLocal := arrLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex dstIdx minD false]
      perm := dstPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    MirStepNode.fail .ub := by
  intro srcPtr dstPtr srcEntry dstEntry
  unfold evalCopyNonOverlappingPermOkProto
  have hRoot :
      resolveCopyEndpointRootSlot s locals₃ srcEntry =
        .some (.init (.aggregate 0 arrElems)) := by
    simp [resolveCopyEndpointRootSlot, srcEntry, hArrSlot]
  have hPlaceTyNil : ∀ p, placeTy .nil emptyLayoutTable p = .none := by
    intro p
    simp [placeTy, get?]
  have hOverlapNil : projectionsOverlap .nil .nil = true := rfl
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hRoot, hSrcPt, hDstPt, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, isCallerReferentBorrow_zero, hArrSlot,
    hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
    Nat.beq_refl, hOverlapNil, hOverlap1, hOverlap2, Bool.or_false]

/--
Disjoint multi-element subplace copy within the same array container
(`srcLoc == dstLoc`, `srcParentProj == dstParentProj = []`, and
`srcIdx + n ≤ dstIdx`) succeeds and splices `[srcIdx, srcIdx + n)` into
`[dstIdx, dstIdx + n)` of the same array local `arrLoc`, even when `srcPtr` and
`dstPtr` share the same provenance tag (`p` and `p.add(k)`).
-/
theorem evalCopyNonOverlappingPermOkProto_sameArray_disjoint_ok
    (s : MachineState)
    (src dst : Operand)
    (srcTag dstTag arrLoc srcIdx minS dstIdx minD n : Nat)
    (srcPerm dstPerm : TreeBorrowPerm)
    (arrElems : List Value)
    (locals₃ : List LocalSlot)
    (hCountPos : Nat.beq n 0 = false)
    (hNotSingle : Nat.beq n 1 = false)
    (_hCallStackNil : s.memory.callStack = .nil)
    (hSrcPt : operandPointeeTy .nil emptyLayoutTable src = .none)
    (hDstPt : operandPointeeTy .nil emptyLayoutTable dst = .none)
    (hArrSlot : get? locals₃ arrLoc = .some (.init (.aggregate 0 arrElems)))
    (hSrcSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 arrElems) [.constantIndex srcIdx minS false] 0 n .none emptyLayoutTable =
      .some (.nil, srcIdx, arrElems))
    (hDstSlice :
      resolveArraySliceEndpoint?
        locals₃ (.aggregate 0 arrElems) [.constantIndex dstIdx minD false] 0 n .none emptyLayoutTable =
      .some (.nil, dstIdx, arrElems))
    (hSrcBounds : Nat.ble (Nat.add srcIdx n) (length arrElems) = true)
    (hDstBounds : Nat.ble (Nat.add dstIdx n) (length arrElems) = true)
    (hDisjoint : Nat.ble (Nat.add srcIdx n) dstIdx = true) :
    let srcPtr : ProvenancePtr := { allocId := srcTag, offsetBytes := 0 }
    let dstPtr : ProvenancePtr := { allocId := dstTag, offsetBytes := 0 }
    let srcEntry : BorrowEntry := {
      tag := srcTag
      targetLocal := arrLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex srcIdx minS false]
      perm := srcPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let dstEntry : BorrowEntry := {
      tag := dstTag
      targetLocal := arrLoc
      targetFrameDepth := 0
      allocDead := false
      targetProjection := [.constantIndex dstIdx minD false]
      perm := dstPerm
      rangeOffset := 0
      rangeLen := 0
      parentTag := .none
    }
    let copiedSlice := takeValues n (dropValues srcIdx arrElems)
    let arrElems' := spliceValues copiedSlice dstIdx arrElems
    let dstSliceInvalProj :=
      match Nat.beq dstIdx 0 && Nat.beq n (length arrElems) with
      | true => .nil
      | false =>
        normalizeSubsliceProjections [.subslice dstIdx (Nat.add dstIdx n) false]
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    commitCopyDstPlaceWriteProto
      s
      { local_ := arrLoc, projection := .nil }
      dstEntry
      dstTag
      locals₃
      (.aggregate 0 arrElems')
      .nil
      emptyLayoutTable
      (.some dstSliceInvalProj) := by
  intro srcPtr dstPtr srcEntry dstEntry copiedSlice arrElems' dstSliceInvalProj
  unfold evalCopyNonOverlappingPermOkProto
  have hRoot :
      resolveCopyEndpointRootSlot s locals₃ srcEntry =
        .some (.init (.aggregate 0 arrElems)) := by
    simp [resolveCopyEndpointRootSlot, srcEntry, hArrSlot]
  have hPlaceTyNil : ∀ p, placeTy .nil emptyLayoutTable p = .none := by
    intro p
    simp [placeTy, get?]
  have hOverlapNil : projectionsOverlap .nil .nil = true := rfl
  have hDstTagEq : dstPtr.tag = dstTag := rfl
  cases hFull : (Nat.beq dstIdx 0 && Nat.beq n (length arrElems)) <;>
    simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
      hRoot, hSrcPt, hDstPt, hSrcSlice, hDstSlice,
      srcEntry, dstEntry, isCallerReferentBorrow_zero, hArrSlot,
      hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
      Nat.beq_refl, hOverlapNil, hDisjoint, Bool.true_or, hDstTagEq,
      copiedSlice, arrElems', dstSliceInvalProj, appendProjections, hFull]

/-! ## 9. Universal Simulation Theorems & Witnesses for Bug 2 and Bug 3 -/

/--
**Bug 2 Universal Theorem (`tailCall_leanMiri_nounwind_callee_simulation`)**:
For any caller frame `caller` on `mem.callStack` (whatever its original
`caller.returnUnwind : UnwindAction` was: `.cleanup bb`, `.continue_`,
`.unreachable`, or `.terminate`) and any tail callee `calleeBody` with
`calleeBody.fnAbi.canUnwind = false`, entering `calleeBody` via
`enterTailCalleeFrameProto` and subsequently unwinding from the resulting
`callStack` via `unwindFromCallStackProto` unconditionally faults with
`MirExecState.faulted .ub` — matching Lean-Miri's `initStackFrame` narrowing
(`lean-miri/vendor/Miri/Interpreter/Call.lean:261-264`) without requiring any
caller-side hypothesis `hCallerNoUnwind`.
-/
theorem tailCall_leanMiri_nounwind_callee_simulation
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (mem : Memory)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (memAtUnwind : Memory)
    (hCalleeNoUnwind : calleeBody.fnAbi.canUnwind = false)
    (hStack : mem.callStack = caller :: restStack) :
    let stEntered := enterTailCalleeFrameProto mem calleeBody argVals
    unwindFromCallStackProto stEntered.memory.callStack memAtUnwind = .faulted .ub := by
  intro stEntered
  simp [stEntered, enterTailCalleeFrameProto, hStack, hCalleeNoUnwind,
    narrowCallStackForTailCallee, unwindFromCallStackProto]

/--
**Bug 2 Multi-Hop Monotonicity (`tailCall_nounwind_multihop_monotonicity`)**:
If `caller` calls `f` (`mem.callStack = caller :: restStack`), `f` tail-calls
`g` with `g.fnAbi.canUnwind = false`, and `g` subsequently tail-calls `h` with
arbitrary `h.fnAbi.canUnwind : Bool` (including `canUnwind = true`), unwinding
from `h` still unconditionally faults with `.faulted .ub` because the `.unreachable`
narrowing on `caller.returnUnwind` is monotone across arbitrary subsequent tail
calls.
-/
theorem tailCall_nounwind_multihop_monotonicity
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (mem : Memory)
    (gBody hBody : CapturedMir)
    (gArgs hArgs : List Value)
    (memAtUnwind : Memory)
    (hGNoUnwind : gBody.fnAbi.canUnwind = false)
    (hStack : mem.callStack = caller :: restStack) :
    let stG := enterTailCalleeFrameProto mem gBody gArgs
    let stH := enterTailCalleeFrameProto stG.memory hBody hArgs
    unwindFromCallStackProto stH.memory.callStack memAtUnwind = .faulted .ub := by
  intro stG stH
  cases hCan : hBody.fnAbi.canUnwind <;>
    simp [stG, stH, enterTailCalleeFrameProto, hStack, hGNoUnwind, hCan,
      narrowCallStackForTailCallee, unwindFromCallStackProto]

/--
**Bug 3 Universal Theorem (`tailCall_witness_root_caller_referent_simulation`)**:
For any root-frame borrow `entry` of a caller-owned referent in `callerLocals`
(`entry.targetFrameDepth = 0`, `entry.targetLocal ≥ nLocals` or already promoted
 via `promoteRootCallerReferentBorrows`, `entry.allocDead = false`,
 `entry.perm ≠ .disabled`):
1. Tearing down the tail-caller frame via `disableFrameBorrowsProto` stamps
   `entry` with `callerReferentFrameDepth` (`isCallerReferentBorrow = true`) and
   preserves its permission `entry.perm`.
2. Even when the tail callee's frame has `length calleeLocals > entry.targetLocal`
   (so `calleeLocals[entry.targetLocal]` exists and holds an unrelated value `shadowVal`),
   dereference reads (`evalPlaceReadProto`, `evalOperandProto (.copy)` / `(.move)`)
   through a pointer to `entry.tag` resolve to `callerLocals[entry.targetLocal]`
   rather than `calleeLocals[entry.targetLocal]`.
3. Writes to the tail callee's own local `calleeLocals[entry.targetLocal]` via
   `invalidateConflictingBorrows` at depth `0` do not invalidate `entry`.
4. Subsequent multi-hop tail-call teardowns (`disableFrameBorrowsProto` at any
   `calleeNLocals`, even `calleeNLocals > entry.targetLocal`) preserve `entry`
   unchanged.
-/
theorem tailCall_witness_root_caller_referent_simulation
    (tag targetLocal nLocals calleeNLocals ptrLoc : Nat)
    (perm : TreeBorrowPerm)
    (rangeOffset rangeLen : Nat)
    (parentTag : Option Nat)
    (calleeLocals callerLocals : List LocalSlot)
    (callerVal : Value)
    (hCallerOwned : Nat.blt targetLocal nLocals = false)
    (hPermLive : perm ≠ .disabled)
    (hPtrSlot : get? calleeLocals ptrLoc =
      .some (.init (.ptr { allocId := tag, offsetBytes := 0 } 8)))
    (hCallerSlot : get? callerLocals targetLocal = .some (.init callerVal)) :
    let rawEntry : BorrowEntry := {
      tag := tag
      targetLocal := targetLocal
      targetFrameDepth := 0
      allocDead := false
      targetProjection := .nil
      perm := perm
      rangeOffset := rangeOffset
      rangeLen := rangeLen
      parentTag := parentTag
    }
    let borrowsAfterTail1 := disableFrameBorrowsProto [rawEntry] 0 nLocals
    let borrowsAfterLocalWrite :=
      invalidateConflictingBorrows borrowsAfterTail1 targetLocal .none 0
    let borrowsAfterTail2 :=
      disableFrameBorrowsProto borrowsAfterLocalWrite 0 calleeNLocals
    evalPlaceReadProto
      calleeLocals
      { local_ := ptrLoc, projection := [.deref] }
      borrowsAfterTail1
      .nil
      emptyLayoutTable
      callerLocals
      .nil
      .nil = .ok callerVal calleeLocals ∧
    borrowsAfterLocalWrite = borrowsAfterTail1 ∧
    borrowsAfterTail2 = borrowsAfterTail1 := by
  intro rawEntry borrowsAfterTail1 borrowsAfterLocalWrite borrowsAfterTail2
  have hTeardown1 :
      borrowsAfterTail1 = [{ rawEntry with targetFrameDepth := callerReferentFrameDepth }] := by
    simp [borrowsAfterTail1, disableFrameBorrowsProto, rawEntry, hCallerOwned]
  have hNonConflict :
      borrowsAfterLocalWrite = borrowsAfterTail1 := by
    simp [borrowsAfterLocalWrite, hTeardown1, invalidateConflictingBorrows,
      rawEntry, callerReferentFrameDepth]
  have hSentinelNotZero : Nat.beq callerReferentFrameDepth 0 = false := rfl
  have hTeardown2 :
      borrowsAfterTail2 = borrowsAfterTail1 := by
    simp [borrowsAfterTail2, hNonConflict, hTeardown1, disableFrameBorrowsProto,
      hSentinelNotZero, rawEntry]
  refine ⟨?_, hNonConflict, hTeardown2⟩
  rw [hTeardown1]
  cases perm <;>
    first
    | exact False.elim (hPermLive rfl)
    | simp [evalPlaceReadProto, derefLookupCallerReferent?, hPtrSlot,
        lookupBorrow, ProvenancePtr.tag, isCallerReferentBorrow,
        callerReferentFrameDepth, evalCallerReferentDerefRead,
        hCallerSlot, readProjectedValue, rawEntry]

namespace TailCallCallerReferentWitnesses

private def wTy : Ty := { kind := .uint .u64, layoutIdx := 0 }
private def wPtrTy : Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }

private def wFnAbi : FnAbi := {
  args := []
  ret := {
    layout := {
      size := { bytes := 8 }
      align := { bytes := 8 }
      backendRepr := .memory
      fields := .primitive
      variants := .single 0
      isUninhabited := false
    }
    mode := .direct
  }
  conv := .rust
  canUnwind := false
}

private def wDecl : LocalDecl := { mutability := .mut, ty := wTy, debugName := none }
private def wPtrDecl : LocalDecl := { mutability := .mut, ty := wPtrTy, debugName := none }
private def wSpan : String := "TcbCopySubplaceAndTailCallPrototype.lean"

private def mkSc (n : Nat) : Value := .scalar { bits := n, sizeBytes := 8 }

private def mkConstOp (n : Nat) : Operand :=
  .constant { ty := wTy, val := .scalar (.int { bits := n, sizeBytes := 8 }) }

private def mkFnOp (path : String) : Operand :=
  .constant { ty := { kind := .fnDef path [], layoutIdx := 0 }, val := .zeroSized }

/--
Tail callee `g_read(p: *mut u64, y: u64) -> u64` with 3 locals (`_0`, `_1 = p`, `_2 = y`)
that returns `*p` (matching `MirUntestedVariantCorrespondenceTests.lean:2441`).
-/
def gReadBody : CapturedMir := {
  defPath := "test::g_read"
  phase := .runtimeOptimized
  role := .subject
  argCount := 2
  localDecls := [wDecl, wPtrDecl, wDecl]
  basicBlocks := [
    { statements := [
        ⟨.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩)), wSpan⟩
      ]
      terminator := ⟨.return_, wSpan⟩
      isCleanup := false }
  ]
  fnAbi := wFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/--
Root function `f_cr(p: *mut u64) -> u64` (`2` locals: `_0`, `_1 = p`) that
tail-calls `g_read(copy _1, 137)` where `p` points to `callerLocals[2] = 42`.
-/
def fCrBody : CapturedMir := {
  defPath := "test::f_cr"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [wDecl, wPtrDecl]
  basicBlocks := [
    { statements := []
      terminator := ⟨.tailCall (mkFnOp "test::g_read") [.copy ⟨1, []⟩, mkConstOp 137], wSpan⟩
      isCleanup := false }
  ]
  fnAbi := wFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/--
Root function `f_rd(p: *mut u64) -> u64` (`2` locals: `_0`, `_1 = p`) that
directly reads `*p` without a tail call.
-/
def fRdBody : CapturedMir := {
  defPath := "test::f_rd"
  phase := .runtimeOptimized
  role := .subject
  argCount := 1
  localDecls := [wDecl, wPtrDecl]
  basicBlocks := [
    { statements := [⟨.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩)), wSpan⟩]
      terminator := ⟨.return_, wSpan⟩
      isCleanup := false }
  ]
  fnAbi := wFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/--
Root function `f_dangle() -> u64` (`3` locals: `_0`, `_1 = p`, `_2 = 99`)
that takes a raw pointer to its own local `_2` and tail-calls `g_read(copy _1, 137)`.
-/
def fDangleBody : CapturedMir := {
  defPath := "test::f_dangle"
  phase := .runtimeOptimized
  role := .subject
  argCount := 0
  localDecls := [wDecl, wPtrDecl, wDecl]
  basicBlocks := [
    { statements := [
        ⟨.storageLive 1, wSpan⟩,
        ⟨.storageLive 2, wSpan⟩,
        ⟨.assign ⟨2, []⟩ (.use (mkConstOp 99)), wSpan⟩,
        ⟨.assign ⟨1, []⟩ (.rawPtr .mut ⟨2, []⟩), wSpan⟩
      ]
      terminator := ⟨.tailCall (mkFnOp "test::g_read") [.copy ⟨1, []⟩, mkConstOp 137], wSpan⟩
      isCleanup := false }
  ]
  fnAbi := wFnAbi
  layouts := emptyLayoutTable
  allocations := []
}

/--
Initial `Memory` with `callerLocals[2] = 42` and borrow tag `0` pointing to
`(depth := 0, targetLocal := 2)`, matching `MirUntestedVariantCorrespondenceTests.lean:2645`.
-/
def crMem : Memory := {
  emptyMemory with
  callees := [gReadBody]
  callerLocals := [.uninit, .uninit, .init (mkSc 42)]
  borrows := [{
    tag := 0
    targetLocal := 2
    targetFrameDepth := 0
    allocDead := false
    targetProjection := []
    perm := .unique
    rangeOffset := 0
    rangeLen := 8
    parentTag := none
  }]
  nextTag := 1
}

def crPtrArg : Value := .ptr { allocId := 0, offsetBytes := 0 } 8

/--
Under `execNProto`, `fCrBody` (`f_cr(p) -> tailCall g_read(p, 137)`) reads
`callerLocals[2] = 42` instead of `gReadBody`'s shadowed local `_2 = 137`,
agreeing with `fRdBody` on the returned scalar `42`.
-/
theorem tailCall_repaired_root_caller_referent_returns_42 :
    (match execNProto fCrBody 3 (.running (initMachineStateWithMemoryProto fCrBody [crPtrArg] crMem)) with
     | some (.halted (.normal (v, _))) => some v
     | _ => none) =
    (match execNProto fRdBody 2 (.running (initMachineStateWithMemoryProto fRdBody [crPtrArg] crMem)) with
     | some (.halted (.normal (v, _))) => some v
     | _ => none) ∧
    (match execNProto fCrBody 3 (.running (initMachineStateWithMemoryProto fCrBody [crPtrArg] crMem)) with
     | some (.halted (.normal (v, _))) => some v
     | _ => none) = some (mkSc 42) :=
  ⟨rfl, rfl⟩

/--
Dangling-pointer soundness preserved: `fDangleBody` (`_1 = &raw mut _2; tailCall g_read(_1, 137)`)
still faults with `.faulted .ub` when `g_read` dereferences `_1` after `fDangleBody`'s
frame is popped.
-/
theorem tailCall_repaired_dangling_frame_local_faults_ub :
    execNProto fDangleBody 6
      (.running (initMachineStateWithMemoryProto fDangleBody [] { emptyMemory with callees := [gReadBody] })) =
    some (.faulted .ub) := by
  rfl

end TailCallCallerReferentWitnesses

/-! ## 10. Universal Simulation Theorems for Bug 4 (`opaqueCast_trusted_root_dispatch_simulation`) -/

/--
Helper lemma: `stripTransparentProjections` strips any leading `.opaqueCast ty`
just like `stripLeadingOpaqueCast`.
-/
@[simp]
theorem stripTransparentProjections_opaqueCast
    (ty : Ty) (rest : List ProjectionElem) :
    stripTransparentProjections (.opaqueCast ty :: rest) =
      stripTransparentProjections rest := rfl

/--
Helper lemma: `placeTy` with `localDecls = []` is always `.none`.
-/
@[simp]
theorem placeTy_nil_localDecls (layouts : LayoutTable) (p : Place) :
    placeTy .nil layouts p = .none := by
  simp [placeTy, get?]

/--
**Bug 4 Universal Simulation Theorem (`opaqueCast_trusted_root_dispatch_simulation`)**:
For any local index `l`, cast type `ty`, value `val`, rvalue `rv`, variant index
`variantIdx`, target block `targetBb`, unwind action `unwind`, and machine state `s`
with `localDecls = []`:
1. **Move operand (`evalOperandProto (.move)`)**:
   `evalOperandProto locals (.move ⟨l, [.opaqueCast ty]⟩) ... = evalOperandProto locals (.move ⟨l, []⟩) ...`
   (both return `.ok v locals'` with `locals'[l] = .uninit`).
2. **Root place write (`writePlaceValueProto`)**:
   `writePlaceValueProto locals borrows ⟨l, [.opaqueCast ty]⟩ val = writePlaceValueProto locals borrows ⟨l, []⟩ val`
   (both succeed on `.uninit` and `.init _` locals).
3. **Root assignment (`evalStmtProto (.assign ⟨l, [.opaqueCast ty]⟩ rv)`)**:
   `evalStmtProto s ⟨.assign ⟨l, [.opaqueCast ty]⟩ rv, span⟩ = evalStmtProto s ⟨.assign ⟨l, []⟩ rv, span⟩`.
4. **Field-shell assignment on `.uninit` (`uninitFieldWriteShellProto?`)**:
   `uninitFieldWriteShellProto? localDecls layouts l (.opaqueCast ty) (.field idx fTy :: rest) = uninitFieldWriteShellProto? localDecls layouts l (.field idx fTy) rest`.
5. **Deinit & SetDiscriminant & Drop (`evalStmtProto (.deinit)` / `(.setDiscriminant)` / `evalTerminatorProto (.drop)`)**:
   `⟨l, [.opaqueCast ty]⟩` steps identically to `⟨l, []⟩`.
-/
theorem opaqueCast_trusted_root_dispatch_simulation
    (s : MachineState)
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (localDecls : List LocalDecl)
    (l idx variantIdx targetBb : Nat)
    (ty fTy : Ty)
    (rest : List ProjectionElem)
    (val : Value)
    (rv : Rvalue)
    (unwind : UnwindAction)
    (span : String) :
    (evalOperandProto
        locals (.move ⟨l, [.opaqueCast ty]⟩) borrows globals layouts callerLocals .nil callStack =
      evalOperandProto
        locals (.move ⟨l, []⟩) borrows globals layouts callerLocals .nil callStack) ∧
    (writePlaceValueProto locals borrows ⟨l, [.opaqueCast ty]⟩ val .nil layouts callStack =
      writePlaceValueProto locals borrows ⟨l, []⟩ val .nil layouts callStack) ∧
    (evalStmtProto s ⟨.assign ⟨l, [.opaqueCast ty]⟩ rv, span⟩ .nil layouts =
      evalStmtProto s ⟨.assign ⟨l, []⟩ rv, span⟩ .nil layouts) ∧
    (uninitFieldWriteShellProto? localDecls layouts l (.opaqueCast ty) (.field idx fTy :: rest) =
      uninitFieldWriteShellProto? localDecls layouts l (.field idx fTy) rest) ∧
    (evalStmtProto s ⟨.deinit ⟨l, [.opaqueCast ty]⟩, span⟩ localDecls layouts =
      evalStmtProto s ⟨.deinit ⟨l, []⟩, span⟩ localDecls layouts) ∧
    (evalStmtProto s ⟨.setDiscriminant ⟨l, [.opaqueCast ty]⟩ variantIdx, span⟩ localDecls layouts =
      evalStmtProto s ⟨.setDiscriminant ⟨l, []⟩ variantIdx, span⟩ localDecls layouts) ∧
    (evalTerminatorProto s ⟨.drop ⟨l, [.opaqueCast ty]⟩ targetBb unwind, span⟩ .none =
      evalTerminatorProto s ⟨.drop ⟨l, []⟩ targetBb unwind, span⟩ .none) := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  unfold evalStmtProto
  cases evalRvalueProto s.frame.locals rv s.memory .nil layouts <;> rfl

/--
Ill-formed `.opaqueCast ty :: .deref :: rest` projections continue to evaluate to
`.unsupported` under `evalPlaceReadProto`, `evalOperandProto`, and `writePlaceValueProto`,
preserving `MirUntestedVariantCorrespondenceTests.lean:2829` and `2925`.
-/
theorem opaqueCast_before_deref_stays_unsupported
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (l : Nat)
    (ty : Ty)
    (rest : List ProjectionElem)
    (rootVal writeVal : Value)
    (hSlot : get? locals l = .some (.init rootVal)) :
    evalPlaceReadProto locals ⟨l, .opaqueCast ty :: .deref :: rest⟩ borrows = .unsupported ∧
    evalOperandProto locals (.move ⟨l, .opaqueCast ty :: .deref :: rest⟩) borrows = .unsupported ∧
    writePlaceValueProto locals borrows ⟨l, .opaqueCast ty :: .deref :: rest⟩ writeVal = .unsupported := by
  have hRead :
      readProjectedValue locals rootVal (.opaqueCast ty :: .deref :: rest) = .unsupported := by
    cases rootVal <;> rfl
  have hWrite :
      writeProjectedValue locals rootVal (.opaqueCast ty :: .deref :: rest) writeVal = .unsupported := by
    cases rootVal <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [evalPlaceReadProto, evalPlaceRead, hSlot, readProjectedForLocal, hRead]
  · simp [evalOperandProto, evalOperand, hSlot, hRead]
  · simp [writePlaceValueProto, writePlaceValue, hSlot, writeProjectedForLocal, hWrite]

end Anneal.TcbCopySubplaceAndTailCallPrototype
