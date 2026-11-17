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
mechanizes and kernel-certifies off `unstable` the four TCB ground-semantics
repairs slated for paired Track A workstream
`ws-tcb-copy-subplace-and-tailcall-opaquecast-correspondence`.

**Conservativity discipline.** Every repaired step function below is
`Trusted.Rustc.V2026_06_01.MirSemantics` *plus exactly one repair*: wherever a
repair does not apply, the prototype delegates to the unmodified `Trusted`
function (`evalRvalue`, `evalOperand`, `evalPlaceWrite`, `evalCallerPlaceWrite`,
`evalForeignFrameDerefWrite`, `evalCopySingleDirect`, `evalTerminator`,
`unwindFromCallStack`, `resumeExternalTailCall`, ...), so the prototype keeps
`Trusted`'s Tree Borrows read transitions (`derefReadTreeUB` /
`freezeDerefReadBorrowsAt`), `validateLoadedValue`, and frame-qualified borrow
resolution everywhere (see `conservativity_*` canaries in the test file).

1. **Bug 1 — Multi-Element Subplace `copy_nonoverlapping` (`RawPtrOffsetMutator:wrong_value:MirDiffTag.normalScalar`)**:
   - Peels trailing `.constantIndex` array-element projections into element
     offsets over the enclosing `.aggregate 0` array container
     (`peelArrayElementProjForMultiCopy`, `resolveArraySliceEndpoint?`),
     converts pointer byte offsets to element indices via `resolvePtrElemOffset?`
     (faulting with `.ub` on a byte offset that is not a whole number of
     elements of the statically known pointee, i.e. a misaligned pointer), writes
     the updated array slice back to the peeled parent projection
     `{ local_ := dstEntry.targetLocal, projection := dstParentProj }`, and runs
     the same Tree Borrows read-then-write transition as `Trusted`'s
     single-element path (`borrowsAfterCopySingleDirect`) scoped to the
     accessed `.subslice` windows (`borrowsAfterCopySliceProto`).
   - Closes the `copyViaBytes` silent-truncation hole by requiring
     `length bs == n * elemBytes`.
   - Kernel-certifies (`by rfl`) both Campaign #14
     (`pass_transmute_u32_byte_array_le__b0_c6`: `19 -> 112`) and Campaign #15
     (`pass_enum_discriminant_valid__b2_c9`: `70 -> 4`) against live Miri.

2. **Bug 2 — `DIV-LM-TAILCALL-NOUNWIND-UNWIND` (`Terminators.lean:846`)**:
   - Nested tail call (`callStack = caller :: rest`): rewrites the inherited
     `caller.returnUnwind` to `.unreachable` when the tail callee cannot unwind
     (`narrowCallStackForTailCallee`, Miri `init_fn_call`), monotonically across
     arbitrarily many subsequent tail calls.
   - Modular-root tail call (`callStack = []`): the root activation inherits its
     external caller's unwind continuation, which Miri narrows the same way. The
     prototype tracks this *root unwind ceiling* (Track A field
     `Memory.rootUnwindCeiling : Bool := true`) in the `fnAbi.canUnwind` of the
     active root activation body (a field `Trusted` never reads), so a panic that
     escapes a root tail callee that cannot unwind (or any later tail callee of
     it) faults with `.ub` instead of `.halted .panic`, while the root's *own*
     panics keep the `MODEL-LM-TAILCALL-MODULAR-ROOT` convention
     (`guardRootUnwindCeiling`).

3. **Bug 3 — `DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`**:
   - `Trusted` addresses the modular root's caller-owned referents as depth-`0`
     slots *past* the root frame (`Memory.callerLocals`, `targetLocal ≥ length
     locals`). A root tail call into a wider callee breaks that representation
     invariant. `relocateRootCallerReferents` restores it at the tail call: every
     caller-owned referent borrow and its `callerLocals` slot move past the new
     frame, so *every unmodified* `Trusted` lookup (`activeFrameSlot?`,
     `foreignFrameSlot?`, `foreignFrameTarget?`, `readFrameLocalSlot`,
     `writeFrameLocalSlot`, `disableFrameBorrows`, ...) — and hence every read,
     write, reborrow, `BinOp.offset`, `copy_nonoverlapping`, Tree Borrows
     transition, inline call, and root return built on them — resolves the
     referent in `callerLocals` and never in the callee's own locals.

4. **Bug 4 — `DIV-TR-OPAQUECAST-ROOT-DISPATCH` (`Places.lean`, `Statements.lean`, `Terminators.lean`)**:
   - Strips leading `ProjectionElem.opaqueCast` projections before root-vs-projected
     (`[]` vs `proj :: rest`) dispatch in `evalOperand (.move)` (inside
     `Rvalue.use`), `writePlaceValue`, `uninitFieldWriteShell?`,
     `evalStmt (.assign / .deinit / .setDiscriminant)`, and `TerminatorKind.drop`,
     while preserving fail-closed `.unsupported` on ill-formed
     `.opaqueCast _ :: .deref :: _` paths and type-switched validity checks.
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


/-! ## 2. Bug 3: Root Caller-Owned Referent Relocation (`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`) -/

/--
`Trusted`'s representation invariant for the modular root's caller-owned
referents (`State.lean` `Memory.callerLocals`, `activeFrameSlot?`,
`foreignFrameSlot?`, `foreignFrameTarget?`): a live (`!entry.allocDead`) depth-`0`
borrow whose `targetLocal` is at or past the root frame's local count `nRoot`
names the slot `Memory.callerLocals[targetLocal]`; every other depth-`0` borrow
names a local of the root frame itself (or a deallocated local from an earlier
wider root tail-caller frame).
-/
@[reducible]
def isRootCallerReferentBorrow (nRoot : Nat) (entry : BorrowEntry) : Bool :=
  Bool.and
    (Bool.not entry.allocDead)
    (Bool.and (Nat.beq entry.targetFrameDepth 0) (Nat.ble nRoot entry.targetLocal))

@[simp]
theorem isRootCallerReferentBorrow_dead_false (nRoot : Nat) (entry : BorrowEntry)
    (hDead : entry.allocDead = true) :
    isRootCallerReferentBorrow nRoot entry = false := by
  simp [isRootCallerReferentBorrow, hDead]

/-- Whether some borrow of `borrows` is a root caller-owned referent of a root frame with `nRoot` locals. -/
def anyRootCallerReferentBorrow (nRoot : Nat) : List BorrowEntry → Bool
  | .nil => false
  | entry :: rest =>
    match isRootCallerReferentBorrow nRoot entry with
    | true => true
    | false => anyRootCallerReferentBorrow nRoot rest

/-- Shift `entry.targetLocal` by `delta` iff `entry` is a root caller-owned referent (`nRoot`). -/
@[reducible]
def shiftRootCallerReferentBorrow (nRoot delta : Nat) (entry : BorrowEntry) : BorrowEntry :=
  match isRootCallerReferentBorrow nRoot entry with
  | true => { entry with targetLocal := Nat.add entry.targetLocal delta }
  | false => entry

/-- Shift every root caller-owned referent borrow of `borrows` by `delta` slots. -/
def shiftRootCallerReferentBorrows (nRoot delta : Nat) : List BorrowEntry → List BorrowEntry
  | .nil => .nil
  | entry :: rest =>
    shiftRootCallerReferentBorrow nRoot delta entry ::
      shiftRootCallerReferentBorrows nRoot delta rest

/-- Prepend `k` `.dead` slots to `slots` (never named by any frame-owned borrow). -/
def padDeadSlots : Nat → List LocalSlot → List LocalSlot
  | .zero, slots => slots
  | .succ k, slots => .dead :: padDeadSlots k slots

/--
Repaired root `TerminatorKind.tailCall` memory transition
(`DIV-TR-TAILCALL-ROOT-CALLER-REFERENT-SHADOW`). When the modular root frame of
`nOld` locals is replaced by a tail callee frame of `nNew > nOld` locals while
some borrow names a caller-owned referent, shift every caller-owned referent
borrow (`isRootCallerReferentBorrow nOld`) *and* the `callerLocals` slots by
`nNew - nOld`: each referent again lies past the (wider) root frame, so
`Trusted`'s own frame-qualified lookups keep resolving it in `callerLocals`
(`relocateRootCallerReferents_readFrameLocalSlot`). Borrow tags (the provenance
carried by pointer values), permissions, protectors, and `parentTag` links are
unchanged, so aliasing and Tree Borrows identity are preserved. Otherwise
(`nNew ≤ nOld`, or no caller-owned referent borrow) the memory is unchanged.

In Track A this is the only TCB change needed for Bug 3: one call in
`evalTailCallTerminator` (`Terminators.lean:3307-3378`) when
`s.memory.callStack = []`.
-/
def relocateRootCallerReferents (mem : Memory) (nOld nNew : Nat) : Memory :=
  match Bool.and (Nat.blt nOld nNew) (anyRootCallerReferentBorrow nOld mem.borrows) with
  | false => mem
  | true =>
    { mem with
      borrows := shiftRootCallerReferentBorrows nOld (Nat.sub nNew nOld) mem.borrows
      callerLocals := padDeadSlots (Nat.sub nNew nOld) mem.callerLocals }

/-- The relocation applied to a single borrow by `relocateRootCallerReferents mem nOld nNew`. -/
@[reducible]
def relocatedRootBorrow (mem : Memory) (nOld nNew : Nat) (entry : BorrowEntry) : BorrowEntry :=
  match Bool.and (Nat.blt nOld nNew) (anyRootCallerReferentBorrow nOld mem.borrows) with
  | false => entry
  | true => shiftRootCallerReferentBorrow nOld (Nat.sub nNew nOld) entry

theorem get?_padDeadSlots_add (slots : List LocalSlot) (i : Nat) :
    ∀ k : Nat, get? (padDeadSlots k slots) (Nat.add i k) = get? slots i
  | .zero => rfl
  | .succ k => by
    have ih := get?_padDeadSlots_add slots i k
    simp only [get?] at ih ⊢
    show (LocalSlot.dead :: padDeadSlots k slots)[Nat.add i k + 1]? = slots[i]?
    rw [List.getElem?_cons_succ]
    exact ih

theorem anyRootCallerReferentBorrow_of_mem (nRoot : Nat) (entry : BorrowEntry)
    (hCr : isRootCallerReferentBorrow nRoot entry = true) :
    ∀ borrows : List BorrowEntry, entry ∈ borrows →
      anyRootCallerReferentBorrow nRoot borrows = true
  | .nil, hMem => absurd hMem List.not_mem_nil
  | e :: rest, hMem => by
    unfold anyRootCallerReferentBorrow
    cases hE : isRootCallerReferentBorrow nRoot e with
    | true => rfl
    | false =>
      rcases List.mem_cons.mp hMem with hEq | hRest
      · subst hEq
        rw [hCr] at hE
        exact absurd hE (by decide)
      · exact anyRootCallerReferentBorrow_of_mem nRoot entry hCr rest hRest

theorem mem_shiftRootCallerReferentBorrows (nRoot delta : Nat) (entry : BorrowEntry) :
    ∀ borrows : List BorrowEntry, entry ∈ borrows →
      shiftRootCallerReferentBorrow nRoot delta entry ∈
        shiftRootCallerReferentBorrows nRoot delta borrows
  | .nil, hMem => absurd hMem List.not_mem_nil
  | e :: rest, hMem => by
    unfold shiftRootCallerReferentBorrows
    rcases List.mem_cons.mp hMem with hEq | hRest
    · subst hEq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_shiftRootCallerReferentBorrows nRoot delta entry rest hRest)

/-- Every borrow of the relocated table is the relocation of a borrow of the original table. -/
theorem mem_relocateRootCallerReferents (mem : Memory) (nOld nNew : Nat) (entry : BorrowEntry)
    (hMem : entry ∈ mem.borrows) :
    relocatedRootBorrow mem nOld nNew entry ∈
      (relocateRootCallerReferents mem nOld nNew).borrows := by
  unfold relocatedRootBorrow relocateRootCallerReferents
  cases Bool.and (Nat.blt nOld nNew) (anyRootCallerReferentBorrow nOld mem.borrows) with
  | false => exact hMem
  | true => exact mem_shiftRootCallerReferentBorrows nOld (Nat.sub nNew nOld) entry mem.borrows hMem

/--
**Bug 3 representation-invariant preservation.** Shifting by `nNew - nOld`
(`nOld ≤ nNew`) maps the root caller-owned referents of the old root frame
(`nOld` locals) *exactly* onto the root caller-owned referents of the new root
frame (`nNew` locals): referents stay referents, and frame-owned borrows (of the
torn-down frame, `targetLocal < nOld`, or of other frames) never become
referents.
-/
theorem isRootCallerReferentBorrow_shift (nOld nNew : Nat) (hle : nOld ≤ nNew)
    (entry : BorrowEntry) :
    isRootCallerReferentBorrow nNew
        (shiftRootCallerReferentBorrow nOld (Nat.sub nNew nOld) entry) =
      isRootCallerReferentBorrow nOld entry := by
  unfold shiftRootCallerReferentBorrow
  cases hCr : isRootCallerReferentBorrow nOld entry with
  | true =>
    simp only [isRootCallerReferentBorrow, Bool.and_eq_true, Bool.not_eq_true',
      Nat.beq_eq, Nat.ble_eq] at hCr ⊢
    exact ⟨hCr.1, hCr.2.1, by simp only [Nat.add_eq, Nat.sub_eq]; omega⟩
  | false =>
    simp only [isRootCallerReferentBorrow] at hCr ⊢
    cases hDead : entry.allocDead with
    | true => rfl
    | false =>
      rw [hDead] at hCr
      simp only [Bool.not_false, Bool.true_and] at hCr ⊢
      cases hD : Nat.beq entry.targetFrameDepth 0 with
      | false => rfl
      | true =>
        rw [hD, Bool.true_and] at hCr
        rw [Bool.true_and]
        have hlt : entry.targetLocal < nOld := by
          apply Nat.lt_of_not_le
          intro h
          rw [← Nat.ble_eq] at h
          rw [h] at hCr
          cases hCr
        cases hB : Nat.ble nNew entry.targetLocal with
        | false => rfl
        | true =>
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans hle (Nat.le_of_ble_eq_true hB)))
            (Nat.lt_irrefl _)

/--
**Bug 3 universal non-shadowing theorem (root frame active).** Let `entry` be
any caller-owned referent borrow (`isRootCallerReferentBorrow nOld entry`) of
the pre-tail-call borrow table, and let the root tail call replace the root
frame of `nOld` locals by the callee frame `calleeLocals` (of *any* width).
After `relocateRootCallerReferents`, `Trusted`'s own, unmodified frame-qualified
lookup `readFrameLocalSlot` — on which every `Trusted` dereference read, write,
reborrow, `copy_nonoverlapping`, and `BinOp.offset` bounds computation is built —
resolves the relocated borrow to the original caller-owned slot
`mem.callerLocals[entry.targetLocal]`, never to a local of the callee, and the
relocated borrow is still a caller-owned referent of the new root frame (so the
callee's teardown at its next tail call or return, `disableFrameBorrows … 0
(length calleeLocals)`, keeps it live).
-/
theorem relocateRootCallerReferents_readFrameLocalSlot
    (mem : Memory) (nOld : Nat) (calleeLocals : List LocalSlot) (entry : BorrowEntry)
    (hMem : entry ∈ mem.borrows)
    (hCr : isRootCallerReferentBorrow nOld entry = true) :
    let mem' := relocateRootCallerReferents mem nOld (length calleeLocals)
    let entry' := relocatedRootBorrow mem nOld (length calleeLocals) entry
    entry' ∈ mem'.borrows ∧
    isRootCallerReferentBorrow (length calleeLocals) entry' = true ∧
    readFrameLocalSlot calleeLocals .nil mem'.callerLocals
        entry'.targetFrameDepth entry'.targetLocal =
      get? mem.callerLocals entry.targetLocal := by
  intro mem' entry'
  have hAny := anyRootCallerReferentBorrow_of_mem nOld entry hCr mem.borrows hMem
  have hCr' := hCr
  simp only [isRootCallerReferentBorrow, Bool.and_eq_true, Bool.not_eq_true',
    Nat.beq_eq, Nat.ble_eq] at hCr'
  refine ⟨mem_relocateRootCallerReferents mem nOld (length calleeLocals) entry hMem, ?_, ?_⟩
  · show isRootCallerReferentBorrow (length calleeLocals)
      (relocatedRootBorrow mem nOld (length calleeLocals) entry) = true
    unfold relocatedRootBorrow
    rw [hAny, Bool.and_true]
    cases hW : Nat.blt nOld (length calleeLocals) with
    | true =>
      have hle : nOld ≤ length calleeLocals := by
        have := Nat.blt_eq.mp hW
        omega
      rw [isRootCallerReferentBorrow_shift nOld (length calleeLocals) hle entry]
      exact hCr
    | false =>
      have hge : length calleeLocals ≤ nOld := by
        apply Nat.le_of_not_lt
        intro h
        rw [← Nat.blt_eq] at h
        rw [h] at hW
        cases hW
      simp only [isRootCallerReferentBorrow, Bool.and_eq_true, Bool.not_eq_true',
        Nat.beq_eq, Nat.ble_eq]
      exact ⟨hCr'.1, hCr'.2.1, by omega⟩
  · show readFrameLocalSlot calleeLocals .nil
        (relocateRootCallerReferents mem nOld (length calleeLocals)).callerLocals
        (relocatedRootBorrow mem nOld (length calleeLocals) entry).targetFrameDepth
        (relocatedRootBorrow mem nOld (length calleeLocals) entry).targetLocal =
      get? mem.callerLocals entry.targetLocal
    unfold relocatedRootBorrow relocateRootCallerReferents
    rw [hAny, Bool.and_true]
    cases hW : Nat.blt nOld (length calleeLocals) with
    | true =>
      simp only [shiftRootCallerReferentBorrow, hCr]
      have hOob : get? calleeLocals (Nat.add entry.targetLocal (Nat.sub (length calleeLocals) nOld)) =
          .none := by
        simp only [get?, length] at hW ⊢
        apply List.getElem?_eq_none
        have := Nat.blt_eq.mp hW
        simp only [Nat.add_eq, Nat.sub_eq]
        omega
      simp only [readFrameLocalSlot, activeFrameSlot?, foreignFrameSlot?, hOob]
      exact get?_padDeadSlots_add mem.callerLocals entry.targetLocal _
    | false =>
      have hge : length calleeLocals ≤ nOld := by
        apply Nat.le_of_not_lt
        intro h
        rw [← Nat.blt_eq] at h
        rw [h] at hW
        cases hW
      have hOob : get? calleeLocals entry.targetLocal = .none := by
        simp only [get?]
        apply List.getElem?_eq_none
        exact Nat.le_trans hge hCr'.2.2
      simp only [readFrameLocalSlot, activeFrameSlot?, foreignFrameSlot?, hOob]

/--
**Bug 3 universal non-shadowing theorem (root frame suspended).** The same
resolution holds after the relocated root activation makes inline calls: with
the root frame saved at the bottom of the call stack (`rest ++ [rootSaved]`, any
`activeLocals` for the callee frame on top), `Trusted`'s `readFrameLocalSlot`
resolves the relocated caller-owned referent borrow through the depth-`0`
`foreignFrameSlot?` fallback to `callerLocals[entry.targetLocal]`.
-/
theorem relocateRootCallerReferents_readFrameLocalSlot_suspended
    (mem : Memory) (nOld : Nat) (rootSaved : SavedCallerFrame) (rest : List SavedCallerFrame)
    (activeLocals : List LocalSlot) (entry : BorrowEntry)
    (hCr : isRootCallerReferentBorrow nOld entry = true)
    (hWider : Nat.blt nOld (length rootSaved.frame.locals) = true)
    (hAny : anyRootCallerReferentBorrow nOld mem.borrows = true) :
    let n := length rootSaved.frame.locals
    let mem' := relocateRootCallerReferents mem nOld n
    let entry' := relocatedRootBorrow mem nOld n entry
    readFrameLocalSlot activeLocals (rest ++ [rootSaved]) mem'.callerLocals
        entry'.targetFrameDepth entry'.targetLocal =
      get? mem.callerLocals entry.targetLocal := by
  intro n mem' entry'
  have hCr' := hCr
  simp only [isRootCallerReferentBorrow, Bool.and_eq_true, Bool.not_eq_true',
    Nat.beq_eq, Nat.ble_eq] at hCr'
  show readFrameLocalSlot activeLocals (rest ++ [rootSaved])
      (relocateRootCallerReferents mem nOld n).callerLocals
      (relocatedRootBorrow mem nOld n entry).targetFrameDepth
      (relocatedRootBorrow mem nOld n entry).targetLocal =
    get? mem.callerLocals entry.targetLocal
  unfold relocatedRootBorrow relocateRootCallerReferents
  simp only [n] at hWider ⊢
  rw [hWider, hAny, Bool.and_self]
  simp only [shiftRootCallerReferentBorrow, hCr, hCr'.2.1]
  have hLen : length (rest ++ [rootSaved]) = Nat.succ (length rest) := by
    simp [length]
  have hNotActive : Nat.beq 0 (length (rest ++ [rootSaved])) = false := by
    rw [hLen]
    rfl
  have hSaved : savedFrameAtDepth? (rest ++ [rootSaved]) 0 = .some rootSaved := by
    unfold savedFrameAtDepth?
    rw [hLen]
    simp only [frameIndexOfDepth, get?]
    show (match Nat.blt 0 (Nat.succ (length rest)) with
      | true => (rest ++ [rootSaved])[length rest]?
      | false => none) = some rootSaved
    have hBlt : Nat.blt 0 (Nat.succ (length rest)) = true := Nat.blt_eq.mpr (Nat.succ_pos _)
    rw [hBlt]
    simp [length]
  have hOob : get? rootSaved.frame.locals
      (Nat.add entry.targetLocal (Nat.sub (length rootSaved.frame.locals) nOld)) = .none := by
    simp only [get?, length] at hWider ⊢
    apply List.getElem?_eq_none
    have := Nat.blt_eq.mp hWider
    simp only [Nat.add_eq, Nat.sub_eq]
    omega
  cases hRest : rest ++ [rootSaved] with
  | nil => simp at hRest
  | cons hd tl =>
    rw [hRest] at hNotActive hSaved
    simp only [readFrameLocalSlot, activeFrameSlot?, hNotActive, foreignFrameSlot?, hSaved, hOob]
    exact get?_padDeadSlots_add mem.callerLocals entry.targetLocal _

/-- No relocation happens when the tail callee is not wider than the tail caller. -/
theorem relocateRootCallerReferents_not_wider (mem : Memory) (nOld nNew : Nat)
    (hNarrow : Nat.blt nOld nNew = false) :
    relocateRootCallerReferents mem nOld nNew = mem := by
  unfold relocateRootCallerReferents
  rw [hNarrow, Bool.false_and]

/-- No relocation happens when no borrow names a caller-owned referent (e.g. no pointer arguments). -/
theorem relocateRootCallerReferents_no_referents (mem : Memory) (nOld nNew : Nat)
    (hNone : anyRootCallerReferentBorrow nOld mem.borrows = false) :
    relocateRootCallerReferents mem nOld nNew = mem := by
  unfold relocateRootCallerReferents
  rw [hNone, Bool.and_false]

/--
Frame-owned borrows (of the torn-down tail-caller frame or any other frame) are
never moved, so `disableFrameBorrows`' dangling-pointer verdicts are untouched
(`fDangle` still faults with `.ub`).
-/
theorem shiftRootCallerReferentBorrow_frameOwned (nRoot delta : Nat) (entry : BorrowEntry)
    (hOwned : isRootCallerReferentBorrow nRoot entry = false) :
    shiftRootCallerReferentBorrow nRoot delta entry = entry := by
  unfold shiftRootCallerReferentBorrow
  rw [hOwned]

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
            let peeled :=
              match fromEnd with
              | false => peelArrayElementProjForMultiCopy normProj ptrElemOffset (.succ (.succ n))
              | true => (parentProj, Nat.add ptrElemOffset baseIdx)
            .some (peeled.1, peeled.2, outerElems)
          | .none => .none
      | _ => .none
    | .none =>
      match readProjectedValue locals₃ rootVal normProj with
      | .ok (.aggregate 0 elems) => .some (normProj, ptrElemOffset, elems)
      | _ => .none

/--
Tree Borrows read-then-write check and permission transition for a
multi-element `copy_nonoverlapping` slice copy. This is exactly
`Trusted.borrowsAfterCopySingleDirect` (`Statements.lean:1720-1864`, the
transition `Trusted` already runs for single-element copies) evaluated at the
accessed windows `srcEffProj` / `dstEffProj`
(`parentProj ++ [.subslice start (start + n) false]`) with *unranged* accesses
(`rangeOffset = rangeLen = 0`): a borrow's own byte range (`entry.rangeLen`,
typically one element) would under-approximate an `n`-element access, so the
accessed window is described by the `.subslice` projection alone and
`borrowEntryOverlapsWrite` / `projectionsOverlap` compare projections.

1. `hasTreeReadUB` on the source window (read through `srcPtr.tag`),
2. the source read transition (`freezeTreeBorrowsOnReadAtProj` /
   `updateBorrowPermOnReadAtProj`: foreign `.unique` borrows of the source
   window become `.frozen`),
3. destination write UB (`.frozen` / `.disabled` destination tag after the read,
   or an ancestor child-write UB),
4. active function-entry protector conflicts on the destination window,
5. the destination write transition (`invalidateTreeBorrowsAtProj` /
   `invalidateConflictingBorrowsAtProj` / `invalidateConflictingBorrows`), which
   disables exactly the foreign borrows overlapping the written window.
-/
def borrowsAfterCopySliceProto
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
        0
        0
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
          0
          0
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
          0
          0
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
              0
              0
              dstEntry.targetFrameDepth
          | _ =>
            hasProtectedWriteConflict
              borrowsAfterRead
              activeProtectors
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEffProj
              0
              0
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
              invalidateConflictingBorrows
                b
                dstEntry.targetLocal
                (.some dstPtr.tag)
                dstEntry.targetFrameDepth
            | pHead :: pTail =>
              invalidateConflictingBorrowsAtProj
                b
                dstEntry.targetLocal
                (.some dstPtr.tag)
                (pHead :: pTail)
                0
                0
                dstEntry.targetFrameDepth
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            invalidateTreeBorrowsAtProj
              allBorrows
              allBorrows
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEffProj
              0
              0
              dstEntry.targetFrameDepth
        .some borrows'

/--
Write `newVal` to `dstPlace` in the frame owning it — the active frame
(`writePlaceValue`), or a modular root's caller-owned referent slot past the
active frame (`Memory.callerLocals`) — committing the already-transitioned
borrow table `borrows'`. This is exactly the write path of
`Trusted.commitCopyDstPlaceWrite` (`Statements.lean:834-916`), with the borrow
update supplied by the caller.
-/
def writeCopyDstPlaceProto
    (s : MachineState)
    (dstPlace : Place)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (borrows' : List BorrowEntry)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match writePlaceValue locals₃ s.memory.borrows dstPlace newVal localDecls layouts with
  | .ok locals₄ =>
    MirStepNode.step (advanceStmt s locals₄ { s.memory with borrows := borrows' })
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
        MirStepNode.step
          (advanceStmt s locals₃
            { s.memory with borrows := borrows', callerLocals := callerLocals' })

/--
Destination commit for the byte-level `copyViaBytes` fallback of
`evalCopyNonOverlappingPermOkProto`: checks active function-entry protectors and
applies the foreign-write transition scoped to `dstPlace.projection` (unranged),
then writes through `writeCopyDstPlaceProto`. (`Trusted.commitCopyDstPlaceWrite`
invalidates the whole local and skips protector checks.)
-/
def commitCopyDstPlaceWriteProto
    (s : MachineState)
    (dstPlace : Place)
    (dstEntry : BorrowEntry)
    (dstTag : Nat)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  let protConflict : Bool :=
    match s.memory.activeProtectors with
    | .nil => false
    | _ :: _ =>
      hasProtectedWriteConflict
        s.memory.borrows
        s.memory.activeProtectors
        dstEntry.targetLocal
        (.some dstTag)
        dstPlace.projection
        0
        0
        dstEntry.targetFrameDepth
  match protConflict with
  | true => MirStepNode.fail .ub
  | false =>
    let borrows' : List BorrowEntry :=
      match dstPlace.projection with
      | .nil =>
        invalidateConflictingBorrows
          s.memory.borrows
          dstEntry.targetLocal
          (.some dstTag)
          dstEntry.targetFrameDepth
      | pHead :: pTail =>
        invalidateConflictingBorrowsAtProj
          s.memory.borrows
          dstEntry.targetLocal
          (.some dstTag)
          (pHead :: pTail)
          0
          0
          dstEntry.targetFrameDepth
    writeCopyDstPlaceProto s dstPlace locals₃ newVal borrows' localDecls layouts

/--
Root slot of a `copy_nonoverlapping` endpoint borrow `entry`: the active
frame's slot, else the modular root's caller-owned referent slot (exactly the
`srcRootSlot` / `dstRootSlot` lookup of `Trusted.evalCopyNonOverlappingPermOk`).
-/
@[reducible]
def resolveCopyEndpointRootSlot
    (s : MachineState)
    (locals₃ : List LocalSlot)
    (entry : BorrowEntry) :
    Option LocalSlot :=
  match get? locals₃ entry.targetLocal with
  | .some slot => .some slot
  | .none =>
    match get? s.memory.callerLocals entry.targetLocal with
    | .some slot => .some slot
    | .none =>
      get? s.memory.callerLocals (Nat.sub entry.targetLocal (length locals₃))

/--
Effective Tree Borrows access window of `n` elements starting at `start` in the
array container `parentProj` holding `len` elements (`.nil` when the window is the
whole top-level array).
-/
@[reducible]
def copySliceWindowProj
    (parentProj : List ProjectionElem)
    (start n len : Nat) :
    List ProjectionElem :=
  match parentProj, Bool.and (Nat.beq start 0) (Nat.beq n len) with
  | .nil, true => .nil
  | _, _ =>
    normalizeSubsliceProjections
      (appendProjections parentProj (.subslice start (Nat.add start n) false :: .nil))

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
Repaired `evalCopyNonOverlappingPermOk` (`Statements.lean:1414-1687`):
1. Zero-count copies, union endpoints (`Trusted.evalCopyUnionBytes`), and
   single-element zero-offset copies (`Trusted.evalCopySingleDirect`) are
   exactly `Trusted`'s.
2. Converts both pointer byte offsets into element offsets of the statically
   known pointee (`resolvePtrElemOffset?`); a byte offset that is not a whole
   number of elements (a misaligned element pointer) faults with `.ub` instead of
   being reinterpreted as an element index (`Trusted` uses raw
   `ProvenancePtr.offsetBytes` as an element index).
3. Peels trailing `.constantIndex` projections of both endpoints via
   `resolveArraySliceEndpoint?`, so `copy_nonoverlapping(&raw const a[i], &raw mut b[j], n)`
   reads and writes `n` elements of the enclosing `.aggregate 0` arrays and writes
   back to `{ local_ := dstEntry.targetLocal, projection := dstParentProj }`.
4. Checks bounds (`srcStart + n ≤ length srcElems`, `dstStart + n ≤ length dstElems`)
   and non-overlap (`sameContainer → srcStart + n ≤ dstStart ∨ dstStart + n ≤ srcStart`),
   allowing disjoint slices of one array while faulting with `.ub` on
   overlapping slices or out-of-bounds counts.
5. Runs the Tree Borrows read-then-write transition of `Trusted`'s
   single-element path on the accessed `.subslice` windows
   (`borrowsAfterCopySliceProto`).
6. Requires `length bs == n * elemBytes` in the byte-level fallback, so `n > 1`
   on a scalar allocation faults with `.ub` instead of copying one element.
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
        evalCopySingleDirect
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
          match
            resolvePtrElemOffset? srcStartRaw effSrcPtOpt layouts,
            resolvePtrElemOffset? dstStartRaw effDstPtOpt layouts
          with
          | .some srcElemOff, .some dstElemOff =>
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
              match get? locals₃ dstRawPlace.local_ with
              | .some _ => placeTy localDecls layouts dstRawPlace
              | .none => .none
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
                    let byteCountStatus : Option Bool :=
                      match expectedMultiCopyBytes? localDecls layouts src dst srcSubVal n with
                      | .some expBytes =>
                        match Nat.beq (length bs) expBytes with
                        | true => .some true
                        | false =>
                          let isCrossFieldWithinRoot : Bool :=
                            match
                              srcEntry.targetProjection,
                              encodeUntypedValueToBytes defaultCodecFuel srcRootVal
                            with
                            | .field _ _ :: _, .some rootBs => Nat.ble expBytes (length rootBs)
                            | _, _ => false
                          match isCrossFieldWithinRoot with
                          | true => .none
                          | false => .some false
                      | .none => .some true
                    match byteCountStatus with
                    | .none => MirStepNode.unsupported
                    | .some false => MirStepNode.fail .ub
                    | .some true =>
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
                match get? locals₃ dstParentPlace.local_ with
                | .some _ => placeTy localDecls layouts dstParentPlace
                | .none => .none
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
                  match
                    borrowsAfterCopySliceProto
                      s.memory.borrows
                      s.memory.activeProtectors
                      srcPtr
                      dstPtr
                      srcEntry
                      dstEntry
                      (copySliceWindowProj srcParentProj srcStart n (length srcElems))
                      (copySliceWindowProj dstParentProj dstStart n (length dstElems))
                  with
                  | .none => MirStepNode.fail .ub
                  | .some borrows' =>
                    writeCopyDstPlaceProto
                      s
                      dstParentPlace
                      locals₃
                      (.aggregate 0 dstElems')
                      borrows'
                      localDecls
                      layouts
            | .some (_, srcStart, srcElems), .none =>
              match readProjectedValue locals₃ dstRootVal dstEntry.targetProjection with
              | .ok dstSubVal =>
                copyViaBytes
                  (.aggregate 0 srcElems)
                  dstSubVal
                  srcStart
                  dstElemOff
                  dstRawPlace
                  dstLocalPlaceTy
                  dstIsAdt
              | .ub =>
                match Nat.beq dstElemOff 0 with
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
                match get? locals₃ dstParentPlace.local_ with
                | .some _ => placeTy localDecls layouts dstParentPlace
                | .none => .none
              let dstParentIsAdt : Bool :=
                match dstParentTy with
                | .some { kind := .adt _ _, .. } => true
                | _ => false
              match readProjectedValue locals₃ srcRootVal srcEntry.targetProjection with
              | .ok srcSubVal =>
                copyViaBytes
                  srcSubVal
                  (.aggregate 0 dstElems)
                  srcElemOff
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
                  srcElemOff
                  dstElemOff
                  dstRawPlace
                  dstLocalPlaceTy
                  dstIsAdt
              | .ok srcSubVal, .ub =>
                match Nat.beq dstElemOff 0 with
                | true =>
                  copyViaBytes
                    srcSubVal
                    .unit
                    srcElemOff
                    0
                    dstRawPlace
                    dstLocalPlaceTy
                    dstIsAdt
                | false => MirStepNode.fail .ub
              | _, _ => MirStepNode.fail .ub
          | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub

/--
Repaired `evalCopyNonOverlappingWithCount` (`Statements.lean:2036-2088`)
delegating active-frame copies to `evalCopyNonOverlappingPermOkProto` (foreign
frame copies stay `Trusted.evalForeignFrameCopySingleDirect`, which fails closed
with `.unsupported` on multi-element counts).
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
          match copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry with
          | false =>
            evalForeignFrameCopySingleDirect
              s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
          | true =>
            evalCopyNonOverlappingPermOkProto
              s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
      | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub

/-! ## 4. Bug 4: Repaired Place Read, Operand, Rvalue, Place Write, and Statement Evaluation -/

/--
Leading `.opaqueCast` prefix of a projection path (the complement of
`stripLeadingOpaqueCast`).
-/
@[reducible]
def takeLeadingOpaqueCast : List ProjectionElem → List ProjectionElem
  | .opaqueCast t :: rest => .opaqueCast t :: takeLeadingOpaqueCast rest
  | _ => .nil

/--
Repaired `uninitFieldWriteShell?` (`Statements.lean:2852-2873`): strips leading
`.opaqueCast` projections before matching `.field fieldIdx fieldTy :: rest'`, and
builds the field shell for the type *after* the casts
(`placeTy localDecls layouts ⟨loc, takeLeadingOpaqueCast (proj :: rest)⟩`), so
`(_l as T).f = rv` on a live `.uninit` local of opaque type materializes the
same `T` shell as its post-borrowck erasure `_l.f = rv` with `_l : T`. Without a
leading cast this is exactly `Trusted.uninitFieldWriteShell?`.
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
    match
      placeTy localDecls layouts
        { local_ := loc, projection := takeLeadingOpaqueCast (proj :: rest) }
    with
    | .some { kind := .adt _ _, .. } =>
      .some (ensureNestedFieldShells (.aggregate 0 .nil) (.field fieldIdx fieldTy :: rest'))
    | .some { kind := .tuple _, .. } =>
      .some (ensureNestedFieldShells (.aggregate 0 .nil) (.field fieldIdx fieldTy :: rest'))
    | _ => .none
  | _ => .none

/--
`localDecls` with local `loc` retyped to the type reached after the leading
`.opaqueCast` chain of `proj` — the declared type of `loc` in the post-borrowck
erasure (`_l : T` for `(_l as T)`). Without a leading cast (or an undeclared
`loc`) this is `localDecls` unchanged. Used for the type-directed projected
write of `(_l as T).f = rv` (`writeProjectedForLocal`,
`resolveBorrowWriteLocalProj`), which `Trusted` keys on the declared type.
-/
def eraseLeadingOpaqueCastDecls
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : List ProjectionElem) :
    List LocalDecl :=
  match takeLeadingOpaqueCast proj with
  | .nil => localDecls
  | ph :: pt =>
    match
      get? localDecls loc,
      placeTy localDecls layouts { local_ := loc, projection := ph :: pt }
    with
    | .some decl, .some castTy => localDecls.set loc { decl with ty := castTy }
    | _, _ => localDecls

theorem eraseLeadingOpaqueCastDecls_no_cast
    (localDecls : List LocalDecl) (layouts : LayoutTable) (loc : Local)
    (proj : List ProjectionElem) (hNo : takeLeadingOpaqueCast proj = .nil) :
    eraseLeadingOpaqueCastDecls localDecls layouts loc proj = localDecls := by
  unfold eraseLeadingOpaqueCastDecls
  rw [hNo]

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

/--
Repaired `evalPlaceRead`: a pure `.opaqueCast` chain on a local
(`p.projection ≠ []`, `stripLeadingOpaqueCast p.projection = []`) reads the root
local exactly like `⟨l, []⟩`, validating against the cast type
`placeTy localDecls layouts p`; every other place is `Trusted.evalPlaceRead`.
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
  match p.projection with
  | .nil => evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack
  | .deref :: _ => evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack
  | _ :: _ =>
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
    | _ :: _ => evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack

/--
Repaired `evalOperand`: `Operand.move p` with a pure `.opaqueCast` chain
(`p.projection ≠ []`, `stripLeadingOpaqueCast p.projection = []`) moves the root
local exactly like `move ⟨l, []⟩` (de-initializing `_l`), validating against the
cast type when `localDecls` is non-empty; every other operand is
`Trusted.evalOperand` (in particular an ordinary `move ⟨l, []⟩` is *not*
re-validated, exactly as in `Trusted`).
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
  | .move p =>
    match p.projection with
    | .nil => evalOperand locals op borrows globals layouts callerLocals localDecls callStack
    | .deref :: _ => evalOperand locals op borrows globals layouts callerLocals localDecls callStack
    | _ :: _ =>
      match stripLeadingOpaqueCast p.projection with
      | .nil =>
        let tyValid :=
          match localDecls with
          | .nil => true
          | _ :: _ =>
            match get? locals p.local_ with
            | .some (.init v) => validateValueForTy? layouts (placeTy localDecls layouts p) v
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
      | _ :: _ => evalOperand locals op borrows globals layouts callerLocals localDecls callStack
  | _ => evalOperand locals op borrows globals layouts callerLocals localDecls callStack

/-- Evaluate a list of `Operand`s left-to-right using `evalOperandProto` (cf. `Trusted.evalOperands`). -/
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
Repaired `evalCopyNonOverlapping` (`Statements.lean:2102`) delegating operand
evaluation to `evalOperandProto` and copy execution to
`evalCopyNonOverlappingWithCountProto`.
-/
def evalCopyNonOverlappingProto
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperandProto
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
      evalOperandProto
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
        evalOperandProto
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

/--
Repaired `writePlaceValue`: a pure `.opaqueCast` chain on a local initializes
the root local exactly like `⟨l, []⟩` (validating `val` against the cast type
`placeTy localDecls layouts dst` when `localDecls` is non-empty); every other
place (including `.opaqueCast _ :: .deref :: _`, which stays `.unsupported`) is
`Trusted.writePlaceValue`.
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
  match dst.projection with
  | .nil => writePlaceValue locals borrows dst val localDecls layouts callStack
  | .deref :: _ => writePlaceValue locals borrows dst val localDecls layouts callStack
  | _ :: _ =>
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
    | _ :: _ => writePlaceValue locals borrows dst val localDecls layouts callStack

/-- True iff `p` is a non-empty pure `.opaqueCast` projection chain (`_l as T...`). -/
@[reducible]
def isPureOpaqueCastPlace (p : Place) : Bool :=
  match p.projection with
  | .nil => false
  | .deref :: _ => false
  | _ :: _ =>
    match stripLeadingOpaqueCast p.projection with
    | .nil => true
    | _ :: _ => false

/-- Erase a pure `.opaqueCast` chain on `p` to `⟨p.local_, []⟩`; leave all other places unchanged. -/
@[reducible]
def erasePureOpaqueCastPlace (p : Place) : Place :=
  match isPureOpaqueCastPlace p with
  | true => { local_ := p.local_, projection := .nil }
  | false => p

/-- True iff `op` is `Operand.move p` with a pure `.opaqueCast` projection chain. -/
@[reducible]
def isPureOpaqueCastMoveOp : Operand → Bool
  | .move p => isPureOpaqueCastPlace p
  | _ => false

/-- True iff some operand in `ops` is `Operand.move p` with a pure `.opaqueCast` projection chain. -/
def anyPureOpaqueCastMoveOp : List Operand → Bool
  | .nil => false
  | op :: rest =>
    match isPureOpaqueCastMoveOp op with
    | true => true
    | false => anyPureOpaqueCastMoveOp rest

/-- Validate `Operand.move p` against `placeTy localDecls layouts p` when `isPureOpaqueCastPlace p = true` and `localDecls ≠ []`. -/
@[reducible]
def validatePureOpaqueCastMoveOp
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Operand → Bool
  | .move p =>
    match isPureOpaqueCastPlace p with
    | false => true
    | true =>
      match localDecls with
      | .nil => true
      | _ :: _ =>
        match get? locals p.local_ with
        | .some (.init v) => validateValueForTy? layouts (placeTy localDecls layouts p) v
        | _ => true
  | _ => true

/-- Validate all pure-`.opaqueCast` `Operand.move` operands in `ops`. -/
def validatePureOpaqueCastMoveOps
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    List Operand → Bool
  | .nil => true
  | op :: rest =>
    Bool.and
      (validatePureOpaqueCastMoveOp locals localDecls layouts op)
      (validatePureOpaqueCastMoveOps locals localDecls layouts rest)

/-- Erase a pure `.opaqueCast` chain on `Operand.move p` to `Operand.move ⟨p.local_, []⟩`. -/
@[reducible]
def erasePureOpaqueCastMoveOp : Operand → Operand
  | .move p => .move (erasePureOpaqueCastPlace p)
  | op => op

/-- Erase pure `.opaqueCast` chains on `Operand.move` operands in `ops`. -/
def erasePureOpaqueCastMoveOps : List Operand → List Operand
  | .nil => .nil
  | op :: rest => erasePureOpaqueCastMoveOp op :: erasePureOpaqueCastMoveOps rest

/-- Update `localDecls` with erased types for any pure-`.opaqueCast` `Operand.move` operand. -/
@[reducible]
def erasePureOpaqueCastMoveDeclsOp
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Operand → List LocalDecl
  | .move p =>
    match isPureOpaqueCastPlace p with
    | true => eraseLeadingOpaqueCastDecls localDecls layouts p.local_ p.projection
    | false => localDecls
  | _ => localDecls

/-- Update `localDecls` with erased types for all pure-`.opaqueCast` `Operand.move` operands in `ops`. -/
def erasePureOpaqueCastMoveDeclsOps
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    List Operand → List LocalDecl
  | .nil => localDecls
  | op :: rest =>
    erasePureOpaqueCastMoveDeclsOps
      (erasePureOpaqueCastMoveDeclsOp localDecls layouts op)
      layouts
      rest

/--
Repaired `evalRvalue`:
- `Rvalue.use (Operand.move p)` with a pure `.opaqueCast` chain moves the root
  local (`evalOperandProto`) and applies `Trusted`'s `validateLoadedValue` check.
- Any other `Rvalue` containing an `Operand.move p` with a pure `.opaqueCast`
  chain validates `p` against its cast type, erases `p` to `⟨p.local_, []⟩` (with
  `localDecls` updated via `eraseLeadingOpaqueCastDecls`), and delegates to
  `Trusted.evalRvalue` so `p.local_` is de-initialized and all `Trusted` checks
  are preserved.
- Every rvalue without a pure-`.opaqueCast` `Operand.move` reduces in one step
  to `Trusted.evalRvalue`.
-/
def evalRvalueProto
    (locals : List LocalSlot)
    (rv : Rvalue)
    (mem : Memory := emptyMemory)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  match rv with
  | .use (.move p) =>
    match p.projection with
    | .nil => evalRvalue locals rv mem localDecls layouts
    | .deref :: _ => evalRvalue locals rv mem localDecls layouts
    | _ :: _ =>
      match stripLeadingOpaqueCast p.projection with
      | .nil =>
        match
          evalOperandProto
            locals (.move p) mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack
        with
        | .ok v locals' =>
          match validateLoadedValue layouts localDecls (.move p) v with
          | false => .ub
          | true => .ok v locals' mem
        | .ub => .ub
        | .unsupported => .unsupported
      | _ :: _ => evalRvalue locals rv mem localDecls layouts
  | .wrapUnsafeBinder op bTy =>
    match isPureOpaqueCastMoveOp op with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOp locals localDecls layouts op with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.wrapUnsafeBinder (erasePureOpaqueCastMoveOp op) bTy)
          mem
          (erasePureOpaqueCastMoveDeclsOp localDecls layouts op)
          layouts
  | .binaryOp op lhsOp rhsOp =>
    match Bool.or (isPureOpaqueCastMoveOp lhsOp) (isPureOpaqueCastMoveOp rhsOp) with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOps locals localDecls layouts [lhsOp, rhsOp] with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.binaryOp op (erasePureOpaqueCastMoveOp lhsOp) (erasePureOpaqueCastMoveOp rhsOp))
          mem
          (erasePureOpaqueCastMoveDeclsOps localDecls layouts [lhsOp, rhsOp])
          layouts
  | .unaryOp uop op =>
    match isPureOpaqueCastMoveOp op with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOp locals localDecls layouts op with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.unaryOp uop (erasePureOpaqueCastMoveOp op))
          mem
          (erasePureOpaqueCastMoveDeclsOp localDecls layouts op)
          layouts
  | .cast kind op targetTy =>
    match isPureOpaqueCastMoveOp op with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOp locals localDecls layouts op with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.cast kind (erasePureOpaqueCastMoveOp op) targetTy)
          mem
          (erasePureOpaqueCastMoveDeclsOp localDecls layouts op)
          layouts
  | .repeat op count =>
    match isPureOpaqueCastMoveOp op with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOp locals localDecls layouts op with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.repeat (erasePureOpaqueCastMoveOp op) count)
          mem
          (erasePureOpaqueCastMoveDeclsOp localDecls layouts op)
          layouts
  | .aggregate kind ops =>
    match anyPureOpaqueCastMoveOp ops with
    | false => evalRvalue locals rv mem localDecls layouts
    | true =>
      match validatePureOpaqueCastMoveOps locals localDecls layouts ops with
      | false => .ub
      | true =>
        evalRvalue
          locals
          (.aggregate kind (erasePureOpaqueCastMoveOps ops))
          mem
          (erasePureOpaqueCastMoveDeclsOps localDecls layouts ops)
          layouts
  | _ => evalRvalue locals rv mem localDecls layouts

/--
Repaired `evalStmt` (`Statements.lean:3906-4570`), equal to `Trusted.evalStmt`
except for:
- Bug 1: `evalCopyNonOverlappingProto` on `StatementKind.intrinsic (.copyNonOverlapping ...)`,
- Bug 4: `stripLeadingOpaqueCast` before root-vs-projected dispatch in
  `StatementKind.assign`, `StatementKind.deinit`, and
  `StatementKind.setDiscriminant`, `uninitFieldWriteShellProto?` for
  `(_l as T).f = rv` on `.uninit` locals, the erased declaration
  `eraseLeadingOpaqueCastDecls` for the type-directed projected write of
  `(_l as T).f = rv`, and `evalRvalueProto` for `Rvalue.use (move (_l as T))`.
The `.deref :: _` destination branch of `.assign` is `Trusted`'s verbatim
(`evalPlaceWrite`, then `evalCallerPlaceWrite` at a modular root or
`evalForeignFrameDerefWrite` in a callee).
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
          evalPlaceWrite
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
          match mem₁.callStack with
          | .nil =>
            match mem₁.callerLocals with
            | .nil => MirStepNode.fail .ub
            | _ :: _ =>
              match
                evalCallerPlaceWrite
                  locals₁
                  mem₁.callerLocals
                  mem₁.borrows
                  dst
                  val
                  mem₁.activeProtectors
              with
              | .ok callerLocals' =>
                match derefWriteTreeUB locals₁ mem₁.borrows dst with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateDerefWriteBorrows
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callerLocals
                  MirStepNode.step
                    (advanceStmt
                      s
                      locals₁
                      { mem₁ with
                        borrows := borrows'
                        callerLocals := callerLocals' })
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
          | _ :: _ =>
            evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
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
        | _ :: _ =>
          let writeDecls := eraseLeadingOpaqueCastDecls localDecls layouts dst.local_ dst.projection
          let rootOpt : Option Value :=
            match get? locals₁ dst.local_ with
            | .some (.init rootVal) => .some (ensureNestedFieldShells rootVal dst.projection)
            | .some .uninit =>
              match dst.projection with
              | p0 :: ps => uninitFieldWriteShellProto? localDecls layouts dst.local_ p0 ps
              | .nil => .none
            | _ => .none
          match rootOpt with
          | .none => MirStepNode.fail .ub
          | .some rootVal =>
            match
              writeProjectedForLocal
                locals₁
                writeDecls
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
                    writeDecls
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
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | _ => evalStmt s stmt localDecls layouts

/-! ## 5. Bug 2 & Bug 3: Repaired `TerminatorKind.tailCall` (`narrowCallStackForTailCallee`, root unwind ceiling, `relocateRootCallerReferents`) -/

/--
Narrow the inherited caller frame's `returnUnwind` on `callStack` to
`.unreachable` when a `TerminatorKind.tailCall` enters a callee that cannot
unwind (`canUnwind = false`), matching Miri's `init_fn_call`
(`if !callee_fn_abi.can_unwind { unwind = Unreachable }` on the continuation the
tail call inherits; LeanMiri `initFnTailCall` with `nounwindAs := some .unreachable`).
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
Set the unwind ceiling of an activation body. The prototype stores the modular
root's unwind ceiling (Track A: `Memory.rootUnwindCeiling : Bool := true`) in
the `fnAbi.canUnwind` field of the active root activation body, a field that no
`Trusted.Rustc.V2026_06_01.MirSemantics` step function reads (call
compatibility only reads `fnAbi.conv`).
-/
@[reducible]
def withUnwindCeiling (canUnwind : Bool) (b : CapturedMir) : CapturedMir :=
  { b with fnAbi := { b.fnAbi with canUnwind := canUnwind } }

/--
The modular root's own activation: its external caller's unwind continuation
starts un-narrowed (`MODEL-LM-TAILCALL-MODULAR-ROOT`: a panic escaping the root
function itself halts with `.halted .panic`), whatever the root's own ABI.
-/
@[reducible]
def rootActivationBody (body : CapturedMir) : CapturedMir :=
  withUnwindCeiling true body

/-- The bottom (depth-`0`, root activation) saved frame's body, if any frame is saved. -/
def bottomCallerBody? : List SavedCallerFrame → Option CapturedMir
  | .nil => .none
  | caller :: rest =>
    match bottomCallerBody? rest with
    | .some b => .some b
    | .none => .some caller.callerBody

/--
Unwind ceiling of the modular root activation of `s`: `false` iff a root tail
call entered a callee that cannot unwind (directly or through earlier hops),
so the root activation's inherited external continuation is `Unreachable`.
-/
def rootUnwindCeiling (rootBody : CapturedMir) (s : MachineState) : Bool :=
  match bottomCallerBody? s.memory.callStack with
  | .some b => b.fnAbi.canUnwind
  | .none => (s.memory.activeCallee.getD rootBody).fnAbi.canUnwind

/--
Root unwind-ceiling guard (`DIV-LM-TAILCALL-NOUNWIND-UNWIND` at a modular
root): when the root activation's ceiling is narrowed, a panic that escapes the
root (`.ret .panic`, in-table or through an external callee's `.panicked`
answer) is undefined behavior ("unwinding past a frame that does not allow
unwinding") instead of `.halted .panic`. The identity when `ceiling = true`.
-/
def guardRootUnwindCeiling (ceiling : Bool) (node : MirStepNode) : MirStepNode :=
  match ceiling with
  | true => node
  | false =>
    match node with
    | .ret .panic => MirStepNode.fail .ub
    | .vis (.inr (.inr (.call req))) k =>
      MirStepNode.extCall req (fun ans =>
        match k ans with
        | .halted .panic => .faulted .ub
        | st => st)
    | other => other

@[simp]
theorem guardRootUnwindCeiling_true (node : MirStepNode) :
    guardRootUnwindCeiling true node = node := rfl

/--
Body stored as the active callee of a tail call: at a modular root it carries
the narrowed root unwind ceiling `ceiling && calleeBody.fnAbi.canUnwind`; in a
callee frame (`callStack ≠ []`) it is `calleeBody` (the narrowing lives in the
top `SavedCallerFrame.returnUnwind`).
-/
@[reducible]
def tailCalleeActivationBody
    (callStack : List SavedCallerFrame)
    (ceiling : Bool)
    (calleeBody : CapturedMir) :
    CapturedMir :=
  match callStack with
  | .nil => withUnwindCeiling (Bool.and ceiling calleeBody.fnAbi.canUnwind) calleeBody
  | _ :: _ => calleeBody

/--
Repaired `enterTailCalleeFrame` (`Terminators.lean:846-860`): enters `calleeBody`
at `bb0[0]` with `initLocals calleeBody argVals` without pushing, narrowing the
inherited unwind continuation when `calleeBody.fnAbi.canUnwind = false` — the top
`SavedCallerFrame.returnUnwind` in a callee frame, the root unwind ceiling at a
modular root (`DIV-LM-TAILCALL-NOUNWIND-UNWIND`).
-/
def enterTailCalleeFrameProto
    (mem : Memory)
    (ceiling : Bool)
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
      activeCallee := .some (tailCalleeActivationBody mem.callStack ceiling calleeBody)
    }
  }

/--
Repaired `evalTailCallTerminator` (`Terminators.lean:3307-3378`), equal to
`Trusted.evalTailCallTerminator` except that:
- argument operands go through `evalOperandsProto` (Bug 4; `localDecls` stays
  `.nil` exactly as in `Trusted`),
- at a modular root (`callStack = []`) the torn-down memory is relocated by
  `relocateRootCallerReferents` (Bug 3) before entering the callee,
- the callee is entered with `enterTailCalleeFrameProto` (Bug 2).
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
  let ceiling : Bool :=
    match currentBody with
    | .some b => b.fnAbi.canUnwind
    | .none => true
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
        .nil
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
          { s.memory with borrows := disableFrameBorrows s.memory.borrows depth nLocals }
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
            let memEntered : Memory :=
              match s.memory.callStack with
              | .nil =>
                relocateRootCallerReferents
                  memAfterTeardown nLocals (length (initLocals calleeBody argVals))
              | _ :: _ => memAfterTeardown
            MirStepNode.step (enterTailCalleeFrameProto memEntered ceiling calleeBody argVals)
        | .none =>
          MirStepNode.extCall
            { defPath := target.defPath
              typeArgs := target.typeArgs
              args := argVals
              memory := memAfterTeardown }
            resumeExternalTailCall

/--
Repaired `writeReturnDestination` (`Terminators.lean:599-725`): strips leading
`.opaqueCast` projections on the caller's return `destination` before
root-vs-projected dispatch, validating against the cast type on pure
`.opaqueCast` chains and using `eraseLeadingOpaqueCastDecls` on `(_l as T).f`
return destinations (so `(_0 as OpaqueTy) = call foo()` and
`(_0 as Pair).0 = call foo()` on an `.uninit` local succeed instead of faulting
with `.ub`). When `dst` has no leading `.opaqueCast`, reduces definitionally to
`Trusted.writeReturnDestination`.
-/
def writeReturnDestinationProto
    (callerLocals : List LocalSlot)
    (mem : Memory)
    (dst : Place)
    (retVal : Value)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    FrameWriteResult :=
  match takeLeadingOpaqueCast dst.projection with
  | .nil => writeReturnDestination callerLocals mem dst retVal localDecls layouts
  | _ :: _ =>
    let writeDecls := eraseLeadingOpaqueCastDecls localDecls layouts dst.local_ dst.projection
    match stripLeadingOpaqueCast dst.projection with
    | .nil =>
      let tyValid :=
        match localDecls with
        | .nil => true
        | _ :: _ => validateValueForTy? layouts (placeTy localDecls layouts dst) retVal
      match tyValid with
      | false => .ub
      | true =>
        writeReturnDestination
          callerLocals mem { local_ := dst.local_, projection := .nil } retVal writeDecls layouts
    | .deref :: _ =>
      writeReturnDestination callerLocals mem dst retVal localDecls layouts
    | p0 :: ps =>
      writeReturnDestination
        callerLocals mem { local_ := dst.local_, projection := p0 :: ps } retVal writeDecls layouts

/--
Repaired `evalTerminator` (`Terminators.lean:3379-3704`), equal to
`Trusted.evalTerminator` except for `.tailCall` (`evalTailCallTerminatorProto`)
and Bug 4 (`stripLeadingOpaqueCast` before root-vs-projected dispatch in `.drop`,
`.return_`, `.call`, `.switchInt`, and `.assert`).
-/
def evalTerminatorProto
    (s : MachineState)
    (term : Terminator)
    (currentBody : Option CapturedMir := .none) :
    MirStepNode :=
  match term.kind with
  | .tailCall func argOps =>
    evalTailCallTerminatorProto s func argOps currentBody
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
  | .return_ =>
    match s.memory.callStack with
    | .nil => evalTerminator s term currentBody
    | caller :: restStack =>
      match takeLeadingOpaqueCast caller.destination.projection with
      | .nil => evalTerminator s term currentBody
      | _ :: _ =>
        match get? s.frame.locals 0 with
        | .some (.init retVal) =>
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
            let borrows₁ := disableFrameBorrows s.memory.borrows depth nLocals
            match caller.isDiverging with
            | true => MirStepNode.fail .ub
            | false =>
              let restoredProtectors := restoreCallerProtectors caller
              let callerMem : Memory := {
                s.memory with
                borrows := borrows₁
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoredProtectors
              }
              match
                writeReturnDestinationProto
                  caller.frame.locals
                  callerMem
                  caller.destination
                  retVal
                  caller.callerBody.localDecls
                  caller.callerBody.layouts
              with
              | .ok updatedCallerLocals mem' =>
                MirStepNode.step {
                  frame := {
                    caller.frame with
                    blockIdx := caller.returnTarget
                    stmtIdx := 0
                    locals := updatedCallerLocals
                  }
                  memory := mem'
                }
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub
  | .call func argOps destination target unwind =>
    let hasCast :=
      Bool.or
        (isPureOpaqueCastPlace destination)
        (Bool.or (isPureOpaqueCastMoveOp func) (anyPureOpaqueCastMoveOp argOps))
    match hasCast with
    | false => evalTerminator s term currentBody
    | true =>
      let bodyLocalDecls := bodyLocalDeclsOf currentBody
      let bodyLayouts : LayoutTable :=
        match currentBody with
        | .some b => b.layouts
        | .none => emptyLayoutTable
      match
        validatePureOpaqueCastMoveOps
          s.frame.locals bodyLocalDecls bodyLayouts (func :: argOps)
      with
      | false => MirStepNode.fail .ub
      | true =>
        let term' : Terminator := {
          term with
          kind := .call
            (erasePureOpaqueCastMoveOp func)
            (erasePureOpaqueCastMoveOps argOps)
            (erasePureOpaqueCastPlace destination)
            target
            unwind
        }
        evalTerminator s term' currentBody
  | .switchInt discr targets =>
    match isPureOpaqueCastMoveOp discr with
    | false => evalTerminator s term currentBody
    | true =>
      let bodyLocalDecls := bodyLocalDeclsOf currentBody
      let bodyLayouts : LayoutTable :=
        match currentBody with
        | .some b => b.layouts
        | .none => emptyLayoutTable
      match validatePureOpaqueCastMoveOp s.frame.locals bodyLocalDecls bodyLayouts discr with
      | false => MirStepNode.fail .ub
      | true =>
        evalTerminator
          s
          { term with kind := .switchInt (erasePureOpaqueCastMoveOp discr) targets }
          currentBody
  | .assert cond expected target unwind =>
    match isPureOpaqueCastMoveOp cond with
    | false => evalTerminator s term currentBody
    | true =>
      let bodyLocalDecls := bodyLocalDeclsOf currentBody
      let bodyLayouts : LayoutTable :=
        match currentBody with
        | .some b => b.layouts
        | .none => emptyLayoutTable
      match validatePureOpaqueCastMoveOp s.frame.locals bodyLocalDecls bodyLayouts cond with
      | false => MirStepNode.fail .ub
      | true =>
        evalTerminator
          s
          { term with kind := .assert (erasePureOpaqueCastMoveOp cond) expected target unwind }
          currentBody
  | _ => evalTerminator s term currentBody

/-! ## 6. Unified Prototype Step Evaluator & Bounded Differential Runner -/

/--
One-step prototype MIR coalgebra transition from an active `MachineState`
(`Machine.lean` `stepMirFn` with the repaired statement / terminator evaluators,
the root activation body `rootActivationBody body`, and the root unwind-ceiling
guard).
-/
def stepMirFnProto (body : CapturedMir) (s : MachineState) : MirStepNode :=
  let rootBody := rootActivationBody body
  let currentBody := s.memory.activeCallee.getD rootBody
  guardRootUnwindCeiling (rootUnwindCeiling rootBody s)
    (match currentBody.phase with
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
             MirStepNode.fail .ub)

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
`n = 1` agreement: a single-element zero-offset `copy_nonoverlapping`
(`countBits == 1`, `srcPtr.offsetBytes == 0`, `dstPtr.offsetBytes == 0`, no union
endpoint) is *exactly* `Trusted.evalCopySingleDirect`.
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
    evalCopySingleDirect
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
  have hPeel :
      peelArrayElementProjForMultiCopy [.constantIndex idx minLen false] 0 (n.succ.succ) =
        (.nil, idx) := by
    rw [peelArrayElementProjForMultiCopy_topLevel_constantIndex idx minLen 0 n, hZeroAdd]
  simp only [stripTransparentProjections,
    normalizeSubsliceProjections, normalizeSubsliceProjectionsAux,
    splitLastConstantIndexWithFromEnd?, readProjectedValue,
    hMinBounds, hIdxBounds, Bool.true_and, hPeel]
  cases get? elems idx with
  | none => rfl
  | some elemVal =>
    cases elemVal with
    | aggregate vIdx _ => cases vIdx <;> rfl
    | _ => rfl

/--
Universal multi-element subplace slice copy characterization:
for any two distinct local array slots `srcLoc ≠ dstLoc` holding
`.aggregate 0 srcElems` / `.aggregate 0 dstElems`, endpoint borrows
`[.constantIndex srcIdx minS false]` / `[.constantIndex dstIdx minD false]` with
zero pointer offsets, `n ≥ 2`, and in-bounds slices,
`evalCopyNonOverlappingPermOkProto` runs the Tree Borrows read-then-write
transition on the accessed windows and writes
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
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    (match
      borrowsAfterCopySliceProto
        s.memory.borrows
        s.memory.activeProtectors
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        (copySliceWindowProj .nil srcIdx n (length srcElems))
        (copySliceWindowProj .nil dstIdx n (length dstElems))
    with
    | .none => MirStepNode.fail .ub
    | .some borrows' =>
      writeCopyDstPlaceProto
        s
        { local_ := dstLoc, projection := .nil }
        locals₃
        (.aggregate 0 dstElems')
        borrows'
        .nil
        emptyLayoutTable) := by
  intro srcPtr dstPtr srcEntry dstEntry copiedSlice dstElems'
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
  have hOff0 : ∀ pt, resolvePtrElemOffset? 0 pt emptyLayoutTable = .some 0 := fun _ => rfl
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hSrcRoot, hDstRoot, hSrcPt, hDstPt, hOff0, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, hDstSlot,
    hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
    Nat.beq_refl, hDistinctLoc, hTagEq, hDstTagEq, hDistinctTag,
    copiedSlice, dstElems', Bool.and_false, Bool.false_and]

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
  have hOff0 : ∀ pt, resolvePtrElemOffset? 0 pt emptyLayoutTable = .some 0 := fun _ => rfl
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hSrcRoot, hDstRoot, hSrcPt, hDstPt, hOff0, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, hDstSlot,
    hPlaceTyNil, Bool.not_false, hSrcOob, Bool.and_false]

/--
Overlapping multi-element subplace copy within the same array container
(`srcLoc == dstLoc`, both parents `[]`, and the index intervals
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
  have hOff0 : ∀ pt, resolvePtrElemOffset? 0 pt emptyLayoutTable = .some 0 := fun _ => rfl
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hRoot, hSrcPt, hDstPt, hOff0, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, hArrSlot,
    hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
    Nat.beq_refl, hOverlapNil, hOverlap1, hOverlap2, Bool.or_false]

/--
Disjoint multi-element subplace copy within the same array container
(`srcLoc == dstLoc`, both parents `[]`, `srcIdx + n ≤ dstIdx`) succeeds — even
when `srcPtr` and `dstPtr` share one provenance tag (`p` and `p.add(k)`) — running
the Tree Borrows transition on the accessed windows and splicing
`[srcIdx, srcIdx + n)` into `[dstIdx, dstIdx + n)` of the array local `arrLoc`.
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
    evalCopyNonOverlappingPermOkProto
      s src dst .nil emptyLayoutTable srcPtr dstPtr srcEntry dstEntry n locals₃ =
    (match
      borrowsAfterCopySliceProto
        s.memory.borrows
        s.memory.activeProtectors
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        (copySliceWindowProj .nil srcIdx n (length arrElems))
        (copySliceWindowProj .nil dstIdx n (length arrElems))
    with
    | .none => MirStepNode.fail .ub
    | .some borrows' =>
      writeCopyDstPlaceProto
        s
        { local_ := arrLoc, projection := .nil }
        locals₃
        (.aggregate 0 arrElems')
        borrows'
        .nil
        emptyLayoutTable) := by
  intro srcPtr dstPtr srcEntry dstEntry copiedSlice arrElems'
  unfold evalCopyNonOverlappingPermOkProto
  have hRoot :
      resolveCopyEndpointRootSlot s locals₃ srcEntry =
        .some (.init (.aggregate 0 arrElems)) := by
    simp [resolveCopyEndpointRootSlot, srcEntry, hArrSlot]
  have hPlaceTyNil : ∀ p, placeTy .nil emptyLayoutTable p = .none := by
    intro p
    simp [placeTy, get?]
  have hOverlapNil : projectionsOverlap .nil .nil = true := rfl
  have hOff0 : ∀ pt, resolvePtrElemOffset? 0 pt emptyLayoutTable = .some 0 := fun _ => rfl
  simp only [hCountPos, hNotSingle, srcPtr, dstPtr, Bool.false_and,
    hRoot, hSrcPt, hDstPt, hOff0, hSrcSlice, hDstSlice,
    srcEntry, dstEntry, hArrSlot,
    hPlaceTyNil, Bool.not_false, Bool.true_and, hSrcBounds, hDstBounds,
    Nat.beq_refl, hOverlapNil, hDisjoint, Bool.true_or,
    copiedSlice, arrElems']

/--
Misaligned element pointer (Rust `copy_nonoverlapping` precondition: "Both
`src` and `dst` must be properly aligned"): when the statically known pointee has
byte size `elemSz` and a pointer's byte offset is not a whole number of elements
(`resolvePtrElemOffset? = .none`), a non-zero-count, non-union, not-single-direct
`copy_nonoverlapping` between initialized endpoints faults with `.ub` instead of
reinterpreting the byte offset as an element index.
-/
theorem evalCopyNonOverlappingPermOkProto_misaligned_src_ub
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (n : Nat)
    (locals₃ : List LocalSlot)
    (srcRootVal dstRootVal : Value)
    (hCountPos : Nat.beq n 0 = false)
    (hNoUnionSrc : resolveUnionEndpoint? localDecls layouts locals₃ srcEntry = .none)
    (hNoUnionDst : resolveUnionEndpoint? localDecls layouts locals₃ dstEntry = .none)
    (hSrcOffPos : Nat.beq srcPtr.offsetBytes 0 = false)
    (hSrcRoot : resolveCopyEndpointRootSlot s locals₃ srcEntry = .some (.init srcRootVal))
    (hDstRoot : resolveCopyEndpointRootSlot s locals₃ dstEntry = .some (.init dstRootVal))
    (hMisaligned :
      resolvePtrElemOffset? srcPtr.offsetBytes
        (match operandPointeeTy localDecls layouts src with
         | .some pt => .some pt
         | .none => operandPointeeTy localDecls layouts dst)
        layouts = .none) :
    evalCopyNonOverlappingPermOkProto
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry n locals₃ =
    MirStepNode.fail .ub := by
  unfold evalCopyNonOverlappingPermOkProto
  simp only [hCountPos, hNoUnionSrc, hNoUnionDst, hSrcOffPos, Bool.false_and, Bool.and_false,
    hSrcRoot, hDstRoot, hMisaligned]

/-! ## 9. Universal Simulation Theorems & Witnesses for Bug 2 and Bug 3 -/

/--
**Bug 2 universal theorem, nested tail call (`tailCall_leanMiri_nounwind_callee_simulation`).**
For any caller frame `caller` on `mem.callStack` — whatever its original
`caller.returnUnwind : UnwindAction` (`.cleanup bb`, `.continue_`,
`.unreachable`, `.terminate`) — and any tail callee with
`calleeBody.fnAbi.canUnwind = false`, entering it via
`enterTailCalleeFrameProto` makes `Trusted`'s own, unmodified unwinder
`unwindFromCallStack` (used by `TerminatorKind.unwindResume`, by
`resumeExternalTailCall (.panicked …)`, and by `applyUnwindAction .continue_`)
fault with `.faulted .ub`, matching LeanMiri `initFnTailCall` with
`nounwindAs := some .unreachable` followed by `unwindResume`. No hypothesis on
`caller.returnUnwind` is needed (`tailCall_leanMiri_nounwind_callee`'s `↔ u = ur`
collapses to unconditional agreement).
-/
theorem tailCall_leanMiri_nounwind_callee_simulation
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (mem : Memory)
    (ceiling : Bool)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (memAtUnwind : Memory)
    (hCalleeNoUnwind : calleeBody.fnAbi.canUnwind = false)
    (hStack : mem.callStack = caller :: restStack) :
    let stEntered := enterTailCalleeFrameProto mem ceiling calleeBody argVals
    unwindFromCallStack stEntered.memory.callStack memAtUnwind = .faulted .ub := by
  intro stEntered
  simp [stEntered, enterTailCalleeFrameProto, hStack, hCalleeNoUnwind,
    narrowCallStackForTailCallee, unwindFromCallStack]

/--
End-to-end form: an `UnwindResume` executed by the non-unwinding tail callee
(under the repaired terminator evaluator) faults with `.ub` for every inherited
action.
-/
theorem tailCall_nounwind_callee_unwindResume_ub
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (mem : Memory)
    (ceiling : Bool)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (f : StackFrame)
    (span : String)
    (cb : Option CapturedMir)
    (hCalleeNoUnwind : calleeBody.fnAbi.canUnwind = false)
    (hStack : mem.callStack = caller :: restStack) :
    evalTerminatorProto
      ⟨f, (enterTailCalleeFrameProto mem ceiling calleeBody argVals).memory⟩
      ⟨.unwindResume, span⟩ cb = MirStepNode.fail .ub := by
  simp [evalTerminatorProto, evalTerminator, enterTailCalleeFrameProto, hStack, hCalleeNoUnwind,
    narrowCallStackForTailCallee, unwindFromCallStack]

/--
**Bug 2 multi-hop monotonicity (`tailCall_nounwind_multihop_monotonicity`).** If
`caller` calls `f`, `f` tail-calls `g` with `g.fnAbi.canUnwind = false`, and `g`
tail-calls `h` with arbitrary `h.fnAbi.canUnwind` (including `true`), unwinding
from `h` still faults with `.faulted .ub`: `g` irreversibly narrowed the
inherited continuation.
-/
theorem tailCall_nounwind_multihop_monotonicity
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (mem : Memory)
    (ceilingG ceilingH : Bool)
    (gBody hBody : CapturedMir)
    (gArgs hArgs : List Value)
    (memAtUnwind : Memory)
    (hGNoUnwind : gBody.fnAbi.canUnwind = false)
    (hStack : mem.callStack = caller :: restStack) :
    let stG := enterTailCalleeFrameProto mem ceilingG gBody gArgs
    let stH := enterTailCalleeFrameProto stG.memory ceilingH hBody hArgs
    unwindFromCallStack stH.memory.callStack memAtUnwind = .faulted .ub := by
  intro stG stH
  cases hCan : hBody.fnAbi.canUnwind <;>
    simp [stG, stH, enterTailCalleeFrameProto, hStack, hGNoUnwind, hCan,
      narrowCallStackForTailCallee, unwindFromCallStack]

/--
**Bug 2 at a modular root: unwind-ceiling narrowing.** A root tail call
(`mem.callStack = []`) records the narrowed root unwind ceiling
`ceiling && calleeBody.fnAbi.canUnwind` in the entered state, so a callee that
cannot unwind narrows it to `false` and every later root tail call keeps it
`false` (monotone, since the next hop's `ceiling` is read back from the active
root activation body).
-/
theorem tailCall_root_unwind_ceiling
    (rootBody : CapturedMir)
    (mem : Memory)
    (ceiling : Bool)
    (calleeBody : CapturedMir)
    (argVals : List Value)
    (hRoot : mem.callStack = []) :
    rootUnwindCeiling rootBody (enterTailCalleeFrameProto mem ceiling calleeBody argVals) =
      Bool.and ceiling calleeBody.fnAbi.canUnwind := by
  simp [rootUnwindCeiling, enterTailCalleeFrameProto, hRoot, narrowCallStackForTailCallee,
    tailCalleeActivationBody, withUnwindCeiling, bottomCallerBody?]

/--
The modular root's own activation starts with an un-narrowed ceiling, whatever
its own ABI (`MODEL-LM-TAILCALL-MODULAR-ROOT`: the root's own panic escapes to its
external caller).
-/
theorem rootUnwindCeiling_initial
    (body : CapturedMir) (s : MachineState)
    (hRoot : s.memory.callStack = []) (hActive : s.memory.activeCallee = .none) :
    rootUnwindCeiling (rootActivationBody body) s = true := by
  simp [rootUnwindCeiling, hRoot, hActive, bottomCallerBody?, rootActivationBody, withUnwindCeiling]

/--
At a modular root, `UnwindResume` reaches `Trusted`'s `.halted .panic`
(`unwindFromCallStack [] = .halted .panic`), which the unwind-ceiling guard
turns into `.ub` exactly when the root ceiling is narrowed.
-/
theorem root_unwindResume_guarded
    (s : MachineState) (span : String) (cb : Option CapturedMir) (ceiling : Bool)
    (hRoot : s.memory.callStack = []) :
    guardRootUnwindCeiling ceiling (evalTerminatorProto s ⟨.unwindResume, span⟩ cb) =
      match ceiling with
      | true => MirStepNode.retOutcome .panic
      | false => MirStepNode.fail .ub := by
  cases ceiling <;>
    simp [guardRootUnwindCeiling, evalTerminatorProto, evalTerminator, hRoot, unwindFromCallStack,
      MirStepNode.retOutcome]

namespace TailCallCallerReferentWitnesses

/-!
Exact replicas of the `MirUntestedVariantCorrespondenceTests.lean` builders and
witnesses (`tyU32`, `wFnAbi`, `mkBody`, `gReadBody`, `fDangleBody`, `fCrBody`,
`fRdBody`, `crMem` at lines 469-504, 2221-2222, 2435-2451, 2633-2648), plus
new non-vacuity witnesses for the paths A0's caller-referent sentinel missed.
-/

def tyU32 : Ty := { kind := .uint .u32, layoutIdx := 0 }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def wFnAbi : FnAbi :=
  { args := [], ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def wLayouts : LayoutTable := { pointerBits := 64, isLittleEndian := true, entries := [] }

/-- A `Runtime(PostCleanup)` body with the given locals and blocks. -/
def mkBody (dp : DefPath) (argCount : Nat) (decls : List LocalDecl)
    (bbs : List BasicBlockData) : CapturedMir :=
  { defPath := dp, argCount, localDecls := decls, basicBlocks := bbs,
    phase := .runtimePostCleanup, role := .subject, fnAbi := wFnAbi, layouts := wLayouts,
    allocations := [] }

def u32Decl (name : String) : LocalDecl := { mutability := .mut, ty := tyU32, debugName := some name }

def cU32 (v : Nat) : Operand := .constant { ty := tyU32, val := .scalar (.int ⟨v, 4⟩) }

def lc (i : Nat) : Place := { local_ := i, projection := [] }

def st (k : StatementKind) : Statement := { kind := k, span := "w" }

def assignU32 (dst v : Nat) : Statement := st (.assign (lc dst) (.use (cU32 v)))

def blk (stmts : List Statement) (t : TerminatorKind) : BasicBlockData :=
  { statements := stmts, terminator := { kind := t, span := "w" }, isCleanup := false }

def fnItem (dp : String) : Operand :=
  .constant { ty := { kind := .fnDef dp [], layoutIdx := 0 }, val := .zeroSized }

/-- `*mut u32`. -/
def tyPtrMutU32 : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }

def ptrDecl (name : String) : LocalDecl :=
  { mutability := .mut, ty := tyPtrMutU32, debugName := some name }

/-- `fn gread(p: *mut u32, y: u32) -> u32 { _0 = copy (*p); return }`. -/
def gReadBody : CapturedMir :=
  mkBody "w::gread" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y"]
    [blk [st (.assign (lc 0) (.use (.copy ⟨1, [.deref]⟩)))] .return_]

/-- `fn fdangle() -> u32 { let mut x = 42; let p = &raw mut x; become gread(p, 137) }`. -/
def fDangleBody : CapturedMir :=
  mkBody "w::fdangle" 0 [u32Decl "_0", ptrDecl "p", u32Decl "x"]
    [blk [st (.storageLive 1), st (.storageLive 2), assignU32 2 42,
          st (.assign (lc 1) (.rawPtr .mut (lc 2)))]
      (.tailCall (fnItem "w::gread") [.copy (lc 1), cU32 137])]

/-- `fn fcr(p: *mut u32) -> u32 { become gread(copy p, 137) }`. -/
def fCrBody : CapturedMir :=
  mkBody "w::fcr" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gread") [.copy (lc 1), cU32 137])]

/-- `fn frd(p: *mut u32) -> u32 { _0 = copy (*p); return }`. -/
def fRdBody : CapturedMir :=
  mkBody "w::frd" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [st (.assign (lc 0) (.use (.copy ⟨1, [.deref]⟩)))] .return_]

/-- `fn gadd(p: *mut u32, y: u32) -> u32 { _0 = Add(copy (*p), 0); return }` (a non-`Use` read). -/
def gAddBody : CapturedMir :=
  mkBody "w::gadd" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y"]
    [blk [st (.assign (lc 0) (.binaryOp .add (.copy ⟨1, [.deref]⟩) (cU32 0)))] .return_]

/-- `fn fcradd(p: *mut u32) -> u32 { become gadd(copy p, 137) }`. -/
def fCrAddBody : CapturedMir :=
  mkBody "w::fcradd" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gadd") [.copy (lc 1), cU32 137])]

/-- `fn hadd(p: *mut u32) -> u32 { _0 = Add(copy (*p), 1); return }`. -/
def hAddBody : CapturedMir :=
  mkBody "w::hadd" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [st (.assign (lc 0) (.binaryOp .add (.copy ⟨1, [.deref]⟩) (cU32 1)))] .return_]

/-- `fn fcall(p: *mut u32) -> u32 { _0 = hadd(copy p) -> bb1; bb1: return }` (no tail call). -/
def fCallBody : CapturedMir :=
  mkBody "w::fcall" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.call (fnItem "w::hadd") [.copy (lc 1)] (lc 0) (some 1) .continue_),
     blk [] .return_]

/-- `fn gcall(p: *mut u32, y: u32) -> u32 { _0 = hadd(copy p) -> bb1; bb1: return }`. -/
def gCallBody : CapturedMir :=
  mkBody "w::gcall" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y"]
    [blk [] (.call (fnItem "w::hadd") [.copy (lc 1)] (lc 0) (some 1) .continue_),
     blk [] .return_]

/-- `fn fcrcall(p: *mut u32) -> u32 { become gcall(copy p, 137) }`. -/
def fCrCallBody : CapturedMir :=
  mkBody "w::fcrcall" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gcall") [.copy (lc 1), cU32 137])]

/--
`fn gwr(p: *mut u32, y: u32) -> u32 { _2 = 137; *p = 77; let r = &mut *p; _0 = *r; return }`
(4 locals: the callee's own `_2` would shadow the referent slot `2`).
-/
def gWriteReborrowBody : CapturedMir :=
  mkBody "w::gwr" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y", ptrDecl "r"]
    [blk [st (.storageLive 3),
          assignU32 2 137,
          st (.assign ⟨1, [.deref]⟩ (.use (cU32 77))),
          st (.assign (lc 3) (.ref (.mut false) ⟨1, [.deref]⟩)),
          st (.assign (lc 0) (.use (.copy ⟨3, [.deref]⟩)))] .return_]

/-- `fn fcrwr(p: *mut u32) -> u32 { become gwr(copy p, 137) }`. -/
def fCrWriteBody : CapturedMir :=
  mkBody "w::fcrwr" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gwr") [.copy (lc 1), cU32 137])]

/-- `fn hwide(p: *mut u32, a: u32, b: u32, c: u32) -> u32 { _0 = copy (*p); return }` (5 locals). -/
def hWideBody : CapturedMir :=
  mkBody "w::hwide" 4 [u32Decl "_0", ptrDecl "p", u32Decl "a", u32Decl "b", u32Decl "c"]
    [blk [st (.assign (lc 0) (.use (.copy ⟨1, [.deref]⟩)))] .return_]

/-- `fn gmid(p: *mut u32, y: u32) -> u32 { become hwide(copy p, 1, 2, 3) }` (3 locals). -/
def gMidBody : CapturedMir :=
  mkBody "w::gmid" 2 [u32Decl "_0", ptrDecl "p", u32Decl "y"]
    [blk [] (.tailCall (fnItem "w::hwide") [.copy (lc 1), cU32 1, cU32 2, cU32 3])]

/-- `fn fhop(p: *mut u32) -> u32 { become gmid(copy p, 137) }` (2 locals; two widening root hops). -/
def fHopBody : CapturedMir :=
  mkBody "w::fhop" 1 [u32Decl "_0", ptrDecl "p"]
    [blk [] (.tailCall (fnItem "w::gmid") [.copy (lc 1), cU32 137])]

/--
The modular root's external caller owns `*p = 42` as caller-owned referent slot
`2` of depth `0`, borrowed by tag `1` (exactly `crMem`), with every witness
callee linked.
-/
def crMem : Memory :=
  { callees := [gReadBody, gAddBody, hAddBody, gCallBody, gWriteReborrowBody, hWideBody, gMidBody],
    callerLocals := [.uninit, .uninit, .init (.scalar ⟨42, 4⟩)],
    borrows := [{ tag := 1, targetLocal := 2, targetProjection := [], perm := .unique }],
    nextTag := 2 }

/-- The pointer argument `p` (provenance tag `1`). -/
def crPtrArg : Value := .ptr ⟨1, 0⟩ 8

/-- One `Trusted` coalgebra step (the correspondence suite's `execStep`). -/
def execStep (body : CapturedMir) (s : MirExecState) : Option MirExecState :=
  match stepMirState body s with
  | .ret out => some (.halted out)
  | .tau s' => some s'
  | .vis (.inl (.fail k)) _ => some (.faulted k)
  | .vis (.inr (.inl _)) k => some (k PUnit.unit)
  | .vis (.inr (.inr _)) _ => none

/-- `n` `Trusted` coalgebra steps (the correspondence suite's `execN`). -/
def execN (body : CapturedMir) : Nat → MirExecState → Option MirExecState
  | 0, s => some s
  | n + 1, s => (execStep body s).bind (execN body n)

/-- The returned value of a halted state. -/
def haltedVal? : Option MirExecState → Option Value
  | some (.halted (.normal (v, _))) => some v
  | _ => none

/-- Root initial state of a caller-referent witness. -/
def crInit (body : CapturedMir) : MirExecState :=
  .running (Trusted.VerificationResult.initMachineStateWithMemory body [crPtrArg] crMem)

/--
**Bug 3 reproduction and repair on the exact correspondence witnesses.**
Unpatched `Trusted` returns `gread`'s own `_2 = 137` for `fcr(p)`
(`tailCall_witness_root_caller_referent_divergence`), the repaired prototype
returns the caller's `*p = 42`, agreeing with the tail-call-free `frd(p)` under
both semantics.
-/
theorem tailCall_repaired_root_caller_referent_returns_42 :
    haltedVal? (execN fCrBody 3 (crInit fCrBody)) = some (.scalar ⟨137, 4⟩) ∧
    haltedVal? (execNProto fCrBody 3 (crInit fCrBody)) = some (.scalar ⟨42, 4⟩) ∧
    haltedVal? (execN fRdBody 2 (crInit fRdBody)) = some (.scalar ⟨42, 4⟩) ∧
    haltedVal? (execNProto fRdBody 2 (crInit fRdBody)) = some (.scalar ⟨42, 4⟩) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
**Non-`Use` reads are repaired too.** `gadd` reads `*p` inside `BinOp.add`
(`Trusted.evalRvalue`'s own operand evaluation, which the repair never
re-implements): unpatched `Trusted` (and A0's sentinel prototype) still returned
`137`; the relocation makes `Trusted`'s own lookup return `42`.
-/
theorem tailCall_repaired_root_caller_referent_binop :
    haltedVal? (execN fCrAddBody 3 (crInit fCrAddBody)) = some (.scalar ⟨137, 4⟩) ∧
    haltedVal? (execNProto fCrAddBody 3 (crInit fCrAddBody)) = some (.scalar ⟨42, 4⟩) := by
  exact ⟨rfl, rfl⟩

/--
**No regression on inline calls.** A root that inline-calls `hadd(p)` (no tail
call at all) returns `43` under unpatched `Trusted` and under the prototype (A0's
init-time sentinel promotion made this program fault with `.ub`), and a root tail
call followed by an inline call (`fcrcall -> become gcall -> hadd`) also returns
`43` through the suspended relocated root frame.
-/
theorem tailCall_repaired_caller_referent_inline_calls :
    haltedVal? (execN fCallBody 6 (crInit fCallBody)) = some (.scalar ⟨43, 4⟩) ∧
    haltedVal? (execNProto fCallBody 6 (crInit fCallBody)) = some (.scalar ⟨43, 4⟩) ∧
    haltedVal? (execNProto fCrCallBody 7 (crInit fCrCallBody)) = some (.scalar ⟨43, 4⟩) := by
  exact ⟨rfl, rfl, rfl⟩

/--
**Write-through and child reborrow in the tail callee.** `gwr` (4 locals, its own
`_2 = 137`) writes `*p = 77`, reborrows `r = &mut *p`, and returns `*r`: the
prototype returns `77`, leaves the callee's `_2` alone, and the caller's referent
— reached from the provenance tag `1` of the argument, exactly as
`VerificationResult` reads `mem.callerLocals[entry.targetLocal]` — holds `77`
(relocated to slot `4 = 2 + (4 - 2)` past the callee frame).
-/
theorem tailCall_repaired_caller_referent_write_and_reborrow :
    (match execNProto fCrWriteBody 7 (crInit fCrWriteBody) with
     | some (.halted (.normal (v, memOut))) =>
       some (v,
         (lookupBorrow memOut.borrows 1).bind (fun e => get? memOut.callerLocals e.targetLocal),
         (lookupBorrow memOut.borrows 1).map (·.targetLocal))
     | _ => none) =
    some (.scalar ⟨77, 4⟩, some (.init (.scalar ⟨77, 4⟩)), some 4) := by
  rfl

/--
**Multi-hop root tail calls.** `fhop` (2 locals) → `gmid` (3 locals) → `hwide`
(5 locals): each widening hop relocates the referent again (`2 → 3 → 5`), and
`hwide` reads `42`. Unpatched `Trusted` is worse than shadowing here: the second
hop's teardown (`disableFrameBorrows … 0 3`) treats the caller-owned slot `2` as
`gmid`'s own local and *disables* the caller's borrow, so `hwide`'s `*p` faults
with a false `.ub`.
-/
theorem tailCall_repaired_caller_referent_multihop :
    execN fHopBody 4 (crInit fHopBody) = some (.faulted .ub) ∧
    haltedVal? (execNProto fHopBody 4 (crInit fHopBody)) = some (.scalar ⟨42, 4⟩) := by
  exact ⟨rfl, rfl⟩

/--
**Dangling-pointer soundness preserved.** `fdangle`'s own local `_2` is
frame-owned (`2 < 3`), so it is disabled and dead after the tail call and never
relocated: `gread`'s `*p` faults with `.ub` under both semantics.
-/
theorem tailCall_repaired_dangling_frame_local_faults_ub :
    execN fDangleBody 6 (.running (initMachineStateWithCallees fDangleBody [] [gReadBody])) =
      some (.faulted .ub) ∧
    execNProto fDangleBody 6 (.running (initMachineStateWithCallees fDangleBody [] [gReadBody])) =
      some (.faulted .ub) := by
  exact ⟨rfl, rfl⟩

/-- `fn hwide_ret(a: u32, b: u32, c: u32) -> u32 { _0 = 99; return }` (4 locals). -/
def hWideRetBody : CapturedMir :=
  mkBody "w::hwideret" 3 [u32Decl "_0", u32Decl "a", u32Decl "b", u32Decl "c"]
    [blk [assignU32 0 99] .return_]

/-- `fn gnarrow() -> u32 { become hwideret(1, 2, 3) }` (1 local). -/
def gNarrowHopBody : CapturedMir :=
  mkBody "w::gnarrow" 0 [u32Decl "_0"]
    [blk [] (.tailCall (fnItem "w::hwideret") [cU32 1, cU32 2, cU32 3])]

/--
`fn fwidedead() -> u32 { let mut x = 42; let p = &raw mut x; become gnarrow() }` (4 locals:
creates borrow tag `1` at `targetLocal = 2`, which is disabled with `allocDead = true` when
entering 1-local `gnarrow`).
-/
def fWideDeadBody : CapturedMir :=
  mkBody "w::fwidedead" 0 [u32Decl "_0", ptrDecl "p", u32Decl "x", u32Decl "pad"]
    [blk [st (.storageLive 1), st (.storageLive 2), assignU32 2 42,
          st (.assign (lc 1) (.rawPtr .mut (lc 2)))]
      (.tailCall (fnItem "w::gnarrow") [])]

/--
**Wide -> narrow -> wide root tail-call chain (`!entry.allocDead` guard in `isRootCallerReferentBorrow`).**
When 4-local `fwidedead` (which borrows its own local `_2`) tail-calls 1-local
`gnarrow`, `_2`'s borrow is disabled (`allocDead = true`) at `targetLocal = 2 >= 1`.
When `gnarrow` then tail-calls 4-local `hwideret`, `isRootCallerReferentBorrow`
ignores the dead borrow (`!entry.allocDead = false`), so `callerLocals` stays
empty (`[]`) and the dead borrow is not shifted to `2 + (4 - 1) = 5`.
-/
theorem tailCall_repaired_wide_narrow_wide_dead_local_not_relocated :
    (match execNProto fWideDeadBody 8
        (.running (initMachineStateWithCallees fWideDeadBody [] [gNarrowHopBody, hWideRetBody])) with
     | some (.halted (.normal (v, memOut))) =>
       some (v, memOut.callerLocals,
         (lookupBorrow memOut.borrows 1).map (fun e => (e.targetLocal, e.allocDead)))
     | _ => none) =
    some (.scalar ⟨99, 4⟩, [], some (2, true)) := by
  rfl

/-! ### Bug 2 witnesses at a modular root -/

/-- `wFnAbi` with `canUnwind := true`. -/
def unwFnAbi : FnAbi := { wFnAbi with canUnwind := true }

/-- `fn gunw() -> u32 { resume }` (`canUnwind = false`, the correspondence suite's `gUnwindBody`). -/
def gUnwindBody : CapturedMir := mkBody "w::gunw" 0 [u32Decl "_0"] [blk [] .unwindResume]

/-- `fn funw() -> u32 { become gunw() }` (the correspondence suite's `fUnwindBody`). -/
def fUnwindBody : CapturedMir :=
  mkBody "w::funw" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gunw") [])]

/-- An unwinding (`canUnwind = true`) variant of `gunw`. -/
def gUnwindCanBody : CapturedMir :=
  { mkBody "w::gunwcan" 0 [u32Decl "_0"] [blk [] .unwindResume] with fnAbi := unwFnAbi }

/-- `fn funwcan() -> u32 { become gunwcan() }` (unwinding root and callee). -/
def fUnwindCanBody : CapturedMir :=
  { mkBody "w::funwcan" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gunwcan") [])] with
    fnAbi := unwFnAbi }

/-- `fn gmidnu() -> u32 { become gunwcan() }` (`canUnwind = false` middle hop). -/
def gMidNoUnwindBody : CapturedMir :=
  mkBody "w::gmidnu" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gunwcan") [])]

/-- `fn fhopnu() -> u32 { become gmidnu() }` (unwinding root, `!canUnwind` middle, unwinding last hop). -/
def fHopNoUnwindBody : CapturedMir :=
  { mkBody "w::fhopnu" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gmidnu") [])] with
    fnAbi := unwFnAbi }

/-- `fn kunw() -> u32 { resume }` (unwinding inline callee). -/
def kUnwindBody : CapturedMir :=
  { mkBody "w::kunw" 0 [u32Decl "_0"] [blk [] .unwindResume] with fnAbi := unwFnAbi }

/-- `fn gcallunw() -> u32 { _0 = kunw() -> [return: bb1, unwind: continue]; bb1: return }` (`!canUnwind`). -/
def gCallUnwindBody : CapturedMir :=
  mkBody "w::gcallunw" 0 [u32Decl "_0"]
    [blk [] (.call (fnItem "w::kunw") [] (lc 0) (some 1) .continue_), blk [] .return_]

/-- `fn fcallunw() -> u32 { become gcallunw() }` (unwinding root). -/
def fCallUnwindBody : CapturedMir :=
  { mkBody "w::fcallunw" 0 [u32Decl "_0"] [blk [] (.tailCall (fnItem "w::gcallunw") [])] with
    fnAbi := unwFnAbi }

/-- `fn rootunw() -> u32 { resume }` (a non-unwinding root that unwinds by itself). -/
def rootUnwindBody : CapturedMir := mkBody "w::rootunw" 0 [u32Decl "_0"] [blk [] .unwindResume]

/-- All Bug 2 witness callees. -/
def unwCallees : List CapturedMir :=
  [gUnwindBody, gUnwindCanBody, gMidNoUnwindBody, kUnwindBody, gCallUnwindBody]

/--
**Bug 2 at a modular root.**
1. `funw → become gunw()` with a non-unwinding `gunw` that unwinds: unpatched
   `Trusted` halts with `.panic` (`tailCall_leanMiri_witness_unwind`), the
   prototype faults with `.ub` (Miri: the inherited continuation is
   `Unreachable` — and at a 1-frame stack also "unwinding past the topmost
   stack frame").
2. Multi-hop: unwinding root → `!canUnwind` middle → unwinding last hop still
   faults with `.ub` (monotone ceiling).
3. A panic of an inline callee of a narrowed root tail callee unwinds through
   the root and faults with `.ub`.
4. `MODEL-LM-TAILCALL-MODULAR-ROOT` is preserved where no narrowing happened:
   an unwinding root tail-calling an unwinding callee, and a non-unwinding root
   that unwinds by itself, both halt with `.panic`.
-/
theorem tailCall_root_nounwind_callee_unwind_ub :
    execN fUnwindBody 2 (.running (initMachineStateWithCallees fUnwindBody [] unwCallees)) =
      some (.halted .panic) ∧
    execNProto fUnwindBody 2 (.running (initMachineStateWithCallees fUnwindBody [] unwCallees)) =
      some (.faulted .ub) ∧
    execNProto fHopNoUnwindBody 3
        (.running (initMachineStateWithCallees fHopNoUnwindBody [] unwCallees)) =
      some (.faulted .ub) ∧
    execNProto fCallUnwindBody 3
        (.running (initMachineStateWithCallees fCallUnwindBody [] unwCallees)) =
      some (.faulted .ub) ∧
    execNProto fUnwindCanBody 2
        (.running (initMachineStateWithCallees fUnwindCanBody [] unwCallees)) =
      some (.halted .panic) ∧
    execNProto rootUnwindBody 1
        (.running (initMachineStateWithCallees rootUnwindBody [] unwCallees)) =
      some (.halted .panic) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- A stacked chain of `.opaqueCast` projections `(… (_l as t₁) … as tₖ)`. -/
def opaqueCastChain : List Ty → List ProjectionElem
  | .nil => .nil
  | t :: ts => .opaqueCast t :: opaqueCastChain ts

@[simp]
theorem stripLeadingOpaqueCast_opaqueCastChain :
    ∀ ts : List Ty, stripLeadingOpaqueCast (opaqueCastChain ts) = .nil
  | .nil => rfl
  | _ :: ts => stripLeadingOpaqueCast_opaqueCastChain ts

theorem stripLeadingOpaqueCast_opaqueCastChain_append (rest : List ProjectionElem) :
    ∀ ts : List Ty,
      stripLeadingOpaqueCast (appendProjections (opaqueCastChain ts) rest) =
        stripLeadingOpaqueCast rest
  | .nil => by cases rest <;> rfl
  | _ :: ts => stripLeadingOpaqueCast_opaqueCastChain_append rest ts

/--
**Bug 4 universal simulation theorem (`opaqueCast_trusted_root_dispatch_simulation`).**
For every stacked chain `(… (_l as t₁) … as tₖ)` (`k ≥ 1`), every machine state,
locals, borrows, globals, layouts, caller locals, call stack, value, rvalue,
variant index, drop target, and unwind action, the `.opaqueCast` place behaves
exactly like its post-borrowck erasure `_l` evaluated by **unmodified
`Trusted`** (`evalOperand`, `writePlaceValue`, `evalStmt`, `evalTerminator`):
1. `move (_l as T…)` (untyped `localDecls = []`) = `Trusted.evalOperand (move _l)`
   (de-initializes `_l`),
2. root write on `.uninit`/`.init` locals = `Trusted.writePlaceValue _l`,
3. `(_l as T…) = rv` = `_l = rv` under the repaired `evalStmtProto`,
4. `Deinit((_l as T…))` = `Trusted` `Deinit(_l)` for *every* `localDecls`,
5. `SetDiscriminant((_l as T…), v)` = `Trusted` `SetDiscriminant(_l, v)` for
   *every* `localDecls`,
6. `Drop((_l as T…))` = `Trusted` `Drop(_l)`.
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
    (l variantIdx targetBb : Nat)
    (t : Ty)
    (ts : List Ty)
    (val : Value)
    (rv : Rvalue)
    (unwind : UnwindAction)
    (span : String)
    (cb : Option CapturedMir) :
    let ocs := opaqueCastChain (t :: ts)
    (evalOperandProto
        locals (.move ⟨l, ocs⟩) borrows globals layouts callerLocals .nil callStack =
      evalOperand
        locals (.move ⟨l, []⟩) borrows globals layouts callerLocals .nil callStack) ∧
    (writePlaceValueProto locals borrows ⟨l, ocs⟩ val .nil layouts callStack =
      writePlaceValue locals borrows ⟨l, []⟩ val .nil layouts callStack) ∧
    (evalStmtProto s ⟨.assign ⟨l, ocs⟩ rv, span⟩ .nil layouts =
      evalStmtProto s ⟨.assign ⟨l, []⟩ rv, span⟩ .nil layouts) ∧
    (evalStmtProto s ⟨.deinit ⟨l, ocs⟩, span⟩ localDecls layouts =
      evalStmt s ⟨.deinit ⟨l, []⟩, span⟩ localDecls layouts) ∧
    (evalStmtProto s ⟨.setDiscriminant ⟨l, ocs⟩ variantIdx, span⟩ localDecls layouts =
      evalStmt s ⟨.setDiscriminant ⟨l, []⟩ variantIdx, span⟩ localDecls layouts) ∧
    (evalTerminatorProto s ⟨.drop ⟨l, ocs⟩ targetBb unwind, span⟩ cb =
      evalTerminator s ⟨.drop ⟨l, []⟩ targetBb unwind, span⟩ cb) := by
  intro ocs
  have hStrip : stripLeadingOpaqueCast (opaqueCastChain ts) = .nil :=
    stripLeadingOpaqueCast_opaqueCastChain ts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ocs, opaqueCastChain, evalOperandProto, hStrip]
    rfl
  · simp only [ocs, opaqueCastChain, writePlaceValueProto, hStrip]
    rfl
  · simp only [ocs, opaqueCastChain, evalStmtProto, hStrip]
  · simp only [ocs, opaqueCastChain, evalStmtProto, hStrip]
    rfl
  · simp only [ocs, opaqueCastChain, evalStmtProto, hStrip]
  · simp only [ocs, opaqueCastChain, evalTerminatorProto, hStrip]
    rfl

/--
**Bug 4 with typed locals: validity is preserved, against the cast type.** For a
stacked chain on a declared local, the repaired root write validates `val`
against the type *after* the casts (`tₖ`, the erased local's type) and otherwise
performs `Trusted`'s erased root write; an invalid value still faults with `.ub`.
-/
theorem opaqueCast_typed_root_write_validates_cast_type
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (layouts : LayoutTable)
    (callStack : List SavedCallerFrame)
    (decl : LocalDecl)
    (declsTail : List LocalDecl)
    (l : Nat)
    (t : Ty)
    (ts : List Ty)
    (val : Value) :
    writePlaceValueProto locals borrows ⟨l, opaqueCastChain (t :: ts)⟩ val (decl :: declsTail)
        layouts callStack =
      match validateValueForTy? layouts
          (placeTy (decl :: declsTail) layouts ⟨l, opaqueCastChain (t :: ts)⟩) val with
      | false => .ub
      | true => writePlaceValue locals borrows ⟨l, []⟩ val .nil layouts callStack := by
  have hStrip : stripLeadingOpaqueCast (opaqueCastChain ts) = .nil :=
    stripLeadingOpaqueCast_opaqueCastChain ts
  simp only [opaqueCastChain, writePlaceValueProto, hStrip]
  cases validateValueForTy? layouts
      (placeTy (decl :: declsTail) layouts ⟨l, .opaqueCast t :: opaqueCastChain ts⟩) val <;> rfl

/--
**Bug 4 field shell through a cast: the shell of the erased local's type.**
`(_l as T).f = rv` on an `.uninit` declared local builds exactly the field shell
that `Trusted.uninitFieldWriteShell?` builds for a local of type `T` (the
post-borrowck erasure `_l : T`), whatever `_l`'s declared (opaque) type is.
-/
theorem opaqueCast_uninit_field_shell_is_cast_type_shell
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (l idx : Nat)
    (t fTy : Ty)
    (rest : List ProjectionElem)
    (decl : LocalDecl)
    (hDecl : get? localDecls l = .some decl) :
    uninitFieldWriteShellProto? localDecls layouts l (.opaqueCast t) (.field idx fTy :: rest) =
      uninitFieldWriteShell? [{ decl with ty := t }] layouts 0 (.field idx fTy) rest := by
  simp only [uninitFieldWriteShellProto?, uninitFieldWriteShell?,
    placeTy, hDecl, resolveProjectedTy]
  rfl

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

theorem takeLeadingOpaqueCast_opaqueCastChain_nonempty (t : Ty) (ts : List Ty) :
    takeLeadingOpaqueCast (opaqueCastChain (t :: ts)) = .opaqueCast t :: takeLeadingOpaqueCast (opaqueCastChain ts) :=
  rfl

/--
**Bug 4 return-destination simulation (`writeReturnDestinationProto_pure_opaqueCast_simulation`).**
For every stacked `.opaqueCast` chain `(_l as t₁ ... as tₖ)` (`k ≥ 1`), returning
from a callee into `destination = ⟨l, opaqueCastChain (t :: ts)⟩` under
`writeReturnDestinationProto` (untyped `localDecls = []`) is identical to
`Trusted.writeReturnDestination` into the erased root local `⟨l, []⟩` (in
particular succeeding when `_l` is `.uninit`, whereas unpatched
`Trusted.writeReturnDestination` faults with `.ub`).
-/
theorem writeReturnDestinationProto_pure_opaqueCast_simulation
    (callerLocals : List LocalSlot)
    (mem : Memory)
    (l : Nat)
    (t : Ty)
    (ts : List Ty)
    (retVal : Value)
    (layouts : LayoutTable) :
    writeReturnDestinationProto callerLocals mem ⟨l, opaqueCastChain (t :: ts)⟩ retVal .nil layouts =
      writeReturnDestination callerLocals mem ⟨l, []⟩ retVal .nil layouts := by
  have hStrip : stripLeadingOpaqueCast (opaqueCastChain ts) = .nil :=
    stripLeadingOpaqueCast_opaqueCastChain ts
  simp only [opaqueCastChain, writeReturnDestinationProto, takeLeadingOpaqueCast,
    eraseLeadingOpaqueCastDecls, get?, List.getElem?_nil, hStrip]

end Anneal.TcbCopySubplaceAndTailCallPrototype

