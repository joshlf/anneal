import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import MiniRust.LibSpecr
import MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
import Correspondence.Framework
import Correspondence.GeneratedGaps
import Correspondence.GeneratedGapWitnesses

namespace Correspondence.V2026_06_01.L5_ControlAndCalls

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRust.LibSpecr
open MiniRust.Snapshots.S2026_05_Matched.Generated.Ops
open Correspondence

/-!
Horizontal Correspondence Slice L5: Control Flow, Terminators, and Procedure Calls
(`Trusted.Rustc.V2026_06_01.MirSemantics.Statements` and
`Trusted.Rustc.V2026_06_01.MirSemantics.Terminators` vs. mechanically extracted
`MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`).

Every theorem in this module universally quantifies (`∀`) over real Anneal TCB
machine states, statements, terminators, and call stacks and proves exact
equational correspondence against the mechanically generated MiniRust operational
definitions in `MiniRust.Snapshots.S2026_05_Matched.Generated.Ops`
(`spec/lang/machine.md` and `spec/lang/step/terminators.md`).
-/

/-- Project an Anneal `StackFrame`'s program-counter coordinates (`blockIdx` and
`stmtIdx`) into MiniRust's mechanically extracted `MrStackFrame` record
(`spec/lang/machine.md:30-34`). -/
def toMrStackFrame (frame : StackFrame) : MrStackFrame :=
  { blockIdx := frame.blockIdx, stmtIdx := frame.stmtIdx }

@[simp]
private theorem lookupCallee_nil
    (callerLayouts : LayoutTable)
    (defPath : DefPath)
    (typeArgs : List RigidTy) :
    lookupCallee .nil callerLayouts defPath typeArgs .nil = .none := by
  cases typeArgs with
  | nil => rfl
  | cons hd _ =>
    cases hd <;> rfl

/-! ## 1. Statement Program Counter & Local Lifecycle Correspondence -/

/-- Universal correspondence between Anneal's `advanceStmt` helper
(`Statements.lean:36-38`) and MiniRust's statement program-counter increment
`Generated.Ops.mrAdvanceStmtPc` (`spec/lang/machine.md:185-223`):
`advanceStmt s locals' mem'` increments `s.frame.stmtIdx` by `1` while
preserving `blockIdx`, updating `locals` to `locals'`, and updating `memory` to
`mem'`. -/
theorem mir_advanceStmt_corresponds
    (s : MachineState) (locals' : List LocalSlot) (mem' : Memory) :
    (advanceStmt s locals' mem').frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx ∧
    (advanceStmt s locals' mem').frame.blockIdx = s.frame.blockIdx ∧
    (advanceStmt s locals' mem').frame.locals = locals' ∧
    (advanceStmt s locals' mem').memory = mem' ∧
    toMrStackFrame (advanceStmt s locals' mem').frame =
      { toMrStackFrame s.frame with stmtIdx := mrAdvanceStmtPc s.frame.stmtIdx } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Universal correspondence for no-op and instrumentation statements
(`Statements.lean:774-776`): `.nop`, `.coverage`, and `.constEvalCounter` step
deterministically to `advanceStmt s s.frame.locals` with `stmtIdx` incremented
according to `Generated.Ops.mrAdvanceStmtPc`. -/
theorem mir_evalStmt_nop_coverage_constEvalCounter
    (s : MachineState) (span : String) :
    evalStmt s ⟨.nop, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.coverage, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    evalStmt s ⟨.constEvalCounter, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    (advanceStmt s s.frame.locals).frame.stmtIdx = mrAdvanceStmtPc s.frame.stmtIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Universal characterization of `StatementKind.placeMention`
(`Statements.lean` vs. `spec/lang/step/statements.md`): mentioning an
out-of-bounds or `.dead` local faults with `MirStepNode.fail .ub`; mentioning a
live (`.uninit` or `.init`) local advances the statement program counter without
mutating locals or memory exactly when every operand read while computing the
place is initialized, i.e. a dereferenced root local holds a value and every
`Index` local holds an initialized scalar (`placeMentionOperandsInit`), and
faults with `MirStepNode.fail .ub` otherwise. In particular, a bare mention of
an uninitialized local (`place.projection = []`) steps, whereas dereferencing an
uninitialized root local or indexing by an uninitialized local faults. -/
theorem mir_evalStmt_placeMention_dead_is_ub
    (s : MachineState) (place : Place) (span : String) :
    (get? s.frame.locals place.local_ = .none →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals place.local_ = .some .dead →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals place.local_ = .some .uninit →
      projectionHasDeref place.projection = false →
      placeIndexLocalsInit s.frame.locals place.projection = true →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    (∀ v : Value, get? s.frame.locals place.local_ = .some (.init v) →
      placeIndexLocalsInit s.frame.locals place.projection = true →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    (get? s.frame.locals place.local_ = .some .uninit →
      place.projection = .nil →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    (get? s.frame.locals place.local_ = .some .uninit →
      projectionHasDeref place.projection = true →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) ∧
    (∀ slot : LocalSlot, get? s.frame.locals place.local_ = .some slot →
      placeIndexLocalsInit s.frame.locals place.projection = false →
      evalStmt s ⟨.placeMention place, span⟩ = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [evalStmt, h]
  · intro h; simp [evalStmt, h]
  · intro h hDeref hIdx
    simp [evalStmt, placeMentionOperandsInit, h, hDeref, hIdx]
  · intro v h hIdx
    cases hDeref : projectionHasDeref place.projection <;>
      simp [evalStmt, placeMentionOperandsInit, h, hDeref, hIdx]
  · intro h hNil
    simp [evalStmt, h, hNil]
  · intro h hDeref
    simp [evalStmt, placeMentionOperandsInit, h, hDeref]
  · intro slot h hIdx
    cases slot <;> cases hDeref : projectionHasDeref place.projection <;>
      simp [evalStmt, placeMentionOperandsInit, h, hDeref, hIdx]

/-- Universal characterization of `StatementKind.storageLive`,
`StatementKind.storageDead`, and protected-tag write conflict checking in
`evalStmt` (`Statements.lean`):
1. `.storageLive loc` transitions an in-bounds slot to `.uninit` and disables
   every borrow-table entry minted from `loc` (`disableLocalBorrows`) unless an
   entry targeting `loc` is still protected by an active function-entry
   protector (`hasProtectedLocalBorrow`), in which case it faults with `.ub`,
   or faults with `.ub` if `loc` is out of bounds;
2. `.storageDead loc` transitions an in-bounds slot to `.dead` and disables
   every borrow-table entry minted from `loc` unless an entry targeting `loc` is
   still protected by an active function-entry protector
   (`hasProtectedLocalBorrow`), in which case it faults with `.ub`, or faults
   with `.ub` if `loc` is out of bounds;
3. Disabling leaves every entry targeting `loc` `.disabled` (so no stale tag can
   reach a revived `loc`) and is the identity when no entry targets `loc`; and
4. Writing to a root local when `hasProtectedWriteConflict` is `true` faults
   immediately with `MirStepNode.fail .ub`. -/
theorem mir_evalStmt_storageLive_and_storageDead
    (s : MachineState) (loc : Local) (slot : LocalSlot)
    (localsUninit localsDead : List LocalSlot) (span : String) :
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false →
      evalStmt s ⟨.storageLive loc, span⟩ =
        MirStepNode.step
          (advanceStmt s localsUninit
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = true →
      evalStmt s ⟨.storageLive loc, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageLive loc, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false →
      evalStmt s ⟨.storageDead loc, span⟩ =
        MirStepNode.step
          (advanceStmt s localsDead
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = true →
      evalStmt s ⟨.storageDead loc, span⟩ = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageDead loc, span⟩ = MirStepNode.fail .ub) ∧
    (∀ entry ∈ disableLocalBorrows s.memory.borrows loc,
      entry.targetLocal = loc → entry.perm = .disabled) ∧
    ((∀ entry ∈ s.memory.borrows, entry.targetLocal ≠ loc) →
      disableLocalBorrows s.memory.borrows loc = s.memory.borrows) ∧
    (∀ (rv : Rvalue) (val : Value) (locals₁ locals₂ : List LocalSlot) (mem₁ : Memory)
       (protHead : Nat) (protTail : List Nat),
      evalRvalue s.frame.locals rv s.memory = .ok val locals₁ mem₁ →
      get? locals₁ loc = .some .uninit →
      set? locals₁ loc (.init val) = .some locals₂ →
      mem₁.activeProtectors = protHead :: protTail →
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) loc .none .nil = true →
      evalStmt s ⟨.assign ⟨loc, .nil⟩ rv, span⟩ = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hGet hSet hP
    cases hAP : s.memory.activeProtectors with
    | nil => simp [evalStmt, hGet, hSet, hAP]
    | cons p ps =>
      rw [hAP] at hP
      simp [evalStmt, hGet, hSet, hAP, hP]
  · intro hGet hSet hP
    cases hAP : s.memory.activeProtectors with
    | nil =>
      rw [hAP, hasProtectedLocalBorrow_nil_protectors] at hP
      nomatch hP
    | cons p ps =>
      rw [hAP] at hP
      simp [evalStmt, hGet, hSet, hAP, hP]
  · intro hGet; simp [evalStmt, hGet]
  · intro hGet hSet hP
    cases hAP : s.memory.activeProtectors with
    | nil => simp [evalStmt, hGet, hSet, hAP]
    | cons p ps =>
      rw [hAP] at hP
      simp [evalStmt, hGet, hSet, hAP, hP]
  · intro hGet hSet hP
    cases hAP : s.memory.activeProtectors with
    | nil =>
      rw [hAP, hasProtectedLocalBorrow_nil_protectors] at hP
      nomatch hP
    | cons p ps =>
      rw [hAP] at hP
      simp [evalStmt, hGet, hSet, hAP, hP]
  · intro hGet; simp [evalStmt, hGet]
  · exact perm_eq_disabled_of_mem_disableLocalBorrows s.memory.borrows loc
  · exact disableLocalBorrows_eq_self_of_forall_ne s.memory.borrows loc
  · intro rv val locals₁ locals₂ mem₁ protHead protTail hEval hGet hSet hProt hConflict
    simp [evalStmt, hEval, hGet, hSet, hProt, hConflict]

/--
`disableLocalBorrows` preserves the length of the borrow table (`Trusted.Sequence.length`),
ensuring that fuel bounds parameterized by `Trusted.Sequence.length borrows` (such as
`isBorrowDescendantOrSelf`) are unchanged.
-/
@[simp]
theorem length_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local) :
    Trusted.Sequence.length (disableLocalBorrows borrows loc) =
      Trusted.Sequence.length borrows := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases hB : Nat.beq hd.targetLocal loc <;>
      simp [disableLocalBorrows, Trusted.Sequence.length, hB] at ih ⊢ <;>
        exact ih

/--
`disableLocalBorrows` is idempotent on the same local: disabling `loc`'s
borrows a second time (e.g. when `StorageLive(loc)` follows `StorageDead(loc)`)
produces the identical borrow table.
-/
@[simp]
theorem disableLocalBorrows_idem
    (borrows : List BorrowEntry)
    (loc : Local) :
    disableLocalBorrows (disableLocalBorrows borrows loc) loc =
      disableLocalBorrows borrows loc := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases hB : Nat.beq hd.targetLocal loc <;>
      simp only [disableLocalBorrows, hB, ih]

/--
`disableLocalBorrows` commutes across arbitrary locals `loc₁` and `loc₂`.
-/
theorem disableLocalBorrows_comm
    (borrows : List BorrowEntry)
    (loc₁ loc₂ : Local) :
    disableLocalBorrows (disableLocalBorrows borrows loc₁) loc₂ =
      disableLocalBorrows (disableLocalBorrows borrows loc₂) loc₁ := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases h₁ : Nat.beq hd.targetLocal loc₁ <;>
      cases h₂ : Nat.beq hd.targetLocal loc₂ <;>
        simp only [disableLocalBorrows, h₁, h₂, ih]

/--
Disabling borrows targeting `loc₁` preserves `hasProtectedLocalBorrow` for
every local `loc₂`, because `disableLocalBorrows` modifies only `perm` while
preserving `targetLocal` and `protector`.
-/
@[simp]
theorem hasProtectedLocalBorrow_disableLocalBorrows
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (loc₁ loc₂ : Local) :
    hasProtectedLocalBorrow (disableLocalBorrows borrows loc₁) activeProtectors loc₂ =
      hasProtectedLocalBorrow borrows activeProtectors loc₂ := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases h₁ : Nat.beq hd.targetLocal loc₁ with
    | false =>
      cases hC : Bool.and (Nat.beq hd.targetLocal loc₂) (isBorrowProtected activeProtectors hd) <;>
        simp only [disableLocalBorrows, h₁, hasProtectedLocalBorrow, hC, ih]
    | true =>
      have hProt :
          isBorrowProtected activeProtectors { hd with perm := .disabled } =
            isBorrowProtected activeProtectors hd := rfl
      cases hC : Bool.and (Nat.beq hd.targetLocal loc₂) (isBorrowProtected activeProtectors hd) <;>
        simp only [disableLocalBorrows, h₁, hasProtectedLocalBorrow, hProt, hC, ih]

/--
`disableLocalBorrows` preserves the parent-tag chain (`tag` and `parentTag`) of
every entry in `borrows`, so Tree Borrows ancestor-descendant reachability
(`isBorrowDescendantOrSelfAux`) is invariant under `disableLocalBorrows`.
-/
theorem isBorrowDescendantOrSelfAux_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    (fuel candidateTag ancestorTag : Nat) :
    isBorrowDescendantOrSelfAux fuel (disableLocalBorrows borrows loc) candidateTag ancestorTag =
      isBorrowDescendantOrSelfAux fuel borrows candidateTag ancestorTag := by
  induction fuel generalizing candidateTag with
  | zero => rfl
  | succ fuel' ih =>
    unfold isBorrowDescendantOrSelfAux
    cases hEq : Nat.beq candidateTag ancestorTag with
    | true => rfl
    | false =>
      dsimp only
      rw [lookupBorrow_disableLocalBorrows]
      cases hLook : lookupBorrow borrows candidateTag with
      | none => rfl
      | some entry =>
        dsimp only
        cases hB : Nat.beq entry.targetLocal loc <;>
          cases hP : entry.parentTag <;>
            simp only [hP] <;>
              exact ih _

/--
Tree Borrows ancestor-descendant reachability (`isBorrowDescendantOrSelf`) is
invariant under `disableLocalBorrows`.
-/
@[simp]
theorem isBorrowDescendantOrSelf_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    (candidateTag ancestorTag : Nat) :
    isBorrowDescendantOrSelf (disableLocalBorrows borrows loc) candidateTag ancestorTag =
      isBorrowDescendantOrSelf borrows candidateTag ancestorTag := by
  unfold isBorrowDescendantOrSelf
  rw [length_disableLocalBorrows, isBorrowDescendantOrSelfAux_disableLocalBorrows]

/--
Two-step `StorageDead(loc)` followed by `StorageLive(loc)` revival theorem
(`D2` / `D14a-storage`): when `loc` is in bounds and unprotected
(`hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false`),
executing `StorageDead(loc)` and then `StorageLive(loc)` steps cleanly in both
transitions without faulting, advances `stmtIdx` twice, sets `loc` to `.uninit`
(`localsRevived`), and leaves the borrow table equal to the single pass
`disableLocalBorrows s.memory.borrows loc` (by `disableLocalBorrows_idem`),
preserving `hasProtectedLocalBorrow` and `isBorrowDescendantOrSelf`.
-/
theorem evalStmt_storageDead_then_storageLive_revive
    (s : MachineState)
    (loc loc₂ : Local)
    (slot : LocalSlot)
    (localsDead localsRevived : List LocalSlot)
    (spanDead spanLive : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (candidateTag ancestorTag : Nat)
    (hGet : get? s.frame.locals loc = .some slot)
    (hSetDead : set? s.frame.locals loc .dead = .some localsDead)
    (hGetDead : get? localsDead loc = .some .dead)
    (hSetRevived : set? localsDead loc .uninit = .some localsRevived)
    (hNoProt : hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false) :
    let borrowsDis := disableLocalBorrows s.memory.borrows loc
    let memDis : Memory := { s.memory with borrows := borrowsDis }
    let sDead : MachineState := advanceStmt s localsDead memDis
    let sRevived : MachineState := advanceStmt sDead localsRevived memDis
    evalStmt s ⟨.storageDead loc, spanDead⟩ localDecls layouts =
      MirStepNode.step sDead ∧
    disableLocalBorrows borrowsDis loc = borrowsDis ∧
    evalStmt sDead ⟨.storageLive loc, spanLive⟩ localDecls layouts =
      MirStepNode.step sRevived ∧
    hasProtectedLocalBorrow borrowsDis s.memory.activeProtectors loc₂ =
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc₂ ∧
    isBorrowDescendantOrSelf borrowsDis candidateTag ancestorTag =
      isBorrowDescendantOrSelf s.memory.borrows candidateTag ancestorTag := by
  dsimp only
  have hDeadStep :
      evalStmt s ⟨.storageDead loc, spanDead⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s localsDead
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) :=
    ((evalStmt_storageDead_purges_borrows
        s loc slot localsDead spanDead localDecls layouts).1
      hGet hSetDead hNoProt).1
  have hIdem :
      disableLocalBorrows (disableLocalBorrows s.memory.borrows loc) loc =
        disableLocalBorrows s.memory.borrows loc :=
    disableLocalBorrows_idem s.memory.borrows loc
  have hNoProtDis :
      hasProtectedLocalBorrow
        (disableLocalBorrows s.memory.borrows loc)
        s.memory.activeProtectors
        loc = false := by
    rw [hasProtectedLocalBorrow_disableLocalBorrows]
    exact hNoProt
  have hLiveStep :
      evalStmt
        (advanceStmt s localsDead
          { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
        ⟨.storageLive loc, spanLive⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt
            (advanceStmt s localsDead
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
            localsRevived
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) := by
    have hRaw :=
      ((evalStmt_storageLive_purges_borrows
          (advanceStmt s localsDead
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
          loc .dead localsRevived spanLive localDecls layouts).1
        hGetDead hSetRevived hNoProtDis).1
    dsimp [advanceStmt] at hRaw ⊢
    rw [hIdem] at hRaw
    exact hRaw
  refine ⟨hDeadStep, hIdem, hLiveStep,
    hasProtectedLocalBorrow_disableLocalBorrows s.memory.borrows s.memory.activeProtectors loc loc₂,
    isBorrowDescendantOrSelf_disableLocalBorrows s.memory.borrows loc candidateTag ancestorTag⟩

/-- Algebraic and structural invariants of `disableLocalBorrows` and two-step
`StorageDead(loc)` + `StorageLive(loc)` revival (`Statements.lean`):
1. `disableLocalBorrows` is idempotent on the same local (`disableLocalBorrows_idem`),
2. `disableLocalBorrows` commutes across locals (`disableLocalBorrows_comm`),
3. `disableLocalBorrows` preserves borrow-table length (`length_disableLocalBorrows`),
   active-protector conflict status (`hasProtectedLocalBorrow_disableLocalBorrows`),
   and Tree Borrows ancestor-descendant reachability
   (`isBorrowDescendantOrSelf_disableLocalBorrows`), and
4. Executing `StorageDead(loc)` followed by `StorageLive(loc)` steps cleanly in
   two steps to the idempotently disabled borrow table
   (`evalStmt_storageDead_then_storageLive_revive`). -/
theorem mir_disableLocalBorrows_algebraic_properties
    (s : MachineState) (loc loc₂ : Local) (slot : LocalSlot)
    (localsDead localsRevived : List LocalSlot)
    (spanDead spanLive : String) (candidateTag ancestorTag : Nat) :
    disableLocalBorrows (disableLocalBorrows s.memory.borrows loc) loc =
      disableLocalBorrows s.memory.borrows loc ∧
    disableLocalBorrows (disableLocalBorrows s.memory.borrows loc) loc₂ =
      disableLocalBorrows (disableLocalBorrows s.memory.borrows loc₂) loc ∧
    Trusted.Sequence.length (disableLocalBorrows s.memory.borrows loc) =
      Trusted.Sequence.length s.memory.borrows ∧
    hasProtectedLocalBorrow (disableLocalBorrows s.memory.borrows loc)
      s.memory.activeProtectors loc₂ =
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc₂ ∧
    isBorrowDescendantOrSelf (disableLocalBorrows s.memory.borrows loc)
      candidateTag ancestorTag =
      isBorrowDescendantOrSelf s.memory.borrows candidateTag ancestorTag ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      get? localsDead loc = .some .dead →
      set? localsDead loc .uninit = .some localsRevived →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false →
      let memDis : Memory := { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }
      let sDead : MachineState := advanceStmt s localsDead memDis
      let sRevived : MachineState := advanceStmt sDead localsRevived memDis
      evalStmt s ⟨.storageDead loc, spanDead⟩ = MirStepNode.step sDead ∧
      evalStmt sDead ⟨.storageLive loc, spanLive⟩ = MirStepNode.step sRevived) := by
  refine ⟨disableLocalBorrows_idem s.memory.borrows loc,
    disableLocalBorrows_comm s.memory.borrows loc loc₂,
    length_disableLocalBorrows s.memory.borrows loc,
    hasProtectedLocalBorrow_disableLocalBorrows s.memory.borrows s.memory.activeProtectors loc loc₂,
    isBorrowDescendantOrSelf_disableLocalBorrows s.memory.borrows loc candidateTag ancestorTag,
    ?_⟩
  intro hGet hSetDead hGetDead hSetRevived hNoProt
  have hRev :=
    evalStmt_storageDead_then_storageLive_revive
      s loc loc₂ slot localsDead localsRevived spanDead spanLive .nil emptyLayoutTable
      candidateTag ancestorTag hGet hSetDead hGetDead hSetRevived hNoProt
  exact ⟨hRev.1, hRev.2.2.1⟩

/-- Unified correspondence consumer for the remaining `Statements.lean`
universal characterizations of `StorageDead`/`StorageLive` borrow-table framing,
protector conflict subsumption, post-revival stale-pointer dereference UB
(including `StatementKind.setDiscriminant`), and `PlaceMention` operand
initialization (including the biconditional `evalStmt_placeMention_nonDeref_index_iff`):
1. `hasProtectedLocalBorrow_of_hasProtectedWriteConflict`: whole-local write
   protector conflicts imply deallocation protector conflicts;
2. `lookupBorrow_disableLocalBorrows_of_targetLocal_ne` and
   `lookupBorrow_disableLocalBorrows_of_eq_none`: `disableLocalBorrows` preserves
   tags targeting other stack locals and leaves non-stack (global) tags unresolved;
3. `evalStmt_storageRevive_old_ptr_deref_ub`: any tag targeting `loc` resolves to
   `.disabled` after `disableLocalBorrows` and faults with `.ub` across all 10
   dereferencing read, write, reborrow, retag, `setDiscriminant`, and
   non-zero-length `copy_nonoverlapping` operations; and
4. `evalStmt_placeMention_local_uninit_ok`, `evalStmt_placeMention_deref_init_ok`,
   `evalStmt_placeMention_deref_uninit_ub`, and
   `evalStmt_placeMention_nonDeref_index_iff`: complete characterization of
   `StatementKind.placeMention` across bare, dereferencing, and non-dereferencing
   projection paths. -/
theorem mir_storageRevive_and_placeMention_characterizations
    (s : MachineState) (loc ptrLoc : Local) (tag n : Nat)
    (slot : LocalSlot) (v writeVal otherVal : Value)
    (ptrVal : ProvenancePtr) (sz : Nat)
    (proj restProj : List ProjectionElem) (localsAfter : List LocalSlot)
    (borrowKind : BorrowKind) (retagKind : RetagKind) (span : String)
    (srcOp dstOp : Operand) (entry : BorrowEntry)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors loc .none .nil = true →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = true) ∧
    (lookupBorrow s.memory.borrows tag = .some entry →
      entry.targetLocal ≠ loc →
      lookupBorrow (disableLocalBorrows s.memory.borrows loc) tag = .some entry) ∧
    (lookupBorrow s.memory.borrows tag = .none →
      lookupBorrow (disableLocalBorrows s.memory.borrows loc) tag = .none) ∧
    (lookupBorrow s.memory.borrows ptrVal.tag = .some entry →
      entry.targetLocal = loc →
      get? localsAfter ptrLoc = .some (.init (.ptr ptrVal sz)) →
      let borrowsAfter := disableLocalBorrows s.memory.borrows loc
      let derefPlace : Place := { local_ := ptrLoc, projection := .deref :: restProj }
      let sAfter : MachineState :=
        { s with
          frame := { s.frame with locals := localsAfter }
          memory := { s.memory with borrows := borrowsAfter } }
      lookupBorrow borrowsAfter ptrVal.tag = .some { entry with perm := .disabled } ∧
      evalStmt sAfter ⟨.setDiscriminant derefPlace n, span⟩ localDecls layouts =
        MirStepNode.fail .ub) ∧
    ((get? s.frame.locals loc = .some .uninit →
        evalStmt s ⟨.placeMention ⟨loc, .nil⟩, span⟩ localDecls layouts =
          MirStepNode.step (advanceStmt s s.frame.locals)) ∧
      (get? s.frame.locals loc = .some (.init v) →
        placeIndexLocalsInit s.frame.locals restProj = true →
        evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
          MirStepNode.step (advanceStmt s s.frame.locals)) ∧
      (get? s.frame.locals loc = .some slot →
        placeIndexLocalsInit s.frame.locals restProj = false →
        evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
          MirStepNode.fail .ub) ∧
      (projectionHasDeref proj = false →
        get? s.frame.locals loc = .some slot →
        slot ≠ .dead →
        (evalStmt s ⟨.placeMention ⟨loc, proj⟩, span⟩ localDecls layouts =
            MirStepNode.step (advanceStmt s s.frame.locals) ↔
          placeIndexLocalsInit s.frame.locals proj = true) ∧
        (evalStmt s ⟨.placeMention ⟨loc, proj⟩, span⟩ localDecls layouts =
            MirStepNode.fail .ub ↔
          placeIndexLocalsInit s.frame.locals proj = false))) := by
  refine ⟨
    hasProtectedLocalBorrow_of_hasProtectedWriteConflict
      s.memory.borrows s.memory.activeProtectors loc,
    lookupBorrow_disableLocalBorrows_of_targetLocal_ne
      s.memory.borrows loc tag entry,
    lookupBorrow_disableLocalBorrows_of_eq_none
      s.memory.borrows loc tag,
    fun hLook hTarget hPtr =>
      let hAll :=
        evalStmt_storageRevive_old_ptr_deref_ub
          s s.memory.borrows s.memory.globals s.memory.callerLocals
          s.memory.activeProtectors localDecls layouts s.memory
          loc ptrLoc ptrVal sz restProj localsAfter writeVal borrowKind
          retagKind span srcOp dstOp otherVal n entry hLook hTarget hPtr
      ⟨hAll.1, hAll.2.2.2.2.2.2.2.2.1⟩,
    ⟨(evalStmt_placeMention_local_uninit_ok s loc span localDecls layouts).1,
      evalStmt_placeMention_deref_init_ok s loc v restProj span localDecls layouts,
      (evalStmt_placeMention_deref_uninit_ub s loc restProj span localDecls layouts).2.2.2 slot,
      evalStmt_placeMention_nonDeref_index_iff s loc slot proj span localDecls layouts⟩⟩

/-! ## 2. Terminator Dispatch, Unwinding, and Call-Stack Correspondence -/

/-- Universal proof by structural induction on `branches : List (Nat × BasicBlockIdx)`
that Anneal's `lookupSwitchTarget` (`Terminators.lean:31-38`) is identical to
MiniRust's mechanically extracted `Generated.Ops.mrLookupSwitchTarget`
(`spec/lang/step/terminators.md:38-45`) for all `val`, `branches`, and `otherwise`. -/
theorem mir_lookupSwitchTarget_corresponds
    (val : Nat) (branches : List (Nat × BasicBlockIdx)) (otherwise : BasicBlockIdx) :
    lookupSwitchTarget val branches otherwise =
      mrLookupSwitchTarget val branches otherwise := by
  induction branches with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨branchVal, targetBb⟩
    cases h : Nat.beq val branchVal <;>
      simp [lookupSwitchTarget, mrLookupSwitchTarget, h, ih]

/-- Reflexivity of `listByteEq` over arbitrary byte sequences (`State.lean:557`). -/
theorem listByteEq_refl (xs : List UInt8) : listByteEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp [listByteEq, Nat.beq_refl, ih]

/-- Reflexivity of `stringEq` over arbitrary `String` values (`State.lean:568`). -/
theorem stringEq_refl (s : String) : stringEq s s = true :=
  listByteEq_refl s.toByteArray.data.toList

/-- Universal proof by induction on `callees : List CapturedMir` that Anneal's
`findCallee?` (`Terminators.lean:43-49`) returns the first captured MIR body
whose `defPath` matches `defPath`, corresponding to MiniRust's callee table
lookup `Generated.Ops.mrFindCalleeById` (`spec/lang/machine.md:321-337`). -/
theorem mir_findCallee_corresponds
    (callees : List CapturedMir) (defPath : String) :
    findCallee? callees defPath =
      callees.find? (fun body => stringEq body.defPath defPath) ∧
    (∀ (body : CapturedMir) (rest : List CapturedMir),
      body.defPath = defPath →
      findCallee? (body :: rest) defPath = .some body) ∧
    (∀ (body : CapturedMir) (rest : List (String × CapturedMir)),
      body.defPath = defPath →
      mrFindCalleeById ((body.defPath, body) :: rest) defPath = .some body) ∧
    (∀ (body : CapturedMir) (rest : List CapturedMir),
      stringEq body.defPath defPath = false →
      findCallee? (body :: rest) defPath = findCallee? rest defPath) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · induction callees with
    | nil => rfl
    | cons body rest ih =>
      cases h : stringEq body.defPath defPath <;>
        simp [findCallee?, List.find?, h, ih]
  · intro body rest hEq
    subst hEq
    simp [findCallee?, stringEq_refl]
  · intro body rest hEq
    subst hEq
    simp [mrFindCalleeById]
  · intro body rest hNe
    simp [findCallee?, hNe]

/-- Universal characterization of `applyUnwindAction` (`Terminators.lean:581-598`)
across all four `UnwindAction` constructors (`.unreachable`, `.terminate`,
`.continue_`, `.cleanup bb`), paired with the corresponding outcomes of
MiniRust's mechanically extracted `Generated.Ops.mrApplyUnwindAction`
(`spec/lang/step/terminators.md:385-455`). -/
theorem mir_applyUnwindAction_characterization
    (s : MachineState) (localsAfter : List LocalSlot) (memAfter : Memory)
    (bb : BasicBlockIdx) :
    (applyUnwindAction s localsAfter memAfter .unreachable = .faulted .ub ∧
      mrApplyUnwindAction none false true = .faultUb) ∧
    (applyUnwindAction s localsAfter memAfter .terminate = .halted .abort ∧
      mrApplyUnwindAction none true false = .abort) ∧
    (applyUnwindAction s localsAfter memAfter .continue_ =
        unwindFromCallStack memAfter.callStack memAfter ∧
      (memAfter.callStack = .nil →
        applyUnwindAction s localsAfter memAfter .continue_ = .halted .panic) ∧
      mrApplyUnwindAction none false false = .panic) ∧
    (applyUnwindAction s localsAfter memAfter (.cleanup bb) =
      .running
        { frame := { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter }
          memory := memAfter } ∧
      mrApplyUnwindAction (some bb) false false = .cleanup bb ∧
      toMrStackFrame { s.frame with blockIdx := bb, stmtIdx := 0, locals := localsAfter } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) bb) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, ?_, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  intro hNil
  simp [applyUnwindAction, hNil]

/-- Universal correspondence for `TerminatorKind.goto` (`Terminators.lean:231-235`
vs. `Generated.Ops.MrStackFrame.jump_to_block` at `spec/lang/step/terminators.md:20-30`):
`evalTerminator s ⟨.goto target, span⟩ currentBody` jumps to `target` with
`stmtIdx := 0`, matching `MrStackFrame.jump_to_block`. -/
theorem mir_evalTerminator_goto_corresponds
    (s : MachineState) (target : BasicBlockIdx) (span : String)
    (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.goto target, span⟩ currentBody =
      MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } } ∧
    toMrStackFrame { s.frame with blockIdx := target, stmtIdx := 0 } =
      MrStackFrame.jump_to_block (toMrStackFrame s.frame) target := by
  exact ⟨rfl, rfl⟩

/-- Universal correspondence for `TerminatorKind.unreachable`
(`Terminators.lean:271` vs. `spec/lang/step/terminators.md:53-56`): reaching an
`.unreachable` terminator immediately faults with `MirStepNode.fail .ub`. -/
theorem mir_evalTerminator_unreachable_is_ub
    (s : MachineState) (span : String) (currentBody : Option CapturedMir) :
    evalTerminator s ⟨.unreachable, span⟩ currentBody = MirStepNode.fail .ub := by
  rfl

/-- Universal characterization of `TerminatorKind.return_` (`Terminators.lean:236-270`
vs. `spec/lang/step/terminators.md:323-373`) across both root-frame return
(`callStack = []`, corresponding to `StackPopAction.BottomOfStack`) and
interprocedural caller-frame return (`callStack = caller :: restStack`,
corresponding to `StackPopAction.BackToCaller` and `MrStackFrame.jump_to_block`),
as well as faulting with `MirStepNode.fail .ub` when `_0` is `.uninit`, `.dead`,
or when returning to a diverging caller frame (`caller.isDiverging = true`). -/
theorem mir_evalTerminator_return_root_and_caller
    (s : MachineState) (span : String) (currentBody : Option CapturedMir) :
    (∀ retVal : Value,
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = .nil →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.retNormal retVal s.memory) ∧
    (∀ (retVal : Value) (caller : SavedCallerFrame) (restStack : List SavedCallerFrame)
       (updatedCallerLocals : List LocalSlot),
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = caller :: restStack →
      caller.isDiverging = false →
      caller.callerProtector = .none →
      writePlaceValue caller.frame.locals s.memory.borrows caller.destination retVal =
        .ok updatedCallerLocals →
      evalTerminator s ⟨.return_, span⟩ currentBody =
        MirStepNode.step
          { frame :=
              { caller.frame with
                blockIdx := caller.returnTarget
                stmtIdx := 0
                locals := updatedCallerLocals }
            memory :=
              { s.memory with
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := caller.calleeProtectors } } ∧
      toMrStackFrame
          { caller.frame with
            blockIdx := caller.returnTarget
            stmtIdx := 0
            locals := updatedCallerLocals } =
        MrStackFrame.jump_to_block (toMrStackFrame caller.frame) caller.returnTarget) ∧
    (∀ (retVal : Value) (caller : SavedCallerFrame) (restStack : List SavedCallerFrame),
      get? s.frame.locals 0 = .some (.init retVal) →
      s.memory.callStack = caller :: restStack →
      caller.isDiverging = true →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (get? s.frame.locals 0 = .some .uninit →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (get? s.frame.locals 0 = .some .dead →
      evalTerminator s ⟨.return_, span⟩ currentBody = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro retVal hRet hStack
    simp [evalTerminator, hRet, hStack]
  · intro retVal caller restStack updatedCallerLocals hRet hStack hDiv hProt hWrite
    refine ⟨?_, rfl⟩
    simp [evalTerminator, hRet, hStack, hDiv, hProt, hWrite]
  · intro retVal caller restStack hRet hStack hDiv
    simp [evalTerminator, hRet, hStack, hDiv]
  · intro hUninit
    simp [evalTerminator, hUninit]
  · intro hDead
    simp [evalTerminator, hDead]

/-- Universal characterization of `TerminatorKind.assert` (`Terminators.lean:407-432`):
when `cond` evaluates to scalar `sc`, matching `expectedBit` jumps to `target`
via `MrStackFrame.jump_to_block`, whereas mismatching `expectedBit` dispatches
`applyUnwindAction s locals' s.memory unwind`. -/
theorem mir_evalTerminator_assert_corresponds
    (s : MachineState) (cond : Operand) (expected : Bool)
    (target : BasicBlockIdx) (unwind : UnwindAction) (span : String)
    (currentBody : Option CapturedMir)
    (sc : ScalarInt) (locals' : List LocalSlot)
    (hEval :
      evalOperand
        s.frame.locals
        cond
        s.memory.borrows
        s.memory.globals
        (match currentBody with | .some b => b.layouts | .none => emptyLayoutTable)
        s.memory.callerLocals = .ok (.scalar sc) locals') :
    let expectedBit := match expected with | true => 1 | false => 0
    (Nat.beq sc.bits expectedBit = true →
      evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody =
        MirStepNode.step
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
      toMrStackFrame { blockIdx := target, stmtIdx := 0, locals := locals' } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) target) ∧
    (Nat.beq sc.bits expectedBit = false →
      evalTerminator s ⟨.assert cond expected target unwind, span⟩ currentBody =
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro hMatch
    refine ⟨?_, rfl⟩
    cases expected <;> cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval, hMatch]
  · intro hMismatch
    cases expected <;> cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval, hMismatch] <;>
      cases applyUnwindAction s locals' s.memory unwind <;> rfl

/-- Universal characterization of `TerminatorKind.call` (`Terminators.lean:298-353`
vs. `spec/lang/step/terminators.md:179-289`):
1. Calling `"core::hint::unreachable_unchecked"` or `"core::intrinsics::unreachable"`
   with `target = .none` immediately faults with `MirStepNode.fail .ub`; and
2. Calling a transparent callee `calleeBody` found via `findCallee?` pushes a
   `SavedCallerFrame` onto `s.memory.callStack` and initializes the new frame at
   `blockIdx := 0, stmtIdx := 0, locals := initLocals calleeBody argVals`. -/
theorem mir_evalTerminator_call_transparent_and_unreachable_unchecked
    (s : MachineState) (func : Operand) (argOps : List Operand)
    (destination : Place) (unwind : UnwindAction) (span : String)
    (currentBody : Option CapturedMir) :
    let bodyLayouts := match currentBody with | .some b => b.layouts | .none => emptyLayoutTable
    (extractCalleeDefPath? func = .some "core::hint::unreachable_unchecked" →
      lookupCallee s.memory.callees bodyLayouts "core::hint::unreachable_unchecked" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      evalTerminator s ⟨.call func .nil destination .none unwind, span⟩ currentBody =
        MirStepNode.fail .ub) ∧
    (extractCalleeDefPath? func = .some "core::intrinsics::unreachable" →
      lookupCallee s.memory.callees bodyLayouts "core::intrinsics::unreachable" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      evalTerminator s ⟨.call func .nil destination .none unwind, span⟩ currentBody =
        MirStepNode.fail .ub) ∧
    (∀ (defPath : DefPath) (targetBb : BasicBlockIdx)
       (calleeBody callerBody : CapturedMir)
       (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some defPath →
      currentBody = .some callerBody →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .some calleeBody →
      let savedCaller : SavedCallerFrame :=
        { callerBody := callerBody
          frame := { s.frame with locals := locals' }
          destination := destination
          returnTarget := targetBb
          calleeProtectors := s.memory.activeProtectors
          returnUnwind := unwind
          isDiverging := false }
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ currentBody =
        MirStepNode.step
          { frame :=
              { blockIdx := 0
                stmtIdx := 0
                locals := initLocals calleeBody argVals }
            memory :=
              { s.memory with
                callStack := savedCaller :: s.memory.callStack
                activeCallee := .some calleeBody } }) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hUnreach hFind
    cases currentBody <;>
      simp [evalTerminator, resolveCallTarget, evalOperands, hUnreach, hFind] <;>
      rfl
  · intro hUnreach hFind
    cases currentBody <;>
      simp [evalTerminator, resolveCallTarget, evalOperands, hUnreach, hFind] <;>
      rfl
  · intro defPath targetBb calleeBody callerBody argVals locals' hFunc hCurr hArgs hFind
    subst hCurr
    simp [evalTerminator, hFunc, hArgs, hFind]

/-- Universal correspondence of `TerminatorKind.switchInt` (`Terminators.lean:387-406`
vs. `Generated.Ops.mrLookupSwitchTarget` at `spec/lang/step/terminators.md:32-49`):
when `evalOperand` evaluates `discr` to `.ok (.scalar sc) locals'`, `evalTerminator`
branches to `Generated.Ops.mrLookupSwitchTarget sc.bits targets.branches targets.otherwise`
with `stmtIdx := 0` (`MrStackFrame.jump_to_block`), and when `evalOperand` returns
`.ub`, `evalTerminator` faults with `MirStepNode.fail .ub`. -/
theorem evalTerminator_switchInt_agrees_with_generated
    (s : MachineState) (discr : Operand) (targets : SwitchTargets)
    (span : String) (currentBody : Option CapturedMir) :
    let bodyLayouts := match currentBody with | .some b => b.layouts | .none => emptyLayoutTable
    (∀ (sc : ScalarInt) (locals' : List LocalSlot),
      evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals =
        .ok (.scalar sc) locals' →
      let target := mrLookupSwitchTarget sc.bits targets.branches targets.otherwise
      evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody =
        MirStepNode.emitStep (.event sc.bits)
          { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
      toMrStackFrame { blockIdx := target, stmtIdx := 0, locals := locals' } =
        MrStackFrame.jump_to_block (toMrStackFrame s.frame) target) ∧
    (evalOperand s.frame.locals discr s.memory.borrows s.memory.globals bodyLayouts s.memory.callerLocals = .ub →
      evalTerminator s ⟨.switchInt discr targets, span⟩ currentBody = MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro sc locals' hEval
    refine ⟨?_, rfl⟩
    rw [← mir_lookupSwitchTarget_corresponds sc.bits targets.branches targets.otherwise]
    cases currentBody <;>
      simp only [evalTerminator] at hEval ⊢ <;>
      simp [hEval]
  · intro hUb
    cases currentBody <;>
      simp only [evalTerminator] at hUb ⊢ <;>
      simp [hUb]

/-! ## 3. Function-Item Reification (`ReifyFnPointer`), `fnPtrToPtr`, and Indirect `FnPtr` Calls (`BRIEF-1.1`) -/

/--
Universal characterization of `CastKind.pointerCoercion "ReifyFnPointer"`,
`CastKind.fnPtrToPtr`, `CastKind.ptrToPtr`, and `CastKind.pointerExposeProvenance`
in `evalRvalue`:
1. Reifying a zero-sized `.fnDef defPath typeArgs` constant operand into a
   `.fnPtr sigInputs sigOut sigSafety sigAbi` target type allocates the canonical
   function-pointer entry `{ allocId := fnPtrAllocBase, defPath, typeArgs, fnSig }`
   in `emptyMemory.fnPtrs` and returns
   `.ptr { allocId := fnPtrAllocBase, offsetBytes := 0 } 8`.
2. Explicit safety-tagged coercions (`"ReifyFnPointer(Safe)"` and
   `"ReifyFnPointer(Unsafe)"`) succeed when the target `fnPtr` safety matches
   and fault with `.ub` on a safety mismatch or `.rustIntrinsic` ABI.
3. Casting a registered function pointer via `CastKind.fnPtrToPtr` to a thin raw
   pointer, then via `CastKind.ptrToPtr`, and then exposing its address via
   `CastKind.pointerExposeProvenance` yields the deterministic exposed scalar
   address `allocId * 65536`.
4. Applying `CastKind.fnPtrToPtr` to an unregistered pointer faults with
   `EvalResult.ub`.
-/
theorem mir_evalRvalue_reifyFnPointer_and_fnPtrToPtr_chain
    (locals : List LocalSlot)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (sigInputs : List RigidTy)
    (sigOut : RigidTy)
    (sigSafety : Safety)
    (sigAbi : CallConv)
    (hNotIntrinsic : callConvEq sigAbi .rustIntrinsic = false) :
    let fnItemTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
    let fnPtrKind : RigidTy := .fnPtr sigInputs sigOut sigSafety sigAbi
    let fnPtrTy : Ty := { kind := fnPtrKind, layoutIdx := 0 }
    let safeFnPtrKind : RigidTy := .fnPtr sigInputs sigOut .safe sigAbi
    let safeFnPtrTy : Ty := { kind := safeFnPtrKind, layoutIdx := 0 }
    let unsafeFnPtrKind : RigidTy := .fnPtr sigInputs sigOut .unsafe_ sigAbi
    let unsafeFnPtrTy : Ty := { kind := unsafeFnPtrKind, layoutIdx := 0 }
    let intrinsicFnPtrTy : Ty :=
      { kind := .fnPtr sigInputs sigOut sigSafety .rustIntrinsic, layoutIdx := 0 }
    let rawConstUnitTy : Ty := { kind := .rawPtr .not (.tuple .nil), layoutIdx := 0 }
    let rawMutUnitTy : Ty := { kind := .rawPtr .mut (.tuple .nil), layoutIdx := 0 }
    let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
    let fnConstOp : Operand := .constant { ty := fnItemTy, val := .zeroSized }
    let expectedEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := typeArgs
        fnSig := .some fnPtrKind }
    let expectedSafeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := typeArgs
        fnSig := .some safeFnPtrKind }
    let expectedPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let memAfterReify : Memory := { emptyMemory with fnPtrs := [expectedEntry] }
    let memAfterSafeReify : Memory := { emptyMemory with fnPtrs := [expectedSafeEntry] }
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp fnPtrTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memAfterReify) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Safe)") fnConstOp safeFnPtrTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memAfterSafeReify) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Safe)") fnConstOp unsafeFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer(Unsafe)") fnConstOp safeFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp intrinsicFnPtrTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        memAfterReify =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memAfterReify) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .ptrToPtr (.copy ⟨0, .nil⟩) rawMutUnitTy)
        memAfterReify =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memAfterReify) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .pointerExposeProvenance (.copy ⟨0, .nil⟩) usizeTy)
        memAfterReify =
      .ok
        (.scalar { bits := fnPtrAllocBase * 65536, sizeBytes := 8 })
        [.init (.ptr expectedPtr 8)]
        { memAfterReify with exposedAllocIds := [fnPtrAllocBase] }) ∧
    (evalRvalue
        [.init (.ptr { allocId := 0, offsetBytes := 0 } 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        emptyMemory =
      .ub) := by
  have hReify1 : isReifyFnPointerCoercion "ReifyFnPointer" = true := by decide
  have hReify2 : isReifyFnPointerCoercion "ReifyFnPointer(Safe)" = true := by decide
  have hReify3 : isReifyFnPointerCoercion "ReifyFnPointer(Unsafe)" = true := by decide
  have hNeUnsafe1 : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
  have hNeUnsafe2 : stringEq "ReifyFnPointer(Safe)" "UnsafeFnPointer" = false := by decide
  have hNeUnsafe3 : stringEq "ReifyFnPointer(Unsafe)" "UnsafeFnPointer" = false := by decide
  have hSafeCompat1 :
      reifyCoercionSafetyCompatible "ReifyFnPointer" sigSafety = true := by
    cases sigSafety <;> rfl
  have hSafeCompat2 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Safe)" .safe = true := by decide
  have hSafeCompat3 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Safe)" .unsafe_ = false := by decide
  have hSafeCompat4 :
      reifyCoercionSafetyCompatible "ReifyFnPointer(Unsafe)" .safe = false := by decide
  have hNotClosure1 : isClosureFnPointerCoercion "ReifyFnPointer" = false := by decide
  have hNotClosure2 : isClosureFnPointerCoercion "ReifyFnPointer(Safe)" = false := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalRvalue, evalReifyFnPointer, hReify1, hNeUnsafe1, hNotIntrinsic,
      hSafeCompat1, hNotClosure1, extractReifyCoercionTarget?, extractFnItemTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify2, hNeUnsafe2, hNotIntrinsic,
      hSafeCompat2, hNotClosure2, extractReifyCoercionTarget?, extractFnItemTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify2, hNeUnsafe2, hNotIntrinsic,
      hSafeCompat3, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify3, hNeUnsafe3, hNotIntrinsic,
      hSafeCompat4, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hReify1, hNeUnsafe1,
      evalOperand, evalConstValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, lookupFnPtr, hNotIntrinsic]
  · simp [evalRvalue, evalCastPtrToPtr, layoutPointerBytes, evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalPointerExposeProvenance, exposeTargetBytes?, isExposePtrSourceTy,
      layoutPointerBytes, evalOperand, get?, readProjectedValue,
      ptrAddress?, emptyMemory, lookupBorrow, recordExposedAllocId,
      isExposedAllocId, fnPtrAllocBase] <;> decide
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, isFnPtrAllocId, fnPtrAllocBase]

/--
Universal characterization of `checkCalleeSig`, `PointerCoercion::ClosureFnPointer`,
`PointerCoercion::UnsafeFnPointer`, and `safetyCompatible` in `evalRvalue` and
`fnEntryCompatibleWithCallSite`:
1. Reifying a function item when `checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi typeArgs = false`
   faults with `RvalueEvalResult.ub`.
2. Applying `"ClosureFnPointer(Safe)"` to a non-capturing closure
   (`.closure defPath .nil`) succeeds, while applying `"ClosureFnPointer(Safe)"`
   to a `.fnDef` or `"ReifyFnPointer"` to a `.closure` faults with `.ub`.
3. Applying `CastKind.pointerCoercion "UnsafeFnPointer"` to a registered safe
   function pointer (`Safety.safe`) produces the same `ProvenancePtr` at the
   matching `Safety.unsafe_` signature, whereas applying `"UnsafeFnPointer"` to
   a `.safe` target signature faults with `RvalueEvalResult.ub`.
4. An `.unsafe_` `FnPtrEntry` is rejected by `fnEntryCompatibleWithCallSite` when
   the call-site operand has `Safety.safe`.
-/
theorem mir_evalRvalue_reifyFnPointer_callee_sig_and_unsafeFnPointer_corresponds
    (locals : List LocalSlot)
    (mem : Memory)
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (sigInputs : List RigidTy)
    (sigOut : RigidTy)
    (sigSafety : Safety)
    (sigAbi : CallConv)
    (hNotIntrinsic : callConvEq sigAbi .rustIntrinsic = false) :
    let fnItemTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
    let fnConstOp : Operand := .constant { ty := fnItemTy, val := .zeroSized }
    let closureTy : Ty := { kind := .closure defPath .nil, layoutIdx := 0 }
    let closureConstOp : Operand := .constant { ty := closureTy, val := .zeroSized }
    let fnPtrTy : Ty := { kind := .fnPtr sigInputs sigOut sigSafety sigAbi, layoutIdx := 0 }
    let safeFnKind : RigidTy := .fnPtr [.uint .u64] (.uint .u64) .safe .rust
    let unsafeFnKind : RigidTy := .fnPtr [.uint .u64] (.uint .u64) .unsafe_ .rust
    let safeFnTy : Ty := { kind := safeFnKind, layoutIdx := 0 }
    let unsafeFnTy : Ty := { kind := unsafeFnKind, layoutIdx := 0 }
    let safeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some safeFnKind }
    let unsafeEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some unsafeFnKind }
    let intrinsicEntry : FnPtrEntry :=
      { allocId := fnPtrAllocBase
        defPath := defPath
        typeArgs := .nil
        fnSig := .some (.fnPtr [.uint .u64] (.uint .u64) .safe .rustIntrinsic) }
    let rawConstUnitTy : Ty := { kind := .rawPtr .not (.tuple .nil), layoutIdx := 0 }
    let expectedPtr : ProvenancePtr := { allocId := fnPtrAllocBase, offsetBytes := 0 }
    let memWithSafe : Memory := { emptyMemory with fnPtrs := [safeEntry] }
    let memWithIntrinsic : Memory := { emptyMemory with fnPtrs := [intrinsicEntry] }
    (checkCalleeSig mem.callees defPath sigInputs sigOut sigAbi typeArgs mem.traitImpls = false →
      evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") fnConstOp fnPtrTy)
        mem = .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ClosureFnPointer(Safe)") closureConstOp safeFnTy)
        emptyMemory =
      .ok (.ptr expectedPtr 8) locals memWithSafe) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ClosureFnPointer(Safe)") fnConstOp safeFnTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        locals
        (.cast (.pointerCoercion "ReifyFnPointer") closureConstOp safeFnTy)
        emptyMemory =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨0, .nil⟩) unsafeFnTy)
        memWithSafe =
      .ok (.ptr expectedPtr 8) [.init (.ptr expectedPtr 8)] memWithSafe) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast (.pointerCoercion "UnsafeFnPointer") (.copy ⟨0, .nil⟩) safeFnTy)
        memWithSafe =
      .ub) ∧
    (evalRvalue
        [.init (.ptr expectedPtr 8)]
        (.cast .fnPtrToPtr (.copy ⟨0, .nil⟩) rawConstUnitTy)
        memWithIntrinsic =
      .ub) ∧
    (fnEntryCompatibleWithCallSite unsafeEntry 1 (.some safeFnTy) = false) := by
  have hReify : isReifyFnPointerCoercion "ReifyFnPointer" = true := by decide
  have hClosureSafe : isReifyFnPointerCoercion "ClosureFnPointer(Safe)" = true := by decide
  have hReifyUnsafe : isReifyFnPointerCoercion "UnsafeFnPointer" = true := by decide
  have hEqUnsafe : stringEq "UnsafeFnPointer" "UnsafeFnPointer" = true := by decide
  have hNeUnsafeClosure : stringEq "ClosureFnPointer(Safe)" "UnsafeFnPointer" = false := by decide
  have hSafeCompat :
      reifyCoercionSafetyCompatible "ReifyFnPointer" sigSafety = true := by
    cases sigSafety <;> rfl
  have hSafeCompatClosure :
      reifyCoercionSafetyCompatible "ClosureFnPointer(Safe)" .safe = true := by decide
  have hNotClosure : isClosureFnPointerCoercion "ReifyFnPointer" = false := by decide
  have hIsClosureSafe : isClosureFnPointerCoercion "ClosureFnPointer(Safe)" = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hSigFalse
    have hNeUnsafe : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
    simp [evalRvalue, evalReifyFnPointer, hReify, hNeUnsafe, hNotIntrinsic,
      hSafeCompat, hNotClosure, extractReifyCoercionTarget?, extractFnItemTarget?,
      hSigFalse, evalOperand, evalConstValue]
  · simp [evalRvalue, evalReifyFnPointer, hClosureSafe, hNeUnsafeClosure,
      hSafeCompatClosure, hIsClosureSafe, extractReifyCoercionTarget?,
      emptyMemory, checkCalleeSig, findFnPtrEntry?, nextFnPtrAllocId,
      evalOperand, evalConstValue, callConvEq]
  · simp [evalRvalue, evalReifyFnPointer, hClosureSafe, hNeUnsafeClosure,
      hSafeCompatClosure, hIsClosureSafe, extractReifyCoercionTarget?,
      evalOperand, evalConstValue, callConvEq]
  · have hNeUnsafe : stringEq "ReifyFnPointer" "UnsafeFnPointer" = false := by decide
    have hSafeCompatReifySafe :
        reifyCoercionSafetyCompatible "ReifyFnPointer" .safe = true := by decide
    simp [evalRvalue, evalReifyFnPointer, hReify, hNeUnsafe,
      hSafeCompatReifySafe, hNotClosure, extractReifyCoercionTarget?, extractFnItemTarget?,
      evalOperand, evalConstValue, callConvEq]
  · simp [evalRvalue, evalReifyFnPointer, hReifyUnsafe, hEqUnsafe, evalUnsafeFnPointer,
      evalOperand, get?, readProjectedValue, emptyMemory, lookupBorrow,
      lookupFnPtr, callConvEq, rigidTyListEq, rigidTyEq,
      rigidTyListEqAux, rigidTyEqAux, uintTyEq]
  · simp [evalRvalue, evalReifyFnPointer, hReifyUnsafe, hEqUnsafe, evalUnsafeFnPointer,
      evalOperand, get?, readProjectedValue]
  · simp [evalRvalue, evalFnPtrToPtr, evalOperand, get?, readProjectedValue,
      isThinRawPtrTy, emptyMemory, lookupBorrow, lookupFnPtr, callConvEq]
  · rfl

/--
Universal proof that dereferencing a reified function pointer (`PlaceElem.deref`)
as data memory in `evalOperand` or `writePlaceValue` faults with `.ub` when
`ptrVal.allocId` is not backed by a global allocation in `s.memory.globals`
(and not a live stack borrow in `s.memory.borrows`).
-/
theorem mir_fnPtr_data_deref_is_ub
    (ptrVal : ProvenancePtr)
    (mem : Memory)
    (writeVal : Value)
    (hNoBorrow : lookupBorrow mem.borrows ptrVal.tag = .none)
    (hNoGlobal : lookupGlobalAlloc mem.globals ptrVal.allocId = .none) :
    let locals : List LocalSlot := [.init (.ptr ptrVal 8)]
    let derefPlace : Place := { local_ := 0, projection := [.deref] }
    evalOperand locals (.copy derefPlace) mem.borrows mem.globals emptyLayoutTable mem.callerLocals = .ub ∧
    writePlaceValue locals mem.borrows derefPlace writeVal = .ub := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simp [evalOperand, get?, hNoBorrow, hNoGlobal]
  · simp [writePlaceValue, get?, hNoBorrow]

/--
Universal characterization of indirect `TerminatorKind.call` and
`TerminatorKind.tailCall` through a function pointer (`BRIEF-1.1`):
1. When `func` evaluates to `.ptr ptrVal 8` with `ptrVal.offsetBytes = 0`, no stack
   borrow on `ptrVal.tag`, and `lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry`
   compatible with the call site (`fnEntryCompatibleWithCallSite = true`):
   - If `lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody` and
     `checkCalleeTargetCompatible` holds, `TerminatorKind.call` pushes a
     `SavedCallerFrame` and enters `calleeBody` at block `0` via `pushCalleeFrame`,
     and `TerminatorKind.tailCall` enters `calleeBody` at block `0` via
     `enterTailCalleeFrame`.
   - If `lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .none`, `TerminatorKind.call`
     and `TerminatorKind.tailCall` emit `MirStepNode.extCall` targeting
     `fnEntry.defPath`.
2. When `func` evaluates to an unregistered pointer (`lookupFnPtr = .none`), a
   non-zero offset pointer, a stack borrow data pointer, a scalar, or a function
   pointer with incompatible signature/arity, both `TerminatorKind.call` and
   `TerminatorKind.tailCall` fault with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_indirect_call_and_tailCall_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (ptrVal : ProvenancePtr)
    (fnEntry : FnPtrEntry)
    (localsAfterFunc locals' : List Value → List LocalSlot)
    (argVals : List Value)
    (hNoDirect : extractCalleeDefPath? func = .none)
    (hEvalFunc :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok (.ptr ptrVal 8) (localsAfterFunc argVals))
    (hOffsetZero : ptrVal.offsetBytes = 0)
    (hNoBorrow : lookupBorrow s.memory.borrows ptrVal.tag = .none) :
    let callerFuncTyOpt := operandTy callerBody.localDecls callerBody.layouts func
    let resolvedTarget : ResolvedCallTarget :=
      { defPath := fnEntry.defPath
        typeArgs := fnEntry.typeArgs
        fnSig := fnEntry.fnSig
        isIndirect := true }
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody →
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = true →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.step
          (pushCalleeFrame s callerBody (locals' argVals) destination targetBb calleeBody argVals unwind) ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.step
          (pushDivergingCalleeFrame s callerBody (locals' argVals) destination unwind calleeBody argVals) ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.step (enterTailCalleeFrame s.memory calleeBody argVals)) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalCall s (locals' argVals) destination targetBb unwind) ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s (locals' argVals) unwind) ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := fnEntry.defPath, typeArgs := fnEntry.typeArgs, args := argVals, memory := s.memory }
          resumeExternalTailCall) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .none →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = false →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupFnPtr s.memory.fnPtrs ptrVal.allocId = .some fnEntry →
      fnEntryCompatibleWithCallSite fnEntry (length argOps) callerFuncTyOpt = true →
      evalOperands
        (localsAfterFunc argVals)
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals (locals' argVals) →
      lookupCallee s.memory.callees callerBody.layouts fnEntry.defPath fnEntry.typeArgs s.memory.traitImpls = .some calleeBody →
      checkCalleeTargetCompatible resolvedTarget calleeBody (length argVals) = false →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hLookup hCompatSite hArgs hFind hCompatBody
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind,
        hCompatBody, Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookup hCompatSite hArgs hFindNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, isDirectExactDivTarget, resolveCallTarget,
        hNoDirect, hEvalFunc, hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFindNone,
        Nat.beq_refl, Bool.and_self] <;> rfl
  · intro hLookupNone
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookupNone, Nat.beq_refl, Bool.and_self]
  · intro hLookup hCompatFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatFalse, Nat.beq_refl, Bool.and_self]
  · intro hLookup hCompatSite hArgs hFind hCompatBodyFalse
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [evalTerminator, evalTailCallTerminator, bodyLocalDeclsOf, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hNoBorrow, hLookup, hCompatSite, hArgs, hFind, hCompatBodyFalse,
        Nat.beq_refl, Bool.and_self] <;> rfl

/--
Universal proof that indirect `TerminatorKind.call` and `TerminatorKind.tailCall`
fault with `MirStepNode.fail .ub` when the function-pointer operand evaluates to
a pointer with a non-zero byte offset (`ptrVal.offsetBytes = n + 1`) or a
live stack borrow data pointer (`lookupBorrow s.memory.borrows ptrVal.tag = .some bEntry`).
-/
theorem mir_evalTerminator_indirect_call_nonZeroOffset_or_borrow_is_ub
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (ptrVal : ProvenancePtr)
    (n : Nat)
    (bEntry : BorrowEntry)
    (localsAfterFunc : List LocalSlot)
    (hNoDirect : extractCalleeDefPath? func = .none)
    (hEvalFunc :
      evalOperand
        s.frame.locals
        func
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok (.ptr ptrVal 8) localsAfterFunc) :
    (ptrVal.offsetBytes = n + 1 →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (ptrVal.offsetBytes = 0 →
      lookupBorrow s.memory.borrows ptrVal.tag = .some bEntry →
      evalTerminator s ⟨.call func argOps destination (.some targetBb) unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub ∧
      evalTerminator s ⟨.tailCall func argOps, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_⟩
  · intro hNonZero
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [evalTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc, hNonZero, Nat.beq]
  · intro hOffsetZero hBorrow
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [evalTerminator, evalTailCallTerminator, resolveCallTarget, hNoDirect, hEvalFunc,
        hOffsetZero, hBorrow]

/-! ## 4. Diverging Calls (`target = .none`) and Unwind Cleanup Terminators (`BRIEF-1.2`) -/

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
argument evaluation order, UB propagation, and unreachable call targets
(`"core::hint::unreachable_unchecked"` and `"core::intrinsics::unreachable"`):
1. If resolving `func` via `resolveCallTarget` faults with `.ub`, the diverging
   call faults with `MirStepNode.fail .ub`.
2. If evaluating `argOps` left-to-right via `evalOperands` faults with `.ub`
   (e.g., reading a `.dead` or `.uninit` local), the diverging call faults with
   `MirStepNode.fail .ub` before dispatching the callee or panic entrypoint.
3. For any `argOps` whose left-to-right evaluation succeeds (`.ok argVals locals'`),
   calling `"core::hint::unreachable_unchecked"` or `"core::intrinsics::unreachable"`
   with `target = .none` faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_diverging_call_args_and_unreachable
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir) :
    (resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts = .ub →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok target localsAfterFunc →
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ub →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some "core::hint::unreachable_unchecked" →
      lookupCallee s.memory.callees callerBody.layouts "core::hint::unreachable_unchecked" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (argVals : List Value) (locals' : List LocalSlot),
      extractCalleeDefPath? func = .some "core::intrinsics::unreachable" →
      lookupCallee s.memory.callees callerBody.layouts "core::intrinsics::unreachable" (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (∀ (target : ResolvedCallTarget) (localsAfterFunc : List LocalSlot)
       (argVals : List Value) (locals' : List LocalSlot),
      resolveCallTarget s func (length argOps) callerBody.localDecls callerBody.layouts =
        .ok target localsAfterFunc →
      target.isIndirect = true →
      lookupCallee s.memory.callees callerBody.layouts target.defPath target.typeArgs s.memory.traitImpls = .none →
      evalOperands
        localsAfterFunc
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals' →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := target.defPath, typeArgs := target.typeArgs, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s locals' unwind)) := by
  have hUnreach1 : isUnreachableCallTarget "core::hint::unreachable_unchecked" = true := by decide
  have hUnreach2 : isUnreachableCallTarget "core::intrinsics::unreachable" = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hResolveUb
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveUb]
  · intro target localsAfterFunc hResolveOk hArgsUb
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveOk, hArgsUb]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach1]
  · intro argVals locals' hFunc hFind hArgsOk
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgsOk, hFind, hUnreach2]
  · intro target localsAfterFunc argVals locals' hResolveOk hIndirect hFind hArgsOk
    simp only [evalTerminator, bodyLocalDeclsOf, hResolveOk, hArgsOk, hFind, hIndirect]

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
when the target callee is linked in `s.memory.callees`:
1. Calling a linked `calleeBody` (`findCallee? s.memory.callees target.defPath = .some calleeBody`
   with `checkCalleeTargetCompatible = true`)
   pushes a diverging `SavedCallerFrame` (`isDiverging = true`, `returnUnwind = unwind`)
   via `pushDivergingCalleeFrame` and enters `calleeBody` at block `0`.
2. If that diverging `calleeBody` subsequently attempts to return normally via
   `TerminatorKind.return_` from ANY local slot state `calleeLocals` (whether `_0`
   is `.uninit`, `.dead`, `.none`, or `.init retVal`) or via an external
   `TerminatorKind.tailCall` receiving `MirCallAns.returned`, execution faults
   with `MirStepNode.fail .ub` (`.faulted .ub`).
3. If that diverging `calleeBody` unwinds via `TerminatorKind.unwindResume` (or
   `applyUnwindAction ... .continue_`), execution pops the diverging caller frame,
   restores `callerBody` and `restoreCallerProtectors`, and applies the caller's
   `unwind : UnwindAction` (`.cleanup cleanupBb`, `.terminate`, `.unreachable`, or
   `.continue_`).
-/
theorem mir_evalTerminator_diverging_call_linked_callee_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals')
    (hFind : lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .some calleeBody) :
    let enteredState :=
      pushDivergingCalleeFrame s callerBody locals' destination unwind calleeBody argVals
    (evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
      MirStepNode.step enteredState) ∧
    (∀ (calleeLocals : List LocalSlot),
      evalTerminator
        { enteredState with frame := { enteredState.frame with locals := calleeLocals } }
        ⟨.return_, span⟩
        (.some calleeBody) = MirStepNode.fail .ub) ∧
    (∀ (retVal : Value),
      resumeExternalTailCall (.returned retVal enteredState.memory) = .faulted .ub) ∧
    (∀ (cleanupBb : BasicBlockIdx),
      unwind = .cleanup cleanupBb →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (unwind = .terminate →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .abort) ∧
    (unwind = .unreachable →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.fail .ub) ∧
    (unwind = .continue_ →
      s.memory.callStack = .nil →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .panic) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFind,
      checkCalleeTargetCompatible]
  · intro calleeLocals
    unfold evalTerminator pushDivergingCalleeFrame
    dsimp only
    cases get? calleeLocals 0 with
    | none => rfl
    | some slot0 =>
      cases slot0 <;> rfl
  · intro retVal
    simp [resumeExternalTailCall, pushDivergingCalleeFrame]
  · intro cleanupBb hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack]
  · intro hUnwind hRoot
    subst hUnwind
    simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, hRoot]

/--
Universal characterization of diverging `TerminatorKind.call` (`target = .none`)
for standard panic entrypoints when unlinked (`findCallee? = .none`):
1. Calling any non-unwinding panic/abort entrypoint (`isAbortingPanicDefPath`:
   `"core::panicking::panic_nounwind"`, `"core::panicking::panic_nounwind_fmt"`,
   `"core::panicking::panic_nounwind_fmt::panic_impl"`,
   `"core::panicking::panic_nounwind_nobacktrace"`,
   `"core::panicking::panic_in_cleanup"`, `"core::panicking::panic_cannot_unwind"`,
   `"core::panicking::panic_misaligned_pointer_dereference"`,
   `"core::panicking::panic_null_pointer_dereference"`,
   `"core::panicking::panic_invalid_enum_construction"`, or
   `"core::intrinsics::abort"`) halts immediately with
   `MirStepNode.retOutcome .abort` under any `unwind : UnwindAction`.
2. Calling any standard unwinding panic entrypoint (`isUnwindingPanicDefPath`:
   `"core::panicking::panic"`, `"core::panicking::panic_fmt"`,
   `"core::panicking::panic_fmt::panic_impl"`, `"core::panicking::const_panic_fmt"`,
   `"core::panicking::assert_failed"`, `"core::panicking::assert_failed_inner"`,
   `"core::panicking::assert_matches_failed"`,
   `"core::slice::index::slice_index_fail"`,
   `"core::panicking::panic_bounds_check"`, `"core::panicking::panic_explicit"`,
   `"core::panicking::panic_display"`, `"core::panicking::panic_str_2015"`,
   `"core::panicking::unreachable_display"`, `"core::option::unwrap_failed"`,
   `"core::option::expect_failed"`, `"core::result::unwrap_failed"`, or any
   `"core::panicking::panic_const::*"` arithmetic overflow/zero-division hook)
   evaluates `argOps` to `locals'` and dispatches
   `applyUnwindAction s locals' s.memory unwind`:
   - under `.continue_` at the root frame (`s.memory.callStack = .nil`), halts with
     `MirStepNode.retOutcome .panic`;
   - under `.continue_` in a nested frame (`s.memory.callStack = caller :: restStack`
     with `caller.returnUnwind = .cleanup cleanupBb`), pops `caller` and jumps to
     `cleanupBb` in `caller.frame`;
   - under `.cleanup cleanupBb`, jumps to `cleanupBb` with `stmtIdx = 0` and
     `locals = locals'`;
   - under `.terminate`, halts with `MirStepNode.retOutcome .abort`; and
   - under `.unreachable`, faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_diverging_call_panic_entrypoints
    (s : MachineState)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (cleanupBb : BasicBlockIdx)
    (span : String)
    (callerBody : CapturedMir)
    (caller : SavedCallerFrame)
    (restStack : List SavedCallerFrame)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    let mkFnOp (p : DefPath) : Operand :=
      .constant { ty := { kind := .fnDef p .nil, layoutIdx := 0 }, val := .zeroSized }
    (∀ pAbort : DefPath,
      (pAbort = "core::panicking::panic_nounwind" ∨
       pAbort = "core::panicking::panic_nounwind_fmt" ∨
       pAbort = "core::panicking::panic_nounwind_fmt::panic_impl" ∨
       pAbort = "core::panicking::panic_nounwind_nobacktrace" ∨
       pAbort = "core::panicking::panic_in_cleanup" ∨
       pAbort = "core::panicking::panic_cannot_unwind" ∨
       pAbort = "core::panicking::panic_misaligned_pointer_dereference" ∨
       pAbort = "core::panicking::panic_null_pointer_dereference" ∨
       pAbort = "core::panicking::panic_invalid_enum_construction" ∨
       pAbort = "core::intrinsics::abort") →
      findCallee? s.memory.callees pAbort = .none →
      evalTerminator
        s
        ⟨.call (mkFnOp pAbort) argOps destination .none unwind, span⟩
        (.some callerBody) = MirStepNode.retOutcome .abort) ∧
    (∀ p : DefPath,
      (p = "core::panicking::panic" ∨
       p = "core::panicking::panic_fmt" ∨
       p = "core::panicking::panic_fmt::panic_impl" ∨
       p = "core::panicking::const_panic_fmt" ∨
       p = "core::panicking::assert_failed" ∨
       p = "core::panicking::assert_failed_inner" ∨
       p = "core::panicking::assert_matches_failed" ∨
       p = "core::slice::index::slice_index_fail" ∨
       p = "core::panicking::panic_bounds_check" ∨
       p = "core::panicking::panic_explicit" ∨
       p = "core::panicking::panic_display" ∨
       p = "core::panicking::panic_str_2015" ∨
       p = "core::panicking::unreachable_display" ∨
       p = "core::option::unwrap_failed" ∨
       p = "core::option::expect_failed" ∨
       p = "core::result::unwrap_failed" ∨
       p = "core::panicking::panic_const::panic_const_add_overflow" ∨
       p = "core::panicking::panic_const::panic_const_sub_overflow" ∨
       p = "core::panicking::panic_const::panic_const_mul_overflow" ∨
       p = "core::panicking::panic_const::panic_const_div_overflow" ∨
       p = "core::panicking::panic_const::panic_const_rem_overflow" ∨
       p = "core::panicking::panic_const::panic_const_neg_overflow" ∨
       p = "core::panicking::panic_const::panic_const_shr_overflow" ∨
       p = "core::panicking::panic_const::panic_const_shl_overflow" ∨
       p = "core::panicking::panic_const::panic_const_div_by_zero" ∨
       p = "core::panicking::panic_const::panic_const_rem_by_zero") →
      findCallee? s.memory.callees p = .none →
      (s.memory.callStack = .nil →
        evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .continue_, span⟩ (.some callerBody) =
          MirStepNode.retOutcome .panic) ∧
      (s.memory.callStack = caller :: restStack →
        caller.returnUnwind = .cleanup cleanupBb →
        evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .continue_, span⟩ (.some callerBody) =
          MirStepNode.step
            { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 }
              memory :=
                { s.memory with
                  callStack := restStack
                  activeCallee := .some caller.callerBody
                  activeProtectors := restoreCallerProtectors caller } }) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none (.cleanup cleanupBb), span⟩ (.some callerBody) =
        MirStepNode.step
          { frame := { s.frame with blockIdx := cleanupBb, stmtIdx := 0, locals := locals' }
            memory := s.memory }) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .terminate, span⟩ (.some callerBody) =
        MirStepNode.retOutcome .abort) ∧
      (evalTerminator s ⟨.call (mkFnOp p) argOps destination .none .unreachable, span⟩ (.some callerBody) =
        MirStepNode.fail .ub)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro pAbort hpAbort hFindNone
    have hpAbortFlags :
        isUnreachableCallTarget pAbort = false ∧
        isAbortingPanicDefPath pAbort = true := by
      rcases hpAbort with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hpAbortFlags with ⟨hNotUnreach, hAbort⟩
    simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
      extractCalleeTypeArgs, hArgs, hFindNone, hNotUnreach, hAbort]
  · intro p hp hFindNone
    have hpFlags :
        isUnreachableCallTarget p = false ∧
        isAbortingPanicDefPath p = false ∧
        isUnwindingPanicDefPath p = true := by
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rcases hpFlags with ⟨hNotUnreach, hNotAbort, hUnwindPanic⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hRoot
      simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction, hRoot, unwindFromCallStack]
    · intro hStack hCallerUnwind
      simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction, hStack, unwindFromCallStack, hCallerUnwind]
    · simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]
    · simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]
    · simp only [evalTerminator, lookupCallee, resolveCalleeBodyAndArgs?, resolveCallTarget, extractCalleeDefPath?,
        extractCalleeTypeArgs, hArgs, hNotUnreach, hFindNone, hNotAbort, hUnwindPanic,
        applyUnwindAction]

/--
Universal characterization of external diverging calls (`target = .none`) and
`resumeExternalDivergingCall`:
1. When `target.defPath` is not an unreachable target, not in `s.memory.callees`,
   and not an inline panic entrypoint, `evalTerminator` emits `MirStepNode.extCall`
   with continuation `resumeExternalDivergingCall s locals' unwind`.
2. If the external call returns normally (`MirCallAns.returned retVal memAfter`),
   `resumeExternalDivergingCall` faults with `.faulted .ub`.
3. If the external call unwinds (`MirCallAns.panicked memAfter`),
   `resumeExternalDivergingCall` transitions via
   `applyUnwindAction s locals' memAfter unwind`.
4. If the external call aborts (`MirCallAns.aborted`),
   `resumeExternalDivergingCall` halts with `.halted .abort`.
-/
theorem mir_evalTerminator_diverging_call_external_corresponds
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (span : String)
    (callerBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hNotUnreach : isUnreachableCallTarget defPath = false)
    (hFindNone : lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none)
    (hNotAbort : isAbortingPanicDefPath defPath = false)
    (hNotPanic : isUnwindingPanicDefPath defPath = false)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    (evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
      MirStepNode.extCall
        { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals, memory := s.memory }
        (resumeExternalDivergingCall s locals' unwind)) ∧
    (∀ (retVal : Value) (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.returned retVal memAfter) = .faulted .ub) ∧
    (∀ (memAfter : Memory),
      resumeExternalDivergingCall s locals' unwind (.panicked memAfter) =
        applyUnwindAction s locals' memAfter unwind) ∧
    (resumeExternalDivergingCall s locals' unwind .aborted = .halted .abort) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evalTerminator, resolveCallTarget, hFunc, hArgs,
      hNotUnreach, hFindNone, hNotAbort, hNotPanic]
  · intro retVal memAfter
    rfl
  · intro memAfter
    rfl
  · rfl

/--
Universal characterization of `TerminatorKind.unwindResume` and
`TerminatorKind.unwindTerminate` across root and nested call-stack frames:
1. `TerminatorKind.unwindTerminate` halts immediately with
   `MirStepNode.retOutcome .abort`.
2. At the root frame (`s.memory.callStack = .nil`), `TerminatorKind.unwindResume`
   halts with `MirStepNode.retOutcome .panic`.
3. When `s.memory.callStack = caller :: restStack`:
   - If `caller.returnUnwind = .cleanup cleanupBb`, `TerminatorKind.unwindResume`
     pops `caller`, restores `caller.callerBody` and `restoreCallerProtectors caller`,
     and jumps to `cleanupBb` in `caller.frame`.
   - If `caller.returnUnwind = .terminate`, `TerminatorKind.unwindResume` halts with
     `MirStepNode.retOutcome .abort`.
   - If `caller.returnUnwind = .unreachable`, `TerminatorKind.unwindResume` faults
     with `MirStepNode.fail .ub`.
   - If `caller.returnUnwind = .continue_` and `restStack = grandCaller :: restStack₂`
     with `grandCaller.returnUnwind = .cleanup grandCleanupBb`, `TerminatorKind.unwindResume`
     transitively pops both `caller` and `grandCaller` and jumps to `grandCleanupBb`
     in `grandCaller.frame`.
-/
theorem mir_evalTerminator_unwindResume_and_unwindTerminate_corresponds
    (s : MachineState)
    (span : String)
    (currentBody : Option CapturedMir)
    (caller grandCaller : SavedCallerFrame)
    (restStack restStack₂ : List SavedCallerFrame)
    (cleanupBb grandCleanupBb : BasicBlockIdx) :
    (evalTerminator s ⟨.unwindTerminate, span⟩ currentBody = MirStepNode.retOutcome .abort) ∧
    (s.memory.callStack = .nil →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.retOutcome .panic) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .cleanup cleanupBb →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody =
        MirStepNode.step
          { frame := { caller.frame with blockIdx := cleanupBb, stmtIdx := 0 }
            memory :=
              { s.memory with
                callStack := restStack
                activeCallee := .some caller.callerBody
                activeProtectors := restoreCallerProtectors caller } }) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .terminate →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.retOutcome .abort) ∧
    (s.memory.callStack = caller :: restStack →
      caller.returnUnwind = .unreachable →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody = MirStepNode.fail .ub) ∧
    (s.memory.callStack = caller :: grandCaller :: restStack₂ →
      caller.returnUnwind = .continue_ →
      grandCaller.returnUnwind = .cleanup grandCleanupBb →
      evalTerminator s ⟨.unwindResume, span⟩ currentBody =
        MirStepNode.step
          { frame := { grandCaller.frame with blockIdx := grandCleanupBb, stmtIdx := 0 }
            memory :=
              { s.memory with
                callStack := restStack₂
                activeCallee := .some grandCaller.callerBody
                activeProtectors := restoreCallerProtectors grandCaller } }) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro hNil
    simp [evalTerminator, hNil]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind
    simp [evalTerminator, hStack, hUnwind]
  · intro hStack hUnwind1 hUnwind2
    simp [evalTerminator, hStack, hUnwind1, hUnwind2]

/--
Universal characterization of interprocedural unwind propagation out of a
non-diverging linked callee (`pushCalleeFrame`, `target = .some targetBb`) and
external call/tail-call continuation handlers (`resumeExternalCall` and
`resumeExternalTailCall`):
1. When a caller invokes a linked `calleeBody` via `pushCalleeFrame` with
   `unwind : UnwindAction` and `calleeBody` unwinds via `TerminatorKind.unwindResume`
   OR via a failing `TerminatorKind.assert` with `.continue_`, execution pops
   the saved caller frame, restores `callerBody` and `s.memory.activeProtectors`,
   and dispatches the caller's `unwind` (`.cleanup cleanupBb`, `.terminate`,
   `.unreachable`, or `.continue_`).
2. `resumeExternalCall` on `.panicked memAfter` transitions via
   `applyUnwindAction s locals' memAfter unwind` and on `.aborted` halts with
   `.halted .abort`.
3. `resumeExternalTailCall` on `.panicked memAfter` unwinds via
   `unwindFromCallStack memAfter.callStack memAfter` and on `.aborted` halts
   with `.halted .abort`.
-/
theorem mir_evalTerminator_callee_unwind_and_external_resume_corresponds
    (s : MachineState)
    (destination : Place)
    (targetBb cleanupBb assertTargetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (argVals : List Value)
    (locals' calleeLocalsAfterCond : List LocalSlot)
    (cond : Operand) :
    let enteredState :=
      pushCalleeFrame s callerBody locals' destination targetBb calleeBody argVals unwind
    (unwind = .cleanup cleanupBb →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (unwind = .terminate →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .abort) ∧
    (unwind = .unreachable →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.fail .ub) ∧
    (unwind = .continue_ →
      s.memory.callStack = .nil →
      evalTerminator enteredState ⟨.unwindResume, span⟩ (.some calleeBody) =
        MirStepNode.retOutcome .panic) ∧
    (unwind = .cleanup cleanupBb →
      evalOperand
        enteredState.frame.locals
        cond
        enteredState.memory.borrows
        enteredState.memory.globals
        calleeBody.layouts
        enteredState.memory.callerLocals =
          .ok (.scalar { bits := 0, sizeBytes := 1 }) calleeLocalsAfterCond →
      evalTerminator
        enteredState
        ⟨.assert cond true assertTargetBb .continue_, span⟩
        (.some calleeBody) =
        MirStepNode.step
          { frame :=
              { s.frame with
                blockIdx := cleanupBb
                stmtIdx := 0
                locals := locals' }
            memory :=
              { s.memory with
                callStack := s.memory.callStack
                activeCallee := .some callerBody
                activeProtectors := s.memory.activeProtectors } }) ∧
    (∀ memAfter : Memory,
      resumeExternalCall s locals' destination targetBb unwind (.panicked memAfter) =
        applyUnwindAction s locals' memAfter unwind ∧
      resumeExternalCall s locals' destination targetBb unwind .aborted = .halted .abort ∧
      resumeExternalTailCall (.panicked memAfter) =
        unwindFromCallStack memAfter.callStack memAfter ∧
      resumeExternalTailCall .aborted = .halted .abort) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack]
  · intro hUnwind
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack]
  · intro hUnwind hNil
    subst hUnwind
    simp [evalTerminator, pushCalleeFrame, unwindFromCallStack, hNil]
  · intro hUnwind hCond
    subst hUnwind
    simp only [evalTerminator, hCond]
    rfl
  · intro memAfter
    exact ⟨rfl, rfl, rfl, rfl⟩

/--
Universal 4-way partition theorem for unlinked direct diverging calls (`target = .none`,
`findCallee? s.memory.callees defPath = .none`) and multi-step interprocedural
cleanup-and-`unwindResume` chains:
1. For every `defPath : DefPath` with `extractCalleeDefPath? func = .some defPath`
   and `findCallee? s.memory.callees defPath = .none`:
   - `isUnreachableCallTarget defPath = true` steps to `MirStepNode.fail .ub`;
   - `isUnreachableCallTarget defPath = false ∧ isAbortingPanicDefPath defPath = true`
     steps to `MirStepNode.retOutcome .abort`;
   - `isUnreachableCallTarget defPath = false ∧ isAbortingPanicDefPath defPath = false ∧ isUnwindingPanicDefPath defPath = true`
     dispatches `applyUnwindAction s locals' s.memory unwind`; and
   - when all three predicates are `false`, emits `MirStepNode.extCall` with
     `resumeExternalDivergingCall s locals' unwind`.
2. When `callerBody` invokes a linked diverging `calleeBody` (`pushDivergingCalleeFrame`)
   with `unwind = .cleanup callerCleanupBb`, and `calleeBody` catches an internal
   panic at `calleeCleanupBb` (`applyUnwindAction ... (.cleanup calleeCleanupBb)`)
   before executing `TerminatorKind.unwindResume` at `calleeCleanupBb`, execution
   pops `calleeBody`'s frame, restores `callerBody` and `s.memory.activeProtectors`,
   lands at `callerCleanupBb` in `callerBody`, and from `callerCleanupBb` a
   subsequent `TerminatorKind.unwindResume` (at root `s.memory.callStack = .nil`)
   halts with `MirStepNode.retOutcome .panic` while `TerminatorKind.unwindTerminate`
   halts with `MirStepNode.retOutcome .abort`.
-/
theorem mir_evalTerminator_diverging_call_partition_and_cleanup_chain
    (s : MachineState)
    (func : Operand)
    (argOps : List Operand)
    (destination : Place)
    (unwind : UnwindAction)
    (callerCleanupBb calleeCleanupBb : BasicBlockIdx)
    (span : String)
    (callerBody calleeBody : CapturedMir)
    (defPath : DefPath)
    (argVals : List Value)
    (locals' calleeLocalsAfterPanic : List LocalSlot)
    (calleeActiveProtectors : List Nat)
    (hFunc : extractCalleeDefPath? func = .some defPath)
    (hArgs :
      evalOperands
        s.frame.locals
        argOps
        s.memory.borrows
        s.memory.globals
        callerBody.layouts
        s.memory.callerLocals = .ok argVals locals') :
    let s₁ :=
      pushDivergingCalleeFrame
        s
        callerBody
        locals'
        destination
        (.cleanup callerCleanupBb)
        calleeBody
        argVals
    let memInCallee : Memory :=
      { s₁.memory with activeProtectors := calleeActiveProtectors }
    let s₂ : MachineState :=
      { frame :=
          { s₁.frame with
            blockIdx := calleeCleanupBb
            stmtIdx := 0
            locals := calleeLocalsAfterPanic }
        memory := memInCallee }
    let s₃ : MachineState :=
      { frame :=
          { s.frame with
            blockIdx := callerCleanupBb
            stmtIdx := 0
            locals := locals' }
        memory :=
          { s.memory with
            callStack := s.memory.callStack
            activeCallee := .some callerBody
            activeProtectors := s.memory.activeProtectors } }
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.fail .ub) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.retOutcome .abort) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = true →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        match applyUnwindAction s locals' s.memory unwind with
        | .running nextState => MirStepNode.step nextState
        | .halted out => MirStepNode.retOutcome out
        | .faulted fk => MirStepNode.fail fk) ∧
    (lookupCallee s.memory.callees callerBody.layouts defPath (extractCalleeTypeArgs func) s.memory.traitImpls = .none →
      isUnreachableCallTarget defPath = false →
      isAbortingPanicDefPath defPath = false →
      isUnwindingPanicDefPath defPath = false →
      evalTerminator s ⟨.call func argOps destination .none unwind, span⟩ (.some callerBody) =
        MirStepNode.extCall
          { defPath := defPath, typeArgs := extractCalleeTypeArgs func, args := argVals, memory := s.memory }
          (resumeExternalDivergingCall s locals' unwind)) ∧
    (applyUnwindAction s₁ calleeLocalsAfterPanic memInCallee (.cleanup calleeCleanupBb) =
      .running s₂ ∧
     evalTerminator s₂ ⟨.unwindResume, span⟩ (.some calleeBody) =
      MirStepNode.step s₃ ∧
     (s.memory.callStack = .nil →
       evalTerminator s₃ ⟨.unwindResume, span⟩ (.some callerBody) =
         MirStepNode.retOutcome .panic) ∧
     evalTerminator s₃ ⟨.unwindTerminate, span⟩ (.some callerBody) =
       MirStepNode.retOutcome .abort) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hFindNone hUnreach
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hUnreach]
  · intro hFindNone hNotUnreach hAbort
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone, hNotUnreach, hAbort]
  · intro hFindNone hNotUnreach hNotAbort hPanic
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hPanic]
    cases applyUnwindAction s locals' s.memory unwind <;> rfl
  · intro hFindNone hNotUnreach hNotAbort hNotPanic
    simp only [evalTerminator, resolveCallTarget, hFunc, hArgs, hFindNone,
      hNotUnreach, hNotAbort, hNotPanic]
  · refine ⟨rfl, ?_, ?_, rfl⟩
    · simp [evalTerminator, pushDivergingCalleeFrame, unwindFromCallStack, restoreCallerProtectors]
    · intro hNil
      simp [evalTerminator, unwindFromCallStack, hNil]

/-! ## 5. `CallConv.rustIntrinsic` Compiler Intrinsics Executed Inside `core` (`BRIEF-1.3`) -/

/--
Helper constructing a direct `TerminatorKind.call` to `defPath` with generic
type arguments `typeArgs` and operand list `argOps`.
-/
def mkIntrinsicCallTerm
    (defPath : DefPath)
    (typeArgs : List RigidTy)
    (argOps : List Operand)
    (dest : Place)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction := .continue_)
    (span : String := "") :
    Terminator :=
  let fnTy : Ty := { kind := .fnDef defPath typeArgs, layoutIdx := 0 }
  let funcOp : Operand := .constant { ty := fnTy, val := .zeroSized }
  ⟨.call funcOp argOps dest (.some targetBb) unwind, span⟩

/--
**Theorem L5.18 (`mir_evalTerminator_exact_div_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for inline
`"core::intrinsics::exact_div"` intrinsic call dispatch in
`Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator`, for the unsigned
(`exact_div::<u32>`) and signed (`exact_div::<i32>`) instantiations:
1. When `evalExactDiv lhs rhs isSigned = .some retScalar`, `evalTerminator`
   writes `.scalar retScalar` to local `0` and steps to `targetBb`;
2. When `evalExactDiv lhs rhs isSigned = .none` (division by zero, signed
   `MIN / -1`, or non-zero remainder), `evalTerminator` faults with
   `MirStepNode.fail .ub`;
3. When neither a type argument nor an operand type names an integer type, so
   the signedness of `T` is unknown, `evalTerminator` steps to
   `MirStepNode.unsupported` instead of assuming an unsigned division.
-/
theorem mir_evalTerminator_exact_div_intrinsic_corresponds
    (lhs rhs : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let uTerm := mkIntrinsicCallTerm "core::intrinsics::exact_div" [.uint .u32] argOps dest targetBb unwind span
    let sTerm := mkIntrinsicCallTerm "core::intrinsics::exact_div" [.int .i32] argOps dest targetBb unwind span
    let untypedTerm := mkIntrinsicCallTerm "core::intrinsics::exact_div" .nil argOps dest targetBb unwind span
    (∀ retScalar : ScalarInt,
      evalExactDiv lhs rhs false = .some retScalar →
      evalTerminator s uTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar retScalar), .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }) ∧
    (evalExactDiv lhs rhs false = .none →
      evalTerminator s uTerm .none = MirStepNode.fail .ub) ∧
    (∀ retScalar : ScalarInt,
      evalExactDiv lhs rhs true = .some retScalar →
      evalTerminator s sTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar retScalar), .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }) ∧
    (evalExactDiv lhs rhs true = .none →
      evalTerminator s sTerm .none = MirStepNode.fail .ub) ∧
    evalTerminator s untypedTerm .none = MirStepNode.unsupported := by
  dsimp only
  have hStr : stringEq "core::intrinsics::exact_div" "core::intrinsics::exact_div" = true := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro retScalar hOk
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, hStr,
      hOk, writePlaceValue, set?]
  · intro hUb
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, hStr, hUb]
  · intro retScalar hOk
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, hStr,
      hOk, writePlaceValue, set?]
  · intro hUb
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, hStr, hUb]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, hStr, resolveIntrinsicIsSigned,
      operandTy, placeTy]

/--
**Theorem L5.19 (`mir_evalTerminator_ub_checks_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::ub_checks"`:
1. Calling `"core::intrinsics::ub_checks"` with zero arguments writes boolean
   `true` (`Value.scalar ⟨1, 1⟩`) to `destination` and steps to `targetBb`;
2. Calling `"core::intrinsics::ub_checks"` with any non-empty argument list
   faults with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_ub_checks_intrinsic_corresponds
    (argVal : Value)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init argVal]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let okTerm := mkIntrinsicCallTerm "core::intrinsics::ub_checks" .nil .nil dest targetBb unwind span
    let badTerm :=
      mkIntrinsicCallTerm
        "core::intrinsics::ub_checks"
        .nil
        [.copy { local_ := 1, projection := .nil }]
        dest
        targetBb
        unwind
        span
    evalTerminator s okTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [.init (.scalar ⟨1, 1⟩), .init argVal]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s badTerm .none = MirStepNode.fail .ub := by
  dsimp only
  have h : classifyRustIntrinsic? "core::intrinsics::ub_checks" = .some .ubChecks := rfl
  have hEx : stringEq "core::intrinsics::ub_checks" "core::intrinsics::exact_div" = false := rfl
  refine ⟨?_, ?_⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, emptyMemory,
      isDirectExactDivTarget, evalDirectRustIntrinsic?, h, hEx,
      evalNonSelectIntrinsicCall, writeIntrinsicReturn,
      writePlaceValue, get?, set?]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]

/--
**Theorem L5.20 (`mir_evalTerminator_const_eval_select_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::const_eval_select"`:
1. When `arg_0` is a tuple `Value.aggregate 0 unpackedArgs` and `arg_2` resolves
   to a linked `calleeBody` with matching `argCount = length unpackedArgs` and
   non-intrinsic ABI, `evalTerminator` pushes `calleeBody` onto `s.memory.callStack`
   with `initLocals calleeBody unpackedArgs`;
2. When `arg_0` is `Value.unit` (0-tuple `()`) and `arg_2` resolves to a 0-arg
   linked `calleeBody`, `evalTerminator` pushes `calleeBody` with
   `initLocals calleeBody .nil`;
3. When `arg_2` resolves to an unlinked unreachable or panic target,
   `evalTerminator` dispatches to `MirStepNode.fail .ub`
   (`core::hint::unreachable_unchecked`), `MirStepNode.retOutcome .abort`
   (`core::panicking::panic_nounwind`), or `applyUnwindAction`
   (`core::panicking::panic`) rather than falling through to `extCall`;
4. When `arg_0` is not a tuple (`Value.scalar sc`) or `calleeBody.argCount` does
   not match `length unpackedArgs`, `evalTerminator` faults with
   `MirStepNode.fail .ub`;
5. When `arg_0` is `Value.unit` and `ARG` is a tuple of inhabited zero-sized
   fields such as `((), ())`, `unpackConstEvalSelectArgs?` yields one
   `Value.unit` per field, and it rejects non-tuple `ARG`, non-ZST tuple
   elements (`(u32,)`), uninhabited elements (`(!,)`), or mismatched `.aggregate`
   tuple arities with `.none`.
-/
theorem mir_evalTerminator_const_eval_select_intrinsic_corresponds
    (v1 v2 : Value)
    (sc : ScalarInt)
    (callerBody calleeBody2 calleeBody0 : CapturedMir)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (hPath2 : calleeBody2.defPath = "core::rt_callee_2")
    (hArgs2 : calleeBody2.argCount = 2)
    (hConv2 : calleeBody2.fnAbi.conv = .rust)
    (hParams2 : calleeBody2.typeParamCount = 0 := by rfl)
    (hPath0 : calleeBody0.defPath = "core::rt_callee_0")
    (hArgs0 : calleeBody0.argCount = 0)
    (hConv0 : calleeBody0.fnAbi.conv = .rust)
    (hParams0 : calleeBody0.typeParamCount = 0 := by rfl) :
    let dest : Place := { local_ := 0, projection := .nil }
    let constFnOp : Operand :=
      .constant { ty := { kind := .fnDef "core::ct_callee" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOp2 : Operand :=
      .constant { ty := { kind := .fnDef "core::rt_callee_2" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOp0 : Operand :=
      .constant { ty := { kind := .fnDef "core::rt_callee_0" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpUnreach : Operand :=
      .constant { ty := { kind := .fnDef "core::hint::unreachable_unchecked" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpNounwind : Operand :=
      .constant { ty := { kind := .fnDef "core::panicking::panic_nounwind" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtFnOpPanic : Operand :=
      .constant { ty := { kind := .fnDef "core::panicking::panic" .nil, layoutIdx := 0 }, val := .zeroSized }
    let argOps2 : List Operand := [
      .copy { local_ := 1, projection := .nil },
      constFnOp,
      rtFnOp2
    ]
    let argOps0 : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOp0
    ]
    let argOpsUnreach : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpUnreach
    ]
    let argOpsNounwind : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpNounwind
    ]
    let argOpsPanic : List Operand := [
      .copy { local_ := 2, projection := .nil },
      constFnOp,
      rtFnOpPanic
    ]
    let argOpsBadTuple : List Operand := [
      .copy { local_ := 3, projection := .nil },
      constFnOp,
      rtFnOp2
    ]
    let argOpsArityMismatch : List Operand := [
      .copy { local_ := 1, projection := .nil },
      constFnOp,
      rtFnOp0
    ]
    let locals : List LocalSlot := [
      .uninit,
      .init (.aggregate 0 [v1, v2]),
      .init .unit,
      .init (.scalar sc)
    ]
    let mem : Memory := { emptyMemory with callees := [calleeBody2, calleeBody0] }
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := mem
    }
    let term2 := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOps2 dest targetBb unwind span
    let term0 := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOps0 dest targetBb unwind span
    let termUnreach := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsUnreach dest targetBb unwind span
    let termNounwind := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsNounwind dest targetBb unwind span
    let termPanic := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsPanic dest targetBb unwind span
    let termBadTuple := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsBadTuple dest targetBb unwind span
    let termBadArity := mkIntrinsicCallTerm "core::intrinsics::const_eval_select" .nil argOpsArityMismatch dest targetBb unwind span
    evalTerminator s term2 (.some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals dest targetBb calleeBody2 [v1, v2] unwind) ∧
    evalTerminator s term0 (.some callerBody) =
      MirStepNode.step (pushCalleeFrame s callerBody locals dest targetBb calleeBody0 .nil unwind) ∧
    evalTerminator s termUnreach (.some callerBody) = MirStepNode.fail .ub ∧
    evalTerminator s termNounwind (.some callerBody) = MirStepNode.retOutcome .abort ∧
    evalTerminator s termPanic (.some callerBody) =
      (match applyUnwindAction s locals mem unwind with
       | .running nextState => MirStepNode.step nextState
       | .halted out => MirStepNode.retOutcome out
       | .faulted fk => MirStepNode.fail fk) ∧
    evalTerminator s termBadTuple (.some callerBody) = MirStepNode.fail .ub ∧
    evalTerminator s termBadArity (.some callerBody) = MirStepNode.fail .ub ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.tuple .nil, .tuple .nil])) = .some [.unit, .unit] ∧
    unpackConstEvalSelectArgs? .unit (.some (.uint .u32)) = .none ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.uint .u32])) = .none ∧
    unpackConstEvalSelectArgs? .unit (.some (.tuple [.never])) = .none ∧
    unpackConstEvalSelectArgs? (.aggregate 0 [v1, v2]) (.some (.uint .u32)) = .none ∧
    unpackConstEvalSelectArgs? (.aggregate 0 [v1, v2]) (.some (.tuple [.uint .u32])) = .none := by
  dsimp only
  have hFindSel2 : stringEq calleeBody2.defPath "core::intrinsics::const_eval_select" = false := by
    rw [hPath2]; rfl
  have hFindSel0 : stringEq calleeBody0.defPath "core::intrinsics::const_eval_select" = false := by
    rw [hPath0]; rfl
  have hMatch2 : stringEq calleeBody2.defPath "core::rt_callee_2" = true := by
    rw [hPath2]; rfl
  have hMiss20 : stringEq calleeBody2.defPath "core::rt_callee_0" = false := by
    rw [hPath2]; rfl
  have hMatch0 : stringEq calleeBody0.defPath "core::rt_callee_0" = true := by
    rw [hPath0]; rfl
  have hMiss2U : stringEq calleeBody2.defPath "core::hint::unreachable_unchecked" = false := by
    rw [hPath2]; rfl
  have hMiss0U : stringEq calleeBody0.defPath "core::hint::unreachable_unchecked" = false := by
    rw [hPath0]; rfl
  have hMiss2N : stringEq calleeBody2.defPath "core::panicking::panic_nounwind" = false := by
    rw [hPath2]; rfl
  have hMiss0N : stringEq calleeBody0.defPath "core::panicking::panic_nounwind" = false := by
    rw [hPath0]; rfl
  have hMiss2P : stringEq calleeBody2.defPath "core::panicking::panic" = false := by
    rw [hPath2]; rfl
  have hMiss0P : stringEq calleeBody0.defPath "core::panicking::panic" = false := by
    rw [hPath0]; rfl
  have hKind : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
  have hEx : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
  have hKindU : classifyRustIntrinsic? "core::hint::unreachable_unchecked" = .none := rfl
  have hExU : stringEq "core::hint::unreachable_unchecked" "core::intrinsics::exact_div" = false := rfl
  have hKindN : classifyRustIntrinsic? "core::panicking::panic_nounwind" = .none := rfl
  have hExN : stringEq "core::panicking::panic_nounwind" "core::intrinsics::exact_div" = false := rfl
  have hKindP : classifyRustIntrinsic? "core::panicking::panic" = .none := rfl
  have hExP : stringEq "core::panicking::panic" "core::intrinsics::exact_div" = false := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?, checkCalleeTargetCompatible,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, unpackConstEvalSelectArgs?, resolveConstEvalSelectTarget?,
      hMatch2, hArgs2, hConv2, hParams2, callConvEq, length]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?, checkCalleeTargetCompatible,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?, hMiss20, hMatch0, hArgs0, hConv0,
      hParams0, callConvEq, length]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2U, hMiss0U, hKindU, hExU]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2N, hMiss0N, hKindN, hExN]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, emptyMemory, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, resolveConstEvalSelectTarget?,
      hMiss2P, hMiss0P, hKindP, hExP]
    rfl
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, evalConstValue, get?, lookupCallee,
      resolveCalleeBodyAndArgs?, findCallee?, checkCalleeTargetCompatible,
      hFindSel2, hFindSel0, isDirectExactDivTarget, evalDirectRustIntrinsic?,
      hKind, hEx, unpackConstEvalSelectArgs?, resolveConstEvalSelectTarget?,
      hMiss20, hMatch0, hArgs0, hConv0, hParams0, callConvEq, length]

/--
**Theorem L5.21 (`mir_evalTerminator_arith_offset_intrinsic_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::arith_offset"`:
1. For any 8-byte `ProvenancePtr` `ptrVal`, any 8-byte `isize` scalar `countSc`,
   and `T = u32` (4 bytes), `evalTerminator` preserves `ptrVal.allocId` and
   `ptrVal.tag` and updates `offsetBytes` via `evalArithOffset ptrVal 8 countSc 4`;
2. Negative signed `isize` offset `-2` (`2^64 - 2`) on `T = u32` subtracts `8`
   bytes modulo `2^64`;
3. Non-pointer first argument, non-8-byte `countSc`, or unsized pointee type
   (`.slice (.uint .u8)` or compound `.tuple [.uint .u32, .slice (.uint .u8)]`)
   faults with `MirStepNode.fail .ub`, while a sized
   pointee without a resolvable layout (an ADT `test::Foo` that no local has as
   its type) steps to `MirStepNode.unsupported` instead of borrowing an
   unrelated layout;
4. For the padded tuple `T = (u32, u8)` with no `LayoutTable` entry, the stride
   is the padded size `8`, not the field sum `5`: `evalTerminator` updates
   `offsetBytes` via `evalArithOffset ptrVal 8 countSc 8`;
5. Static sizes resolve through nested floats, arrays, and tuples: `[f64; 4]` is
   `32`, `((u32, u32), f64)` is `16`, `(u32, u8)` is `8`, `[(u32, u8); 2]` is
   `16`, `((u32, u8), u8)` is `12` (inner padding is not reused), and a 12-field
   tuple of `u8` is `12` (tuple arity does not consume the nesting fuel).
-/
theorem mir_evalTerminator_arith_offset_intrinsic_corresponds
    (ptrVal : ProvenancePtr)
    (countSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let okTerm := mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.uint .u32] argOps dest targetBb unwind span
    let paddedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .uint .u8]]
        argOps dest targetBb unwind span
    let unsizedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.slice (.uint .u8)] argOps dest targetBb unwind span
    let compoundUnsizedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .slice (.uint .u8)]]
        argOps dest targetBb unwind span
    let adtTerm :=
      mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.adt "test::Foo" .nil]
        argOps dest targetBb unwind span
    let u8x12 : RigidTy :=
      .tuple [.uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8,
        .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8]
    (∀ newPtr : ProvenancePtr,
      evalArithOffset ptrVal 8 countSc 4 = .some newPtr →
      evalTerminator s okTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.ptr newPtr 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
          }
          memory := emptyMemory
        }) ∧
    (evalArithOffset ptrVal 8 countSc 4 = .none →
      evalTerminator s okTerm .none = MirStepNode.fail .ub) ∧
    (∀ newPtr : ProvenancePtr,
      evalArithOffset ptrVal 8 countSc 8 = .some newPtr →
      evalTerminator s paddedTerm .none =
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.ptr newPtr 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
          }
          memory := emptyMemory
        }) ∧
    evalTerminator s unsizedTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s compoundUnsizedTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s adtTerm .none = MirStepNode.unsupported ∧
    evalArithOffset { allocId := 7, offsetBytes := 20 } 8 ⟨18446744073709551614, 8⟩ 4 =
      .some { allocId := 7, offsetBytes := 12 } ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.array (.float .f64) 4) = .some 32 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.tuple [.uint .u32, .uint .u32], .float .f64]) = .some 16 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.array (.tuple [.uint .u32, .uint .u8]) 2) = .some 16 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.tuple [.uint .u32, .uint .u8], .uint .u8]) = .some 12 ∧
    intrinsicRigidTyByteSize .nil emptyLayoutTable u8x12 = .some 12 := by
  dsimp only
  have hKind : classifyRustIntrinsic? "core::intrinsics::arith_offset" = .some .arithOffset := rfl
  have hEx : stringEq "core::intrinsics::arith_offset" "core::intrinsics::exact_div" = false := rfl
  have hPadSz : intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 := rfl
  have hCalc :
      evalTerminator
        { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)] },
          memory := emptyMemory }
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.uint .u32]
          [.copy { local_ := 1, projection := .nil }, .copy { local_ := 2, projection := .nil }]
          { local_ := 0, projection := .nil } targetBb unwind span)
        .none =
      (match evalArithOffset ptrVal 8 countSc 4 with
       | .some retPtrVal =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.ptr retPtrVal 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) := by
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalArithOffset ptrVal 8 countSc 4 <;> rfl
  have hCalcPad :
      evalTerminator
        { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)] },
          memory := emptyMemory }
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" [.tuple [.uint .u32, .uint .u8]]
          [.copy { local_ := 1, projection := .nil }, .copy { local_ := 2, projection := .nil }]
          { local_ := 0, projection := .nil } targetBb unwind span)
        .none =
      (match evalArithOffset ptrVal 8 countSc 8 with
       | .some retPtrVal =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.ptr retPtrVal 8), .init (.ptr ptrVal 8), .init (.scalar countSc)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) := by
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall, hPadSz,
      writeIntrinsicReturn, writePlaceValue, set?]
    cases evalArithOffset ptrVal 8 countSc 8 <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro newPtr hOk
    rw [hCalc, hOk]
  · intro hNone
    rw [hCalc, hNone]
  · intro newPtr hOk
    rw [hCalcPad, hOk]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, findDeclLayoutForRigidTy,
      intrinsicUnresolvedLayoutStep]
  · have hUnsizedSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .slice (.uint .u8)]) = .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall, hUnsizedSz,
      intrinsicUnresolvedLayoutStep]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hKind, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux,
      findDeclLayoutForRigidTy, intrinsicUnresolvedLayoutStep]

/--
**Theorem L5.22 (`mir_evalTerminator_bit_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for the bit-manipulation
intrinsics (`ctlz`, `ctlz_nonzero`, `cttz`, `cttz_nonzero`, `ctpop`, `bswap`,
`bitreverse`):
1. For any scalar `sc : ScalarInt`, `ctlz`, `cttz`, `ctpop`, `bswap`, and
   `bitreverse` write their evaluated `ScalarInt` result to `destination` when
   `sc.sizeBytes > 0`, and fault with `MirStepNode.fail .ub` when `sc.sizeBytes = 0`;
2. `ctlz_nonzero` and `cttz_nonzero` step to `targetBb` when `sc` is non-zero
   and fault with `MirStepNode.fail .ub` when `sc` is zero (`⟨0, sz⟩`).
-/
theorem mir_evalTerminator_bit_intrinsics_corresponds
    (sc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar sc)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let mkCall (name : DefPath) := mkIntrinsicCallTerm name .nil argOps dest targetBb unwind span
    let mkExpected (resOpt : Option ScalarInt) : MirStepNode :=
      match resOpt with
      | .some ret =>
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar ret), .init (.scalar sc)]
          }
          memory := emptyMemory
        }
      | .none => MirStepNode.fail .ub
    evalTerminator s (mkCall "core::intrinsics::ctlz") .none = mkExpected (evalCtlz sc) ∧
    evalTerminator s (mkCall "core::intrinsics::ctlz_nonzero") .none = mkExpected (evalCtlzNonzero sc) ∧
    evalTerminator s (mkCall "core::intrinsics::cttz") .none = mkExpected (evalCttz sc) ∧
    evalTerminator s (mkCall "core::intrinsics::cttz_nonzero") .none = mkExpected (evalCttzNonzero sc) ∧
    evalTerminator s (mkCall "core::intrinsics::ctpop") .none = mkExpected (evalCtpop sc) ∧
    evalTerminator s (mkCall "core::intrinsics::bswap") .none = mkExpected (evalBswap sc) ∧
    evalTerminator s (mkCall "core::intrinsics::bitreverse") .none = mkExpected (evalBitreverse sc) ∧
    evalCtlzNonzero ⟨0, 4⟩ = .none ∧
    evalCttzNonzero ⟨0, 8⟩ = .none ∧
    evalCtlz ⟨0, 1⟩ = .some ⟨8, 4⟩ ∧
    evalCttz ⟨0, 2⟩ = .some ⟨16, 4⟩ ∧
    evalCtpop ⟨0xF0F0, 2⟩ = .some ⟨8, 4⟩ ∧
    evalBswap ⟨0x12345678, 4⟩ = .some ⟨0x78563412, 4⟩ ∧
    evalBitreverse ⟨0x80, 1⟩ = .some ⟨0x01, 1⟩ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::ctlz" = .some .ctlz := rfl
    have hEx : stringEq "core::intrinsics::ctlz" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtlz sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::ctlz_nonzero" = .some .ctlzNonzero := rfl
    have hEx : stringEq "core::intrinsics::ctlz_nonzero" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtlzNonzero sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::cttz" = .some .cttz := rfl
    have hEx : stringEq "core::intrinsics::cttz" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCttz sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::cttz_nonzero" = .some .cttzNonzero := rfl
    have hEx : stringEq "core::intrinsics::cttz_nonzero" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCttzNonzero sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::ctpop" = .some .ctpop := rfl
    have hEx : stringEq "core::intrinsics::ctpop" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalCtpop sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::bswap" = .some .bswap := rfl
    have hEx : stringEq "core::intrinsics::bswap" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalBswap sc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::bitreverse" = .some .bitreverse := rfl
    have hEx : stringEq "core::intrinsics::bitreverse" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalBitreverse sc <;> rfl

/--
**Theorem L5.23 (`mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for wrapping, saturating,
and unchecked arithmetic and shift intrinsics (`wrapping_add`, `wrapping_sub`,
`wrapping_mul`, `saturating_add`, `saturating_sub`, `unchecked_shl`,
`unchecked_shr`, `unchecked_add`, `unchecked_sub`, `unchecked_mul`,
`unchecked_div`, `unchecked_rem`).
-/
theorem mir_evalTerminator_wrapping_saturating_unchecked_intrinsics_corresponds
    (lhs rhs : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let mkCall (name : DefPath) (tyArgs : List RigidTy) :=
      mkIntrinsicCallTerm name tyArgs argOps dest targetBb unwind span
    let mkExpected (resOpt : Option ScalarInt) : MirStepNode :=
      match resOpt with
      | .some ret =>
        MirStepNode.step {
          frame := {
            blockIdx := targetBb
            stmtIdx := 0
            locals := [.init (.scalar ret), .init (.scalar lhs), .init (.scalar rhs)]
          }
          memory := emptyMemory
        }
      | .none => MirStepNode.fail .ub
    evalTerminator s (mkCall "core::intrinsics::wrapping_add" .nil) .none =
      mkExpected (evalWrappingAdd lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::wrapping_sub" .nil) .none =
      mkExpected (evalWrappingSub lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::wrapping_mul" .nil) .none =
      mkExpected (evalWrappingMul lhs rhs) ∧
    evalTerminator s (mkCall "core::intrinsics::saturating_add" [.int .i32]) .none =
      mkExpected (evalSaturatingAdd lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::saturating_sub" [.uint .u32]) .none =
      mkExpected (evalSaturatingSub lhs rhs false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_shl" [.uint .u32, .int .i32]) .none =
      mkExpected (evalUncheckedShl lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_shr" [.int .i32, .uint .u32]) .none =
      mkExpected (evalUncheckedShr lhs rhs true false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_add" [.int .i32]) .none =
      mkExpected (evalUncheckedAdd lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_sub" [.uint .u32]) .none =
      mkExpected (evalUncheckedSub lhs rhs false) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_mul" [.int .i16]) .none =
      mkExpected (evalUncheckedMul lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_div" [.int .i32]) .none =
      mkExpected (evalUncheckedDiv lhs rhs true) ∧
    evalTerminator s (mkCall "core::intrinsics::unchecked_rem" [.int .i32]) .none =
      mkExpected (evalUncheckedRem lhs rhs true) ∧
    evalUncheckedAdd ⟨255, 1⟩ ⟨1, 1⟩ false = .none ∧
    evalUncheckedSub ⟨0, 1⟩ ⟨1, 1⟩ false = .none ∧
    evalUncheckedDiv ⟨128, 1⟩ ⟨255, 1⟩ true = .none ∧
    evalUncheckedRem ⟨128, 1⟩ ⟨255, 1⟩ true = .none ∧
    evalUncheckedShl ⟨1, 4⟩ ⟨32, 4⟩ false = .none ∧
    evalUncheckedShr ⟨1, 4⟩ ⟨255, 1⟩ false true = .none := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_add" = .some .wrappingAdd := rfl
    have hEx : stringEq "core::intrinsics::wrapping_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingAdd lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_sub" = .some .wrappingSub := rfl
    have hEx : stringEq "core::intrinsics::wrapping_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingSub lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::wrapping_mul" = .some .wrappingMul := rfl
    have hEx : stringEq "core::intrinsics::wrapping_mul" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalWrappingMul lhs rhs <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_add" = .some .saturatingAdd := rfl
    have hEx : stringEq "core::intrinsics::saturating_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSaturatingAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_sub" = .some .saturatingSub := rfl
    have hEx : stringEq "core::intrinsics::saturating_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSaturatingSub lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shl" = .some .uncheckedShl := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shl" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedShl lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shr" = .some .uncheckedShr := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shr" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedShr lhs rhs true false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_add" = .some .uncheckedAdd := rfl
    have hEx : stringEq "core::intrinsics::unchecked_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_sub" = .some .uncheckedSub := rfl
    have hEx : stringEq "core::intrinsics::unchecked_sub" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedSub lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_mul" = .some .uncheckedMul := rfl
    have hEx : stringEq "core::intrinsics::unchecked_mul" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedMul lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_div" = .some .uncheckedDiv := rfl
    have hEx : stringEq "core::intrinsics::unchecked_div" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedDiv lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_rem" = .some .uncheckedRem := rfl
    have hEx : stringEq "core::intrinsics::unchecked_rem" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalUncheckedRem lhs rhs true <;> rfl

/--
**Theorem L5.24 (`mir_evalTerminator_comparison_and_layout_intrinsics_corresponds`)**:
Universal positive and negative (`.ub`) correspondence for
`"core::intrinsics::three_way_compare"`, `"core::intrinsics::size_of_val"`, and
`"core::intrinsics::align_of_val"`:
1. `three_way_compare` evaluates `evalThreeWayCompare lhs rhs isSigned` and
   returns `Ordering::Less` (`⟨255, 1⟩`), `Ordering::Equal` (`⟨0, 1⟩`), or
   `Ordering::Greater` (`⟨1, 1⟩`);
2. `size_of_val` and `align_of_val` compute static size/alignment for sized
   thin pointers and dynamic byte size `elemSz * len` / element alignment for
   slice and `str` fat pointers `Value.aggregate 0 [.ptr p 8, .scalar lenSc]`,
   faulting with `MirStepNode.fail .ub` when `elemSz * len > isize::MAX` (for
   `align_of_val` as well as `size_of_val`, since both share the safety
   conditions of `size_of_val_raw`) or when pointer metadata is malformed;
3. `size_of_val::<(u32, u8)>` on a thin pointer returns the padded size `8`;
   `evalSliceSizeOfVal 4 ⟨2^61, 8⟩` faults (`2^63 = isize::MAX + 1` bytes) while
   `evalSliceSizeOfVal 1 ⟨isize::MAX, 8⟩` succeeds; `[(u32, u64); 2]` and the
   9-field tuple `(u8, u8, u8, u8, u8, u8, u8, u8, u64)` have alignment `8`;
4. `size_of_val` and `align_of_val` on `dyn Trait` with a valid wide pointer
   step to `MirStepNode.unsupported` (because dynamic size and alignment live in
   the vtable), whereas passing a thin pointer to `size_of_val::<dyn Trait>` or
   `align_of_val::<dyn Trait>` faults with `MirStepNode.fail .ub`; `size_of_val`
   on an ADT without a resolvable layout steps to `MirStepNode.unsupported`; and
   `findDeclLayoutForRigidTy` resolves layouts by matching a local's type, never
   by position;
5. `size_of_val` and `align_of_val` step to `MirStepNode.unsupported` rather
   than faulting on well-typed custom dynamically sized types the model cannot
   size: a wide pointer to an ADT (`test::SliceTail`) or to a tuple with a
   slice tail (`(u32, [u8])`), and a thin pointer to an extern type
   (`test::Opaque`) or to a tuple with an extern-type tail; a thin pointer to
   the slice-tailed tuple and a wide pointer to `u64` remain malformed and
   fault with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_comparison_and_layout_intrinsics_corresponds
    (lhs rhs : ScalarInt)
    (ptrVal : ProvenancePtr)
    (lenSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let cmpOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let thinOps : List Operand := [.copy { local_ := 3, projection := .nil }]
    let fatOps : List Operand := [.copy { local_ := 4, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [
      .uninit,
      .init (.scalar lhs),
      .init (.scalar rhs),
      .init (.ptr ptrVal 8),
      .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
    ]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    let cmpTerm := mkIntrinsicCallTerm "core::intrinsics::three_way_compare" [.int .i32] cmpOps dest targetBb unwind span
    let szSizedTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.uint .u64] thinOps dest targetBb unwind span
    let szSliceTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.slice (.uint .u32)] fatOps dest targetBb unwind span
    let alignSizedTerm := mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.uint .u128] thinOps dest targetBb unwind span
    let alignSliceTerm := mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.slice (.uint .u32)] fatOps dest targetBb unwind span
    let badSizedWithFatTerm := mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.uint .u64] fatOps dest targetBb unwind span
    let szPaddedTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.tuple [.uint .u32, .uint .u8]]
        thinOps dest targetBb unwind span
    let szDynTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.dynamic "core::fmt::Debug"]
        fatOps dest targetBb unwind span
    let alignDynTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.dynamic "core::fmt::Debug"]
        fatOps dest targetBb unwind span
    let badDynThinSzTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.dynamic "core::fmt::Debug"]
        thinOps dest targetBb unwind span
    let badDynThinAlignTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.dynamic "core::fmt::Debug"]
        thinOps dest targetBb unwind span
    let szAdtTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.adt "test::Foo" .nil]
        thinOps dest targetBb unwind span
    let alignStrTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.str] fatOps dest targetBb unwind span
    let szAdtDstTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.adt "test::SliceTail" .nil]
        fatOps dest targetBb unwind span
    let alignTupleDstTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val"
        [.tuple [.uint .u32, .slice (.uint .u8)]] fatOps dest targetBb unwind span
    let szExternTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val" [.foreign "test::Opaque"]
        thinOps dest targetBb unwind span
    let alignExternTailTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val"
        [.tuple [.uint .u8, .foreign "test::Opaque"]] thinOps dest targetBb unwind span
    let badTupleDstThinTerm :=
      mkIntrinsicCallTerm "core::intrinsics::size_of_val"
        [.tuple [.uint .u32, .slice (.uint .u8)]] thinOps dest targetBb unwind span
    let badAlignSizedWithFatTerm :=
      mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.uint .u64] fatOps dest targetBb unwind span
    let u8Layout : TypeLayout :=
      { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory,
        fields := .primitive, variants := .single 0, isUninhabited := false }
    let u8Decls : List LocalDecl :=
      [{ mutability := .mut, ty := { kind := .uint .u8, layoutIdx := 0 }, debugName := none }]
    let u8Table : LayoutTable := { emptyLayoutTable with entries := [u8Layout] }
    evalTerminator s cmpTerm .none =
      (match evalThreeWayCompare lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ret),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s szSizedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨8, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s szSliceTerm .none =
      (match evalSliceSizeOfVal 4 lenSc with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ret),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s alignSizedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨16, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalTerminator s alignSliceTerm .none =
      (match evalSliceSizeOfVal 4 lenSc with
       | .some _ =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ⟨4, 8⟩),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s badSizedWithFatTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s szPaddedTerm .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [
            .init (.scalar ⟨8, 8⟩),
            .init (.scalar lhs),
            .init (.scalar rhs),
            .init (.ptr ptrVal 8),
            .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
          ]
        }
        memory := emptyMemory
      } ∧
    evalSliceSizeOfVal 4 ⟨2305843009213693952, 8⟩ = .none ∧
    evalSliceSizeOfVal 1 ⟨9223372036854775807, 8⟩ = .some ⟨9223372036854775807, 8⟩ ∧
    intrinsicRigidTyAlign .nil emptyLayoutTable (.array (.tuple [.uint .u32, .uint .u64]) 2) = .some 8 ∧
    intrinsicRigidTyAlign .nil emptyLayoutTable
      (.tuple [.uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8, .uint .u8,
        .uint .u8, .uint .u8, .uint .u64]) = .some 8 ∧
    evalTerminator s szDynTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignDynTerm .none = MirStepNode.unsupported ∧
    evalTerminator s badDynThinSzTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s badDynThinAlignTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s szAdtTerm .none = MirStepNode.unsupported ∧
    findDeclLayoutForRigidTy u8Decls u8Table (.uint .u8) = .some u8Layout ∧
    findDeclLayoutForRigidTy u8Decls u8Table (.adt "test::Foo" .nil) = .none ∧
    evalTerminator s alignStrTerm .none =
      (match evalSliceSizeOfVal 1 lenSc with
       | .some _ =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [
               .init (.scalar ⟨1, 8⟩),
               .init (.scalar lhs),
               .init (.scalar rhs),
               .init (.ptr ptrVal 8),
               .init (.aggregate 0 [.ptr ptrVal 8, .scalar lenSc])
             ]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s szAdtDstTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignTupleDstTerm .none = MirStepNode.unsupported ∧
    evalTerminator s szExternTerm .none = MirStepNode.unsupported ∧
    evalTerminator s alignExternTailTerm .none = MirStepNode.unsupported ∧
    evalTerminator s badTupleDstThinTerm .none = MirStepNode.fail .ub ∧
    evalTerminator s badAlignSizedWithFatTerm .none = MirStepNode.fail .ub := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::three_way_compare" = .some .threeWayCompare := rfl
    have hEx : stringEq "core::intrinsics::three_way_compare" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalThreeWayCompare lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, writeIntrinsicScalarResult, writeIntrinsicReturn,
      writePlaceValue, set?]
    cases evalSliceSizeOfVal 4 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSliceSizeOfVal 4 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hPadSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .uint .u8]) = .some 8 :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hPadSz,
      writeIntrinsicReturn, writePlaceValue, set?]
    rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux,
      findDeclLayoutForRigidTy, intrinsicUnresolvedLayoutStep]

  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicReturn, writePlaceValue, set?]
    cases evalSliceSizeOfVal 1 lenSc <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable (.tuple [.uint .u32, .slice (.uint .u8)]) =
          .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hSz,
      intrinsicUnresolvedLayoutStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]

/--
**Theorem L5.25 (`mir_evalTerminator_align_of_val_rejects_oversized_slices`)**:
Concrete instance of the `align_of_val` slice-size check in L5.24. For a wide
pointer whose length metadata is `2^61`, `align_of_val::<[u32]>` faults with
`MirStepNode.fail .ub`, because the slice would span `2^63` bytes, one more than
`isize::MAX`; `align_of_val::<str>` on the same pointer returns `1`, because
`2^61` bytes fit in `isize`.
-/
theorem mir_evalTerminator_align_of_val_rejects_oversized_slices
    (ptrVal : ProvenancePtr)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let fatOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let dest : Place := { local_ := 0, projection := .nil }
    let fatPtr : Value := .aggregate 0 [.ptr ptrVal 8, .scalar ⟨2305843009213693952, 8⟩]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init fatPtr] }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.slice (.uint .u32)]
          fatOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" [.str]
          fatOps dest targetBb unwind span) .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := [.init (.scalar ⟨1, 8⟩), .init fatPtr]
        }
        memory := emptyMemory
      } := by
  dsimp only
  have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
  have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
  have hBig : evalSliceSizeOfVal 4 ⟨2305843009213693952, 8⟩ = .none := rfl
  have hFit :
      evalSliceSizeOfVal 1 ⟨2305843009213693952, 8⟩ = .some ⟨2305843009213693952, 8⟩ :=
    rfl
  refine ⟨?_, ?_⟩
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intrinsicRigidTyAlign, intrinsicRigidTyAlignAux, intrinsicRigidTyKindAlign,
      intCastTargetBytes, hBig]
  · unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hFit,
      writeIntrinsicReturn, writePlaceValue, set?]

/--
**Theorem L5.26 (`mir_evalTerminator_intrinsic_signedness_fails_closed`)**:
Signedness resolution for the integer intrinsics accepts exactly the types each
intrinsic is defined for and never guesses:
1. `three_way_compare::<char>` compares as unsigned
   (`evalThreeWayCompare lhs rhs false`), because `core` documents that its
   arguments "must be of character or integer (signed or unsigned) type";
2. `saturating_add::<char>` steps to `MirStepNode.unsupported`, because `char`
   is not an integer type;
3. `unchecked_shl::<u32>` without a second type argument or operand types steps
   to `MirStepNode.unsupported`, because the signedness of the shift count `U`
   decides whether a count with its top bit set is negative.
-/
theorem mir_evalTerminator_intrinsic_signedness_fails_closed
    (lhs rhs : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let argOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let dest : Place := { local_ := 0, projection := .nil }
    let locals : List LocalSlot := [.uninit, .init (.scalar lhs), .init (.scalar rhs)]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::three_way_compare" [.char]
          argOps dest targetBb unwind span) .none =
      (match evalThreeWayCompare lhs rhs false with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := [.init (.scalar ret), .init (.scalar lhs), .init (.scalar rhs)]
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::saturating_add" [.char]
          argOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::unchecked_shl" [.uint .u32]
          argOps dest targetBb unwind span) .none =
      MirStepNode.unsupported := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::three_way_compare" = .some .threeWayCompare := rfl
    have hEx : stringEq "core::intrinsics::three_way_compare" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      writeIntrinsicScalarResult, writeIntrinsicReturn, writePlaceValue, set?]
    cases evalThreeWayCompare lhs rhs false <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_add" = .some .saturatingAdd := rfl
    have hEx : stringEq "core::intrinsics::saturating_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shl" = .some .uncheckedShl := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shl" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicShiftSigned, operandTy, placeTy]

/--
Lift an `Option ScalarInt` returned by a scalar intrinsic evaluator to an
`RvalueEvalResult` (`.some sc ↦ .ok (.scalar sc) locals mem`, `.none ↦ .ub`),
matching `evalScalarBinOp`'s return type.
-/
@[reducible]
def liftIntrinsicScalarResult
    (res : Option ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory) :
    RvalueEvalResult :=
  match res with
  | .some sc => .ok (.scalar sc) locals mem
  | .none => .ub

/--
**Theorem L5.27 (`mir_intrinsic_scalars_agree_with_evalScalarBinOp`)**:
Universal correspondence between the `CallConv.rustIntrinsic` scalar evaluators
and `evalScalarBinOp` across all 11 operations lowered by `rustc`'s
`LowerIntrinsics` pass (`wrapping_add`, `wrapping_sub`, `wrapping_mul`,
`unchecked_add`, `unchecked_sub`, `unchecked_mul`, `unchecked_div`,
`unchecked_rem`, `unchecked_shl`, `unchecked_shr`, `three_way_compare`). For
any canonical equal-width non-zero-byte `ScalarInt` operands `lhs` and `rhs` and
any signedness `isSigned : Bool`, evaluating the intrinsic before
`LowerIntrinsics` produces the exact same result (or `.ub` fault) as evaluating
the corresponding `Rvalue.binaryOp` after `LowerIntrinsics`.
-/
theorem mir_intrinsic_scalars_agree_with_evalScalarBinOp
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (hNonZero : Nat.beq lhs.sizeBytes 0 = false)
    (hSameSz : Nat.beq lhs.sizeBytes rhs.sizeBytes = true)
    (hEqSz : rhs.sizeBytes = lhs.sizeBytes)
    (hCanonL : wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes) = lhs.bits)
    (hCanonR : wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes) = rhs.bits) :
    liftIntrinsicScalarResult (evalWrappingAdd lhs rhs) locals mem =
      evalScalarBinOp .add lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalWrappingSub lhs rhs) locals mem =
      evalScalarBinOp .sub lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalWrappingMul lhs rhs) locals mem =
      evalScalarBinOp .mul lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedAdd lhs rhs isSigned) locals mem =
      evalScalarBinOp .addUnchecked lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedSub lhs rhs isSigned) locals mem =
      evalScalarBinOp .subUnchecked lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedMul lhs rhs isSigned) locals mem =
      evalScalarBinOp .mulUnchecked lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedDiv lhs rhs isSigned) locals mem =
      evalScalarBinOp .div lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedRem lhs rhs isSigned) locals mem =
      evalScalarBinOp .rem lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedShl lhs rhs false) locals mem =
      evalScalarBinOp .shlUnchecked lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalUncheckedShr lhs rhs isSigned false) locals mem =
      evalScalarBinOp .shrUnchecked lhs rhs locals mem isSigned ∧
    liftIntrinsicScalarResult (evalThreeWayCompare lhs rhs isSigned) locals mem =
      evalScalarBinOp .cmp lhs rhs locals mem isSigned := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold liftIntrinsicScalarResult evalWrappingAdd evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
  · unfold liftIntrinsicScalarResult evalWrappingSub evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases Nat.ble rhs.bits lhs.bits <;> rfl
  · unfold liftIntrinsicScalarResult evalWrappingMul evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
  · unfold liftIntrinsicScalarResult evalUncheckedAdd evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases isSigned
    · cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.add lhs.bits rhs.bits) <;> rfl
    · cases signedOverflowAdd lhs.bits rhs.bits lhs.sizeBytes <;> rfl
  · unfold liftIntrinsicScalarResult evalUncheckedSub evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases isSigned
    · cases Nat.ble rhs.bits lhs.bits
      · rfl
      · cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.sub lhs.bits rhs.bits) <;> rfl
    · cases signedOverflowSub lhs.bits rhs.bits lhs.sizeBytes <;> rfl
  · unfold liftIntrinsicScalarResult evalUncheckedMul evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases isSigned
    · cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.mul lhs.bits rhs.bits) <;> rfl
    · cases signedOverflowMul lhs.bits rhs.bits lhs.sizeBytes <;> rfl
  · unfold liftIntrinsicScalarResult evalUncheckedDiv evalScalarBinOp evalSignedDiv
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases Nat.beq rhs.bits 0
    · cases isSigned
      · rfl
      · cases
          Bool.and
            (Nat.beq lhs.bits (scalarPow2 (Nat.sub (Nat.mul lhs.sizeBytes 8) 1)))
            (Nat.beq rhs.bits (Nat.sub (scalarModulus lhs.sizeBytes) 1)) <;> rfl
    · rfl
  · unfold liftIntrinsicScalarResult evalUncheckedRem evalScalarBinOp evalSignedRem
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases Nat.beq rhs.bits 0
    · cases isSigned
      · rfl
      · cases
          Bool.and
            (Nat.beq lhs.bits (scalarPow2 (Nat.sub (Nat.mul lhs.sizeBytes 8) 1)))
            (Nat.beq rhs.bits (Nat.sub (scalarModulus lhs.sizeBytes) 1)) <;> rfl
    · rfl
  · unfold liftIntrinsicScalarResult evalUncheckedShl evalScalarBinOp
    simp only [hEqSz, hNonZero, hCanonL, hCanonR, Bool.or_false, Bool.false_and, Bool.false_or]
    cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
  · unfold liftIntrinsicScalarResult evalUncheckedShr evalScalarBinOp
    simp only [hEqSz, hNonZero, hCanonL, hCanonR, Bool.or_false, Bool.false_and, Bool.false_or]
    cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
  · unfold liftIntrinsicScalarResult evalThreeWayCompare evalScalarBinOp
    simp only [hNonZero, hSameSz, hCanonL, hCanonR, Bool.not_true, Bool.or_false]
    cases isSigned <;> cases Nat.beq lhs.bits rhs.bits
    · cases Nat.ble lhs.bits rhs.bits <;> rfl
    · rfl
    · cases signedLt lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    · rfl

/--
**Theorem L5.28 (`mir_evalTerminator_dst_prefix_meta_decl_and_select_typeArgs_corresponds`)**:
Correspondence for DST layout-lookup filtering, non-last tuple field DST
validation, wide-pointer metadata validation, and `const_eval_select` tuple
type-argument propagation:
1. `findDeclLayoutForRigidTy`, `intrinsicRigidTyByteSize`, and
   `intrinsicRigidTyAlign` reject unsized types (`[u8]` and `(u32, [u8])`) even
   when `localDecls` contains a declaration of that unsized type with a layout
   table entry;
2. `size_of_val` and `align_of_val` fault with `MirStepNode.fail .ub` (rather
   than `.unsupported`) on tuples with an unsized non-last field
   (`([u8], ExternType)` with a thin pointer and `([u8], [u8])` with a wide
   pointer);
3. `size_of_val` and `align_of_val` fault with `MirStepNode.fail .ub` when a
   wide pointer to `dyn Trait` or `(u32, [u8])` carries non-scalar/non-pointer
   metadata (`.unit`), while an 8-byte vtable pointer `.ptr ptrVal 8` on
   `dyn Trait` steps to `MirStepNode.unsupported`;
4. `const_eval_select` with `ARG = (i32, i32)` or `(*const u32, isize)` in
   `target.typeArgs` forwards the argument/pointee types to an unlinked
   runtime intrinsic target (`exact_div`, `unchecked_add`, `arith_offset`) whose
   own `rtTarget.typeArgs` is `.nil`.
-/
theorem mir_evalTerminator_dst_prefix_meta_decl_and_select_typeArgs_corresponds
    (lhs rhs : ScalarInt)
    (ptrVal : ProvenancePtr)
    (offsetSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let fakeLayout : TypeLayout :=
      { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
        fields := .primitive, variants := .single 0, isUninhabited := false }
    let unsizedDecls : List LocalDecl :=
      [ { mutability := .mut, ty := { kind := .slice (.uint .u8), layoutIdx := 0 }, debugName := none },
        { mutability := .mut,
          ty := { kind := .tuple [.uint .u32, .slice (.uint .u8)], layoutIdx := 0 },
          debugName := none } ]
    let unsizedTable : LayoutTable := { emptyLayoutTable with entries := [fakeLayout] }
    let dest : Place := { local_ := 0, projection := .nil }
    let thinOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let fatValidOps : List Operand := [.copy { local_ := 2, projection := .nil }]
    let fatBadMetaOps : List Operand := [.copy { local_ := 3, projection := .nil }]
    let fatVtableOps : List Operand := [.copy { local_ := 4, projection := .nil }]
    let constFnOp : Operand :=
      .constant { ty := { kind := .fnDef "core::ct_callee" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtExactDivOp : Operand :=
      .constant { ty := { kind := .fnDef "core::intrinsics::exact_div" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtUncheckedAddOp : Operand :=
      .constant { ty := { kind := .fnDef "core::intrinsics::unchecked_add" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtArithOffsetOp : Operand :=
      .constant { ty := { kind := .fnDef "core::intrinsics::arith_offset" .nil, layoutIdx := 0 }, val := .zeroSized }
    let selectIntOps : List Operand := [
      .copy { local_ := 5, projection := .nil },
      constFnOp,
      rtExactDivOp
    ]
    let selectAddOps : List Operand := [
      .copy { local_ := 5, projection := .nil },
      constFnOp,
      rtUncheckedAddOp
    ]
    let selectPtrOps : List Operand := [
      .copy { local_ := 6, projection := .nil },
      constFnOp,
      rtArithOffsetOp
    ]
    let locals : List LocalSlot := [
      .uninit,
      .init (.ptr ptrVal 8),
      .init (.aggregate 0 [.ptr ptrVal 8, .scalar ⟨4, 8⟩]),
      .init (.aggregate 0 [.ptr ptrVal 8, .unit]),
      .init (.aggregate 0 [.ptr ptrVal 8, .ptr ptrVal 8]),
      .init (.aggregate 0 [.scalar lhs, .scalar rhs]),
      .init (.aggregate 0 [.ptr ptrVal 8, .scalar offsetSc])
    ]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    findDeclLayoutForRigidTy unsizedDecls unsizedTable (.slice (.uint .u8)) = .none ∧
    findDeclLayoutForRigidTy unsizedDecls unsizedTable
      (.tuple [.uint .u32, .slice (.uint .u8)]) = .none ∧
    intrinsicRigidTyByteSize unsizedDecls unsizedTable (.slice (.uint .u8)) = .none ∧
    intrinsicRigidTyAlign unsizedDecls unsizedTable
      (.tuple [.uint .u32, .slice (.uint .u8)]) = .none ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val"
          [.tuple [.slice (.uint .u8), .foreign "test::Opaque"]]
          thinOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val"
          [.tuple [.slice (.uint .u8), .foreign "test::Opaque"]]
          thinOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val"
          [.tuple [.slice (.uint .u8), .slice (.uint .u8)]]
          fatValidOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val"
          [.tuple [.slice (.uint .u8), .slice (.uint .u8)]]
          fatValidOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val"
          [.dynamic "core::fmt::Debug"]
          fatBadMetaOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val"
          [.dynamic "core::fmt::Debug"]
          fatBadMetaOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val"
          [.tuple [.uint .u32, .slice (.uint .u8)]]
          fatBadMetaOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val"
          [.tuple [.uint .u32, .slice (.uint .u8)]]
          fatBadMetaOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val"
          [.dynamic "core::fmt::Debug"]
          fatVtableOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.int .i32, .int .i32]]
          selectIntOps dest targetBb unwind span) .none =
      (match evalExactDiv lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.scalar ret) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.int .i32, .int .i32]]
          selectAddOps dest targetBb unwind span) .none =
      (match evalUncheckedAdd lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.scalar ret) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.rawPtr .not (.uint .u32), .int .isize]]
          selectPtrOps dest targetBb unwind span) .none =
      (match evalArithOffset ptrVal 8 offsetSc 4 with
       | .some ptr' =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.ptr ptr' 8) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hSz :
        intrinsicRigidTyByteSize .nil emptyLayoutTable
          (.tuple [.slice (.uint .u8), .foreign "test::Opaque"]) = .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hSz,
      intrinsicUnresolvedLayoutStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    have hAl :
        intrinsicRigidTyAlign .nil emptyLayoutTable
          (.tuple [.slice (.uint .u8), .foreign "test::Opaque"]) = .none :=
      rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall, hAl,
      intrinsicUnresolvedLayoutStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      intrinsicWidePointeeStep]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall]
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::exact_div" "core::intrinsics::exact_div" = true := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, length]
    cases evalExactDiv lhs rhs true <;> rfl
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::unchecked_add" "core::intrinsics::exact_div" = false := rfl
    have hAdd : classifyRustIntrinsic? "core::intrinsics::unchecked_add" = .some .uncheckedAdd := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hAdd, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, evalNonSelectIntrinsicCall, length]
    cases evalUncheckedAdd lhs rhs true <;> rfl
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::arith_offset" "core::intrinsics::exact_div" = false := rfl
    have hOff : classifyRustIntrinsic? "core::intrinsics::arith_offset" = .some .arithOffset := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hOff, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux,
      rigidTyKindByteSize, intCastTargetBytes, length]
    cases evalArithOffset ptrVal 8 offsetSc 4 <;> rfl

/-- Every scalar modulus `256 ^ k` is positive. -/
private theorem shiftParity_scalarModulus_ge_one : ∀ k : Nat, 1 ≤ scalarModulus k
  | 0 => by decide
  | k + 1 => by
    have ih := shiftParity_scalarModulus_ge_one k
    show 1 ≤ 256 * scalarModulus k
    omega

/-- The modulus of a non-zero byte width is at least `256`. -/
private theorem shiftParity_scalarModulus_succ_ge (k : Nat) : 256 ≤ scalarModulus (k + 1) := by
  have h := shiftParity_scalarModulus_ge_one k
  show 256 ≤ 256 * scalarModulus k
  omega

/--
A shift count whose sign bit is set is at least `128`, which is at least the
bit width `8 * lw` of any integer type of at most 16 bytes, so for every integer
type such a count is already an over-wide shift.
-/
private theorem shiftParity_negative_count_overshifts
    (lw rw b : Nat)
    (hR : Nat.beq rw 0 = false)
    (hW : lw ≤ 16)
    (hNeg : Nat.ble (Nat.div (scalarModulus rw) 2) b = true) :
    Nat.ble (Nat.mul lw 8) b = true := by
  cases rw with
  | zero => simp at hR
  | succ k =>
    have hm := shiftParity_scalarModulus_succ_ge k
    have h1 : scalarModulus (k + 1) / 2 ≤ b := Nat.le_of_ble_eq_true hNeg
    have h2 : lw * 8 ≤ b := by omega
    exact Nat.ble_eq_true_of_le h2

/--
**Theorem L5.29 (`mir_intrinsic_shifts_agree_with_evalScalarBinOp`)**:
Universal correspondence between `unchecked_shl::<T, U>` /
`unchecked_shr::<T, U>` and the `BinOp.shlUnchecked` / `BinOp.shrUnchecked`
that `rustc`'s `LowerIntrinsics` pass substitutes for them, for operands of
different widths and for signed shift counts. L5.27 covers only equal widths
and unsigned counts, but `core`'s integer methods shift by a `u32`
(`u64::unchecked_shl(self, rhs: u32)` calls `unchecked_shl::<u64, u32>`), so
most captured shifts have `T` and `U` of different widths.

For any canonical `lhs : T` of 1 to 16 bytes (the widths of Rust's integer
types), any canonical `rhs : U` of non-zero width, and any signedness of `T`
and `U`, the intrinsic and the binary operation agree, including on `.ub`. In
particular, the intrinsic's separate rejection of negative signed counts adds
nothing: a count with its sign bit set is at least `128` and therefore at least
the bit width of `T`.
-/
theorem mir_intrinsic_shifts_agree_with_evalScalarBinOp
    (lhs rhs : ScalarInt)
    (locals : List LocalSlot)
    (mem : Memory)
    (lhsSigned rhsSigned : Bool)
    (hL : Nat.beq lhs.sizeBytes 0 = false)
    (hR : Nat.beq rhs.sizeBytes 0 = false)
    (hW : lhs.sizeBytes ≤ 16)
    (hCanonL : wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes) = lhs.bits)
    (hCanonR : wrapScalarBits rhs.bits (scalarModulus rhs.sizeBytes) = rhs.bits) :
    liftIntrinsicScalarResult (evalUncheckedShl lhs rhs rhsSigned) locals mem =
      evalScalarBinOp .shlUnchecked lhs rhs locals mem lhsSigned ∧
    liftIntrinsicScalarResult (evalUncheckedShr lhs rhs lhsSigned rhsSigned) locals mem =
      evalScalarBinOp .shrUnchecked lhs rhs locals mem lhsSigned := by
  have key :
      Bool.or
          (Bool.and rhsSigned (isSignedNegative rhs.bits rhs.sizeBytes))
          (Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits) =
        Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits := by
    cases hb : Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits
    · cases rhsSigned
      · rfl
      · cases hn : isSignedNegative rhs.bits rhs.sizeBytes
        · rfl
        · exfalso
          unfold isSignedNegative at hn
          simp only [hR, hCanonR] at hn
          have h := shiftParity_negative_count_overshifts
            lhs.sizeBytes rhs.sizeBytes rhs.bits hR hW hn
          rw [hb] at h
          exact Bool.false_ne_true h
    · cases rhsSigned <;> simp
  refine ⟨?_, ?_⟩
  · unfold liftIntrinsicScalarResult evalUncheckedShl evalScalarBinOp
    simp only [hL, hR, hCanonL, hCanonR, Bool.or_false, key]
    cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
  · unfold liftIntrinsicScalarResult evalUncheckedShr evalScalarBinOp
    simp only [hL, hR, hCanonL, hCanonR, Bool.or_false, key]
    cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl

/--
Instances of L5.29 for the shapes `core` produces: `u64 << u32` by `63`
(defined, `2^63`), `u64 << u32` by `64` (`.ub`), and `i8 >> i32` by `-1` (`.ub`,
rejected as an over-wide shift).
-/
theorem mir_intrinsic_shifts_agree_with_evalScalarBinOp_instances :
    liftIntrinsicScalarResult (evalUncheckedShl ⟨1, 8⟩ ⟨63, 4⟩ false) .nil emptyMemory =
      .ok (.scalar ⟨9223372036854775808, 8⟩) .nil emptyMemory ∧
    evalScalarBinOp .shlUnchecked ⟨1, 8⟩ ⟨63, 4⟩ .nil emptyMemory false =
      .ok (.scalar ⟨9223372036854775808, 8⟩) .nil emptyMemory ∧
    liftIntrinsicScalarResult (evalUncheckedShl ⟨1, 8⟩ ⟨64, 4⟩ false) .nil emptyMemory = .ub ∧
    evalScalarBinOp .shlUnchecked ⟨1, 8⟩ ⟨64, 4⟩ .nil emptyMemory false = .ub ∧
    liftIntrinsicScalarResult (evalUncheckedShr ⟨128, 1⟩ ⟨4294967295, 4⟩ true true)
      .nil emptyMemory = .ub ∧
    evalScalarBinOp .shrUnchecked ⟨128, 1⟩ ⟨4294967295, 4⟩ .nil emptyMemory true = .ub := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/--
**Theorem L5.30 (`mir_evalTerminator_pointee_resolution_fails_closed`)**:
When neither a type argument nor an operand type names the pointee `T` of
`arith_offset::<T>`, `size_of_val::<T>`, or `align_of_val::<T>`, the stride,
size, or alignment is unknown, so `evalTerminator` steps to
`MirStepNode.unsupported` instead of reporting undefined behavior for a call
whose behavior the model cannot determine.
-/
theorem mir_evalTerminator_pointee_resolution_fails_closed
    (ptrVal : ProvenancePtr)
    (countSc : ScalarInt)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String) :
    let dest : Place := { local_ := 0, projection := .nil }
    let offsetOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let ptrOps : List Operand := [.copy { local_ := 1, projection := .nil }]
    let s : MachineState := {
      frame := {
        blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.ptr ptrVal 8), .init (.scalar countSc)]
      }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" .nil
          offsetOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          ptrOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" .nil
          ptrOps dest targetBb unwind span) .none =
      MirStepNode.unsupported := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::arith_offset" = .some .arithOffset := rfl
    have hEx : stringEq "core::intrinsics::arith_offset" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy]

/--
**Theorem L5.31 (`mir_evalTerminator_missing_pointee_ub_and_rhs_signedness_corresponds`)**:
Completes the positive and negative (`.ub`) correspondence for missing-pointee
pointer validation, `const_eval_select` tuple argument type forwarding, and
homogeneous binary intrinsic second-operand signedness resolution:
1. When `target.typeArgs = .nil` and `currentBody = .some callerBody` types the
   first operand as a non-pointer (`.uint .usize`), `arith_offset`, `size_of_val`,
   and `align_of_val` fault with `MirStepNode.fail .ub` via
   `intrinsicMissingPointeeStep` even if the runtime slot holds `.ptr ptrVal 8`;
2. When `target.typeArgs = .nil` and `currentBody = .none` (unknown pointee),
   `size_of_val` and `align_of_val` still validate `isValidIntrinsicPtrArgVal`
   first and fault with `MirStepNode.fail .ub` on non-pointer values
   (`.scalar ⟨0, 8⟩`, `.unit`), 32-bit pointers (`.ptr ptrVal 4`), or wide
   pointers with malformed metadata (`.aggregate 0 [.ptr ptrVal 8, .unit]`);
3. When `const_eval_select` carries `ARG = .tuple [.rawPtr .not (.uint .u32)]`
   (or non-pointer `ARG = .tuple [.uint .u32]`) and dispatches to unlinked
   `size_of_val` or `align_of_val` with `rtTarget.typeArgs = .nil`,
   `constEvalSelectTupleArgOps` forwards the element types of `ARG` so a
   non-pointer `ARG` element faults with `MirStepNode.fail .ub` via
   `intrinsicMissingPointeeStep` while a pointer `ARG` element evaluates
   `size_of_val::<u32>` to `4`;
4. When `target.typeArgs = .nil` and the first operand is an untyped local copy
   (`currentBody = .none`) while the second operand is a typed `i32` constant,
   homogeneous binary intrinsics (`exact_div`, `saturating_add`, `unchecked_add`)
   resolve `isSigned = true` from the second operand, whereas `unchecked_shr`
   (`sameRhsTy = false`) does not conflate `U` with `T` and steps to
   `MirStepNode.unsupported`;
5. When `const_eval_select` dispatches to `"std::hint::unreachable_unchecked"`
   (the visible `std` re-export path in `std`-linked crates), execution faults
   immediately with `MirStepNode.fail .ub`.
-/
theorem mir_evalTerminator_missing_pointee_ub_and_rhs_signedness_corresponds
    (ptrVal : ProvenancePtr)
    (countSc lhs rhs : ScalarInt)
    (callerBody : CapturedMir)
    (targetBb : BasicBlockIdx)
    (unwind : UnwindAction)
    (span : String)
    (hDecls :
      callerBody.localDecls =
        [ { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := .none },
          { mutability := .not, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := .none },
          { mutability := .not, ty := { kind := .int .isize, layoutIdx := 0 }, debugName := .none } ]) :
    let dest : Place := { local_ := 0, projection := .nil }
    let offsetOps : List Operand := [
      .copy { local_ := 1, projection := .nil },
      .copy { local_ := 2, projection := .nil }
    ]
    let ptrOps1 : List Operand := [.copy { local_ := 1, projection := .nil }]
    let ptrOps3 : List Operand := [.copy { local_ := 3, projection := .nil }]
    let ptrOps4 : List Operand := [.copy { local_ := 4, projection := .nil }]
    let ptrOps5 : List Operand := [.copy { local_ := 5, projection := .nil }]
    let constFnOp : Operand :=
      .constant { ty := { kind := .fnDef "core::ct_fn" .nil, layoutIdx := 0 }, val := .zeroSized }
    let rtSizeOfValOp : Operand :=
      .constant
        { ty := { kind := .fnDef "core::intrinsics::size_of_val" .nil, layoutIdx := 0 },
          val := .zeroSized }
    let rtAlignOfValOp : Operand :=
      .constant
        { ty := { kind := .fnDef "core::intrinsics::align_of_val" .nil, layoutIdx := 0 },
          val := .zeroSized }
    let rtStdUnreachOp : Operand :=
      .constant
        { ty := { kind := .fnDef "std::hint::unreachable_unchecked" .nil, layoutIdx := 0 },
          val := .zeroSized }
    let selectSizeOps : List Operand := [
      .copy { local_ := 6, projection := .nil },
      constFnOp,
      rtSizeOfValOp
    ]
    let selectAlignOps : List Operand := [
      .copy { local_ := 6, projection := .nil },
      constFnOp,
      rtAlignOfValOp
    ]
    let selectStdUnreachOps : List Operand := [
      .copy { local_ := 3, projection := .nil },
      constFnOp,
      rtStdUnreachOp
    ]
    let rhsSignedConstOp : Operand :=
      .constant { ty := { kind := .int .i32, layoutIdx := 0 }, val := .scalar (.int rhs) }
    let binMixedOps : List Operand := [
      .copy { local_ := 7, projection := .nil },
      rhsSignedConstOp
    ]
    let locals : List LocalSlot := [
      .uninit,
      .init (.ptr ptrVal 8),
      .init (.scalar countSc),
      .init .unit,
      .init (.ptr ptrVal 4),
      .init (.aggregate 0 [.ptr ptrVal 8, .unit]),
      .init (.aggregate 0 [.ptr ptrVal 8]),
      .init (.scalar lhs)
    ]
    let s : MachineState := {
      frame := { blockIdx := 0, stmtIdx := 0, locals := locals }
      memory := emptyMemory
    }
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::arith_offset" .nil
          offsetOps dest targetBb unwind span) (.some callerBody) =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          ptrOps1 dest targetBb unwind span) (.some callerBody) =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" .nil
          ptrOps1 dest targetBb unwind span) (.some callerBody) =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          [.copy { local_ := 2, projection := .nil }] dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" .nil
          [.copy { local_ := 2, projection := .nil }] dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          ptrOps3 dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          ptrOps4 dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::size_of_val" .nil
          ptrOps5 dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::align_of_val" .nil
          ptrOps5 dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.uint .u32]]
          selectSizeOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.uint .u32]]
          selectAlignOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple [.rawPtr .not (.uint .u32)]]
          selectSizeOps dest targetBb unwind span) .none =
      MirStepNode.step {
        frame := {
          blockIdx := targetBb
          stmtIdx := 0
          locals := .init (.scalar ⟨4, 8⟩) :: locals.tail
        }
        memory := emptyMemory
      } ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::exact_div" .nil
          binMixedOps dest targetBb unwind span) .none =
      (match evalExactDiv lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.scalar ret) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::saturating_add" .nil
          binMixedOps dest targetBb unwind span) .none =
      (match evalSaturatingAdd lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.scalar ret) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::unchecked_add" .nil
          binMixedOps dest targetBb unwind span) .none =
      (match evalUncheckedAdd lhs rhs true with
       | .some ret =>
         MirStepNode.step {
           frame := {
             blockIdx := targetBb
             stmtIdx := 0
             locals := .init (.scalar ret) :: locals.tail
           }
           memory := emptyMemory
         }
       | .none => MirStepNode.fail .ub) ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::unchecked_shr" .nil
          binMixedOps dest targetBb unwind span) .none =
      MirStepNode.unsupported ∧
    evalTerminator s
        (mkIntrinsicCallTerm "core::intrinsics::const_eval_select"
          [.tuple .nil]
          selectStdUnreachOps dest targetBb unwind span) .none =
      MirStepNode.fail .ub := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : classifyRustIntrinsic? "core::intrinsics::arith_offset" = .some .arithOffset := rfl
    have hEx : stringEq "core::intrinsics::arith_offset" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy,
      resolveProjectedTy, hDecls]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy,
      resolveProjectedTy, hDecls]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, intrinsicMissingPointeeStep, operandTy, placeTy,
      resolveProjectedTy, hDecls]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    have hEx : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, isValidIntrinsicPtrArgVal, operandTy, placeTy]
  · have h : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    have hEx : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicPointeeTy?, isValidIntrinsicPtrArgVal, operandTy, placeTy]
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hSz : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hSz, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, evalNonSelectIntrinsicCall,
      intrinsicMissingPointeeStep, length]
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::align_of_val" "core::intrinsics::exact_div" = false := rfl
    have hAl : classifyRustIntrinsic? "core::intrinsics::align_of_val" = .some .alignOfVal := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hAl, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, evalNonSelectIntrinsicCall,
      intrinsicMissingPointeeStep, length]
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "core::intrinsics::size_of_val" "core::intrinsics::exact_div" = false := rfl
    have hSz : classifyRustIntrinsic? "core::intrinsics::size_of_val" = .some .sizeOfVal := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hSz, unpackConstEvalSelectArgs?,
      resolveConstEvalSelectTarget?, evalNonSelectIntrinsicCall,
      intrinsicRigidTyByteSize, intrinsicRigidTyByteSizeAux, rigidTyKindByteSize,
      intCastTargetBytes, signedHalfModulus, scalarModulus, writeIntrinsicReturn,
      writePlaceValue, set?, length]
  · have hEx : stringEq "core::intrinsics::exact_div" "core::intrinsics::exact_div" = true := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      hEx, resolveIntrinsicIsSigned, operandTy, placeTy]
    cases evalExactDiv lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::saturating_add" = .some .saturatingAdd := rfl
    have hEx : stringEq "core::intrinsics::saturating_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicIsSigned, operandTy, placeTy]
    cases evalSaturatingAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_add" = .some .uncheckedAdd := rfl
    have hEx : stringEq "core::intrinsics::unchecked_add" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicIsSigned, operandTy, placeTy]
    cases evalUncheckedAdd lhs rhs true <;> rfl
  · have h : classifyRustIntrinsic? "core::intrinsics::unchecked_shr" = .some .uncheckedShr := rfl
    have hEx : stringEq "core::intrinsics::unchecked_shr" "core::intrinsics::exact_div" = false := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, h, hEx, evalNonSelectIntrinsicCall,
      resolveIntrinsicIsSigned, operandTy, placeTy]
  · have hSel : classifyRustIntrinsic? "core::intrinsics::const_eval_select" = .some .constEvalSelect := rfl
    have hEx1 : stringEq "core::intrinsics::const_eval_select" "core::intrinsics::exact_div" = false := rfl
    have hEx2 : stringEq "std::hint::unreachable_unchecked" "core::intrinsics::exact_div" = false := rfl
    have hUnr : classifyRustIntrinsic? "std::hint::unreachable_unchecked" = .none := rfl
    unfold evalTerminator mkIntrinsicCallTerm
    simp [extractCalleeDefPath?, extractCalleeTypeArgs, evalOperands, evalOperand,
      evalConstValue, readProjectedValue, emptyMemory, get?, isDirectExactDivTarget,
      evalDirectRustIntrinsic?, hSel, hEx1, hEx2, hUnr, resolveConstEvalSelectTarget?, length]
    rfl

/-! ## DIFF-C: `copy_nonoverlapping` Over Uninitialized and Initialized Union Bytes -/

section DiffCUnionCopyConfirmation

open Trusted.Effect
open Trusted.ITree

/-- Universal characterization of `extractUnionFieldProj?` across direct union
field borrows (`[.field idx fieldTy]`) and array-to-element thin-pointer casts
(`[.field idx fieldTy, .subslice 0 toIdx false]`). -/
theorem mir_extractUnionFieldProj_corresponds
    (idx : Nat) (fieldTy : Ty) (toIdx : Nat) :
    extractUnionFieldProj? [.field idx fieldTy] = .some fieldTy ∧
    extractUnionFieldProj? [.field idx fieldTy, .subslice 0 toIdx false] =
      .some fieldTy := by
  exact ⟨rfl, rfl⟩

/-- Active statement or terminator span at the current program counter of `s`. -/
private def diffCActiveSpan (body : CapturedMir) (s : MachineState) : String :=
  let currentBody := s.memory.activeCallee.getD body
  match get? currentBody.basicBlocks s.frame.blockIdx with
  | .none => "<none>"
  | .some bb =>
    match get? bb.statements s.frame.stmtIdx with
    | .some stmt => stmt.span
    | .none => bb.terminator.span

/-- Step `body` for `n` transitions starting from `.running s`. -/
private def diffCStepN : Nat → CapturedMir → MirExecState → MirExecState
  | 0, _, es => es
  | n + 1, body, .running s =>
    match stepMirFn body s with
    | .tau nextEs => diffCStepN n body nextEs
    | .vis (.inr (.inl _)) k => diffCStepN n body (k PUnit.unit)
    | .vis (.inl (.fail fk)) _ => .faulted fk
    | .ret out => .halted out
    | .vis (.inr (.inr _)) _ => .faulted .unsupported
  | _, _, es => es

/-- Fuel-bounded execution probe returning either `(none, "none")` paired with
the normal return `Value` on return, or `(some fk, span)` at the faulting
statement/terminator. -/
private def diffCProbeBounded :
    Nat → CapturedMir → MirExecState →
      Option (Option FailureKind × String × Option Value)
  | 0, _, _ => .none
  | fuel + 1, body, .running s =>
    let span := diffCActiveSpan body s
    match stepMirFn body s with
    | .tau nextEs => diffCProbeBounded fuel body nextEs
    | .vis (.inr (.inl _)) k => diffCProbeBounded fuel body (k PUnit.unit)
    | .vis (.inl (.fail fk)) _ => .some (.some fk, span, .none)
    | .ret (.normal (retVal, _)) => .some (.none, "none", .some retVal)
    | .ret _ => .some (.none, "none", .none)
    | .vis (.inr (.inr _)) _ => .some (.some .unsupported, span, .none)
  | _, _, .halted (.normal (retVal, _)) => .some (.none, "none", .some retVal)
  | _, _, .halted _ => .some (.none, "none", .none)
  | _, _, .faulted fk => .some (.some fk, "<faulted>", .none)

/-- Exact `LayoutTable` from `finding_0002` (`pass_copy_nonoverlapping_uninit_bytes_to_uninit__b2_c8`). -/
private def diffCFinding0002Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 4 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.union 2), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.arbitrary List.nil List.nil), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } (List.cons { size := { bytes := 4 }, align := { bytes := 1 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.array { bytes := 1 } 4), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 5 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 64 false) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 2 }, align := { bytes := 1 }, backendRepr := (BackendRepr.scalarPair (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 255 }) (ScalarLayout.initialized (PrimitiveKind.int 8 false) { start := 0, end_ := 1 })), fields := (FieldsShape.arbitrary (List.cons { bytes := 0 } (List.cons { bytes := 1 } List.nil)) (List.cons 0 (List.cons 1 List.nil))), variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 3 (List.cons 8 List.nil)) } (List.cons { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := BackendRepr.memory, fields := (FieldsShape.union 2), variants := (VariantsShape.single 0), isUninhabited := false } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 0, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } (List.cons { size := { bytes := 8 }, align := { bytes := 8 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.pointer 0) { start := 1, end_ := 18446744073709551615 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false, fieldLayouts := (List.cons 0 List.nil) } List.nil))))))))))))) }

/-- Exact `CapturedMir` body from `finding_0002` (`pass_copy_nonoverlapping_uninit_bytes_to_uninit__b2_c8`). -/
private def diffCFinding0002Body : CapturedMir :=
  {
    defPath := "miri_diff_corpus::pass_copy_nonoverlapping_uninit_bytes_to_uninit__b2_c8",
    phase := MirPhaseTag.runtimeOptimized,
    role := ContractRole.subject,
    argCount := 0,
    localDecls := (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.adt "miri_diff_corpus::Uninit" (List.cons (RigidTy.array (RigidTy.uint UintTy.u8) 4) List.nil)), layoutIdx := 1 }, debugName := (Option.some "src") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::Uninit" (List.cons (RigidTy.array (RigidTy.uint UintTy.u8) 4) List.nil)), layoutIdx := 1 }, debugName := (Option.some "dst") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_valid_25034") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u8)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.not (RigidTy.array (RigidTy.uint UintTy.u8) 4)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u8)), layoutIdx := 4 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.array (RigidTy.uint UintTy.u8) 4)), layoutIdx := 6 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple (List.cons (RigidTy.uint UintTy.u8) (List.cons RigidTy.bool List.nil))), layoutIdx := 9 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := (Option.some "__valid_b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::Uninit" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 10 }, debugName := (Option.some "__valid_slot") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_valid_25034") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_tb_46355") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tb_slot") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 11 }, debugName := (Option.some "__tb_root") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 12 }, debugName := (Option.some "__tb_res") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 12 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.ref Mutability.mut (RigidTy.uint UintTy.u32)), layoutIdx := 12 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tb_parent_read") } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_tb_46355") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__tail___miri_valid_57231") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := (Option.some "__valid_b") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.adt "miri_diff_corpus::Uninit" (List.cons (RigidTy.uint UintTy.u32) List.nil)), layoutIdx := 10 }, debugName := (Option.some "__valid_slot") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.tuple List.nil), layoutIdx := 2 }, debugName := Option.none } (List.cons { mutability := Mutability.not, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := (Option.some "__miri_valid_57231") } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := RigidTy.bool, layoutIdx := 8 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } (List.cons { mutability := Mutability.mut, ty := { kind := (RigidTy.uint UintTy.u32), layoutIdx := 0 }, debugName := Option.none } List.nil)))))))))))))))))))))))))))))))))))))))))))))))))),
    basicBlocks := (List.cons { statements := (List.cons { kind := (StatementKind.storageLive 14), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 17), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 18), span := "<dummy>" } (List.cons { kind := (StatementKind.storageLive 1), span := "src/lib.rs:1449:9: 1449:12" } (List.cons { kind := (StatementKind.storageLive 2), span := "src/lib.rs:1449:49: 1449:51" } (List.cons { kind := (StatementKind.assign { local_ := 2, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple List.nil)), span := "src/lib.rs:1449:49: 1449:51" } (List.cons { kind := (StatementKind.assign { local_ := 1, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::Uninit" 0 (Option.some 0)) (List.cons (Operand.move { local_ := 2, projection := List.nil }) List.nil))), span := "src/lib.rs:1449:32: 1449:53" } (List.cons { kind := (StatementKind.storageDead 2), span := "src/lib.rs:1449:52: 1449:53" } (List.cons { kind := (StatementKind.storageLive 3), span := "src/lib.rs:1450:9: 1450:16" } (List.cons { kind := (StatementKind.storageLive 4), span := "src/lib.rs:1450:53: 1450:55" } (List.cons { kind := (StatementKind.assign { local_ := 4, projection := List.nil } (Rvalue.aggregate AggregateKind.tuple List.nil)), span := "src/lib.rs:1450:53: 1450:55" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := List.nil } (Rvalue.aggregate (AggregateKind.adt "miri_diff_corpus::Uninit" 0 (Option.some 0)) (List.cons (Operand.move { local_ := 4, projection := List.nil }) List.nil))), span := "src/lib.rs:1450:36: 1450:57" } (List.cons { kind := (StatementKind.storageDead 4), span := "src/lib.rs:1450:56: 1450:57" } (List.cons { kind := (StatementKind.storageLive 5), span := "src/lib.rs:1451:9: 1451:34" } (List.cons { kind := (StatementKind.assign { local_ := 3, projection := (List.cons (ProjectionElem.field 1 { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 5 }) List.nil) } (Rvalue.aggregate (AggregateKind.array { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 1, sizeBytes := 1 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 2, sizeBytes := 1 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 3, sizeBytes := 1 })) }) (List.cons (Operand.constant { ty := { kind := (RigidTy.uint UintTy.u8), layoutIdx := 3 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 1 })) }) List.nil)))))), span := "src/lib.rs:1452:9: 1452:33" } (List.cons { kind := (StatementKind.storageLive 6), span := "src/lib.rs:1453:9: 1457:10" } (List.cons { kind := (StatementKind.storageLive 7), span := "src/lib.rs:1454:13: 1454:48" } (List.cons { kind := (StatementKind.storageLive 8), span := "src/lib.rs:1454:13: 1454:35" } (List.cons { kind := (StatementKind.assign { local_ := 8, projection := List.nil } (Rvalue.rawPtr Mutability.not { local_ := 1, projection := (List.cons (ProjectionElem.field 1 { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 5 }) List.nil) })), span := "src/lib.rs:1454:13: 1454:35" } (List.cons { kind := (StatementKind.assign { local_ := 7, projection := List.nil } (Rvalue.cast CastKind.ptrToPtr (Operand.move { local_ := 8, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.not (RigidTy.uint UintTy.u8)), layoutIdx := 4 })), span := "src/lib.rs:1454:13: 1454:48" } (List.cons { kind := (StatementKind.storageDead 8), span := "src/lib.rs:1454:47: 1454:48" } (List.cons { kind := (StatementKind.storageLive 9), span := "src/lib.rs:1455:13: 1455:44" } (List.cons { kind := (StatementKind.storageLive 10), span := "src/lib.rs:1455:13: 1455:33" } (List.cons { kind := (StatementKind.assign { local_ := 10, projection := List.nil } (Rvalue.rawPtr Mutability.mut { local_ := 3, projection := (List.cons (ProjectionElem.field 1 { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 5 }) List.nil) })), span := "src/lib.rs:1455:13: 1455:33" } (List.cons { kind := (StatementKind.assign { local_ := 9, projection := List.nil } (Rvalue.cast CastKind.ptrToPtr (Operand.move { local_ := 10, projection := List.nil }) { kind := (RigidTy.rawPtr Mutability.mut (RigidTy.uint UintTy.u8)), layoutIdx := 4 })), span := "src/lib.rs:1455:13: 1455:44" } (List.cons { kind := (StatementKind.storageDead 10), span := "src/lib.rs:1455:43: 1455:44" } (List.cons { kind := (StatementKind.intrinsic (NonDivergingIntrinsic.copyNonOverlapping (Operand.move { local_ := 7, projection := List.nil }) (Operand.move { local_ := 9, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 8 })) }))), span := "src/lib.rs:1453:9: 1457:10" } (List.cons { kind := (StatementKind.storageDead 9), span := "src/lib.rs:1457:9: 1457:10" } (List.cons { kind := (StatementKind.storageDead 7), span := "src/lib.rs:1457:9: 1457:10" } (List.cons { kind := (StatementKind.storageDead 6), span := "src/lib.rs:1457:10: 1457:11" } (List.cons { kind := (StatementKind.storageLive 11), span := "src/lib.rs:1458:9: 1458:38" } (List.cons { kind := (StatementKind.storageLive 12), span := "src/lib.rs:1458:10: 1458:22" } (List.cons { kind := (StatementKind.storageLive 13), span := "src/lib.rs:1458:20: 1458:21" } (List.cons { kind := (StatementKind.assign { local_ := 13, projection := List.nil } (Rvalue.use (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, val := (ConstValue.scalar (ConstScalar.int { bits := 0, sizeBytes := 8 })) }))), span := "src/lib.rs:1458:20: 1458:21" } (List.cons { kind := (StatementKind.assign { local_ := 14, projection := List.nil } (Rvalue.binaryOp BinOp.lt (Operand.copy { local_ := 13, projection := List.nil }) (Operand.constant { ty := { kind := (RigidTy.uint UintTy.usize), layoutIdx := 7 }, val := (ConstValue.scalar (ConstScalar.int { bits := 4, sizeBytes := 8 })) }))), span := "src/lib.rs:1458:10: 1458:22" } List.nil))))))))))))))))))))))))))))))))))), terminator := { kind := (TerminatorKind.assert (Operand.move { local_ := 14, projection := List.nil }) true 1 UnwindAction.continue_), span := "src/lib.rs:1458:10: 1458:22" }, isCleanup := false } (List.cons { statements := (List.cons { kind := (StatementKind.assign { local_ := 12, projection := List.nil } (Rvalue.use (Operand.copy { local_ := 3, projection := (List.cons (ProjectionElem.field 1 { kind := (RigidTy.array (RigidTy.uint UintTy.u8) 4), layoutIdx := 5 }) (List.cons (ProjectionElem.index 13) List.nil)) }))), span := "src/lib.rs:1458:10: 1458:22" } List.nil), terminator := { kind := TerminatorKind.return_, span := "src/lib.rs:1482:2: 1482:2" }, isCleanup := false } List.nil)),
    fnAbi := { args := List.nil, ret := { layout := { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := (BackendRepr.scalar (ScalarLayout.initialized (PrimitiveKind.int 32 false) { start := 0, end_ := 4294967295 })), fields := FieldsShape.primitive, variants := (VariantsShape.single 0), isUninhabited := false }, mode := AbiPassMode.direct }, conv := CallConv.rust, canUnwind := true },
    layouts := diffCFinding0002Layouts,
    allocations := List.nil
  }

/-- Extract `(blockIdx, stmtIdx, local_3)` from a `MirExecState`. -/
private def diffCInspectDstSlot (es : MirExecState) :
    Option (Nat × Nat × Option LocalSlot) :=
  match es with
  | .running s =>
    .some (s.frame.blockIdx, s.frame.stmtIdx, get? s.frame.locals 3)
  | _ => .none

/-- Kernel confirmation (1a): in `finding_0002`
(`pass_copy_nonoverlapping_uninit_bytes_to_uninit__b2_c8`), stepping `bb0`
through `copy_nonoverlapping` (`stmtIdx = 26`, `count = 4`) succeeds, advances
to `(blockIdx = 0, stmtIdx = 27)`, and resets `dst` (`_3`) to uninitialized
union state `Value.aggregate 0 [.aggregate 0 []]`. -/
theorem confirm_finding_0002_bb0_copy_nonoverlapping_resets_dst :
    diffCInspectDstSlot
      (diffCStepN 27 diffCFinding0002Body
        (.running (initMachineState diffCFinding0002Body []))) =
      .some (0, 27, .some (.init (.aggregate 0 [.aggregate 0 []]))) := by
  rfl

/-- Kernel confirmation (1b): exact reproduction of `finding_0002`
(`pass_copy_nonoverlapping_uninit_bytes_to_uninit__b2_c8`) — execution steps
past `bb0`'s `copy_nonoverlapping` into `bb1` and faults with `FailureKind.ub`
on `_12 = copy (_3.1: [u8; 4])[_13]` at `"src/lib.rs:1458:10: 1458:22"`. -/
theorem confirm_finding_0002_ub_at_bb1_read :
    diffCProbeBounded 64 diffCFinding0002Body
      (.running (initMachineState diffCFinding0002Body [])) =
      .some (.some .ub, "src/lib.rs:1458:10: 1458:22", .none) := by
  rfl

/-- MIR body where `src` (`_1: Uninit<[u8; 4]>`) is initialized to `[1, 2, 3, 4]`
and copied via `(&raw const src.value) as *const u8` into uninitialized `dst`
(`_3: Uninit<[u8; 4]>`) via `(&raw mut dst.value) as *mut u8` (`count = 4`),
followed in `bb1` by returning `dst.value[0]` (`_0 = copy (_3.1: [u8; 4])[_6]`). -/
private def diffCInitUnionToUninitBody : CapturedMir :=
  let u8Ty : Ty := { kind := .uint .u8, layoutIdx := 3 }
  let arr4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 5 }
  let uninitArrTy : Ty :=
    { kind := .adt "miri_diff_corpus::Uninit" [.array (.uint .u8) 4], layoutIdx := 1 }
  let unitTy : Ty := { kind := .tuple [], layoutIdx := 2 }
  let usizeTy : Ty := { kind := .uint .usize, layoutIdx := 7 }
  let rawConstArrTy : Ty :=
    { kind := .rawPtr .not (.array (.uint .u8) 4), layoutIdx := 6 }
  let rawConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 4 }
  let rawMutArrTy : Ty :=
    { kind := .rawPtr .mut (.array (.uint .u8) 4), layoutIdx := 6 }
  let rawMutU8Ty : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 4 }
  { defPath := "test::copy_init_union_bytes_to_uninit",
    phase := .runtimeOptimized,
    role := .subject,
    argCount := 0,
    localDecls := [
      { mutability := .mut, ty := u8Ty, debugName := .none },          -- _0: u8
      { mutability := .mut, ty := uninitArrTy, debugName := .some "src" }, -- _1
      { mutability := .mut, ty := unitTy, debugName := .none },        -- _2: ()
      { mutability := .mut, ty := uninitArrTy, debugName := .some "dst" }, -- _3
      { mutability := .mut, ty := rawConstArrTy, debugName := .none }, -- _4
      { mutability := .mut, ty := rawConstU8Ty, debugName := .none },  -- _5
      { mutability := .not, ty := usizeTy, debugName := .none },       -- _6
      { mutability := .mut, ty := rawMutArrTy, debugName := .none },   -- _7
      { mutability := .mut, ty := rawMutU8Ty, debugName := .none }     -- _8
    ],
    basicBlocks := [
      { statements := [
          { kind := .storageLive 1, span := "s0" },
          { kind := .storageLive 2, span := "s1" },
          { kind := .assign ⟨2, []⟩ (.aggregate .tuple []), span := "s2" },
          { kind := .assign ⟨1, []⟩
              (.aggregate (.adt "miri_diff_corpus::Uninit" 0 (.some 0))
                [.copy ⟨2, []⟩]), span := "s3" },
          { kind := .assign ⟨1, [.field 1 arr4Ty]⟩
              (.aggregate (.array u8Ty) [
                .constant ⟨u8Ty, .scalar (.int ⟨1, 1⟩)⟩,
                .constant ⟨u8Ty, .scalar (.int ⟨2, 1⟩)⟩,
                .constant ⟨u8Ty, .scalar (.int ⟨3, 1⟩)⟩,
                .constant ⟨u8Ty, .scalar (.int ⟨4, 1⟩)⟩
              ]), span := "s4" },
          { kind := .storageLive 3, span := "s5" },
          { kind := .assign ⟨3, []⟩
              (.aggregate (.adt "miri_diff_corpus::Uninit" 0 (.some 0))
                [.move ⟨2, []⟩]), span := "s6" },
          { kind := .storageLive 4, span := "s7" },
          { kind := .storageLive 5, span := "s8" },
          { kind := .assign ⟨4, []⟩
              (.rawPtr .not ⟨1, [.field 1 arr4Ty]⟩), span := "s9" },
          { kind := .assign ⟨5, []⟩
              (.cast .ptrToPtr (.move ⟨4, []⟩) rawConstU8Ty), span := "s10" },
          { kind := .storageLive 7, span := "s11" },
          { kind := .storageLive 8, span := "s12" },
          { kind := .assign ⟨7, []⟩
              (.rawPtr .mut ⟨3, [.field 1 arr4Ty]⟩), span := "s13" },
          { kind := .assign ⟨8, []⟩
              (.cast .ptrToPtr (.move ⟨7, []⟩) rawMutU8Ty), span := "s14" },
          { kind := .intrinsic
              (.copyNonOverlapping
                (.move ⟨5, []⟩)
                (.move ⟨8, []⟩)
                (.constant ⟨usizeTy, .scalar (.int ⟨4, 8⟩)⟩)),
            span := "copy_init_to_uninit" },
          { kind := .storageLive 6, span := "s16" },
          { kind := .assign ⟨6, []⟩
              (.use (.constant ⟨usizeTy, .scalar (.int ⟨0, 8⟩)⟩)), span := "s17" }
        ],
        terminator := { kind := .goto 1, span := "t0" },
        isCleanup := false },
      { statements := [
          { kind := .assign ⟨0, []⟩
              (.use (.copy ⟨3, [.field 1 arr4Ty, .index 6]⟩)),
            span := "read_dst_0" }
        ],
        terminator := { kind := .return_, span := "ret" },
        isCleanup := false }
    ],
    fnAbi := {
      args := [],
      ret := {
        layout := {
          size := { bytes := 1 }, align := { bytes := 1 },
          backendRepr := .scalar (.initialized (.int 8 false) { start := 0, end_ := 255 }),
          fields := .primitive, variants := .single 0, isUninhabited := false
        },
        mode := .direct
      },
      conv := .rust, canUnwind := true
    },
    layouts := diffCFinding0002Layouts,
    allocations := []
  }

/-- Kernel confirmation (2): copying initialized union bytes via `*const u8`
(derived from `&raw const src.value as *const u8`) into an uninitialized
`dst: Uninit<[u8; 4]>` initializes `dst.value` to `[1, 2, 3, 4]` and reading
`dst.value[0]` succeeds and returns `1`. -/
theorem confirm_copy_nonoverlapping_init_union_bytes_to_uninit :
    diffCInspectDstSlot
      (diffCStepN 16 diffCInitUnionToUninitBody
        (.running (initMachineState diffCInitUnionToUninitBody []))) =
      .some
        (0, 16,
         .some
           (.init
             (.aggregate 0
               [.aggregate 0 [],
                .aggregate 0
                  [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩,
                   .scalar ⟨3, 1⟩, .scalar ⟨4, 1⟩]]))) ∧
    diffCProbeBounded 32 diffCInitUnionToUninitBody
      (.running (initMachineState diffCInitUnionToUninitBody [])) =
      .some (.none, "none", .some (.scalar ⟨1, 1⟩)) := by
  exact ⟨rfl, rfl⟩

/-- Kernel confirmation (2b): even when `dst`'s borrow carries a `.subslice 0 4 false`
projection while `dst` holds uninitialized union state `Value.aggregate 0 [.aggregate 0 []]`,
`evalCopyNonOverlappingWithCount` initializes `dst.value` to `[1, 2, 3, 4]`. -/
theorem confirm_copy_nonoverlapping_init_union_to_subslice_uninit_dst :
    let u8PtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 4 }
    let mutU8PtrTy : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 4 }
    let arr4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 5 }
    let uninitArrTy : Ty :=
      { kind := .adt "miri_diff_corpus::Uninit" [.array (.uint .u8) 4], layoutIdx := 1 }
    let decls : List LocalDecl := [
      { mutability := .not, ty := uninitArrTy, debugName := .none },
      { mutability := .mut, ty := uninitArrTy, debugName := .none },
      { mutability := .not, ty := u8PtrTy, debugName := .none },
      { mutability := .not, ty := mutU8PtrTy, debugName := .none }
    ]
    let initArr : Value :=
      .aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨4, 1⟩]
    let locals : List LocalSlot := [
      .init (.aggregate 0 [.aggregate 0 [], initArr]),
      .init (.aggregate 0 [.aggregate 0 []]),
      .init (.ptr ⟨1, 0⟩ 8),
      .init (.ptr ⟨2, 0⟩ 8)
    ]
    let borrows : List BorrowEntry := [
      { tag := 1, targetLocal := 0,
        targetProjection := [.field 1 arr4Ty, .subslice 0 4 false], perm := .frozen },
      { tag := 2, targetLocal := 1,
        targetProjection := [.field 1 arr4Ty, .subslice 0 4 false], perm := .active }
    ]
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := locals },
        memory := { emptyMemory with borrows := borrows, nextTag := 3 } }
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨2, []⟩) (.copy ⟨3, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 4 locals =
      MirStepNode.step
        (advanceStmt s0
          [.init (.aggregate 0 [.aggregate 0 [], initArr]),
           .init (.aggregate 0 [.aggregate 0 [], initArr]),
           .init (.ptr ⟨1, 0⟩ 8),
           .init (.ptr ⟨2, 0⟩ 8)]
          s0.memory) := by
  rfl

/-- Kernel confirmation (3): out-of-bounds `copy_nonoverlapping` (`count = 5` on
`[u8; 4]`), copying uninitialized union bytes into a non-union `[u8; 4]`
destination, misaligned pointer offsets (`offsetBytes = 1` at `align = 4`),
overlapping same-union ranges (`src == dst`, `count = 4`), and frozen destination
borrows all return `MirStepNode.fail .ub`, whereas `count = 1` uninitialized
union copy resets `dst` cleanly. -/
theorem confirm_copy_nonoverlapping_union_ub_and_edge_cases :
    let u8PtrTy : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 4 }
    let mutU8PtrTy : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 4 }
    let u32PtrTy : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 11 }
    let arr4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 5 }
    let uninitArrTy : Ty :=
      { kind := .adt "miri_diff_corpus::Uninit" [.array (.uint .u8) 4], layoutIdx := 1 }
    let decls : List LocalDecl := [
      { mutability := .not, ty := uninitArrTy, debugName := .none }, -- _0: union src (uninit)
      { mutability := .mut, ty := uninitArrTy, debugName := .none }, -- _1: union dst (init)
      { mutability := .mut, ty := arr4Ty, debugName := .none },      -- _2: non-union [u8; 4]
      { mutability := .not, ty := u8PtrTy, debugName := .none },     -- _3: *const u8
      { mutability := .not, ty := mutU8PtrTy, debugName := .none },  -- _4: *mut u8
      { mutability := .not, ty := u32PtrTy, debugName := .none }     -- _5: *mut u32 (align 4)
    ]
    let initArr : Value :=
      .aggregate 0 [.scalar ⟨1, 1⟩, .scalar ⟨2, 1⟩, .scalar ⟨3, 1⟩, .scalar ⟨4, 1⟩]
    let locals : List LocalSlot := [
      .init (.aggregate 0 [.aggregate 0 []]),
      .init (.aggregate 0 [.aggregate 0 [], initArr]),
      .init initArr,
      .init .unit, .init .unit, .init .unit
    ]
    let borrows : List BorrowEntry := [
      { tag := 1, targetLocal := 0,
        targetProjection := [.field 1 arr4Ty, .subslice 0 4 false], perm := .frozen },
      { tag := 2, targetLocal := 1,
        targetProjection := [.field 1 arr4Ty, .subslice 0 4 false], perm := .active },
      { tag := 3, targetLocal := 2,
        targetProjection := [.subslice 0 4 false], perm := .active },
      { tag := 4, targetLocal := 1,
        targetProjection := [.field 1 arr4Ty, .subslice 0 4 false], perm := .frozen }
    ]
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := locals },
        memory := { emptyMemory with borrows := borrows, nextTag := 5 } }
    -- (a) Out-of-bounds `count = 5` on `[u8; 4]` union fields -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨3, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 5 locals = MirStepNode.fail .ub ∧
    -- (b) Copying uninitialized union bytes (`count = 4`) into non-union `[u8; 4]` -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨3, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨3, 0⟩ 8) 4 locals = MirStepNode.fail .ub ∧
    -- (c) Partial uninitialized union copy (`count = 1`) into non-union `[u8; 4]` -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨3, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨3, 0⟩ 8) 1 locals = MirStepNode.fail .ub ∧
    -- (d) Misaligned offset (`offsetBytes = 1`, pointee `u32` align = 4) -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨5, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 1⟩ 8) (.ptr ⟨2, 0⟩ 8) 1 locals = MirStepNode.fail .ub ∧
    -- (e) Overlapping same-union copy (`src == dst`, `count = 4`) -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨4, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨2, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 4 locals = MirStepNode.fail .ub ∧
    -- (f) Immutable (`perm = .frozen`) destination pointer -> `.ub`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨3, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨4, 0⟩ 8) 4 locals = MirStepNode.fail .ub ∧
    -- (g) Partial `count = 1` uninitialized union copy into union `dst` succeeds and resets `dst`
    evalCopyNonOverlappingWithCount
      s0 (.copy ⟨3, []⟩) (.copy ⟨4, []⟩) decls diffCFinding0002Layouts
      (.ptr ⟨1, 0⟩ 8) (.ptr ⟨2, 0⟩ 8) 1 locals =
      MirStepNode.step
        (advanceStmt s0
          [.init (.aggregate 0 [.aggregate 0 []]),
           .init (.aggregate 0 [.aggregate 0 []]),
           .init initArr,
           .init .unit, .init .unit, .init .unit]
          { s0.memory with
            borrows :=
              invalidateConflictingBorrows borrows 1 (.some 2) }) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end DiffCUnionCopyConfirmation

/-! ## 6. Statement-Level Divergence Regressions (`D2`, `D14a-storage`, `D9`)

Kernel-checked executions of `Runtime(PostCleanup)` MIR bodies exercising the
`StorageDead`/`StorageLive` borrow invalidation (`disableLocalBorrows`), the
`StorageDead`/`StorageLive` protector checks, and the `PlaceMention`
operand-initialization checks in `evalStmt`. Unless noted otherwise, each
`*_is_ub` witness below terminated without `.ub` before these checks existed. -/

section StatementDivergenceRegressions

open Trusted.Effect

/-- `u64` local type used by the statement divergence regression bodies. -/
private def stmtDivU64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

/-- `usize` local type used by the statement divergence regression bodies. -/
private def stmtDivUsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }

/-- `[u64; 2]` local type used by the `Index` regression body. -/
private def stmtDivArrTy : Ty := { kind := .array (.uint .u64) 2, layoutIdx := 0 }

/-- `*mut u64` local type used by the statement divergence regression bodies. -/
private def stmtDivRawMutU64Ty : Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }

/-- `&u64` local type used by the dangling-reborrow regression body. -/
private def stmtDivRefU64Ty : Ty := { kind := .ref .not (.uint .u64), layoutIdx := 0 }

/-- `&mut u64` local type used by the two-phase-borrow revival regression bodies. -/
private def stmtDivRefMutU64Ty : Ty := { kind := .ref .mut (.uint .u64), layoutIdx := 0 }

/-- `u64` constant operand. -/
private def stmtDivConstU64 (n : Nat) : Operand :=
  .constant ⟨stmtDivU64Ty, .scalar (.int ⟨n, 8⟩)⟩

/-- `usize` constant operand. -/
private def stmtDivConstUsize (n : Nat) : Operand :=
  .constant ⟨stmtDivUsizeTy, .scalar (.int ⟨n, 8⟩)⟩

/-- Mutable local declaration of type `ty`. -/
private def stmtDivDecl (ty : Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := .none }

/-- `extern "Rust"` ABI returning a `u64` directly. -/
private def stmtDivFnAbiU64 : FnAbi :=
  { args := [],
    ret := {
      layout := {
        size := { bytes := 8 }, align := { bytes := 8 },
        backendRepr :=
          .scalar (.initialized (.int 64 false) { start := 0, end_ := 18446744073709551615 }),
        fields := .primitive, variants := .single 0, isUninhabited := false
      },
      mode := .direct
    },
    conv := .rust, canUnwind := true }

/-- Single-block `Runtime(PostCleanup)` body with locals `decls` and
statements `stmts` that returns `_0`. -/
private def stmtDivBody (name : String) (decls : List LocalDecl)
    (stmts : List Statement) : CapturedMir :=
  { defPath := name,
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := 0,
    localDecls := decls,
    basicBlocks := [
      { statements := stmts,
        terminator := { kind := .return_, span := "return" },
        isCleanup := false }],
    fnAbi := stmtDivFnAbiU64,
    layouts := emptyLayoutTable,
    allocations := [] }

/-- `D2` (`wit_lm3_1_storage_revive_prog`): read through a raw pointer
`&raw const _1` after `_1` is deallocated by `StorageDead(_1)`, revived by
`StorageLive(_1)`, and re-initialized to `20`:
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &raw const _1;
StorageDead(_1); StorageLive(_1); _1 = const 20_u64; _0 = copy *_2; return
```
Noted exception: this program already faulted before `disableLocalBorrows`
existed, because the direct write `_1 = 20` disables the `.frozen` tag of
`&raw const _1` (a Tree Borrows foreign write), so it is kept only as a
regression guard. The variant through a two-phase mutable borrow, whose
`.reserved` tag survives that write, did return `20`
(`stmt_div_storage_revive_two_phase_read_is_ub`). -/
private def stmtDivReviveReadBody : CapturedMir :=
  stmtDivBody "stmt_div::read_through_pointer_into_revived_and_reinit_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .not ⟨1, []⟩), span := "_2 = &raw const _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 20)), span := "_1 = 20" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "stmt5: _0 = copy (*_2)" } ]

/-- `D2` read-after-revive-and-reinit regression (`wit_lm3_1_storage_revive_prog`):
even after `_1` is revived by `StorageLive(_1)` and re-initialized to `20`,
reading `*_2` through the pointer minted before `StorageDead(_1)` faults with
`FailureKind.ub`. -/
theorem stmt_div_storage_revive_dangling_read_is_ub :
    diffCProbeBounded 16 stmtDivReviveReadBody
      (.running (initMachineState stmtDivReviveReadBody [])) =
      .some (.some .ub, "stmt5: _0 = copy (*_2)", .none) := by
  rfl

/-- `D2` implicit-deallocation regression: calling `StorageLive(_1)` on an
already-allocated local `_1` (without an intervening `StorageDead(_1)`)
implicitly deallocates the old allocation of `_1` and disables its borrows, so
a subsequent read through the two-phase mutable borrow `_2` after
re-initializing `_1 = 20` faults with `FailureKind.ub` (Anneal previously
returned `20`, since the `.reserved` tag of `_2` survives the direct write):
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &two-phase mut _1;
StorageLive(_1); _1 = const 20_u64; _0 = copy *_2; return
``` -/
private def stmtDivReviveWithoutDeadBody : CapturedMir :=
  stmtDivBody "stmt_div::storage_live_implicit_dealloc_disables_borrows"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRefMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut true) ⟨1, []⟩), span := "_2 = &two-phase mut _1" },
      { kind := .storageLive 1, span := "revive _1 directly" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 20)), span := "_1 = 20" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "_0 = copy (*_2)" } ]

theorem stmt_div_storage_live_implicit_dealloc_dangling_read_is_ub :
    diffCProbeBounded 16 stmtDivReviveWithoutDeadBody
      (.running (initMachineState stmtDivReviveWithoutDeadBody [])) =
      .some (.some .ub, "_0 = copy (*_2)", .none) := by
  rfl

/-- `D2` read-after-revive regression through a two-phase mutable borrow, whose
`.reserved` Tree Borrows tag survives the direct write `_1 = 20`:
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &two-phase mut _1;
StorageDead(_1); StorageLive(_1); _1 = const 20_u64; _0 = copy *_2; return
```
Anneal previously returned `20` from the revived allocation of `_1`. -/
private def stmtDivReviveTwoPhaseReadBody : CapturedMir :=
  stmtDivBody "stmt_div::read_through_two_phase_borrow_into_revived_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRefMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut true) ⟨1, []⟩), span := "_2 = &two-phase mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 20)), span := "_1 = 20" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "_0 = copy *_2" } ]

/-- `D2` read-after-revive regression: reading `*_2` through the stale two-phase
borrow faults with `FailureKind.ub`. -/
theorem stmt_div_storage_revive_two_phase_read_is_ub :
    diffCProbeBounded 16 stmtDivReviveTwoPhaseReadBody
      (.running (initMachineState stmtDivReviveTwoPhaseReadBody [])) =
      .some (.some .ub, "_0 = copy *_2", .none) := by
  rfl

/-- Captured global allocation with identifier `1` holding the `u64` value `42`.
`anneal-rustc-capture` numbers captured global allocations from `1`, the same
numbering that stack borrow tags use (`Memory.nextTag` starts at `1`). -/
private def stmtDivGlobal1 : CapturedAllocation :=
  { allocId := 1,
    bytes := [.some 42, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0, .some 0],
    relocations := [], align := ⟨8⟩, mutability := .not }

/-- `stmtDivBody` with the single captured global allocation `stmtDivGlobal1`. -/
private def stmtDivBodyWithGlobal (name : String) (decls : List LocalDecl)
    (stmts : List Statement) : CapturedMir :=
  { stmtDivBody name decls stmts with allocations := [stmtDivGlobal1] }

/-- `D2` tag/global aliasing body: the stack borrow tag `1` minted for `_2`
equals the identifier of the captured global `stmtDivGlobal1`:
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &raw const _1;
StorageDead(_1); _0 = copy *_2; return
``` -/
private def stmtDivDeadGlobalAliasReadBody : CapturedMir :=
  stmtDivBodyWithGlobal "stmt_div::read_through_dead_pointer_aliasing_global"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .not ⟨1, []⟩), span := "_2 = &raw const _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "_0 = copy *_2" } ]

/-- `D2` tag/global aliasing regression: reading through the dangling pointer
faults with `FailureKind.ub`. Removing (rather than disabling) `_1`'s borrow
entries on `StorageDead(_1)` made `*_2` fall back to `lookupGlobalAlloc` and
return the global's `42`. -/
theorem stmt_div_storage_dead_global_alias_read_is_ub :
    diffCProbeBounded 16 stmtDivDeadGlobalAliasReadBody
      (.running (initMachineState stmtDivDeadGlobalAliasReadBody [])) =
      .some (.some .ub, "_0 = copy *_2", .none) := by
  rfl

/-- `D14a-storage` tag/global aliasing body: reborrow through the dangling
pointer, then read through the reborrow:
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 10_u64;
_2 = &raw const _1; StorageDead(_1); _3 = &*_2; _0 = copy *_3; return
``` -/
private def stmtDivDeadGlobalAliasReborrowBody : CapturedMir :=
  stmtDivBodyWithGlobal "stmt_div::reborrow_through_dead_pointer_aliasing_global"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 },
      stmtDivDecl stmtDivRefU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .not ⟨1, []⟩), span := "_2 = &raw const _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .assign ⟨3, []⟩ (.ref .shared ⟨2, [.deref]⟩), span := "_3 = &*_2" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨3, [.deref]⟩)), span := "_0 = copy *_3" } ]

/-- `D14a-storage` tag/global aliasing regression: the reborrow through the
dangling pointer faults with `FailureKind.ub`. Removing (rather than disabling)
`_1`'s borrow entries made the reborrow resolve to the global allocation and
the body return the global's `42`. -/
theorem stmt_div_storage_dead_global_alias_reborrow_is_ub :
    diffCProbeBounded 16 stmtDivDeadGlobalAliasReborrowBody
      (.running (initMachineState stmtDivDeadGlobalAliasReborrowBody [])) =
      .some (.some .ub, "_3 = &*_2", .none) := by
  rfl

/-- Positive control for the aliasing regressions: a pointer to the captured
global `stmtDivGlobal1` reads its `42` when no stack borrow shares its
identifier:
```text
StorageLive(_1); _1 = const {alloc1: *const u64}; _0 = copy *_1; return
``` -/
private def stmtDivGlobalReadOkBody : CapturedMir :=
  stmtDivBodyWithGlobal "stmt_div::read_through_global_pointer"
    [stmtDivDecl stmtDivU64Ty,
      stmtDivDecl { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, []⟩
          (.use (.constant ⟨{ kind := .rawPtr .not (.uint .u64), layoutIdx := 0 },
            .scalar (.ptr { allocId := 1, offsetBytes := 0 } 8)⟩)),
        span := "_1 = &GLOBAL" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩)), span := "_0 = copy *_1" } ]

/-- Positive control: the body returns the global's `42`. -/
theorem stmt_div_global_read_ok :
    diffCProbeBounded 16 stmtDivGlobalReadOkBody
      (.running (initMachineState stmtDivGlobalReadOkBody [])) =
      .some (.none, "none", .some (.scalar ⟨42, 8⟩)) := by
  rfl

/-- `D2` (`wit_lm3_1_anneal_storage_revive_divergence`): write and read through a
raw pointer after its pointee's storage has ended and restarted:
```text
StorageLive(_1); StorageLive(_2); _1 = const 42_u64; _2 = &raw mut _1;
StorageDead(_1); StorageLive(_1); *_2 = const 7_u64; _0 = copy *_2; return
``` -/
private def stmtDivReviveBody : CapturedMir :=
  stmtDivBody "stmt_div::write_through_pointer_into_revived_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 42)), span := "_1 = 42" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨2, [.deref]⟩ (.use (stmtDivConstU64 7)), span := "*_2 = 7" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "_0 = copy *_2" } ]

/-- `D2` regression: the write through the stale pointer `_2` into the revived
local `_1` faults with `FailureKind.ub` (Anneal previously returned `7`). -/
theorem stmt_div_storage_revive_write_is_ub :
    diffCProbeBounded 16 stmtDivReviveBody
      (.running (initMachineState stmtDivReviveBody [])) =
      .some (.some .ub, "*_2 = 7", .none) := by
  rfl

/-- Positive control for `D2`: a pointer freshly minted after `StorageLive(_1)`
revives `_1` still reads and writes the new storage:
```text
StorageLive(_1); StorageLive(_2); _1 = const 42_u64; _2 = &raw mut _1;
StorageDead(_1); StorageLive(_1); _1 = const 9_u64; _2 = &raw mut _1;
*_2 = const 7_u64; _0 = copy *_2; return
``` -/
private def stmtDivReviveFreshBody : CapturedMir :=
  stmtDivBody "stmt_div::write_through_fresh_pointer_into_revived_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 42)), span := "_1 = 42" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 9)), span := "_1 = 9" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1 (fresh)" },
      { kind := .assign ⟨2, [.deref]⟩ (.use (stmtDivConstU64 7)), span := "*_2 = 7" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨2, [.deref]⟩)), span := "_0 = copy *_2" } ]

/-- Positive control for `D2`: the fresh pointer returns `7`. -/
theorem stmt_div_storage_revive_fresh_pointer_ok :
    diffCProbeBounded 16 stmtDivReviveFreshBody
      (.running (initMachineState stmtDivReviveFreshBody [])) =
      .some (.none, "none", .some (.scalar ⟨7, 8⟩)) := by
  rfl

/-- `D14a-storage` (`evalRvalue_reborrow_dangling_divergence`): reborrow a shared
reference through a raw pointer whose pointee was killed by `StorageDead`:
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3); _1 = const 42_u64;
_2 = &raw mut _1; StorageDead(_1); _3 = &*_2; _0 = const 0_u64; return
``` -/
private def stmtDivDanglingReborrowBody : CapturedMir :=
  stmtDivBody "stmt_div::reborrow_through_dangling_pointer"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRawMutU64Ty,
      stmtDivDecl stmtDivRefU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 42)), span := "_1 = 42" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .assign ⟨3, []⟩ (.ref .shared ⟨2, [.deref]⟩), span := "_3 = &*_2" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

/-- `D14a-storage` regression: reborrowing through the dangling pointer faults
with `FailureKind.ub` instead of minting a dangling reference. -/
theorem stmt_div_storage_dead_reborrow_is_ub :
    diffCProbeBounded 16 stmtDivDanglingReborrowBody
      (.running (initMachineState stmtDivDanglingReborrowBody [])) =
      .some (.some .ub, "_3 = &*_2", .none) := by
  rfl

/-- `D9` (`step_placeMention_deref_uninit_divergence`): mention a dereference of
an uninitialized raw-pointer local:
```text
StorageLive(_1); PlaceMention(*_1); _0 = const 0_u64; return
``` -/
private def stmtDivPlaceMentionDerefUninitBody : CapturedMir :=
  stmtDivBody "stmt_div::place_mention_deref_uninit_pointer"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .placeMention ⟨1, [.deref]⟩, span := "PlaceMention(*_1)" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

/-- `D9` regression: computing `*_1` loads the uninitialized pointer `_1` and
faults with `FailureKind.ub`. -/
theorem stmt_div_placeMention_deref_uninit_is_ub :
    diffCProbeBounded 8 stmtDivPlaceMentionDerefUninitBody
      (.running (initMachineState stmtDivPlaceMentionDerefUninitBody [])) =
      .some (.some .ub, "PlaceMention(*_1)", .none) := by
  rfl

/-- `D9` index regression body: mention `_1[_2]` with an uninitialized index:
```text
StorageLive(_1); StorageLive(_2); _1 = [const 1_u64, const 2_u64];
PlaceMention(_1[_2]); _0 = const 0_u64; return
``` -/
private def stmtDivPlaceMentionIndexUninitBody : CapturedMir :=
  stmtDivBody "stmt_div::place_mention_index_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivArrTy, stmtDivDecl stmtDivUsizeTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩
          (.aggregate (.array stmtDivU64Ty) [stmtDivConstU64 1, stmtDivConstU64 2]),
        span := "_1 = [1, 2]" },
      { kind := .placeMention ⟨1, [.index 2]⟩, span := "PlaceMention(_1[_2])" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

/-- `D9` regression: computing `_1[_2]` reads the uninitialized index local `_2`
and faults with `FailureKind.ub`. -/
theorem stmt_div_placeMention_index_uninit_is_ub :
    diffCProbeBounded 8 stmtDivPlaceMentionIndexUninitBody
      (.running (initMachineState stmtDivPlaceMentionIndexUninitBody [])) =
      .some (.some .ub, "PlaceMention(_1[_2])", .none) := by
  rfl

/-- Positive control for `D9`: mentioning an uninitialized local without
projections (`let _ = x;` on a live local) and mentioning an initialized index
both remain defined:
```text
StorageLive(_1); StorageLive(_2); PlaceMention(_2); _2 = const 1_usize;
_1 = [const 1_u64, const 2_u64]; PlaceMention(_1[_2]); _0 = const 5_u64; return
``` -/
private def stmtDivPlaceMentionOkBody : CapturedMir :=
  stmtDivBody "stmt_div::place_mention_defined"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivArrTy, stmtDivDecl stmtDivUsizeTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .placeMention ⟨2, []⟩, span := "PlaceMention(_2)" },
      { kind := .assign ⟨2, []⟩ (.use (stmtDivConstUsize 1)), span := "_2 = 1" },
      { kind := .assign ⟨1, []⟩
          (.aggregate (.array stmtDivU64Ty) [stmtDivConstU64 1, stmtDivConstU64 2]),
        span := "_1 = [1, 2]" },
      { kind := .placeMention ⟨1, [.index 2]⟩, span := "PlaceMention(_1[_2])" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 5)), span := "_0 = 5" } ]

/-- Positive control for `D9`: the body returns `5`. -/
theorem stmt_div_placeMention_defined_ok :
    diffCProbeBounded 16 stmtDivPlaceMentionOkBody
      (.running (initMachineState stmtDivPlaceMentionOkBody [])) =
      .some (.none, "none", .some (.scalar ⟨5, 8⟩)) := by
  rfl

/-- Machine state at `StorageDead(_1)` in which `_1` is borrowed by a tag
carrying function-entry protector `protId`, with active protectors `prots`. -/
private def stmtDivProtectedState (prots : List Nat) : MachineState :=
  { frame := {
      blockIdx := 0
      stmtIdx := 0
      locals := [.uninit, .init (.scalar ⟨42, 8⟩)]
    }
    memory := {
      emptyMemory with
      borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                    perm := .active, protector := .some 1 }]
      nextTag := 2
      activeProtectors := prots
      nextProtector := 2
    } }

/-- `D2` protector regression: `StorageDead(_1)` faults with `FailureKind.ub`
while a tag minted from `_1` is protected by an active function-entry
protector. -/
theorem stmt_div_storage_dead_protected_is_ub :
    evalStmt (stmtDivProtectedState [1]) ⟨.storageDead 1, "dead _1"⟩ =
      MirStepNode.fail .ub := by
  rfl

/-- Once the protector is no longer active, `StorageDead(_1)` succeeds and
disables every tag minted from `_1` in the borrow table. -/
theorem stmt_div_storage_dead_unprotected_disables :
    evalStmt (stmtDivProtectedState []) ⟨.storageDead 1, "dead _1"⟩ =
      MirStepNode.step
        (advanceStmt (stmtDivProtectedState []) [.uninit, .dead]
          { (stmtDivProtectedState []).memory with
            borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                          perm := .disabled, protector := .some 1 }] }) := by
  rfl

/-- `D2` protector regression on `StorageLive(_1)`: implicitly deallocating an
already-allocated local `_1` via `StorageLive(_1)` while a tag minted from `_1`
is protected by an active function-entry protector faults with `FailureKind.ub`. -/
theorem stmt_div_storage_live_protected_is_ub :
    evalStmt (stmtDivProtectedState [1]) ⟨.storageLive 1, "live _1"⟩ =
      MirStepNode.fail .ub := by
  rfl

/-- Once the protector is no longer active, `StorageLive(_1)` succeeds and
disables every tag minted from `_1` in the borrow table. -/
theorem stmt_div_storage_live_unprotected_disables :
    evalStmt (stmtDivProtectedState []) ⟨.storageLive 1, "live _1"⟩ =
      MirStepNode.step
        (advanceStmt (stmtDivProtectedState []) [.uninit, .uninit]
          { (stmtDivProtectedState []).memory with
            borrows := [{ tag := 1, targetLocal := 1, targetProjection := [],
                          perm := .disabled, protector := .some 1 }] }) := by
  rfl

/-- `D2` retag-after-`StorageDead` regression (with global-allocation tag
aliasing): retagging a reference `_2` after `StorageDead(_1)` faults with
`FailureKind.ub` even when captured global allocation `stmtDivGlobal1` shares
`allocId = 1` (removing `_1`'s borrow entry instead of disabling it would fall
back to `lookupGlobalAlloc` and allow `Retag(_2)` to succeed):
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &_1;
StorageDead(_1); Retag([default] _2); _0 = const 0_u64; return
``` -/
private def stmtDivDeadGlobalAliasRetagBody : CapturedMir :=
  stmtDivBodyWithGlobal "stmt_div::retag_dead_reference_aliasing_global"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivRefU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref .shared ⟨1, []⟩), span := "_2 = &_1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .retag .default ⟨2, []⟩, span := "Retag(_2)" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_storage_dead_retag_is_ub :
    diffCProbeBounded 16 stmtDivDeadGlobalAliasRetagBody
      (.running (initMachineState stmtDivDeadGlobalAliasRetagBody [])) =
      .some (.some .ub, "Retag(_2)", .none) := by
  rfl

/-- `D2` `copy_nonoverlapping` source after `StorageDead` + `StorageLive`
revival: copying 1 element out of the revived and re-initialized `_1` through
the two-phase mutable borrow `_2` minted before `StorageDead(_1)` (whose
`.reserved` tag survives the direct write `_1 = 20`):
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_1 = const 10_u64; _2 = &two-phase mut _1; _0 = const 0_u64; _3 = &raw mut _0;
StorageDead(_1); StorageLive(_1); _1 = const 20_u64;
copy_nonoverlapping(src = copy _2, dst = copy _3, count = const 1_usize); return
``` -/
private def stmtDivReviveCopySrcBody : CapturedMir :=
  stmtDivBody "stmt_div::copy_nonoverlapping_from_revived_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl stmtDivRefMutU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut true) ⟨1, []⟩), span := "_2 = &two-phase mut _1" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" },
      { kind := .assign ⟨3, []⟩ (.rawPtr .mut ⟨0, []⟩), span := "_3 = &raw mut _0" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 20)), span := "_1 = 20" },
      { kind := .intrinsic (.copyNonOverlapping (.copy ⟨2, []⟩) (.copy ⟨3, []⟩) (stmtDivConstUsize 1)),
        span := "copy_nonoverlapping(src=_2, dst=_3, 1)" } ]

/-- `D2` `copy_nonoverlapping` source regression: the copy faults with
`FailureKind.ub` (Anneal previously copied the revived `20` into `_0` and
returned it). -/
theorem stmt_div_storage_revive_copy_nonoverlapping_is_ub :
    diffCProbeBounded 20 stmtDivReviveCopySrcBody
      (.running (initMachineState stmtDivReviveCopySrcBody [])) =
      .some (.some .ub, "copy_nonoverlapping(src=_2, dst=_3, 1)", .none) := by
  rfl

/-- `D2` `copy_nonoverlapping` destination after `StorageDead` + `StorageLive`
revival: copying 1 element into the revived `_1` through the raw pointer `_2`
minted before `StorageDead(_1)`:
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_1 = const 10_u64; _2 = &raw mut _1; _0 = const 5_u64; _3 = &raw mut _0;
StorageDead(_1); StorageLive(_1);
copy_nonoverlapping(src = copy _3, dst = copy _2, count = const 1_usize);
_0 = copy _1; return
``` -/
private def stmtDivReviveCopyDstBody : CapturedMir :=
  stmtDivBody "stmt_div::copy_nonoverlapping_into_revived_local"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl stmtDivRawMutU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 5)), span := "_0 = 5" },
      { kind := .assign ⟨3, []⟩ (.rawPtr .mut ⟨0, []⟩), span := "_3 = &raw mut _0" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .intrinsic (.copyNonOverlapping (.copy ⟨3, []⟩) (.copy ⟨2, []⟩) (stmtDivConstUsize 1)),
        span := "copy_nonoverlapping(src=_3, dst=_2, 1)" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)), span := "_0 = copy _1" } ]

/-- `D2` `copy_nonoverlapping` destination regression: the copy faults with
`FailureKind.ub` (Anneal previously wrote `5` into the revived `_1` through the
stale pointer and returned it). -/
theorem stmt_div_storage_revive_copy_nonoverlapping_dst_is_ub :
    diffCProbeBounded 20 stmtDivReviveCopyDstBody
      (.running (initMachineState stmtDivReviveCopyDstBody [])) =
      .some (.some .ub, "copy_nonoverlapping(src=_3, dst=_2, 1)", .none) := by
  rfl

/-- Positive control for `D9` + `D2` (`rustc_middle/src/mir/syntax.rs`:
"`let _ = *ptr;` is fine even if the pointer is dangling"): mentioning `*_2` via
`PlaceMention(*_2)` when `_2` is initialized succeeds even after its pointee
`_1` has been deallocated by `StorageDead(_1)`:
```text
StorageLive(_1); StorageLive(_2); _1 = const 10_u64; _2 = &raw const _1;
StorageDead(_1); PlaceMention(*_2); _0 = const 99_u64; return
``` -/
private def stmtDivPlaceMentionDanglingPtrOkBody : CapturedMir :=
  stmtDivBody "stmt_div::place_mention_deref_dangling_pointer_ok"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .not ⟨1, []⟩), span := "_2 = &raw const _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .placeMention ⟨2, [.deref]⟩, span := "PlaceMention(*_2)" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 99)), span := "_0 = 99" } ]

theorem stmt_div_placeMention_deref_dangling_ok :
    diffCProbeBounded 16 stmtDivPlaceMentionDanglingPtrOkBody
      (.running (initMachineState stmtDivPlaceMentionDanglingPtrOkBody [])) =
      .some (.none, "none", .some (.scalar ⟨99, 8⟩)) := by
  rfl

/-- `D2` transitive child-reborrow revival regression: reborrowing a mutable
reference `_3 = &mut *_2` (`parentTag = .some 1`, `targetLocal = 1`, initialized
in `.reserved` permission) from raw pointer `_2 = &raw mut _1` before
`StorageDead(_1)`, reviving and re-initializing `_1 = 20` (which only disables
`.active` tags at base `12c9ecb8`, leaving `.reserved` child tag `2` alive),
and reading `_0 = copy *_3`:
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_1 = const 10_u64; _2 = &raw mut _1; _3 = &mut *_2;
StorageDead(_1); StorageLive(_1); _1 = const 20_u64;
_0 = copy *_3; return
``` -/
private def stmtDivReviveChildReborrowReadBody : CapturedMir :=
  stmtDivBody "stmt_div::read_through_child_reborrow_after_revival"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl stmtDivRawMutU64Ty, stmtDivDecl stmtDivRefMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .assign ⟨3, []⟩ (.ref (.mut false) ⟨2, [.deref]⟩), span := "_3 = &mut *_2" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 20)), span := "_1 = 20" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨3, [.deref]⟩)), span := "_0 = copy *_3" } ]

/-- `D2` child-reborrow revival regression: `disableLocalBorrows` disables every
borrow entry with `targetLocal = 1` (both parent tag `1` and child reborrow tag
`2`), so reading `*_3` after revival faults with `FailureKind.ub` (Anneal
previously returned the revived `20`). -/
theorem stmt_div_storage_revive_child_reborrow_read_is_ub :
    diffCProbeBounded 20 stmtDivReviveChildReborrowReadBody
      (.running (initMachineState stmtDivReviveChildReborrowReadBody [])) =
      .some (.some .ub, "_0 = copy *_3", .none) := by
  rfl

/-- `D2` pointer-offset (`BinOp.offset`) after `StorageDead` + `StorageLive`
revival: offsetting the raw pointer `_2 = &raw mut _1` minted before
`StorageDead(_1)` by one `u64` element (a non-zero byte offset, which MiniRust
`ptr_offset_inbounds` and `ptr::offset` only allow inside a live allocation)
faults with `FailureKind.ub` (Anneal previously allowed `Offset` on the stale
tag and returned `0`):
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_1 = const 10_u64; _2 = &raw mut _1;
StorageDead(_1); StorageLive(_1);
_3 = Offset(copy _2, const 1_isize); _0 = const 0_u64; return
```
A zero offset is defined on dangling pointers in MiniRust and Miri; Anneal
currently also faults on it because `evalPtrOffsetBinOp` (`Places.lean`)
rejects disabled tags before inspecting the offset. -/
private def stmtDivRevivePtrOffsetBody : CapturedMir :=
  stmtDivBody "stmt_div::ptr_offset_after_storage_revival"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivU64Ty,
      stmtDivDecl stmtDivRawMutU64Ty, stmtDivDecl stmtDivRawMutU64Ty]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩ (.use (stmtDivConstU64 10)), span := "_1 = 10" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .mut ⟨1, []⟩), span := "_2 = &raw mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨3, []⟩
          (.binaryOp .offset (.copy ⟨2, []⟩)
            (.constant ⟨{ kind := .int .isize, layoutIdx := 0 }, .scalar (.int ⟨1, 8⟩)⟩)),
        span := "_3 = Offset(_2, 1)" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_storage_revive_ptr_offset_is_ub :
    diffCProbeBounded 16 stmtDivRevivePtrOffsetBody
      (.running (initMachineState stmtDivRevivePtrOffsetBody [])) =
      .some (.some .ub, "_3 = Offset(_2, 1)", .none) := by
  rfl

/-- Two-variant enum `enum E { A(u64), B(u64) }` used by the `SetDiscriminant`
regression body (`SetDiscriminant` is only well-formed on enums). -/
private def stmtDivEnumTy : Ty := { kind := .adt "stmt_div::E" [], layoutIdx := 0 }

/-- `D2` `SetDiscriminant` after `StorageDead` + `StorageLive` revival:
writing a discriminant through the two-phase mutable borrow `_2 = &two-phase mut _1`
(whose `.reserved` tag survives the direct write `_1 = E::A(20)` at base
`12c9ecb8`) after `_1` has been deallocated by `StorageDead(_1)`, revived by
`StorageLive(_1)`, and re-initialized faults with `FailureKind.ub` (Anneal
previously updated the revived `_1`'s discriminant and returned `0`):
```text
StorageLive(_1); StorageLive(_2);
_1 = E::A(const 10_u64); _2 = &two-phase mut _1;
StorageDead(_1); StorageLive(_1); _1 = E::A(const 20_u64);
SetDiscriminant(*_2, 1); _0 = const 0_u64; return
``` -/
private def stmtDivReviveSetDiscrBody : CapturedMir :=
  stmtDivBody "stmt_div::set_discriminant_through_revived_local_borrow"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivEnumTy,
      stmtDivDecl { kind := .ref .mut (.adt "stmt_div::E" []), layoutIdx := 0 }]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨1, []⟩
          (.aggregate (.adt "stmt_div::E" 0 .none) [stmtDivConstU64 10]),
        span := "_1 = E::A(10)" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut true) ⟨1, []⟩), span := "_2 = &two-phase mut _1" },
      { kind := .storageDead 1, span := "dead _1" },
      { kind := .storageLive 1, span := "revive _1" },
      { kind := .assign ⟨1, []⟩
          (.aggregate (.adt "stmt_div::E" 0 .none) [stmtDivConstU64 20]),
        span := "_1 = E::A(20)" },
      { kind := .setDiscriminant ⟨2, [.deref]⟩ 1, span := "SetDiscriminant(*_2, 1)" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_storage_revive_set_discriminant_is_ub :
    diffCProbeBounded 16 stmtDivReviveSetDiscrBody
      (.running (initMachineState stmtDivReviveSetDiscrBody [])) =
      .some (.some .ub, "SetDiscriminant(*_2, 1)", .none) := by
  rfl

/-- `D9` compound deref-plus-uninitialized-index regression: mentioning
`(*_2)[_3]` when the root pointer `_2 = &raw const _1` is initialized (so the
leading `.deref` check passes) but the subsequent `.index 3` operand `_3` is
uninitialized (`placeIndexLocalsInit locals [.deref, .index 3] = false`) faults
with `FailureKind.ub` (Anneal previously checked only that root local `_2` was
live and returned `0`):
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_1 = [const 1_u64, const 2_u64]; _2 = &raw const _1;
PlaceMention((*_2)[_3]); _0 = const 0_u64; return
``` -/
private def stmtDivPlaceMentionDerefIndexUninitBody : CapturedMir :=
  stmtDivBody "stmt_div::place_mention_deref_with_uninit_index"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivArrTy,
      stmtDivDecl { kind := .rawPtr .not (.array (.uint .u64) 2), layoutIdx := 0 },
      stmtDivDecl stmtDivUsizeTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨1, []⟩
          (.aggregate (.array stmtDivU64Ty) [stmtDivConstU64 1, stmtDivConstU64 2]),
        span := "_1 = [1, 2]" },
      { kind := .assign ⟨2, []⟩ (.rawPtr .not ⟨1, []⟩), span := "_2 = &raw const _1" },
      { kind := .placeMention ⟨2, [.deref, .index 3]⟩, span := "PlaceMention((*_2)[_3])" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_placeMention_deref_index_uninit_is_ub :
    diffCProbeBounded 16 stmtDivPlaceMentionDerefIndexUninitBody
      (.running (initMachineState stmtDivPlaceMentionDerefIndexUninitBody [])) =
      .some (.some .ub, "PlaceMention((*_2)[_3])", .none) := by
  rfl

end StatementDivergenceRegressions

/-! ## 7. Uninitialized Aggregate Field Writes (`D13b`)

Kernel-checked executions of projected assignments into a field of a live but
uninitialized struct, union, or tuple local (`uninitFieldWriteShell?` in
`evalStmt`). Each body faulted with `.ub` at its first field write before the
default aggregate shell was introduced. -/

section UninitAggregateFieldWrites

open Trusted.Effect

/-- `u32` local type used by the union field regression body. -/
private def stmtDivU32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- `u32` constant operand. -/
private def stmtDivConstU32 (n : Nat) : Operand :=
  .constant ⟨stmtDivU32Ty, .scalar (.int ⟨n, 4⟩)⟩

/-- `union U { f0: u32, f1: u32 }`. -/
private def stmtDivUnionTy : Ty := { kind := .adt "stmt_div::U" [], layoutIdx := 0 }

/-- `struct S { a: u64, b: u64 }`. -/
private def stmtDivStructTy : Ty := { kind := .adt "stmt_div::S" [], layoutIdx := 0 }

/-- `(u64, u64)`. -/
private def stmtDivPairTy : Ty := { kind := .tuple [.uint .u64, .uint .u64], layoutIdx := 0 }

/-- `D13b` (`step_union_field_write_uninit_divergence`): initialize field `f0`
of an uninitialized union local and read it back:
```text
StorageLive(_1); _1.f0 = const 42_u32; _0 = copy (_1.f0); return
``` -/
private def stmtDivUnionFieldInitBody : CapturedMir :=
  stmtDivBody "stmt_div::union_field_write_into_uninit"
    [stmtDivDecl stmtDivU32Ty, stmtDivDecl stmtDivUnionTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 0 stmtDivU32Ty]⟩ (.use (stmtDivConstU32 42)),
        span := "_1.f0 = 42" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 stmtDivU32Ty]⟩)),
        span := "_0 = copy _1.f0" } ]

/-- `D13b` regression: the union field write initializes `_1.f0` and the body
returns `42` (Anneal previously faulted with `.ub` at `_1.f0 = 42`). -/
theorem stmt_div_assign_uninit_union_field_ok :
    diffCProbeBounded 16 stmtDivUnionFieldInitBody
      (.running (initMachineState stmtDivUnionFieldInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨42, 4⟩)) := by
  rfl

/-- `D13b` struct variant: initialize both fields of an uninitialized struct
local out of declaration order and read the first one back:
```text
StorageLive(_1); _1.b = const 7_u64; _1.a = const 5_u64; _0 = copy (_1.a); return
``` -/
private def stmtDivStructFieldInitBody : CapturedMir :=
  stmtDivBody "stmt_div::struct_fields_written_out_of_order_into_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivStructTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 1 stmtDivU64Ty]⟩ (.use (stmtDivConstU64 7)),
        span := "_1.b = 7" },
      { kind := .assign ⟨1, [.field 0 stmtDivU64Ty]⟩ (.use (stmtDivConstU64 5)),
        span := "_1.a = 5" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 stmtDivU64Ty]⟩)),
        span := "_0 = copy _1.a" } ]

/-- `D13b` struct regression: the body returns `5` (Anneal previously faulted
with `.ub` at `_1.b = 7`). -/
theorem stmt_div_assign_uninit_struct_fields_ok :
    diffCProbeBounded 16 stmtDivStructFieldInitBody
      (.running (initMachineState stmtDivStructFieldInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨5, 8⟩)) := by
  rfl

/-- `D13b` tuple variant: initialize both fields of an uninitialized pair local
and read the second one back:
```text
StorageLive(_1); _1.0 = const 3_u64; _1.1 = const 4_u64; _0 = copy (_1.1); return
``` -/
private def stmtDivPairFieldInitBody : CapturedMir :=
  stmtDivBody "stmt_div::tuple_fields_written_into_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivPairTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 0 stmtDivU64Ty]⟩ (.use (stmtDivConstU64 3)),
        span := "_1.0 = 3" },
      { kind := .assign ⟨1, [.field 1 stmtDivU64Ty]⟩ (.use (stmtDivConstU64 4)),
        span := "_1.1 = 4" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 1 stmtDivU64Ty]⟩)),
        span := "_0 = copy _1.1" } ]

/-- `D13b` tuple regression: the body returns `4` (Anneal previously faulted
with `.ub` at `_1.0 = 3`). -/
theorem stmt_div_assign_uninit_tuple_fields_ok :
    diffCProbeBounded 16 stmtDivPairFieldInitBody
      (.running (initMachineState stmtDivPairFieldInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨4, 8⟩)) := by
  rfl

/-- `struct Outer { a: S, b: S }` with two nested struct fields. -/
private def stmtDivOuterStructTy : Ty :=
  { kind := .adt "stmt_div::Outer" [], layoutIdx := 0 }

/-- `(u32, u32)` pair type used inside a union field. -/
private def stmtDivU32PairTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }

/-- `D13b` nested aggregate regression (reverse field order): initialize all
four leaf fields of an uninitialized `Outer { a: S, b: S }` local in reverse
order (`_1.b.b`, `_1.b.a`, `_1.a.b`, `_1.a.a`) and read `_1.a.a` back:
```text
StorageLive(_1);
(_1.b).b = const 40_u64; (_1.b).a = const 30_u64;
(_1.a).b = const 20_u64; (_1.a).a = const 10_u64;
_0 = copy ((_1.a).a); return
```
Without `ensureNestedFieldShells`, `_1.b.b = 40` faulted with `.ub` against the
flat shell `.aggregate 0 []`, and `_1.a.b = 20` faulted against the `.unit`
padding left at field `0` by `setOrExtendFields`. -/
private def stmtDivNestedStructRevInitBody : CapturedMir :=
  stmtDivBody "stmt_div::nested_struct_fields_reverse_order_into_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivOuterStructTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 1 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 40)),
        span := "(_1.b).b = 40" },
      { kind := .assign ⟨1, [.field 1 stmtDivStructTy, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 30)),
        span := "(_1.b).a = 30" },
      { kind := .assign ⟨1, [.field 0 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 20)),
        span := "(_1.a).b = 20" },
      { kind := .assign ⟨1, [.field 0 stmtDivStructTy, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 10)),
        span := "(_1.a).a = 10" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivStructTy, .field 0 stmtDivU64Ty]⟩)),
        span := "_0 = copy (_1.a).a" } ]

theorem stmt_div_assign_uninit_nested_struct_rev_ok :
    diffCProbeBounded 16 stmtDivNestedStructRevInitBody
      (.running (initMachineState stmtDivNestedStructRevInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨10, 8⟩)) := by
  rfl

/-- `D13b` nested aggregate regression (forward field order): initialize all
four leaf fields of an uninitialized `Outer { a: S, b: S }` local in declaration
order (`_1.a.a`, `_1.a.b`, `_1.b.a`, `_1.b.b`) and read `_1.b.b` back:
```text
StorageLive(_1);
(_1.a).a = const 10_u64; (_1.a).b = const 20_u64;
(_1.b).a = const 30_u64; (_1.b).b = const 40_u64;
_0 = copy ((_1.b).b); return
```
Without `ensureNestedFieldShells`, `(_1.a).a = 10` collapsed `.field 0` onto
`.unit` in `writeProjectedValue` (storing a bare scalar `10` at `_1.a`), causing
the second statement `(_1.a).b = 20` to fault with `.ub`. -/
private def stmtDivNestedStructFwdInitBody : CapturedMir :=
  stmtDivBody "stmt_div::nested_struct_fields_forward_order_into_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivOuterStructTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 0 stmtDivStructTy, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 10)),
        span := "(_1.a).a = 10" },
      { kind := .assign ⟨1, [.field 0 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 20)),
        span := "(_1.a).b = 20" },
      { kind := .assign ⟨1, [.field 1 stmtDivStructTy, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 30)),
        span := "(_1.b).a = 30" },
      { kind := .assign ⟨1, [.field 1 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 40)),
        span := "(_1.b).b = 40" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 1 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩)),
        span := "_0 = copy (_1.b).b" } ]

theorem stmt_div_assign_uninit_nested_struct_fwd_ok :
    diffCProbeBounded 16 stmtDivNestedStructFwdInitBody
      (.running (initMachineState stmtDivNestedStructFwdInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨40, 8⟩)) := by
  rfl

/-- `D13b` union with nested tuple field (`union U { pair: (u32, u32), raw: u64 }`):
initialize both elements of `_1.pair` on an uninitialized union local and read
`(_1.pair).1` back:
```text
StorageLive(_1); (_1.pair).1 = const 99_u32; (_1.pair).0 = const 77_u32;
_0 = copy ((_1.pair).1); return
``` -/
private def stmtDivUnionNestedPairInitBody : CapturedMir :=
  stmtDivBody "stmt_div::union_nested_pair_field_write_into_uninit"
    [stmtDivDecl stmtDivU32Ty, stmtDivDecl stmtDivUnionTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 0 stmtDivU32PairTy, .field 1 stmtDivU32Ty]⟩
          (.use (stmtDivConstU32 99)),
        span := "(_1.pair).1 = 99" },
      { kind := .assign ⟨1, [.field 0 stmtDivU32PairTy, .field 0 stmtDivU32Ty]⟩
          (.use (stmtDivConstU32 77)),
        span := "(_1.pair).0 = 77" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivU32PairTy, .field 1 stmtDivU32Ty]⟩)),
        span := "_0 = copy (_1.pair).1" } ]

theorem stmt_div_assign_uninit_union_nested_pair_ok :
    diffCProbeBounded 16 stmtDivUnionNestedPairInitBody
      (.running (initMachineState stmtDivUnionNestedPairInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨99, 4⟩)) := by
  rfl

/-- `D13b` nested aggregate regression with transparent `.opaqueCast` and
`.unwrapUnsafeBinder` wrappers: initialize `(_1.b as S).b = 40` on an
uninitialized `Outer { a: S, b: S }` local and then initialize
`(unwrap_unsafe_binder(_1.a)).b = 20` into the `.unit`-padded sibling slot at
`_1.a`, reading `(_1.a).b` back:
```text
StorageLive(_1);
((_1.b) as S).b = const 40_u64;
(unwrap_unsafe_binder(_1.a)).b = const 20_u64;
_0 = copy ((_1.a).b); return
```
Without stripping transparent projections in `ensureNestedFieldShells` and
`fieldShellChainPopulated`, both writes faulted with `.ub` because the
intermediate `.opaqueCast` / `.unwrapUnsafeBinder` hid the trailing `.field`
projection. -/
private def stmtDivNestedOpaqueCastInitBody : CapturedMir :=
  stmtDivBody "stmt_div::nested_struct_fields_with_transparent_projections"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivOuterStructTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 1 stmtDivStructTy, .opaqueCast stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 40)),
        span := "((_1.b) as S).b = 40" },
      { kind := .assign ⟨1, [.field 0 stmtDivStructTy, .unwrapUnsafeBinder stmtDivStructTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 20)),
        span := "(unwrap(_1.a)).b = 20" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivStructTy, .field 1 stmtDivU64Ty]⟩)),
        span := "_0 = copy (_1.a).b" } ]

theorem stmt_div_assign_uninit_nested_opaque_cast_field_ok :
    diffCProbeBounded 16 stmtDivNestedOpaqueCastInitBody
      (.running (initMachineState stmtDivNestedOpaqueCastInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨20, 8⟩)) := by
  rfl

/-- `((u64, u64), u64)` nested tuple type. -/
private def stmtDivNestedTupleTy : Ty :=
  { kind := .tuple [.tuple [.uint .u64, .uint .u64], .uint .u64], layoutIdx := 0 }

/-- `D13b` nested tuple-in-tuple regression (`((u64, u64), u64)`): initialize
`(_1.0).1 = 88`, `(_1.0).0 = 66`, and `_1.1 = 99` on an uninitialized nested
tuple local and read `(_1.0).0` back:
```text
StorageLive(_1); (_1.0).1 = const 88_u64; (_1.0).0 = const 66_u64;
_1.1 = const 99_u64; _0 = copy ((_1.0).0); return
``` -/
private def stmtDivNestedTupleInitBody : CapturedMir :=
  stmtDivBody "stmt_div::nested_tuple_fields_written_into_uninit"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivNestedTupleTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 0 stmtDivPairTy, .field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 88)),
        span := "(_1.0).1 = 88" },
      { kind := .assign ⟨1, [.field 0 stmtDivPairTy, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 66)),
        span := "(_1.0).0 = 66" },
      { kind := .assign ⟨1, [.field 1 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 99)),
        span := "_1.1 = 99" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivPairTy, .field 0 stmtDivU64Ty]⟩)),
        span := "_0 = copy (_1.0).0" } ]

theorem stmt_div_assign_uninit_nested_tuple_fields_ok :
    diffCProbeBounded 16 stmtDivNestedTupleInitBody
      (.running (initMachineState stmtDivNestedTupleInitBody [])) =
      .some (.none, "none", .some (.scalar ⟨66, 8⟩)) := by
  rfl

/-- `&U` shared reference type to `union U`. -/
private def stmtDivRefUnionTy : Ty :=
  { kind := .ref .not (.adt "stmt_div::U" []), layoutIdx := 0 }

/-- `&mut U` mutable reference type to `union U`. -/
private def stmtDivRefMutUnionTy : Ty :=
  { kind := .ref .mut (.adt "stmt_div::U" []), layoutIdx := 0 }

/-- `struct PairOfUnions { a: U, b: U }` containing two union fields (valid
while uninitialized in Rust, Miri, and MiniRust). -/
private def stmtDivPairOfUnionsTy : Ty :=
  { kind := .adt "stmt_div::PairOfUnions" [], layoutIdx := 0 }

/-- `D13b` Tree Borrows invalidation regression on an uninitialized union field
write: taking a shared reference `_2 = &_1` to an uninitialized `Freeze` union
local `_1 : U` (accepted at the MIR level by Miri and MiniRust, whose reference
validity does not require an initialized pointee; surface Rust rejects the
borrow statically) mints a `.frozen` borrow on `_1`; initializing
`_1.f0 = const 42_u32` via the `D13b` `.uninit` branch disables that conflicting
`.frozen` borrow, so a subsequent read `_0 = copy ((*_2).f0)` faults with
`FailureKind.ub` at the read (whereas Anneal previously faulted earlier at
`_1.f0 = 42`):
```text
StorageLive(_1); StorageLive(_2); _2 = &_1; _1.f0 = const 42_u32;
_0 = copy ((*_2).f0); return
``` -/
private def stmtDivUninitUnionInvalidatesSharedRefBody : CapturedMir :=
  stmtDivBody "stmt_div::uninit_union_field_write_invalidates_shared_ref"
    [stmtDivDecl stmtDivU32Ty, stmtDivDecl stmtDivUnionTy, stmtDivDecl stmtDivRefUnionTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨2, []⟩ (.ref .shared ⟨1, []⟩), span := "_2 = &_1" },
      { kind := .assign ⟨1, [.field 0 stmtDivU32Ty]⟩ (.use (stmtDivConstU32 42)),
        span := "_1.f0 = 42" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨2, [.deref, .field 0 stmtDivU32Ty]⟩)),
        span := "_0 = copy (*_2).f0" } ]

theorem stmt_div_assign_uninit_union_field_invalidates_shared_ref_ub :
    diffCProbeBounded 16 stmtDivUninitUnionInvalidatesSharedRefBody
      (.running (initMachineState stmtDivUninitUnionInvalidatesSharedRefBody [])) =
      .some (.some .ub, "_0 = copy (*_2).f0", .none) := by
  rfl

/-- `D13b` projection-aware borrow preservation on an uninitialized sibling
field write: taking `_2 = &mut (_1.a)` on an uninitialized
`PairOfUnions { a: U, b: U }` local `_1` mints an `.active` borrow on `_1` at
`[.field 0 U]`; initializing the disjoint sibling field `(_1.b).f0 = 20_u32` via
`D13b` + `ensureNestedFieldShells` preserves `_2` via
`invalidateConflictingBorrowsAtProj`, so writing `(*_2) = move _3` (`U { f0: 10 }`)
and reading `(_1.a).f0` succeeds and returns `10` (whereas Anneal previously
faulted at `_3.f0 = 10` / `(_1.b).f0 = 20`, and whole-local borrow invalidation
would fault at `(*_2) = move _3`):
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_3.f0 = const 10_u32; _2 = &mut (_1.a); (_1.b).f0 = const 20_u32;
(*_2) = move _3; _0 = copy ((_1.a).f0); return
``` -/
private def stmtDivUninitSiblingPreservesMutRefBody : CapturedMir :=
  stmtDivBody "stmt_div::uninit_sibling_union_field_write_preserves_mut_ref"
    [stmtDivDecl stmtDivU32Ty, stmtDivDecl stmtDivPairOfUnionsTy,
      stmtDivDecl stmtDivRefMutUnionTy, stmtDivDecl stmtDivUnionTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨3, [.field 0 stmtDivU32Ty]⟩ (.use (stmtDivConstU32 10)),
        span := "_3.f0 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut false) ⟨1, [.field 0 stmtDivUnionTy]⟩),
        span := "_2 = &mut (_1.a)" },
      { kind := .assign ⟨1, [.field 1 stmtDivUnionTy, .field 0 stmtDivU32Ty]⟩
          (.use (stmtDivConstU32 20)),
        span := "(_1.b).f0 = 20" },
      { kind := .assign ⟨2, [.deref]⟩ (.use (.move ⟨3, []⟩)),
        span := "(*_2) = move _3" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivUnionTy, .field 0 stmtDivU32Ty]⟩)),
        span := "_0 = copy (_1.a).f0" } ]

theorem stmt_div_assign_uninit_sibling_union_field_preserves_mut_ref_ok :
    diffCProbeBounded 16 stmtDivUninitSiblingPreservesMutRefBody
      (.running (initMachineState stmtDivUninitSiblingPreservesMutRefBody [])) =
      .some (.none, "none", .some (.scalar ⟨10, 4⟩)) := by
  rfl

/-- `D13b` overlapping-field complement of
`stmt_div_assign_uninit_sibling_union_field_preserves_mut_ref_ok`: the same body
with the nested `D13b` write moved from the disjoint sibling `(_1.b).f0` onto the
borrowed field `(_1.a).f0` disables the `.active` borrow `_2 = &mut (_1.a)`
(`invalidateConflictingBorrowsAtProj` on the overlapping two-level path
`[.field 0 U, .field 0 u32]`), so the later write through `_2` faults with
`FailureKind.ub`. Miri reports UB at the same statement (the direct write to
`_1.a` is a foreign write that disables `_2` under Tree Borrows, and pops it
under Stacked Borrows). Together with the sibling witness, this pins
projection-aware invalidation on the nested `.uninit` path: dropping the
invalidation would return `10` here, and whole-local invalidation would fault
in the sibling witness. Anneal previously faulted at `_3.f0 = 10`:
```text
StorageLive(_1); StorageLive(_2); StorageLive(_3);
_3.f0 = const 10_u32; _2 = &mut (_1.a); (_1.a).f0 = const 20_u32;
(*_2) = move _3; _0 = copy ((_1.a).f0); return
``` -/
private def stmtDivUninitOverlapDisablesMutRefBody : CapturedMir :=
  stmtDivBody "stmt_div::uninit_overlapping_union_field_write_disables_mut_ref"
    [stmtDivDecl stmtDivU32Ty, stmtDivDecl stmtDivPairOfUnionsTy,
      stmtDivDecl stmtDivRefMutUnionTy, stmtDivDecl stmtDivUnionTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .storageLive 3, span := "live _3" },
      { kind := .assign ⟨3, [.field 0 stmtDivU32Ty]⟩ (.use (stmtDivConstU32 10)),
        span := "_3.f0 = 10" },
      { kind := .assign ⟨2, []⟩ (.ref (.mut false) ⟨1, [.field 0 stmtDivUnionTy]⟩),
        span := "_2 = &mut (_1.a)" },
      { kind := .assign ⟨1, [.field 0 stmtDivUnionTy, .field 0 stmtDivU32Ty]⟩
          (.use (stmtDivConstU32 20)),
        span := "(_1.a).f0 = 20" },
      { kind := .assign ⟨2, [.deref]⟩ (.use (.move ⟨3, []⟩)),
        span := "(*_2) = move _3" },
      { kind := .assign ⟨0, []⟩
          (.use (.copy ⟨1, [.field 0 stmtDivUnionTy, .field 0 stmtDivU32Ty]⟩)),
        span := "_0 = copy (_1.a).f0" } ]

theorem stmt_div_assign_uninit_overlapping_nested_field_write_disables_mut_ref_ub :
    diffCProbeBounded 16 stmtDivUninitOverlapDisablesMutRefBody
      (.running (initMachineState stmtDivUninitOverlapDisablesMutRefBody [])) =
      .some (.some .ub, "(*_2) = move _3", .none) := by
  rfl

/-- Known `D13b` limitation, pinned so that a future fix is noticed: after an
out-of-order write that initializes only field `b` of an uninitialized struct
local, reading the never-written field `a` returns the `.unit` padding that
`setOrExtendFields` (`Places.lean`) inserted below `b`, instead of faulting as
MiniRust and Miri do for a read of uninitialized memory. Closing this gap needs
an uninitialized-field representation in `Value` (or a typed-copy validity
check), both outside the `Statements.lean` scope:
```text
StorageLive(_1); _1.b = const 7_u64; _0 = copy (_1.a); return
``` -/
private def stmtDivUnwrittenLowerFieldBody : CapturedMir :=
  stmtDivBody "stmt_div::struct_read_of_unwritten_lower_field"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivStructTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.field 1 stmtDivU64Ty]⟩ (.use (stmtDivConstU64 7)),
        span := "_1.b = 7" },
      { kind := .assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 stmtDivU64Ty]⟩)),
        span := "_0 = copy _1.a" } ]

/-- Known `D13b` limitation witness: the body returns the `.unit` padding. -/
theorem stmt_div_known_limitation_unwritten_lower_field_reads_unit :
    diffCProbeBounded 16 stmtDivUnwrittenLowerFieldBody
      (.running (initMachineState stmtDivUnwrittenLowerFieldBody [])) =
      .some (.none, "none", .some .unit) := by
  rfl

/-- `D13b` array-field scope-boundary witness
(`evalStmt_assign_uninit_array_field_elem_ub`): writing element `_2` of the
never-written array field `_1.arr` of an uninitialized union local
(`union U { arr: [u64; 2], wide: u64 }`) still faults with `FailureKind.ub`:
```text
StorageLive(_1); StorageLive(_2); _2 = const 0_usize;
(_1.arr)[_2] = const 11_u64; _0 = const 0_u64; return
```
MiniRust and Miri accept this write. Anneal keeps the fault: materializing the
array would fill the unwritten element `(_1.arr)[1]` with a `.unit` placeholder
that a later `copy (_1.arr)[1]` would return instead of faulting on the
uninitialized element. -/
private def stmtDivUnionArrayFieldElemBody : CapturedMir :=
  stmtDivBody "stmt_div::union_array_field_elem_write_into_uninit_is_ub"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivUnionTy, stmtDivDecl stmtDivUsizeTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨2, []⟩
          (.use (.constant ⟨stmtDivUsizeTy, .scalar (.int ⟨0, 8⟩)⟩)),
        span := "_2 = 0" },
      { kind := .assign ⟨1, [.field 0 stmtDivArrTy, .index 2]⟩
          (.use (stmtDivConstU64 11)),
        span := "(_1.arr)[_2] = 11" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_assign_uninit_array_field_elem_is_ub :
    diffCProbeBounded 16 stmtDivUnionArrayFieldElemBody
      (.running (initMachineState stmtDivUnionArrayFieldElemBody [])) =
      .some (.some .ub, "(_1.arr)[_2] = 11", .none) := by
  rfl

/-- `D13b` scope-boundary witness (`evalStmt_assign_uninit_non_aggregate_ub`):
writing an array element `_1[_2] = const 10_u64` into an uninitialized array
local `_1` (where `_2 = const 0_usize`) still faults with `FailureKind.ub`.
MiniRust (`eval_place` on `PlaceExpr::Index` only checks the index against the
static element count) and Miri accept this write; Anneal keeps the fault because
the `D13b` repair is scoped to field projections, so this witness guards that
boundary rather than asserting Rust semantics:
```text
StorageLive(_1); StorageLive(_2); _2 = const 0_usize;
_1[_2] = const 10_u64; _0 = const 0_u64; return
``` -/
private def stmtDivUninitArrayIndexWriteBody : CapturedMir :=
  stmtDivBody "stmt_div::array_index_write_into_uninit_is_ub"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivArrTy, stmtDivDecl stmtDivUsizeTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .storageLive 2, span := "live _2" },
      { kind := .assign ⟨2, []⟩
          (.use (.constant ⟨stmtDivUsizeTy, .scalar (.int ⟨0, 8⟩)⟩)),
        span := "_2 = 0" },
      { kind := .assign ⟨1, [.index 2]⟩ (.use (stmtDivConstU64 10)),
        span := "_1[_2] = 10" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_assign_uninit_array_index_is_ub :
    diffCProbeBounded 16 stmtDivUninitArrayIndexWriteBody
      (.running (initMachineState stmtDivUninitArrayIndexWriteBody [])) =
      .some (.some .ub, "_1[_2] = 10", .none) := by
  rfl

/-- `D13b` scope-boundary witness (`evalStmt_assign_uninit_non_aggregate_ub`):
writing an enum variant field `((_1 as Variant#0).0) = const 10_u64` into an
uninitialized enum local `_1` (without `SetDiscriminant`) still faults with
`FailureKind.ub`. MiniRust (`eval_place` on `PlaceExpr::Downcast` returns the
root place at the variant type without any check) and Miri accept this write;
Anneal keeps the fault because the `D13b` repair is scoped to field projections,
so this witness guards that boundary rather than asserting Rust semantics:
```text
StorageLive(_1); ((_1 as A).0) = const 10_u64; _0 = const 0_u64; return
``` -/
private def stmtDivUninitDowncastWriteBody : CapturedMir :=
  stmtDivBody "stmt_div::enum_downcast_field_write_into_uninit_is_ub"
    [stmtDivDecl stmtDivU64Ty, stmtDivDecl stmtDivEnumTy]
    [ { kind := .storageLive 1, span := "live _1" },
      { kind := .assign ⟨1, [.downcast "A" 0, .field 0 stmtDivU64Ty]⟩
          (.use (stmtDivConstU64 10)),
        span := "((_1 as A).0) = 10" },
      { kind := .assign ⟨0, []⟩ (.use (stmtDivConstU64 0)), span := "_0 = 0" } ]

theorem stmt_div_assign_uninit_downcast_is_ub :
    diffCProbeBounded 16 stmtDivUninitDowncastWriteBody
      (.running (initMachineState stmtDivUninitDowncastWriteBody [])) =
      .some (.some .ub, "((_1 as A).0) = 10", .none) := by
  rfl

/-- **Theorem L5.24 (`mir_uninit_aggregate_field_write_characterizations`)**:
Consolidates the `Statements.lean` universal characterizations for `D13b`
(`ensureNestedFieldShells`, `fieldShellChainPopulated`, `uninitFieldWriteShell?`,
and `evalStmt` on projected writes into live uninitialized and initialized locals):
1. `ensureNestedFieldShells` is the identity on any single-element projection
   list (`ensureNestedFieldShells_singleton`) and on any root whose intermediate
   field slots along the written chain are populated
   (`ensureNestedFieldShells_eq_self_of_populated`,
   `writeProjectedValue_ensureNestedFieldShells_of_populated`,
   `evalStmt_assign_init_projected_step`), while materializing inner aggregate
   shells when writing into an unpopulated (`.none` or `.some .unit`) outer
   field slot of an already-initialized aggregate
   (`evalStmt_assign_init_unpopulated_nested_field_ok`).
2. `uninitFieldWriteShell?` returns `.some (.aggregate 0 .nil)` for single-level
   field projections on `.adt` and `.tuple` locals (`uninitFieldWriteShell?_field_adt`,
   `uninitFieldWriteShell?_field_tuple`) and `.none` for non-field projection
   heads or non-aggregate root types (`uninitFieldWriteShell?_eq_none_of_not_field`,
   `uninitFieldWriteShell?_eq_none_of_non_aggregate_ty`,
   `uninitFieldWriteShell?_eq_none_iff`).
3. `evalStmt` initializes `.uninit` struct, union, tuple, and nested aggregate
   locals when `writeProjectedValue` succeeds and no active protector conflicts
   (`evalStmt_assign_uninit_aggregate_field_step`,
   `evalStmt_assign_uninit_union_field_ok`,
   `evalStmt_assign_uninit_tuple_field_ok`,
   `evalStmt_assign_uninit_nested_field_ok`), and faults with
   `MirStepNode.fail .ub` when a protected borrow conflicts
   (`evalStmt_assign_uninit_aggregate_field_protected_conflict_ub`), when the
   write goes through a never-written array field or non-field sub-projection
   (`evalStmt_assign_uninit_array_field_elem_ub`,
   `evalStmt_assign_uninit_field_non_field_subproj_ub`), or when no aggregate
   shell applies (`evalStmt_assign_uninit_non_aggregate_ub`). -/
theorem mir_uninit_aggregate_field_write_characterizations
    (s : MachineState)
    (dstLoc idxLocal : Local)
    (variantIdx : VariantIdx)
    (fields : List Value)
    (fieldIdx innerIdx : FieldIdx)
    (outerTy fieldTy : Ty)
    (elemKind : RigidTy)
    (count arrLayoutIdx : Nat)
    (proj nextProj : ProjectionElem)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (defPath : DefPath)
    (args tupleFields : List RigidTy)
    (layoutIdx : Nat)
    (val rootVal : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (shell rootVal' : Value)
    (locals₂ : List LocalSlot)
    (protHead : Nat)
    (protTail : List Nat) :
    ensureNestedFieldShells val [proj] = val ∧
    (fieldShellChainPopulated rootVal (proj :: rest) = true →
      ensureNestedFieldShells rootVal (proj :: rest) = rootVal) ∧
    (fieldShellChainPopulated rootVal (proj :: rest) = true →
      writeProjectedValue locals₁ (ensureNestedFieldShells rootVal (proj :: rest))
        (proj :: rest) val =
        writeProjectedValue locals₁ rootVal (proj :: rest) val) ∧
    (proj ≠ .deref →
      evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some (.init rootVal) →
      fieldShellChainPopulated rootVal (proj :: rest) = true →
      writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal (proj :: rest) val =
        .ok rootVal' →
      set? locals₁ dstLoc (.init rootVal') = .some locals₂ →
      (∀ (pH : Nat) (pT : List Nat),
        mem₁.activeProtectors = pH :: pT →
        hasProtectedWriteConflict mem₁.borrows (pH :: pT) dstLoc .none
          (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
            (proj :: rest)) = false) →
      evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s locals₂
            { mem₁ with
              borrows :=
                invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                  (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                    (proj :: rest)) })) ∧
    (let projs : List ProjectionElem := [.field fieldIdx outerTy, .field innerIdx fieldTy];
      evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some (.init (.aggregate variantIdx fields)) →
      ((∃ innerDefPath innerArgs, outerTy.kind = .adt innerDefPath innerArgs) ∨
       (∃ innerFields, outerTy.kind = .tuple innerFields)) →
      (get? fields fieldIdx = .none ∨ get? fields fieldIdx = .some .unit) →
      set? locals₁ dstLoc
        (.init
          (.aggregate variantIdx
            (setOrExtendFields fields fieldIdx
              (.aggregate 0 (setOrExtendFields .nil innerIdx val))))) =
        .some locals₂ →
      mem₁.activeProtectors = .nil →
      placeTouchesUnion localDecls layouts { local_ := dstLoc, projection := projs } = false →
      evalStmt s ⟨.assign ⟨dstLoc, projs⟩ rv, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s locals₂
            { mem₁ with
              borrows :=
                invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                  (match resolveBorrowProjectionElems locals₁ projs with
                   | .some rp => rp
                   | .none => projs) })) ∧
    (placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
        .some { kind := .adt defPath args, layoutIdx := layoutIdx } →
      uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) =
        .some (.aggregate 0 .nil)) ∧
    (placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
        .some { kind := .tuple tupleFields, layoutIdx := layoutIdx } →
      uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) =
        .some (.aggregate 0 .nil)) ∧
    ((∀ (fIdx : FieldIdx) (fTy : Ty), proj ≠ .field fIdx fTy) →
      uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none) ∧
    ((∀ (dp : DefPath) (as_ : List RigidTy) (lIdx : Nat),
        placeTy localDecls layouts { local_ := dstLoc, projection := .nil } ≠
          .some { kind := .adt dp as_, layoutIdx := lIdx }) →
      (∀ (fs : List RigidTy) (lIdx : Nat),
        placeTy localDecls layouts { local_ := dstLoc, projection := .nil } ≠
          .some { kind := .tuple fs, layoutIdx := lIdx }) →
      uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none) ∧
    (uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none ↔
      uninitFieldWriteShell? localDecls layouts dstLoc proj .nil = .none) ∧
    (evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) rest =
        .some shell →
      writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
        (.field fieldIdx fieldTy :: rest) val = .ok rootVal' →
      set? locals₁ dstLoc (.init rootVal') = .some locals₂ →
      mem₁.activeProtectors = protHead :: protTail →
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
        (resolveBorrowWriteLocalProj
          localDecls layouts locals₁ dstLoc (.field fieldIdx fieldTy :: rest)) = true →
      evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: rest⟩ rv, span⟩
        localDecls layouts = MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
        .some { kind := .adt defPath args, layoutIdx := layoutIdx } →
      set? locals₁ dstLoc (.init (.aggregate 0 (setOrExtendFields .nil fieldIdx val))) =
        .some locals₂ →
      mem₁.activeProtectors = .nil →
      placeTouchesUnion localDecls layouts
        { local_ := dstLoc, projection := .field fieldIdx fieldTy :: .nil } = false →
      evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: .nil⟩ rv, span⟩
        localDecls layouts =
        MirStepNode.step
          (advanceStmt s locals₂
            { mem₁ with
              borrows :=
                invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                  (match resolveBorrowProjectionElems locals₁ (.field fieldIdx fieldTy :: .nil) with
                   | .some rp => rp
                   | .none => .field fieldIdx fieldTy :: .nil) })) ∧
    (evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
        .some { kind := .tuple tupleFields, layoutIdx := layoutIdx } →
      set? locals₁ dstLoc (.init (.aggregate 0 (setOrExtendFields .nil fieldIdx val))) =
        .some locals₂ →
      mem₁.activeProtectors = .nil →
      evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: .nil⟩ rv, span⟩
        localDecls layouts =
        MirStepNode.step
          (advanceStmt s locals₂
            { mem₁ with
              borrows :=
                invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                  (match resolveBorrowProjectionElems locals₁ (.field fieldIdx fieldTy :: .nil) with
                   | .some rp => rp
                   | .none => .field fieldIdx fieldTy :: .nil) })) ∧
    (let projs : List ProjectionElem := [.field fieldIdx outerTy, .field innerIdx fieldTy];
      evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      ((∃ dp as_ lIdx,
          placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
            .some { kind := .adt dp as_, layoutIdx := lIdx }) ∨
       (∃ tfs lIdx,
          placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
            .some { kind := .tuple tfs, layoutIdx := lIdx })) →
      ((∃ innerDefPath innerArgs, outerTy.kind = .adt innerDefPath innerArgs) ∨
       (∃ innerFields, outerTy.kind = .tuple innerFields)) →
      set? locals₁ dstLoc
        (.init
          (.aggregate 0
            (setOrExtendFields .nil fieldIdx
              (.aggregate 0 (setOrExtendFields .nil innerIdx val))))) =
        .some locals₂ →
      mem₁.activeProtectors = .nil →
      placeTouchesUnion localDecls layouts { local_ := dstLoc, projection := projs } = false →
      evalStmt s ⟨.assign ⟨dstLoc, projs⟩ rv, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s locals₂
            { mem₁ with
              borrows :=
                invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                  (match resolveBorrowProjectionElems locals₁ projs with
                   | .some rp => rp
                   | .none => projs) })) ∧
    (evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      evalStmt s
          ⟨.assign
            ⟨dstLoc,
              .field fieldIdx { kind := .array elemKind count, layoutIdx := arrLayoutIdx } ::
                .index idxLocal :: rest⟩ rv,
            span⟩
          localDecls layouts =
        MirStepNode.fail .ub) ∧
    (evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      ((∃ iLoc, nextProj = .index iLoc) ∨
       (∃ offset minLen fromEnd, nextProj = .constantIndex offset minLen fromEnd) ∨
       (∃ fromIdx toIdx fromEnd, nextProj = .subslice fromIdx toIdx fromEnd) ∨
       (∃ variantName vIdx, nextProj = .downcast variantName vIdx)) →
      evalStmt s
          ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: nextProj :: rest⟩ rv, span⟩
          localDecls layouts =
        MirStepNode.fail .ub) ∧
    (proj ≠ .deref →
      evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some .uninit →
      uninitFieldWriteShell? localDecls layouts dstLoc proj = .none →
      evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  refine ⟨ensureNestedFieldShells_singleton val proj,
    ensureNestedFieldShells_eq_self_of_populated (proj :: rest) rootVal,
    writeProjectedValue_ensureNestedFieldShells_of_populated locals₁ rootVal (proj :: rest) val,
    evalStmt_assign_init_projected_step s dstLoc proj rest rv span localDecls layouts
      val rootVal rootVal' locals₁ locals₂ mem₁,
    fun hRv hInit hOuterAgg hSlot hSet hProt hNoUnion =>
      evalStmt_assign_init_unpopulated_nested_field_ok s dstLoc variantIdx fields
        fieldIdx innerIdx outerTy fieldTy rv span localDecls layouts val locals₁ locals₂ mem₁
        hRv hInit hOuterAgg hSlot hSet hProt hNoUnion,
    uninitFieldWriteShell?_field_adt localDecls layouts dstLoc fieldIdx fieldTy
      defPath args layoutIdx,
    uninitFieldWriteShell?_field_tuple localDecls layouts dstLoc fieldIdx fieldTy
      tupleFields layoutIdx,
    uninitFieldWriteShell?_eq_none_of_not_field localDecls layouts dstLoc proj rest,
    uninitFieldWriteShell?_eq_none_of_non_aggregate_ty localDecls layouts dstLoc proj rest,
    uninitFieldWriteShell?_eq_none_iff localDecls layouts dstLoc proj rest,
    evalStmt_assign_uninit_aggregate_field_protected_conflict_ub s dstLoc fieldIdx fieldTy
      rest rv span localDecls layouts val locals₁ mem₁ shell rootVal' locals₂ protHead protTail,
    fun hRv hUninit hTy hSet hProt hNoUnion =>
      evalStmt_assign_uninit_union_field_ok s dstLoc fieldIdx fieldTy rv span localDecls layouts
        defPath args layoutIdx val locals₁ mem₁ locals₂
        hRv hUninit hTy hSet hProt hNoUnion,
    evalStmt_assign_uninit_tuple_field_ok s dstLoc fieldIdx fieldTy rv span localDecls layouts
      tupleFields layoutIdx val locals₁ mem₁ locals₂,
    fun hRv hUninit hRootAgg hOuterAgg hSet hProt hNoUnion =>
      evalStmt_assign_uninit_nested_field_ok s dstLoc fieldIdx innerIdx outerTy fieldTy rv span
        localDecls layouts val locals₁ mem₁ locals₂
        hRv hUninit hRootAgg hOuterAgg hSet hProt hNoUnion,
    evalStmt_assign_uninit_array_field_elem_ub s dstLoc idxLocal fieldIdx elemKind count
      arrLayoutIdx rest rv span localDecls layouts val locals₁ mem₁,
    evalStmt_assign_uninit_field_non_field_subproj_ub s dstLoc fieldIdx fieldTy nextProj
      rest rv span localDecls layouts val locals₁ mem₁,
    evalStmt_assign_uninit_non_aggregate_ub s dstLoc proj rest rv span localDecls layouts
      val locals₁ mem₁⟩

/--
Correspondence theorem for projected local union field writes (`R1`):
1. `resolveBorrowWriteLocalProj` reduces to `resolveBorrowProjectionElems` with
   fallback `projs` whenever `placeTouchesUnion = false`.
2. On a union root local (`isUnionLayout = true`), `truncateTyProjAtUnion` and
   `resolveBorrowWriteLocalProj` truncate `.field writeIdx writeTy :: rest` to
   `.nil`, so writing one union field disables active/frozen borrows of any
   sibling union field (`.field borIdx borTy`) and faults with `.ub` when a
   sibling union field borrow carries an active function-entry protector.
-/
theorem stmt_assign_union_field_sibling_borrow_invalidation_and_protector_ub
    (s : MachineState)
    (dstLoc : Local)
    (decl : LocalDecl)
    (writeIdx borIdx : FieldIdx)
    (writeTy borTy : Ty)
    (projs rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val rootVal rootVal' : Value)
    (locals₁ locals₂ : List LocalSlot)
    (mem₁ : Memory)
    (tag protId : Nat)
    (perm : TreeBorrowPerm) :
    (placeTouchesUnion localDecls layouts { local_ := dstLoc, projection := projs } = false →
      resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc projs =
        (match resolveBorrowProjectionElems locals₁ projs with
         | .some rp => rp
         | .none => projs)) ∧
    (layouts.entries ≠ .nil →
      get? localDecls dstLoc = .some decl →
      isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = true →
      truncateTyProjAtUnion localDecls layouts decl.ty (.field writeIdx writeTy :: rest) = .nil ∧
      resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
        (.field writeIdx writeTy :: rest) = .nil) ∧
    (layouts.entries ≠ .nil →
      get? localDecls dstLoc = .some decl →
      isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = true →
      evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁ →
      get? locals₁ dstLoc = .some (.init rootVal) →
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        (ensureNestedFieldShells rootVal (.field writeIdx writeTy :: .nil))
        (.field writeIdx writeTy :: .nil) val = .ok rootVal' →
      set? locals₁ dstLoc (.init rootVal') = .some locals₂ →
      (perm = .active ∨ perm = .frozen) →
      (let sibEntry : BorrowEntry :=
         { tag := tag, targetLocal := dstLoc,
           targetProjection := .field borIdx borTy :: .nil, perm := perm }
       mem₁.borrows = sibEntry :: .nil →
       mem₁.activeProtectors = .nil →
       evalStmt s ⟨.assign ⟨dstLoc, .field writeIdx writeTy :: .nil⟩ rv, span⟩
           localDecls layouts =
         MirStepNode.step
           (advanceStmt s locals₂
             { mem₁ with borrows := { sibEntry with perm := .disabled } :: .nil })) ∧
      (let protEntry : BorrowEntry :=
         { tag := tag, targetLocal := dstLoc,
           targetProjection := .field borIdx borTy :: .nil, perm := perm,
           protector := .some protId }
       mem₁.borrows = protEntry :: .nil →
       mem₁.activeProtectors = protId :: .nil →
       evalStmt s ⟨.assign ⟨dstLoc, .field writeIdx writeTy :: .nil⟩ rv, span⟩
           localDecls layouts =
         MirStepNode.fail .ub)) := by
  refine ⟨resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc projs,
    fun hEntries hDecl hUnion =>
      ⟨by unfold truncateTyProjAtUnion; dsimp only; rw [hUnion],
       resolveBorrowWriteLocalProj_union_root localDecls layouts locals₁ dstLoc decl
         writeIdx writeTy rest hEntries hDecl hUnion⟩,
    fun hEntries hDecl hUnion hRv hInit hWrite hSet hPerm =>
      evalStmt_assign_union_field_sibling_borrow_invalidation_and_protector_ub
        s dstLoc decl writeIdx borIdx writeTy borTy rv span localDecls layouts
        val rootVal rootVal' locals₁ locals₂ mem₁ tag protId perm
        hEntries hDecl hUnion hRv hInit hWrite hSet hPerm⟩

end UninitAggregateFieldWrites

end Correspondence.V2026_06_01.L5_ControlAndCalls
