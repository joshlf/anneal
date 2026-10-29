-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal

namespace AnnealTests

/-- Captured `MirBody` for `pub fn id(x: usize) -> usize { x }` defined using
    only `Trusted.*` constructors (`ci.type` origin-clean). -/
def idBody : Trusted.MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `pub fn id(x: usize) -> usize { x }` with
    postcondition `Trusted.EnsuresEqArg 1` (`ret == x`). -/
def idCrate : Trusted.Crate where
  functions := [
    { name := "id"
      prog := idBody
      specs := [Trusted.EnsuresEqArg 1] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "id" idBody]

/-- Top-level `Trusted.CrateTheorem` for `idCrate`, whose statement (`ci.type`)
    references only `Trusted` and locked foundation constants while its proof
    term (`ci.value?`) discharges the obligation via
    `Anneal.prove_id_copy_ensures_crate` in `theory/`. -/
theorem verify_id_crate : Trusted.CrateTheorem idCrate :=
  Anneal.prove_id_copy_ensures_crate "id"

/-- Captured `MirBody` for
    `pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed)
    }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def loadRelaxedBody : Trusted.MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.ordering .relaxed)))]
      terminator := .callAtomicLoad ⟨0⟩ (.copy ⟨1⟩) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `load_relaxed` with weak-memory postcondition
    `Trusted.EnsuresAtomicLoad 1`. -/
def loadRelaxedCrate : Trusted.Crate where
  functions := [
    { name := "load_relaxed"
      prog := loadRelaxedBody
      specs := [Trusted.EnsuresAtomicLoad 1] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "load_relaxed" loadRelaxedBody]

/-- Top-level `Trusted.CrateTheorem` for `loadRelaxedCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via
    `Anneal.prove_load_relaxed_ensures_crate` in `theory/`. -/
theorem verify_load_relaxed_crate : Trusted.CrateTheorem loadRelaxedCrate :=
  Anneal.prove_load_relaxed_ensures_crate "load_relaxed"

/-- Captured `MirBody` for
    `pub fn max_assign(x: &mut usize, y: usize) -> usize { if *x < y { *x = y; }
    *x }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def maxAssignBody : Trusted.MirBody where
  argTys := [.refMutUsize, .usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨2⟩)]
      terminator := .goto ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨1⟩)]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `max_assign` with postcondition
    `Trusted.EnsuresMaxAssign`. -/
def maxAssignCrate : Trusted.Crate where
  functions := [
    { name := "max_assign"
      prog := maxAssignBody
      specs := [Trusted.EnsuresMaxAssign] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "max_assign" maxAssignBody]

/-- Top-level `Trusted.CrateTheorem` for `maxAssignCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_max_assign_ensures_crate`). -/
theorem verify_max_assign_crate : Trusted.CrateTheorem maxAssignCrate :=
  Anneal.prove_max_assign_ensures_crate "max_assign"

/-- Captured `MirBody` for
    `pub fn update_min(x: &mut usize, y: &mut usize, v: usize) -> usize { let r
    = if *x <= *y { &mut *x } else { &mut *y }; *r = v; *x }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def updateMinBody : Trusted.MirBody where
  argTys := [.refMutUsize, .refMutUsize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨1⟩),
        .assign ⟨7⟩ (.deref ⟨2⟩),
        .assign ⟨5⟩ (.binaryOp .le (.move ⟨6⟩) (.move ⟨7⟩))
      ]
      terminator := .switchInt (.move ⟨5⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨1⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨4⟩ (.copy ⟨3⟩),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `update_min` with postcondition
    `Trusted.EnsuresUpdateMin`. -/
def updateMinCrate : Trusted.Crate where
  functions := [
    { name := "update_min"
      prog := updateMinBody
      specs := [Trusted.EnsuresUpdateMin] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "update_min" updateMinBody]

/-- Top-level `Trusted.CrateTheorem` for `updateMinCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_update_min_ensures_crate`). -/
theorem verify_update_min_crate : Trusted.CrateTheorem updateMinCrate :=
  Anneal.prove_update_min_ensures_crate "update_min"

/-- Captured `MirBody` for
    `pub fn clamp_assign(x: &mut usize, lo: usize, hi: usize) -> usize { if *x <
    lo { *x = lo; } else if *x > hi { *x = hi; } *x }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def clampAssignBody : Trusted.MirBody where
  argTys := [.refMutUsize, .usize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨5⟩ (.deref ⟨1⟩),
        .assign ⟨4⟩ (.binaryOp .lt (.move ⟨5⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨2⟩)]
      terminator := .goto ⟨4⟩ },
    { stmts := [
        .assign ⟨7⟩ (.deref ⟨1⟩),
        .assign ⟨6⟩ (.binaryOp .gt (.move ⟨7⟩) (.copy ⟨3⟩))
      ]
      terminator := .switchInt (.move ⟨6⟩) ⟨4⟩ ⟨3⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨3⟩)]
      terminator := .goto ⟨4⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨1⟩)]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `clamp_assign` with postcondition
    `Trusted.EnsuresClampAssign`. -/
def clampAssignCrate : Trusted.Crate where
  functions := [
    { name := "clamp_assign"
      prog := clampAssignBody
      specs := [Trusted.EnsuresClampAssign] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "clamp_assign" clampAssignBody]

/-- Top-level `Trusted.CrateTheorem` for `clampAssignCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_clamp_assign_ensures_crate`). -/
theorem verify_clamp_assign_crate : Trusted.CrateTheorem clampAssignCrate :=
  Anneal.prove_clamp_assign_ensures_crate "clamp_assign"

/-- Captured `MirBody` for
    `pub fn is_aligned_mask(addr: usize, mask: usize) -> bool { (addr & mask) ==
    0 }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def isAlignedMaskBody : Trusted.MirBody where
  argTys := [.usize, .usize]
  retTy := .bool
  localCount := 4
  blocks := [
    { stmts := [
        .assign ⟨3⟩ (.binaryOp .bitAnd (.copy ⟨1⟩) (.copy ⟨2⟩)),
        .assign ⟨0⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `is_aligned_mask` with postcondition
    `Trusted.EnsuresIsAlignedMask`. -/
def isAlignedMaskCrate : Trusted.Crate where
  functions := [
    { name := "is_aligned_mask"
      prog := isAlignedMaskBody
      specs := [Trusted.EnsuresIsAlignedMask] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "is_aligned_mask" isAlignedMaskBody]

/-- Top-level `Trusted.CrateTheorem` for `isAlignedMaskCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_is_aligned_mask_ensures_crate`). -/
theorem verify_is_aligned_mask_crate : Trusted.CrateTheorem isAlignedMaskCrate :=
  Anneal.prove_is_aligned_mask_ensures_crate "is_aligned_mask"

/-- Captured `MirBody` for
    `pub fn shared_max(x: &usize, y: &usize) -> usize { let r = if *x < *y { y }
    else { x }; *r }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def sharedMaxBody : Trusted.MirBody where
  argTys := [.refSharedUsize, .refSharedUsize]
  retTy := .usize
  localCount := 7
  blocks := [
    { stmts := [
        .assign ⟨5⟩ (.deref ⟨1⟩),
        .assign ⟨6⟩ (.deref ⟨2⟩),
        .assign ⟨4⟩ (.binaryOp .lt (.move ⟨5⟩) (.move ⟨6⟩))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assign ⟨3⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨3⟩ (.use (.copy ⟨1⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨3⟩)]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `shared_max` with postcondition
    `Trusted.EnsuresSharedMax`. -/
def sharedMaxCrate : Trusted.Crate where
  functions := [
    { name := "shared_max"
      prog := sharedMaxBody
      specs := [Trusted.EnsuresSharedMax] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "shared_max" sharedMaxBody]

/-- Top-level `Trusted.CrateTheorem` for `sharedMaxCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_shared_max_ensures_crate`). -/
theorem verify_shared_max_crate : Trusted.CrateTheorem sharedMaxCrate :=
  Anneal.prove_shared_max_ensures_crate "shared_max"

/-- Captured `MirBody` for
    `pub fn max_assign_shared(dst: &mut usize, src: &usize) -> usize { if *dst <
    *src { *dst = *src; } *dst }`
    defined using only `Trusted.*` constructors (`ci.type` origin-clean). -/
def maxAssignSharedBody : Trusted.MirBody where
  argTys := [.refMutUsize, .refSharedUsize]
  retTy := .usize
  localCount := 7
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨5⟩ (.deref ⟨2⟩),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.move ⟨5⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨2⟩),
        .assignDeref ⟨1⟩ (.move ⟨6⟩)
      ]
      terminator := .goto ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨1⟩)]
      terminator := .return_ }
  ]

/-- Captured `Trusted.Crate` for `max_assign_shared` with postcondition
    `Trusted.EnsuresMaxAssignShared`. -/
def maxAssignSharedCrate : Trusted.Crate where
  functions := [
    { name := "max_assign_shared"
      prog := maxAssignSharedBody
      specs := [Trusted.EnsuresMaxAssignShared] }
  ]
  tcb := [Trusted.TCBItem.rustcLowering "max_assign_shared" maxAssignSharedBody]

/-- Top-level `Trusted.CrateTheorem` for `maxAssignSharedCrate`, whose statement
    (`ci.type`) references only `Trusted` and locked foundation constants while
    its proof term (`ci.value?`) discharges the obligation via the plan-guided
    functional translation (`Anneal.prove_max_assign_shared_ensures_crate`). -/
theorem verify_max_assign_shared_crate : Trusted.CrateTheorem maxAssignSharedCrate :=
  Anneal.prove_max_assign_shared_ensures_crate "max_assign_shared"

/-!
## Non-Step-Based Axiomatic Event-Graph Toy Language

`Trusted.Refinement` (Layer 1A) parameterizes refinement (`≤`), monotone
behavior mappings (`Trusted.Monotone`), compilation and abstraction passes
(`Trusted.Compiles`, `Trusted.Abstracts`), and the top-level verification
envelope (`Trusted.VerificationResultOn`, `Trusted.VerificationResult`) over an
arbitrary `Trusted.Language` (`Query → Partial (Out → Prop)`), without assuming
a step counter, a global machine state, or `Trusted.StepResult` (Layer 1B).

To exercise Layer 1A and `Anneal.verify_through_passes` directly on a
non-step-based semantics, this section defines an axiomatic weak-memory model
for a two-thread Message-Passing (`MP`) litmus test whose behaviors are sets of
candidate execution event graphs (`CandExec → Prop`) ordered by happens-before
(`Hb`).
-/
namespace AxiomaticMP

/-- `Event` enumerates the memory events of the two-thread Message-Passing
    (`MP`) litmus program: initialization writes (`initData`, `initFlag`),
    Thread 1's stores (`writeData`, `writeFlag`), and Thread 2's loads
    (`readFlag`, `readData`). -/
inductive Event where
  | initData
  | initFlag
  | writeData
  | writeFlag
  | readFlag
  | readData

/-- `DataWrite` identifies the candidate write sources for the `data` location
    (`0` at initialization or `42` from Thread 1's store). -/
inductive DataWrite where
  | initData
  | writeData

/-- `DataWrite.toEvent` maps a `DataWrite` source to its write event. -/
def DataWrite.toEvent : DataWrite → Event
  | .initData => .initData
  | .writeData => .writeData

/-- `DataWrite.val` returns the value written by a `DataWrite` source. -/
def DataWrite.val : DataWrite → Nat
  | .initData => 0
  | .writeData => 42

/-- `FlagWrite` identifies the candidate write sources for the `flag` location
    (`0` at initialization or `1` from Thread 1's store). -/
inductive FlagWrite where
  | initFlag
  | writeFlag

/-- `FlagWrite.val` returns the value written by a `FlagWrite` source. -/
def FlagWrite.val : FlagWrite → Nat
  | .initFlag => 0
  | .writeFlag => 1

/-- `Ordering` enumerates the memory orderings of the toy axiomatic language
    (`relaxed`, `acquire`, and `release`). -/
inductive Ordering where
  | relaxed
  | acquire
  | release

/-- `Prog` represents a two-thread Message-Passing program parameterized by the
    memory orderings on Thread 1's store to `flag` and Thread 2's load from
    `flag`. -/
structure Prog where
  ordWriteFlag : Ordering
  ordReadFlag  : Ordering

/-- `CandExec` represents a candidate execution graph by the reads-from (`rf`)
    choice for the `flag` and `data` loads, without a step counter or global
    machine state. -/
structure CandExec where
  rfFlag : FlagWrite
  rfData : DataWrite

/-- `HbStep` defines the single-edge generators of the happens-before relation
    for program `p` and candidate execution `ce`: initialization order,
    per-thread program order (`po`), and release-acquire synchronizes-with
    (`sw`) when `readFlag` reads from `writeFlag` under `.release`/`.acquire`
    orderings. -/
inductive HbStep (p : Prog) (ce : CandExec) : Event → Event → Prop where
  | initData_writeData : HbStep p ce .initData .writeData
  | initData_readData  : HbStep p ce .initData .readData
  | initFlag_writeFlag : HbStep p ce .initFlag .writeFlag
  | initFlag_readFlag  : HbStep p ce .initFlag .readFlag
  | po_writer          : HbStep p ce .writeData .writeFlag
  | po_reader          : HbStep p ce .readFlag .readData
  | sw_flag            : ce.rfFlag = .writeFlag →
                         p.ordWriteFlag = .release →
                         p.ordReadFlag = .acquire →
                         HbStep p ce .writeFlag .readFlag

/-- `Hb` is the reflexive-transitive happens-before partial order on `Event`
    for program `p` and candidate execution `ce`. -/
inductive Hb (p : Prog) (ce : CandExec) : Event → Event → Prop where
  | refl (e : Event) : Hb p ce e e
  | tail {a b c : Event} : Hb p ce a b → HbStep p ce b c → Hb p ce a c

/-- `Hb.trans` establishes transitivity of the happens-before relation
    `Hb p ce`. -/
theorem Hb.trans {p : Prog} {ce : CandExec} {a b c : Event}
    (hab : Hb p ce a b) (hbc : Hb p ce b c) : Hb p ce a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact Hb.tail ih hstep

/-- `ScopedEvent` scopes an `Event` to program `p` and candidate execution `ce`
    so that events carry a `Trusted.Preorder` instance ordered by
    happens-before (`Hb p ce`). -/
structure ScopedEvent (p : Prog) (ce : CandExec) where
  event : Event

/-- Happens-before `Hb p ce` equips `ScopedEvent p ce` with a
    `Trusted.Preorder` (`a ≤ b` iff `Hb p ce a.event b.event`). -/
instance instPreorderScopedEvent (p : Prog) (ce : CandExec) :
    Trusted.Preorder (ScopedEvent p ce) where
  le a b := Hb p ce a.event b.event
  le_refl a := Hb.refl a.event
  le_trans := Hb.trans

/-- `DataCoherent` enforces write-read coherence (`CoWR`) on `data`: if Thread
    1's overwriting store `writeData` happens-before Thread 2's load `readData`
    (`⟨.writeData⟩ ≤ ⟨.readData⟩` in `ScopedEvent p ce`), then `readData`
    cannot read the overwritten initialization write `initData`. -/
def DataCoherent (p : Prog) (ce : CandExec) : Prop :=
  ce.rfData = .initData → ¬ ((⟨.writeData⟩ : ScopedEvent p ce) ≤ ⟨.readData⟩)

/-- `NoDataRace` enforces happens-before race freedom on the non-atomic `data`
    location when Thread 2 enters the `flag == 1` branch (`ce.rfFlag =
    .writeFlag`):
    Thread 1's store `writeData` and Thread 2's load `readData` must be ordered
    by happens-before (`⟨.writeData⟩ ≤ ⟨.readData⟩` in `ScopedEvent p ce`). -/
def NoDataRace (p : Prog) : Prop :=
  ∀ ce : CandExec,
    ce.rfFlag = .writeFlag →
    ((⟨.writeData⟩ : ScopedEvent p ce) ≤ ⟨.readData⟩)

/-- `AxiomaticSem` defines the non-step-based axiomatic semantics of `Prog` as
    a partial behavior over candidate execution event graphs:
    - `defined`: `NoDataRace p` (absence of data races on non-atomic `data`),
    - `val`: `DataCoherent p` (write-read coherence on `data`). -/
def AxiomaticSem (p : Prog) : Unit → Trusted.Partial (CandExec → Prop) :=
  fun _ => {
    defined := NoDataRace p
    val := fun _ => DataCoherent p
  }

/-- `SummarySem` defines the normalized synchronization-summary semantics used
    by the verifier pass:
    - `defined`: `flag` uses `.release`/`.acquire` synchronization,
    - `val`: observing `rfFlag = .writeFlag` directly implies
      `rfData = .writeData`. -/
def SummarySem (p : Prog) : Unit → Trusted.Partial (CandExec → Prop) :=
  fun _ => {
    defined := p.ordWriteFlag = .release ∧ p.ordReadFlag = .acquire
    val := fun _ ce =>
      (p.ordWriteFlag = .release ∧ p.ordReadFlag = .acquire ∧ ce.rfFlag = .writeFlag) →
        ce.rfData = .writeData
  }

/-- `MpSpec` is the Message-Passing specification: the program is race-free
    (`defined := True`), and whenever Thread 2's load of `flag` observes `1`,
    its subsequent load of `data` observes `42`. -/
def MpSpec : Unit → Trusted.Partial (CandExec → Prop) :=
  fun _ => Trusted.Partial.pure (fun ce => ce.rfFlag.val = 1 → ce.rfData.val = 42)

/-- `mpAcqRelProg` instantiates `Prog` with a `.release` store and an
    `.acquire` load on `flag`. -/
def mpAcqRelProg : Prog where
  ordWriteFlag := .release
  ordReadFlag  := .acquire

/-- `mpRelaxedProg` instantiates `Prog` with a `.relaxed` store and a
    `.relaxed` load on `flag`. -/
def mpRelaxedProg : Prog where
  ordWriteFlag := .relaxed
  ordReadFlag  := .relaxed

/-- `ArchProg` pairs a lowered source `Prog` with an architectural
    release/acquire instruction-selection flag. -/
structure ArchProg where
  src : Prog
  usesStlrLdar : Bool

/-- `ArchExec` pairs a source `CandExec` with an architectural
    barrier-observation witness. -/
structure ArchExec where
  base : CandExec
  barriersObserved : Bool

/-- `ArchSem` defines the lowered target semantics (`Unit → Trusted.Partial
    (ArchExec → Prop)`). -/
def ArchSem (ap : ArchProg) : Unit → Trusted.Partial (ArchExec → Prop) :=
  fun _ => {
    defined := NoDataRace ap.src
    val := fun _ ae => DataCoherent ap.src ae.base ∧ ae.barriersObserved = ap.usesStlrLdar
  }

/-- `π_arch` maps source partial candidate-execution behaviors to target
    partial candidate-execution behaviors via `Trusted.Partial.map`. -/
def π_arch (b : Unit → Trusted.Partial (CandExec → Prop)) :
    Unit → Trusted.Partial (ArchExec → Prop) :=
  fun q => Trusted.Partial.map (fun pred ae => pred ae.base) (b q)

/-- `π_arch` is monotone with respect to `Trusted.Preorder` (`≤`). -/
theorem monotone_π_arch : Trusted.Monotone π_arch :=
  fun _ _ hb q =>
    Anneal.Partial.monotone_map (by intro _ _ hsub ae hae; exact hsub ae.base hae) (hb q)

/-- `mpArchProg` is the target program lowered from `mpAcqRelProg`. -/
def mpArchProg : ArchProg where
  src := mpAcqRelProg
  usesStlrLdar := true

/-- In `mpAcqRelProg`, reading `rfFlag = .writeFlag` induces a happens-before
    chain `.writeData → .writeFlag → .readFlag → .readData`. -/
theorem hb_writeData_readData_of_acqRel {ce : CandExec}
    (hrf : ce.rfFlag = .writeFlag) :
    Hb mpAcqRelProg ce .writeData .readData := by
  have h1 : Hb mpAcqRelProg ce .writeData .writeFlag :=
    Hb.tail (Hb.refl .writeData) HbStep.po_writer
  have h2 : Hb mpAcqRelProg ce .writeData .readFlag :=
    Hb.tail h1 (HbStep.sw_flag hrf rfl rfl)
  exact Hb.tail h2 HbStep.po_reader

/-- Every happens-before-coherent execution of `mpAcqRelProg` refines its
    synchronization summary `SummarySem mpAcqRelProg`. -/
theorem axiomatic_refines_summary_acqRel :
    AxiomaticSem mpAcqRelProg ≤ SummarySem mpAcqRelProg := by
  intro _ _
  refine ⟨fun _ hrf => hb_writeData_readData_of_acqRel hrf, ?_⟩
  intro ce hcoh ⟨_, _, hrf⟩
  cases hdata : ce.rfData with
  | writeData => rfl
  | initData =>
    exfalso
    exact hcoh hdata (hb_writeData_readData_of_acqRel hrf)

/-- The synchronization summary of `mpAcqRelProg` refines `MpSpec`. -/
theorem summary_acqRel_refines_mpSpec :
    SummarySem mpAcqRelProg ≤ MpSpec := by
  intro _ _
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro ce hsum hflag
  cases hrf : ce.rfFlag with
  | initFlag =>
    rw [hrf] at hflag
    contradiction
  | writeFlag =>
    have hdata : ce.rfData = .writeData := hsum ⟨rfl, rfl, hrf⟩
    rw [hdata]
    rfl

/-- `AxiomaticLang` packages `AxiomaticSem` as a `Trusted.Language`. -/
def AxiomaticLang : Trusted.Language where
  Prog := Prog
  Query := Unit
  Out := CandExec
  sem := AxiomaticSem

/-- `SummaryLang` packages `SummarySem` as a verifier `Trusted.Language`. -/
def SummaryLang : Trusted.Language where
  Prog := Prog
  Query := Unit
  Out := CandExec
  sem := SummarySem

/-- `ArchLang` packages `ArchSem` as a target `Trusted.Language`. -/
def ArchLang : Trusted.Language where
  Prog := ArchProg
  Query := Unit
  Out := ArchExec
  sem := ArchSem

/-- `ArchCompiler` lowers `AxiomaticLang` programs to `ArchLang` under
    `π_arch`. -/
def ArchCompiler : Trusted.Compiler AxiomaticLang ArchLang where
  compile p := { src := p, usesStlrLdar := true }
  π := π_arch

/-- `ArchAssumption` enumerates the TCB assumptions for `AxiomaticMP`. -/
inductive ArchAssumption where
  | archLowering (p : Prog)

instance instTrustedAssumptionArch : Trusted.TrustedAssumption ArchAssumption where
  meaning
    | .archLowering p => ArchCompiler.SoundOn p

/-- `archTrustPolicy` permits `ArchAssumption.archLowering`. -/
def archTrustPolicy : Trusted.TrustPolicy ArchAssumption where
  isAllowed
    | .archLowering _ => True

/-- `verify_axiomatic_mp_claim` discharges the end-to-end
    `Trusted.VerificationResult` claim for the non-step-based axiomatic
    language via `Anneal.verify_through_passes` and
    `Anneal.Compiler.Verified.with_wellFormedOn` across a verifier abstraction
    pass (`SummaryLang` to `AxiomaticLang`) and a target compiler
    (`ArchCompiler`). -/
theorem verify_axiomatic_mp_claim :
    Trusted.VerificationResult
      ArchCompiler
      archTrustPolicy
      []
      mpAcqRelProg
      [MpSpec] := by
  refine ⟨True.intro, fun _ => ?_⟩
  have hcomp : ArchCompiler.SoundOn mpAcqRelProg :=
    ⟨monotone_π_arch, fun _ hdef => ⟨hdef, fun _ hsem => hsem.1⟩⟩
  have hver_spec : ArchCompiler.Verified mpAcqRelProg MpSpec :=
    Anneal.verify_through_passes
      (L_v := SummaryLang)
      (C := ArchCompiler)
      (π_v := fun b => b)
      (spec := MpSpec)
      (v := mpAcqRelProg)
      (s := mpAcqRelProg)
      summary_acqRel_refines_mpSpec
      axiomatic_refines_summary_acqRel
      Anneal.monotone_id
      hcomp
  exact Anneal.Compiler.Verified.with_wellFormedOn
    hver_spec
    (Anneal.pure_le_wellFormed (L := AxiomaticLang) _)
    monotone_π_arch

/-- `isWriterEvent` returns `true` for events belonging to Thread 1 (the writer
    thread). -/
def isWriterEvent : Event → Bool
  | .writeData | .writeFlag => true
  | _ => false

/-- Under `mpRelaxedProg`, no single happens-before step leaves Thread 1,
    because `.relaxed` operations do not induce a `sw_flag` edge. -/
theorem relaxed_hbStep_preserves_writer {ce : CandExec} {a b : Event}
    (hstep : HbStep mpRelaxedProg ce a b) (ha : isWriterEvent a = true) :
    isWriterEvent b = true := by
  cases hstep with
  | po_writer => rfl
  | sw_flag _ hrel _ => cases hrel
  | initData_writeData | initData_readData | initFlag_writeFlag | initFlag_readFlag | po_reader =>
    cases ha

/-- Under `mpRelaxedProg`, any event reachable from a Thread 1 event in the
    `Hb` partial order remains in Thread 1. -/
theorem relaxed_hb_preserves_writer {ce : CandExec} {a b : Event}
    (hhb : Hb mpRelaxedProg ce a b) (ha : isWriterEvent a = true) :
    isWriterEvent b = true := by
  induction hhb with
  | refl => exact ha
  | tail _ hstep ih => exact relaxed_hbStep_preserves_writer hstep ih

/-- `staleCandidate` is the candidate execution in which Thread 2 observes the
    updated `flag = 1` (`writeFlag`) together with the stale initial `data = 0`
    (`initData`). -/
def staleCandidate : CandExec where
  rfFlag := .writeFlag
  rfData := .initData

/-- Under `mpRelaxedProg`, `writeData` and `readData` are incomparable in the
    happens-before partial order `Hb`, causing a data race (`defined = False`)
    on `staleCandidate` and refuting `AxiomaticLang.WellFormed`. -/
theorem axiomatic_mp_relaxed_not_wellFormed :
    ¬ (AxiomaticLang.sem mpRelaxedProg ≤ AxiomaticLang.WellFormed) := by
  intro hwf
  have hdef := (Anneal.le_wellFormed_iff (L := AxiomaticLang) _).mp hwf ()
  have hhb : Hb mpRelaxedProg staleCandidate .writeData .readData :=
    hdef staleCandidate rfl
  have hwriter := relaxed_hb_preserves_writer hhb rfl
  contradiction

/-- Because `mpRelaxedProg` exhibits a data race (`defined = False`), it also
    refutes refinement of `MpSpec`. -/
theorem axiomatic_mp_relaxed_not_refines_spec :
    ¬ (AxiomaticLang.sem mpRelaxedProg ≤ MpSpec) := by
  intro href
  exact axiomatic_mp_relaxed_not_wellFormed
    (Trusted.Preorder.le_trans href (Anneal.pure_le_wellFormed (L := AxiomaticLang) _))

end AxiomaticMP

end AnnealTests
