/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.ExtTreeMapAllocAndNoWritable
import LeanMiriSpec.Correspondence.PtrLM3_1
import LeanMiriSpec.Correspondence.RefLM3_2
import LeanMiriSpec.Correspondence.TreeBorrowsRel

/-!
# Keyed allocation maps, `FnEntry` retags, and safe-pointer / vtable validity against `lean-miri`

Kernel-checked correspondence between the `Classical.choice`-free theory
`Anneal.ExtTreeMapAllocAndNoWritable` (`MiriAllocId`, `KeyedAllocWorld`,
`LinearAllocWorld`, `AllocWorldRel`, `checkPtrAccess`, `selectFnEntryPolicy`,
`MiriRetagPolicyMirror`, the borrow-tree traversal schedule,
`protectorEndAccessIsWrite?`, `vtableMatchesExpectedSpec`) and the vendored
`lean-miri` model under `lean-miri/vendor/Miri`. Every correspondence theorem
about a vendored operation mentions the vendored definition itself
(`Miri.Memory.checkPtrAccess`, `RetagPolicy.create`, `TraversalTree.traverse`,
`Permission.associatedAccess`, `classifyPointerAccessError`,
`VTable.checkForTypeRead`). Two objects are RESTATEMENTS whose link to their
originals cannot be stated under the axiom budget below: `MiriAllocRows` (the
row-level content of `Miri.Memory.MemoryState`) and `resolveWithBase` (the body
of `annealResolvePtr` with the machine's base-address table as a parameter).

## Axiom budget, and what it excludes

Every declaration of this module (theorems, definitions, and the
name-resolution macro) depends on at most `propext` and `Quot.sound`: no
`Classical.choice`, no `sorryAx`, no `Lean.ofReduceBool`. Part 4 pins this for
each public theorem with `#guard_msgs in #print axioms`.

That budget excludes part of the vendored model BY STATEMENT, independently of
any proof. The vendored `Miri.Memory.MemoryState` TYPE depends on
`Classical.choice`: its issued-ID and global tables are
`Miri.Memory.KeyedArray`s indexed by `Std.HashMap`, and `Std.HashMap` itself
depends on `Classical.choice` in the pinned toolchain. Every constant that
mentions `MemoryState` inherits the dependency, so NO theorem of this module
can mention any of:

* `Miri.Memory.MemoryState.{reserveAllocId, isAllocLive, getAllocInfo,
  getLiveAllocSizeAndAlign}`, `Miri.Memory.MemoryLifecycle.{insertAllocation,
  allocatePtr, deallocatePtrWith}`, `Miri.Interpreter.AllocationMachine`;
* `StateRelLM3_1`, `StateRelLM3_2`, `AllocMapRel` (they quantify over the
  machine state, which contains `MemoryState`);
* `Miri.Interpreter.ValidityMachine` (`scalarMayBeNull`,
  `checkPointerAccessResult`), `ValidityVisitor.validatePlace`,
  `annealValidityHooks`;
* `Miri.TreeBorrows.BorrowTree.releaseProtector`.

Part 4 pins that obstruction (`#print axioms` on those vendored constants); the
pins fail, signalling that the bridge can be stated, as soon as the vendored
definitions stop depending on `Classical.choice`. Until then the lifecycle
operations (`reserve`, `allocate`, `deallocate` with its failure ordering and
race-detector hook), the `StateRelLM3_1` / `StateRelLM3_2` lifting, the
machine-level validity visitor, and `releaseProtector` are NOT covered by this
module.

## What is proved (on the choice-free vendored surface)

* **Part 1A** — `Miri.Memory.AllocId` and `MiriAllocId` are in exact
  full-width bijection (`allocId_bijection`), compatible with both `ofUInt64`
  constructors, `==`, the keyed-map order, and `toTrustedAllocId`.
* **Part 1B** — translations of memory kinds, global kinds, mutability,
  `AllocationKind`, `AllocationInfo`, and the vendored error vocabularies
  (`AllocationIdError`, `MemoryMetadataError`, `MemoryLifecycleError`).
* **Part 1C** — the row-level observation surface of the vendored memory state
  (`MiriAllocRows`: cursor, exhaustion latch, issued / global / `live` / `dead`
  rows in the vendored row types) projects to `LinearAllocWorld` and
  `KeyedAllocWorld`; the keyed lookups are first-match row lookups by ID, as
  in the vendored code (`toKeyed_findLive?`, `toKeyed_getAllocInfo`,
  `toKeyed_isAllocLive`), and the
  projection is PERMUTATION INVARIANT (`rows_toKeyed_eq_of_perm`,
  `keyedRowsRel_perm_invariant`). The byte payload and the classification of
  machine memory kinds are parameters (`RowProjection`); race clocks are not
  part of the rows.
* **Part 1D** — the vendored `Miri.Memory.{sizeAsI64, checkAndDerefPtr,
  checkPtrAccess, getPtrAccess}` against a keyed world, with the exact source
  failure order (`keyedAccessOutcome`, `checkPtrAccess_keyed_eq`), the theory
  verdict (`checkPtrAccess_isOk_eq_keyed`, `checkPtrAccess_isOk_eq_linear`),
  and the `PtrRel` instance (`ptrRel_checkPtrAccess_isOk_eq_keyed`).
* **Part 1E** — `MiriRetagPolicyMirror.create` IS the vendored
  `RetagPolicy.create` on every input (`mirror_create_eq_miri_create`,
  `selectFnEntryPolicy_eq_miri_create`); `protectorEndAccessIsWrite?` is the
  vendored `Permission.associatedAccess` gated by `accessed`; the vendored
  `TraversalTree.traverse` emits exactly the theory's foreign schedule
  (`miri_traverse_eq_schedule`), and the ancestor paths agree on rooted
  dense-tag trees (`ancestorPathTags_eq_miri_ancestorPath`).
* **Part 2** — the access stage of the vendored safe-pointer check
  (`classifyPointerAccessError_isUB`, including the size-gate failure-class
  separation `sizeGate_failure_class_separation`), and the vendored
  `VTable.checkForTypeRead` on auto-trait-only existentials
  (`miri_checkForTypeRead_autoOnly_ok`).
* **Part 3** — closed (hypothesis-free) canaries evaluating the vendored
  definitions on concrete inputs, positive and negative.

## Further limits of this module

* The theory's fuel for the foreign postorder is `nodes.length + 1`; the
  vendored one is `nodes.size`. `miri_traverse_eq_schedule` is stated at the
  vendored fuel; the equality of the two schedules on rooted trees is not
  proved here.
* The `[T; N]` syntactic `Sized` fast path, `validateSafeThinRef` beyond its
  access stage, the wide-`dyn` validators, and the recursive value visitor are
  not connected to `ValidityVisitor.checkSafe` / `visit` here.
* `VTable.checkForTypeRead` and `vtableMatchesExpectedSpec` are related only on
  auto-trait-only existentials and on the Part 3 canaries; they differ in
  general when distinct predicates share a stable key.
-/

namespace LeanMiriSpec.ExtTreeMapAllocLM

open Anneal.ExtTreeMapAllocAndNoWritable
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## Part 0. Vendored private helpers -/

open Lean in
/-- `miri_etm_private% M D` expands to the identifier of the declaration `D`
that the vendored module `M` declares `private` (name resolution only: no
axioms, no new definitions, and no elaborator: a plain syntax macro). -/
macro "miri_etm_private% " mod:ident decl:ident : term =>
  pure (mkIdent (mkPrivateNameCore mod.getId.eraseMacroScopes decl.getId.eraseMacroScopes))

/-! ## Part 1A. `Miri.Memory.AllocId` and `MiriAllocId` -/

/-- Vendored `Miri.Memory.AllocId` (`NonZeroU64`) as the theory `MiriAllocId`. -/
def ofMiriAllocId (id : Miri.Memory.AllocId) : MiriAllocId := ⟨id.value, id.nonzero⟩

/-- Theory `MiriAllocId` as the vendored `Miri.Memory.AllocId`. -/
def toMiriAllocId (id : MiriAllocId) : Miri.Memory.AllocId := ⟨id.value, id.nonzero⟩

theorem ofMiriAllocId_value (id : Miri.Memory.AllocId) : (ofMiriAllocId id).value = id.value := rfl

theorem toMiriAllocId_value (id : MiriAllocId) : (toMiriAllocId id).value = id.value := rfl

theorem ofMiriAllocId_toMiriAllocId (id : MiriAllocId) :
    ofMiriAllocId (toMiriAllocId id) = id := rfl

theorem toMiriAllocId_ofMiriAllocId (id : Miri.Memory.AllocId) :
    toMiriAllocId (ofMiriAllocId id) = id := rfl

theorem ofMiriAllocId_injective : Function.Injective ofMiriAllocId := by
  intro a b h
  have h' := congrArg toMiriAllocId h
  exact h'

theorem toMiriAllocId_injective : Function.Injective toMiriAllocId := by
  intro a b h
  have h' := congrArg ofMiriAllocId h
  exact h'

/-- The two identifier types are in exact full-width bijection: the maps are
mutually inverse, preserve the raw `UInt64`, and the raw value is never `0`. -/
theorem allocId_bijection :
    (∀ id : MiriAllocId, ofMiriAllocId (toMiriAllocId id) = id) ∧
    (∀ id : Miri.Memory.AllocId, toMiriAllocId (ofMiriAllocId id) = id) ∧
    (∀ id : Miri.Memory.AllocId, (ofMiriAllocId id).value = id.value ∧ id.value ≠ 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun id => ⟨rfl, id.nonzero⟩⟩

/-- Both `ofUInt64` constructors reject exactly the reserved `0` and agree on
every other raw value. -/
theorem allocId_ofUInt64_comm (v : UInt64) :
    (Miri.Memory.AllocId.ofUInt64 v).map ofMiriAllocId = MiriAllocId.ofUInt64 v := by
  unfold Miri.Memory.AllocId.ofUInt64 MiriAllocId.ofUInt64
  split
  · rename_i h
    split
    · rename_i h'
      exact absurd h h'
    · rfl
  · rfl

theorem miriAllocId_ofUInt64_comm (v : UInt64) :
    (MiriAllocId.ofUInt64 v).map toMiriAllocId = Miri.Memory.AllocId.ofUInt64 v := by
  rw [← allocId_ofUInt64_comm]
  cases Miri.Memory.AllocId.ofUInt64 v <;> rfl

/-- Composition with `MiriAllocId.toTrustedAllocId`: the trusted `Nat`
allocation identifier is the raw `UInt64` value. -/
theorem toTrustedAllocId_ofMiriAllocId (id : Miri.Memory.AllocId) :
    (ofMiriAllocId id).toTrustedAllocId = id.value.toNat := rfl

theorem toTrustedAllocId_ofMiriAllocId_pos (id : Miri.Memory.AllocId) :
    0 < (ofMiriAllocId id).toTrustedAllocId :=
  MiriAllocId.toTrustedAllocId_pos _

theorem toTrustedAllocId_ofMiriAllocId_injective :
    Function.Injective (fun id : Miri.Memory.AllocId => (ofMiriAllocId id).toTrustedAllocId) := by
  intro a b h
  exact ofMiriAllocId_injective (MiriAllocId.toTrustedAllocId_injective h)

theorem ofMiriAllocId_beq (a b : Miri.Memory.AllocId) :
    (ofMiriAllocId a == ofMiriAllocId b) = (a == b) := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, beq_self_eq_true]
  · have h' : ofMiriAllocId a ≠ ofMiriAllocId b := fun he => h (ofMiriAllocId_injective he)
    rw [beq_false_of_ne h, beq_false_of_ne h']

theorem toMiriAllocId_beq (a b : MiriAllocId) :
    (toMiriAllocId a == toMiriAllocId b) = (a == b) := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, beq_self_eq_true]
  · have h' : toMiriAllocId a ≠ toMiriAllocId b := fun he => h (toMiriAllocId_injective he)
    rw [beq_false_of_ne h, beq_false_of_ne h']

/-- The keyed-map order on `MiriAllocId` is the numeric order of the vendored
raw identifier. -/
theorem compare_ofMiriAllocId (a b : Miri.Memory.AllocId) :
    compare (ofMiriAllocId a) (ofMiriAllocId b) = compare a.value.toNat b.value.toNat := rfl

/-! ## Part 1B. Kind, mutability, metadata, and error translations -/

/-- Vendored `Miri.Memory.MemoryKind` as the theory `AllocMemKind`; the
machine-specific kinds are classified by `machineKind`. -/
def memKindOfMiri {K : Type} (machineKind : K → AllocMemKind) :
    Miri.Memory.MemoryKind K → AllocMemKind
  | .stack => .stack
  | .callerLocation => .callerLocation
  | .machine k => machineKind k

def globalKindOfMiri : Miri.Memory.GlobalAllocationKind → GlobalAllocKind
  | .function => .function
  | .vtable => .vtable
  | .typeId => .typeId
  | .static => .static
  | .memory => .memory

def globalKindToMiri : GlobalAllocKind → Miri.Memory.GlobalAllocationKind
  | .function => .function
  | .vtable => .vtable
  | .typeId => .typeId
  | .static => .static
  | .memory => .memory

theorem globalKindOfMiri_toMiri (k : GlobalAllocKind) :
    globalKindOfMiri (globalKindToMiri k) = k := by
  cases k <;> rfl

theorem globalKindToMiri_ofMiri (k : Miri.Memory.GlobalAllocationKind) :
    globalKindToMiri (globalKindOfMiri k) = k := by
  cases k <;> rfl

def mutabilityOfMiri : Miri.Memory.Mutability → AllocMutability
  | .Not => .not
  | .Mut => .mut

def mutabilityToMiri : AllocMutability → Miri.Memory.Mutability
  | .not => .Not
  | .mut => .Mut

theorem mutabilityOfMiri_toMiri (m : AllocMutability) :
    mutabilityOfMiri (mutabilityToMiri m) = m := by
  cases m <;> rfl

theorem mutabilityToMiri_ofMiri (m : Miri.Memory.Mutability) :
    mutabilityToMiri (mutabilityOfMiri m) = m := by
  cases m <;> rfl

/-- Theory `AllocInfoKind` as vendored `Miri.Memory.AllocationKind`. -/
def infoKindToMiri : AllocInfoKind → Miri.Memory.AllocationKind
  | .liveData => .liveData
  | .function => .function
  | .vtable => .vtable
  | .typeId => .typeId
  | .dead => .dead

/-- Vendored `AllocationKind` as theory `AllocInfoKind`; the va-list kind is
outside the theory (`none`). -/
def infoKindOfMiri : Miri.Memory.AllocationKind → Option AllocInfoKind
  | .liveData => some .liveData
  | .function => some .function
  | .vaList => none
  | .vtable => some .vtable
  | .typeId => some .typeId
  | .dead => some .dead

theorem infoKindOfMiri_toMiri (k : AllocInfoKind) :
    infoKindOfMiri (infoKindToMiri k) = some k := by
  cases k <;> rfl

theorem infoKindOfMiri_eq_none_iff (k : Miri.Memory.AllocationKind) :
    infoKindOfMiri k = none ↔ k = .vaList := by
  cases k <;> simp [infoKindOfMiri]

theorem infoKindToMiri_beq_dead (k : AllocInfoKind) :
    (infoKindToMiri k == Miri.Memory.AllocationKind.dead) = (k == AllocInfoKind.dead) := by
  cases k <;> rfl

/-- Theory `AllocInfo` in the vendored `Miri.Memory.AllocationInfo` shape
returned by `get_alloc_info`. -/
def allocInfoToMiri (info : AllocInfo) : Miri.Memory.AllocationInfo :=
  ⟨Miri.ABI.Size.ofBytes info.sizeBytes, ⟨info.alignPow2.toNat⟩,
    infoKindToMiri info.kind, mutabilityToMiri info.mutability⟩

def allocIdErrOfMiri : Miri.Memory.AllocationIdError → AllocIdErr
  | .exhausted => .exhausted
  | .alreadyIssued id => .alreadyIssued (ofMiriAllocId id)

def allocIdErrToMiri : AllocIdErr → Miri.Memory.AllocationIdError
  | .exhausted => .exhausted
  | .alreadyIssued id => .alreadyIssued (toMiriAllocId id)

theorem allocIdErrOfMiri_toMiri (e : AllocIdErr) : allocIdErrOfMiri (allocIdErrToMiri e) = e := by
  cases e <;> rfl

theorem allocIdErrToMiri_ofMiri (e : Miri.Memory.AllocationIdError) :
    allocIdErrToMiri (allocIdErrOfMiri e) = e := by
  cases e <;> rfl

/-- Vendored global-registration failures; the export-ID failures have no
theory counterpart (export-ID tables are not modeled). -/
def globalRegErrOfMiri : Miri.Memory.MemoryMetadataError → Option GlobalRegErr
  | .duplicateRuntimeId id => some (.duplicateRuntimeId (ofMiriAllocId id))
  | .globalIdAlreadyPresent id => some (.globalIdAlreadyPresent (ofMiriAllocId id))
  | .duplicateExportId _ => none
  | .missingExportId _ => none

def globalRegErrToMiri : GlobalRegErr → Miri.Memory.MemoryMetadataError
  | .duplicateRuntimeId id => .duplicateRuntimeId (toMiriAllocId id)
  | .globalIdAlreadyPresent id => .globalIdAlreadyPresent (toMiriAllocId id)

theorem globalRegErrOfMiri_toMiri (e : GlobalRegErr) :
    globalRegErrOfMiri (globalRegErrToMiri e) = some e := by
  cases e <;> rfl

/-- Theory deallocation failures in the vendored
`Miri.Memory.MemoryLifecycleError` vocabulary of `deallocate_ptr`. -/
def deallocErrToMiri : DeallocErr → Miri.Memory.MemoryLifecycleError
  | .danglingPointer addr => .danglingPointer addr
  | .nonzeroOffset id off =>
    .nonzeroAllocationOffset "deallocate" (toMiriAllocId id) (Miri.ABI.Size.ofBytes off)
  | .globalErr id kind => .globalAllocationDeallocation (toMiriAllocId id) (globalKindToMiri kind)
  | .useAfterFree id => .useAfterFree (toMiriAllocId id)
  | .immutableAllocation id => .immutableAllocation (toMiriAllocId id)
  | .memoryKindMismatch id => .memoryKindMismatch (toMiriAllocId id)
  | .layoutMismatch id actualSize requestedSize actualAlign requestedAlign =>
    .layoutMismatch (toMiriAllocId id) (Miri.ABI.Size.ofBytes actualSize)
      (Miri.ABI.Size.ofBytes requestedSize) ⟨actualAlign.toNat⟩ ⟨requestedAlign.toNat⟩
  | .hookFailure reason => .hookFailure "beforeMemoryDeallocation" reason
  | .duplicateDeadAllocation id => .duplicateDeadAllocation (toMiriAllocId id)

/-- Vendored lifecycle failures that `deallocate_ptr` can report, as theory
`DeallocErr`; allocation-only failures map to `none`. -/
def deallocErrOfMiri : Miri.Memory.MemoryLifecycleError → Option DeallocErr
  | .danglingPointer addr => some (.danglingPointer addr)
  | .nonzeroAllocationOffset _ id off => some (.nonzeroOffset (ofMiriAllocId id) off.bytes)
  | .globalAllocationDeallocation id kind =>
    some (.globalErr (ofMiriAllocId id) (globalKindOfMiri kind))
  | .useAfterFree id => some (.useAfterFree (ofMiriAllocId id))
  | .immutableAllocation id => some (.immutableAllocation (ofMiriAllocId id))
  | .memoryKindMismatch id => some (.memoryKindMismatch (ofMiriAllocId id))
  | .hookFailure _ message => some (.hookFailure message)
  | .duplicateDeadAllocation id => some (.duplicateDeadAllocation (ofMiriAllocId id))
  | _ => none

/-- Every theory deallocation failure whose layout payload is absent
round-trips through the vendored error vocabulary. -/
theorem deallocErrOfMiri_toMiri (e : DeallocErr)
    (hlay : ∀ id s₁ s₂ a₁ a₂, e ≠ .layoutMismatch id s₁ s₂ a₁ a₂) :
    deallocErrOfMiri (deallocErrToMiri e) = some e := by
  cases e with
  | layoutMismatch id s₁ s₂ a₁ a₂ => exact absurd rfl (hlay id s₁ s₂ a₁ a₂)
  | globalErr id kind =>
    show some (DeallocErr.globalErr _ (globalKindOfMiri (globalKindToMiri kind))) = _
    rw [globalKindOfMiri_toMiri]
    rfl
  | _ => rfl

/-! ## Part 1D. `sizeAsI64`, `checkAndDerefPtr`, and `checkPtrAccess` -/

/-- The `Miri.Memory.LiveAllocationLookup` induced by a keyed allocation world,
in the result shape of `get_alloc_info`: absent metadata is `.unavailable`, and
tombstones are reported as `.dead` metadata (not as a lookup error). -/
def keyedLookup (kw : KeyedAllocWorld) : Miri.Memory.LiveAllocationLookup :=
  fun id =>
    match kw.getAllocInfo (ofMiriAllocId id) with
    | some info => .ok (allocInfoToMiri info)
    | none => .error (.unavailable id)

/-- Linear-list twin of `keyedLookup`. -/
def linearLookup (lw : LinearAllocWorld) : Miri.Memory.LiveAllocationLookup :=
  fun id =>
    match lw.getAllocInfo (ofMiriAllocId id) with
    | some info => .ok (allocInfoToMiri info)
    | none => .error (.unavailable id)

theorem linearLookup_eq_keyedLookup {lw : LinearAllocWorld} {kw : KeyedAllocWorld}
    (h : AllocWorldRel lw kw) : linearLookup lw = keyedLookup kw := by
  funext id
  unfold linearLookup keyedLookup
  rw [allocWorldRel_getAllocInfo h]

/-- `Miri.Memory.sizeAsI64` is the `isize::MAX` gate: exactly the sizes below
`2 ^ 63` are converted. -/
theorem sizeAsI64_eq (size : Miri.ABI.Size) :
    Miri.Memory.sizeAsI64 size =
      if size.bytes.toNat < 9223372036854775808 then .ok (Int.ofNat size.bytes.toNat)
      else .error (.sizeDoesNotFitI64 size) := rfl

/-- Exact outcome, in source failure order, of the vendored pointer-access
check against a keyed world: (1) the `isize::MAX` size gate, (2) the zero-size
fast path (no resolution, no lookup), (3) pointer resolution, (4) allocation
metadata lookup, (5) the dead-allocation check, (6) the bounds check. -/
def keyedAccessOutcome {Prov ProvExtra : Type} (target : Miri.Memory.PointerArithmetic)
    (ptr : Miri.Memory.Pointer (Option Prov)) (size : Miri.ABI.Size)
    (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld) :
    Except Miri.Memory.AccessError (Option (Miri.Memory.CheckedPointerAccess ProvExtra)) :=
  if 9223372036854775808 ≤ size.bytes.toNat then .error (.sizeDoesNotFitI64 size)
  else if size.bytes.toNat = 0 then .ok none
  else
    match resolve ptr (Int.ofNat size.bytes.toNat) with
    | .error addr =>
      .error (.danglingIntegerPointer addr (Int.ofNat size.bytes.toNat) msg)
    | .ok r =>
      match kw.getAllocInfo (ofMiriAllocId r.allocId) with
      | none => .error (.allocationLookup (.unavailable r.allocId))
      | some info =>
        if info.kind = .dead then .error (.allocationLookup (.deadAllocation r.allocId))
        else if r.offset.bytes.toNat + size.bytes.toNat ≤ info.sizeBytes.toNat then
          .ok (some ⟨r, allocInfoToMiri info⟩)
        else
          match target.signExtendToTargetIsize r.offset.bytes with
          | .ok signedOffset =>
            .error (.pointerOutOfBounds r.allocId (Miri.ABI.Size.ofBytes info.sizeBytes)
              signedOffset.toInt (Int.ofNat size.bytes.toNat) msg)
          | .error e => .error (.pointerArithmetic e)

/-- Vendored `Miri.Memory.checkAndDerefPtr` on a size that passed the
`sizeAsI64` gate, with the keyed world as its allocation lookup. -/
theorem checkAndDerefPtr_keyed_eq {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld)
    (hfit : size.bytes.toNat < 9223372036854775808) :
    Miri.Memory.checkAndDerefPtr target ptr (Int.ofNat size.bytes.toNat) msg resolve
        (keyedLookup kw) =
      keyedAccessOutcome target ptr size msg resolve kw := by
  have hnot : ¬ 9223372036854775808 ≤ size.bytes.toNat := Nat.not_le.mpr hfit
  unfold keyedAccessOutcome
  simp only [hnot, ↓reduceIte]
  by_cases hz : size.bytes.toNat = 0
  · simp only [hz, ↓reduceIte]
    exact Miri.Memory.zero_sized_check_skips_resolution ptr msg resolve (keyedLookup kw) target
  · simp only [hz, ↓reduceIte]
    have hlo : -(2 ^ 63 : Int) ≤ Int.ofNat size.bytes.toNat :=
      Int.le_trans (by decide) (Int.natCast_nonneg _)
    have hhi : Int.ofNat size.bytes.toNat < 2 ^ 63 := by
      have h63 : (2 ^ 63 : Int) = 9223372036854775808 := by decide
      rw [h63]
      exact Int.ofNat_lt.mpr hfit
    have hne0 : Int.ofNat size.bytes.toNat ≠ 0 := by
      intro h0
      exact hz (Int.ofNat.inj h0)
    rw [checkAndDerefPtr_nonzero_eq target ptr _ msg resolve (keyedLookup kw) hlo hhi hne0]
    cases hres : resolve ptr (Int.ofNat size.bytes.toNat) with
    | error addr => rfl
    | ok r =>
      simp only []
      unfold keyedLookup
      cases hinfo : kw.getAllocInfo (ofMiriAllocId r.allocId) with
      | none => rfl
      | some info =>
        simp only []
        by_cases hdead : info.kind = .dead
        · have hk : ((allocInfoToMiri info).kind == Miri.Memory.AllocationKind.dead) = true := by
            show (infoKindToMiri info.kind == Miri.Memory.AllocationKind.dead) = true
            rw [hdead]
            rfl
          simp only [hk, hdead, ↓reduceIte]
        · have hk : ((allocInfoToMiri info).kind == Miri.Memory.AllocationKind.dead) = false := by
            show (infoKindToMiri info.kind == Miri.Memory.AllocationKind.dead) = false
            rw [infoKindToMiri_beq_dead]
            exact beq_false_of_ne hdead
          simp only [hk, hdead, Bool.false_eq_true, ↓reduceIte]
          have hcb := checkedBounds_ofNat_eq target r.allocId (allocInfoToMiri info).size r.offset
            size.bytes.toNat msg hhi
          have hsz : (allocInfoToMiri info).size.bytes.toNat = info.sizeBytes.toNat := rfl
          rw [hsz] at hcb
          rw [show Miri.Memory.checkedBounds target r.allocId (allocInfoToMiri info).size r.offset
              (Int.ofNat size.bytes.toNat) msg = _ from hcb]
          by_cases hib : r.offset.bytes.toNat + size.bytes.toNat ≤ info.sizeBytes.toNat
          · simp only [hib, ↓reduceIte]
          · simp only [hib, ↓reduceIte]
            cases target.signExtendToTargetIsize r.offset.bytes <;> rfl

private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- Vendored `Miri.Memory.checkPtrAccess` (`check_ptr_access`) against a keyed
world, for EVERY size, pointer, and resolver. -/
theorem checkPtrAccess_keyed_eq {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld) :
    Miri.Memory.checkPtrAccess target ptr size msg resolve (keyedLookup kw) =
      (keyedAccessOutcome target ptr size msg resolve kw).map (fun _ => ()) := by
  unfold Miri.Memory.checkPtrAccess
  rw [sizeAsI64_eq]
  by_cases hfit : size.bytes.toNat < 9223372036854775808
  · simp only [hfit, ↓reduceIte]
    rw [except_ok_bind, checkAndDerefPtr_keyed_eq target ptr size msg resolve kw hfit]
    generalize keyedAccessOutcome target ptr size msg resolve kw = outcome
    cases outcome <;> rfl
  · have hbig : 9223372036854775808 ≤ size.bytes.toNat := Nat.le_of_not_lt hfit
    simp only [hfit, ↓reduceIte]
    unfold keyedAccessOutcome
    simp only [hbig, ↓reduceIte]
    rfl

/-- Vendored `Miri.Memory.getPtrAccess` (`get_ptr_access`) against a keyed
world: on success it reports the allocation size and alignment recorded by the
keyed world together with the resolved pointer. -/
theorem getPtrAccess_keyed_eq {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld) :
    Miri.Memory.getPtrAccess target ptr size msg resolve (keyedLookup kw) =
      (keyedAccessOutcome target ptr size msg resolve kw).map (fun checked =>
        checked.map fun access =>
          (access.allocation.size, access.allocation.align,
            (access.pointer.allocId, access.pointer.offset, access.pointer.extra))) := by
  unfold Miri.Memory.getPtrAccess
  rw [sizeAsI64_eq]
  by_cases hfit : size.bytes.toNat < 9223372036854775808
  · simp only [hfit, ↓reduceIte]
    rw [except_ok_bind, checkAndDerefPtr_keyed_eq target ptr size msg resolve kw hfit]
    generalize keyedAccessOutcome target ptr size msg resolve kw = outcome
    cases outcome <;> rfl
  · have hbig : 9223372036854775808 ≤ size.bytes.toNat := Nat.le_of_not_lt hfit
    simp only [hfit, ↓reduceIte]
    unfold keyedAccessOutcome
    simp only [hbig, ↓reduceIte]
    rfl

/-- `resolve` resolves `ptr` exactly as the theory provenance describes: no
provenance is an integer-address failure, and `(id, off)` is allocation `id` at
relative offset `off`. -/
def ResolvesAs {Prov ProvExtra : Type} (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (ptr : Miri.Memory.Pointer (Option Prov)) : Option (MiriAllocId × UInt64) → Prop
  | none => ∀ signedSize, ∃ addr, resolve ptr signedSize = .error addr
  | some (id, off) =>
    ∀ signedSize, ∃ extra,
      resolve ptr signedSize = .ok ⟨toMiriAllocId id, Miri.ABI.Size.ofBytes off, extra⟩

/-- **`checkPtrAccess` correspondence.** The vendored `check_ptr_access`
succeeds exactly when the theory's `KeyedAllocWorld.checkPtrAccess` holds, for
every size (including the `isize::MAX` gate and the zero-size fast path). -/
theorem checkPtrAccess_isOk_eq_keyed {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld)
    (prov : Option (MiriAllocId × UInt64)) (hres : ResolvesAs resolve ptr prov) :
    (Miri.Memory.checkPtrAccess target ptr size msg resolve (keyedLookup kw)).isOk =
      kw.checkPtrAccess prov size.bytes.toNat := by
  rw [checkPtrAccess_keyed_eq]
  unfold keyedAccessOutcome KeyedAllocWorld.checkPtrAccess
  by_cases hbig : 9223372036854775808 ≤ size.bytes.toNat
  · simp only [hbig, ↓reduceIte]
    rfl
  · simp only [hbig, ↓reduceIte]
    by_cases hz : size.bytes.toNat = 0
    · simp only [hz, ↓reduceIte, beq_self_eq_true]
      rfl
    · have hz' : (size.bytes.toNat == 0) = false := beq_false_of_ne hz
      simp only [hz, hz', ↓reduceIte, Bool.false_eq_true]
      cases prov with
      | none =>
        obtain ⟨addr, haddr⟩ := hres (Int.ofNat size.bytes.toNat)
        rw [haddr]
        rfl
      | some p =>
        obtain ⟨id, off⟩ := p
        obtain ⟨extra, hok⟩ := hres (Int.ofNat size.bytes.toNat)
        rw [hok]
        simp only [ofMiriAllocId_toMiriAllocId]
        cases hinfo : kw.getAllocInfo id with
        | none => rfl
        | some info =>
          simp only []
          by_cases hdead : info.kind = .dead
          · simp only [hdead, ↓reduceIte]
            rfl
          · have hne : (info.kind != AllocInfoKind.dead) = true := bne_iff_ne.mpr hdead
            simp only [hdead, hne, ↓reduceIte, Bool.true_and]
            by_cases hib : off.toNat + size.bytes.toNat ≤ info.sizeBytes.toNat
            · have hib' : (Miri.ABI.Size.ofBytes off).bytes.toNat + size.bytes.toNat ≤
                  info.sizeBytes.toNat := hib
              simp only [hib, hib', ↓reduceIte, decide_true]
              rfl
            · have hib' : ¬ ((Miri.ABI.Size.ofBytes off).bytes.toNat + size.bytes.toNat ≤
                  info.sizeBytes.toNat) := hib
              simp only [hib, hib', ↓reduceIte, decide_false]
              cases target.signExtendToTargetIsize (Miri.ABI.Size.ofBytes off).bytes <;> rfl

/-- Linear-list form of `checkPtrAccess_isOk_eq_keyed`. -/
theorem checkPtrAccess_isOk_eq_linear {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    {lw : LinearAllocWorld} {kw : KeyedAllocWorld} (hrel : AllocWorldRel lw kw)
    (prov : Option (MiriAllocId × UInt64)) (hres : ResolvesAs resolve ptr prov) :
    (Miri.Memory.checkPtrAccess target ptr size msg resolve (linearLookup lw)).isOk =
      lw.checkPtrAccess prov size.bytes.toNat := by
  rw [linearLookup_eq_keyedLookup hrel, allocWorldRel_checkPtrAccess hrel]
  exact checkPtrAccess_isOk_eq_keyed target ptr size msg resolve kw prov hres

/-- Allocation-relative pointer resolution with an explicit base-address table
(the body of `annealResolvePtr`, with the machine's `lookupBaseAddr` as a
parameter). -/
def resolveWithBase (lookupBaseAddr : Miri.Memory.AllocId → Option UInt64) :
    Miri.Memory.PointerResolver AnnealProv Miri.Memory.BorTag :=
  fun ptr _signedSize =>
    match ptr.provenance with
    | none => .error ptr.offset.bytes
    | some (.concrete allocId borTag) =>
      match lookupBaseAddr allocId with
      | some baseAddr =>
        if baseAddr ≤ ptr.offset.bytes then
          .ok ⟨allocId, Miri.ABI.Size.ofBytes (ptr.offset.bytes - baseAddr), borTag⟩
        else
          .error ptr.offset.bytes
      | none => .error ptr.offset.bytes
    | some .wildcard => .error ptr.offset.bytes

/-- **`PtrRel` lifts to keyed provenance.** A `PtrRel`-related `lean-miri`
pointer resolves, under the `id <<< 32` stack base addresses, to the keyed
provenance `(allocId, offsetBytes)` of its `allocMap` entry. -/
theorem ptrRel_resolvesAs {allocMap : List AllocMapEntry}
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (h : PtrRel allocMap p mptr)
    (lookupBaseAddr : Miri.Memory.AllocId → Option UInt64)
    (hbase : ∀ e ∈ allocMap, lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      ResolvesAs (resolveWithBase lookupBaseAddr) ⟨mptr.offset, some mptr.provenance⟩
        (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes)) := by
  cases h with
  | mk allocId borTag hprov hid hoff haddr htarget =>
    obtain ⟨e, he, htag, halloc⟩ := htarget
    subst halloc
    refine ⟨e, he, htag, ?_⟩
    intro signedSize
    refine ⟨borTag, ?_⟩
    have hb := hbase e he
    have hno_ovf := PtrRel.base_add_offset_lt_u64 e.allocId p.offsetBytes hid hoff
    have hoff_lt : p.offsetBytes < 2 ^ 64 := by omega
    have hu64 : (UInt64.ofNat p.offsetBytes).toNat = p.offsetBytes :=
      UInt64.toNat_ofNat_of_lt hoff_lt
    have hadd_toNat :
        (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes).toNat =
          (annealStackBaseAddr e.allocId).toNat + p.offsetBytes := by
      rw [UInt64.toNat_add, hu64, Nat.mod_eq_of_lt hno_ovf]
    have hle_raw :
        annealStackBaseAddr e.allocId ≤
          annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes := by
      rw [UInt64.le_iff_toNat_le, hadd_toNat]
      omega
    have hsub :
        (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes) -
          annealStackBaseAddr e.allocId = UInt64.ofNat p.offsetBytes := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ hle_raw, hadd_toNat, hu64]
      omega
    have hle : annealStackBaseAddr e.allocId ≤
        (Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes)).bytes := hle_raw
    have hsub' :
        (Miri.ABI.Size.ofBytes
            (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes)).bytes -
          annealStackBaseAddr e.allocId = UInt64.ofNat p.offsetBytes := hsub
    show resolveWithBase lookupBaseAddr ⟨mptr.offset, some mptr.provenance⟩ signedSize = _
    unfold resolveWithBase
    simp only [hprov, hb, haddr, hle, hsub', ↓reduceIte]
    rfl

/-- `PtrRel`-related pointers pass the vendored `check_ptr_access` exactly when
the theory's keyed `checkPtrAccess` accepts their keyed provenance. -/
theorem ptrRel_checkPtrAccess_isOk_eq_keyed {allocMap : List AllocMapEntry}
    {p : Trusted.Rustc.V2026_06_01.MirAst.ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (h : PtrRel allocMap p mptr)
    (lookupBaseAddr : Miri.Memory.AllocId → Option UInt64)
    (hbase : ∀ e ∈ allocMap, lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId))
    (target : Miri.Memory.PointerArithmetic) (size : Miri.ABI.Size)
    (msg : Miri.Memory.CheckInAllocMsg) (kw : KeyedAllocWorld) :
    ∃ e ∈ allocMap, e.tag = p.tag ∧
      (Miri.Memory.checkPtrAccess target ⟨mptr.offset, some mptr.provenance⟩ size msg
          (resolveWithBase lookupBaseAddr) (keyedLookup kw)).isOk =
        kw.checkPtrAccess (some (ofMiriAllocId e.allocId, UInt64.ofNat p.offsetBytes))
          size.bytes.toNat := by
  obtain ⟨e, he, htag, hres⟩ := ptrRel_resolvesAs h lookupBaseAddr hbase
  exact ⟨e, he, htag, checkPtrAccess_isOk_eq_keyed target _ size msg _ kw _ hres⟩

/-! ## Part 1C. Vendored memory rows as linear and keyed allocation worlds -/

/-- Projection parameters that the vendored memory rows do not determine: the
classification of machine memory kinds and the byte payload abstraction. -/
structure RowProjection (Prov Extra MachineKind : Type) where
  machineKind : MachineKind → AllocMemKind
  liveBytes : Miri.Memory.Allocation Prov Extra → List MemByte
  globalBytes : Miri.Memory.GlobalAllocation → List MemByte

/-- The row-level observation surface of the vendored
`Miri.Memory.MemoryState`: its allocation-ID cursor and exhaustion latch, the
issued-ID rows (`issuedIds`), the compiler-global rows (`globals`), and the
public `live` / `dead` row arrays, all in the vendored row types. -/
structure MiriAllocRows (Prov Extra MachineKind : Type) where
  nextAllocId : UInt64 := 1
  idSupplyExhausted : Bool := false
  issued : Array Miri.Memory.AllocId := #[]
  globals : Array Miri.Memory.GlobalAllocation := #[]
  live : Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation Prov Extra MachineKind) := #[]
  dead : Array Miri.Memory.DeadAllocation := #[]

section Rows

variable {Prov Extra MachineKind : Type}

def liveEntryOfMiri (proj : RowProjection Prov Extra MachineKind)
    (la : Miri.Memory.LocalAllocation Prov Extra MachineKind) : LiveAllocEntry :=
  { sizeBytes := la.allocation.byteSize.bytes
    alignPow2 := UInt8.ofNat la.allocation.align.pow2
    kind := memKindOfMiri proj.machineKind la.kind
    mutability := mutabilityOfMiri la.allocation.mutability
    bytes := proj.liveBytes la.allocation }

def deadEntryOfMiri (d : Miri.Memory.DeadAllocation) : DeadAllocEntry :=
  ⟨d.size.bytes, UInt8.ofNat d.align.pow2⟩

def globalEntryOfMiri (proj : RowProjection Prov Extra MachineKind)
    (g : Miri.Memory.GlobalAllocation) : GlobalAllocEntry :=
  ⟨globalKindOfMiri g.kind, g.size.bytes, UInt8.ofNat g.align.pow2,
    mutabilityOfMiri g.mutability, proj.globalBytes g⟩

/-- Vendored rows as the theory's linear allocation world (row order kept). -/
def MiriAllocRows.toLinear (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) : LinearAllocWorld :=
  { nextAllocId := rows.nextAllocId
    idSupplyExhausted := rows.idSupplyExhausted
    issued := rows.issued.toList.map ofMiriAllocId
    globals := rows.globals.toList.map fun g => (ofMiriAllocId g.allocId, globalEntryOfMiri proj g)
    live := rows.live.toList.map fun row => (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)
    dead := rows.dead.toList.map fun d => (ofMiriAllocId d.allocId, deadEntryOfMiri d)
    race := [] }

/-- Vendored rows as the theory's keyed `ExtTreeMap0` allocation world. -/
def MiriAllocRows.toKeyed (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) : KeyedAllocWorld :=
  KeyedAllocWorld.ofLinear (rows.toLinear proj)

theorem allocWorldRel_rows (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) :
    AllocWorldRel (rows.toLinear proj) (rows.toKeyed proj) :=
  allocWorldRel_ofLinear _

/-- The keyed projection is the UNIQUE keyed world refining the rows. -/
theorem allocWorldRel_rows_iff (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (kw : KeyedAllocWorld) :
    AllocWorldRel (rows.toLinear proj) kw ↔ kw = rows.toKeyed proj :=
  allocWorldRel_iff_eq_ofLinear _ _

private theorem linearFind?_map_ofMiri {α β : Type} (l : List α)
    (key : α → Miri.Memory.AllocId) (val : α → β) (id : Miri.Memory.AllocId) :
    linearFind? (l.map fun a => (ofMiriAllocId (key a), val a)) (ofMiriAllocId id) =
      (l.find? (fun a => key a == id)).map val := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, linearFind?, List.find?]
    rw [ofMiriAllocId_beq]
    cases key a == id with
    | true => rfl
    | false => exact ih

/-- Keyed live lookup is the vendored first-match row lookup
`live.find? (·.1 == id)`. -/
theorem toKeyed_findLive? (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).findLive? (ofMiriAllocId id) =
      (rows.live.toList.find? (fun entry => entry.1 == id)).map
        (fun row => liveEntryOfMiri proj row.2) := by
  rw [← (allocWorldRel_rows proj rows).live_rel]
  exact linearFind?_map_ofMiri rows.live.toList (fun row => row.1)
    (fun row => liveEntryOfMiri proj row.2) id

/-- Keyed tombstone lookup is the vendored row lookup
`dead.find? (·.allocId == id)`. -/
theorem toKeyed_findDead? (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).findDead? (ofMiriAllocId id) =
      (rows.dead.toList.find? (fun entry => entry.allocId == id)).map deadEntryOfMiri := by
  rw [← (allocWorldRel_rows proj rows).dead_rel]
  exact linearFind?_map_ofMiri rows.dead.toList (fun d => d.allocId) deadEntryOfMiri id

/-- Keyed global lookup is the first global row with the runtime ID. -/
theorem toKeyed_findGlobal? (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).findGlobal? (ofMiriAllocId id) =
      (rows.globals.toList.find? (fun g => g.allocId == id)).map (globalEntryOfMiri proj) := by
  rw [← (allocWorldRel_rows proj rows).globals_rel]
  exact linearFind?_map_ofMiri rows.globals.toList (fun g => g.allocId)
    (globalEntryOfMiri proj) id

private theorem any_map_ofMiri (l : List Miri.Memory.AllocId) (id : Miri.Memory.AllocId) :
    (l.map ofMiriAllocId).any (fun x => x == ofMiriAllocId id) = l.any (fun x => x == id) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.any_cons]
    rw [ofMiriAllocId_beq, ih]

/-- Keyed issued-ID membership is membership in the vendored issued rows. -/
theorem toKeyed_hasIssued (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).hasIssued (ofMiriAllocId id) =
      rows.issued.toList.any (fun x => x == id) := by
  rw [← (allocWorldRel_rows proj rows).issued_rel]
  exact any_map_ofMiri rows.issued.toList id

private theorem isSome_map_find? {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    ((l.find? p).map f).isSome = l.any p := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.find?, List.any_cons]
    cases p a with
    | true => rfl
    | false => exact ih

/-- **`is_alloc_live` on rows**: live local rows and compiler-global rows are
live; tombstones are not (the row-level content of the vendored
`MemoryState.isAllocLive`, whose function-pointer and va-list tables are
outside the theory). -/
theorem toKeyed_isAllocLive (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).isAllocLive (ofMiriAllocId id) =
      (rows.live.toList.any (fun entry => entry.1 == id) ||
        rows.globals.toList.any (fun g => g.allocId == id)) := by
  unfold KeyedAllocWorld.isAllocLive
  rw [toKeyed_findLive?, toKeyed_findGlobal?, isSome_map_find?, isSome_map_find?]

/-- **`get_alloc_info` precedence on rows**: live local row, then global row
(kind-specific size and alignment), then tombstone row. -/
theorem toKeyed_getAllocInfo (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (id : Miri.Memory.AllocId) :
    (rows.toKeyed proj).getAllocInfo (ofMiriAllocId id) =
      match rows.live.toList.find? (fun entry => entry.1 == id) with
      | some row =>
        some ⟨row.2.allocation.byteSize.bytes, UInt8.ofNat row.2.allocation.align.pow2,
          .liveData, mutabilityOfMiri row.2.allocation.mutability⟩
      | none =>
        match rows.globals.toList.find? (fun g => g.allocId == id) with
        | some g => some (globalEntryOfMiri proj g).toAllocInfo
        | none =>
          match rows.dead.toList.find? (fun entry => entry.allocId == id) with
          | some d => some ⟨d.size.bytes, UInt8.ofNat d.align.pow2, .dead, .not⟩
          | none => none := by
  unfold KeyedAllocWorld.getAllocInfo
  rw [toKeyed_findLive?, toKeyed_findGlobal?, toKeyed_findDead?]
  cases rows.live.toList.find? (fun entry => entry.1 == id) with
  | some row => rfl
  | none =>
    cases rows.globals.toList.find? (fun g => g.allocId == id) with
    | some g => rfl
    | none =>
      cases rows.dead.toList.find? (fun entry => entry.allocId == id) <;> rfl

end Rows

/-! ### Permutation invariance of the keyed projection -/

private theorem linearFind?_eq_some_iff_mem {α : Type} (xs : List (MiriAllocId × α))
    (hnd : (xs.map Prod.fst).Nodup) (id : MiriAllocId) (v : α) :
    linearFind? xs id = some v ↔ (id, v) ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons x rest ih =>
    obtain ⟨k, a⟩ := x
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk, hrest⟩ := hnd
    have hunf : linearFind? ((k, a) :: rest) id =
        if k == id then some a else linearFind? rest id := by
      simp only [linearFind?, List.find?]
      cases k == id <;> rfl
    rw [hunf]
    by_cases hkid : k = id
    · subst hkid
      rw [beq_self_eq_true]
      simp only [↓reduceIte]
      constructor
      · intro h
        cases h
        exact List.mem_cons_self
      · intro h
        cases h with
        | head => rfl
        | tail _ hmem =>
          exact absurd (List.mem_map_of_mem (f := Prod.fst) hmem) hk
    · rw [beq_false_of_ne hkid]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih hrest]
      constructor
      · intro h
        exact List.mem_cons_of_mem _ h
      · intro h
        cases h with
        | head => exact absurd rfl hkid
        | tail _ hmem => exact hmem

private theorem option_eq_of_some_iff {α : Type} {o₁ o₂ : Option α}
    (h : ∀ v, o₁ = some v ↔ o₂ = some v) : o₁ = o₂ := by
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some v => exact ((h v).2 rfl).symm ▸ rfl
  | some v => exact ((h v).1 rfl).symm

/-- First-match lookup is invariant under any reordering of distinct-key rows. -/
theorem linearFind?_eq_of_perm {α : Type} {xs ys : List (MiriAllocId × α)}
    (hperm : xs.Perm ys) (hnd : (xs.map Prod.fst).Nodup) (id : MiriAllocId) :
    linearFind? xs id = linearFind? ys id := by
  have hnd' : (ys.map Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.mp hnd
  apply option_eq_of_some_iff
  intro v
  rw [linearFind?_eq_some_iff_mem xs hnd, linearFind?_eq_some_iff_mem ys hnd']
  exact hperm.mem_iff

private theorem any_beq_eq_true_iff_mem (xs : List MiriAllocId) (id : MiriAllocId) :
    xs.any (fun x => x == id) = true ↔ id ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons x rest ih =>
    rw [List.any_cons, Bool.or_eq_true, ih]
    constructor
    · intro h
      cases h with
      | inl h => exact (eq_of_beq h) ▸ List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem _ h
    · intro h
      cases h with
      | head => exact Or.inl (beq_self_eq_true _)
      | tail _ hmem => exact Or.inr hmem

private theorem any_beq_eq_of_perm {xs ys : List MiriAllocId} (hperm : xs.Perm ys)
    (id : MiriAllocId) : xs.any (fun x => x == id) = ys.any (fun x => x == id) := by
  have hiff : xs.any (fun x => x == id) = true ↔ ys.any (fun x => x == id) = true := by
    rw [any_beq_eq_true_iff_mem, any_beq_eq_true_iff_mem]
    exact hperm.mem_iff
  cases h1 : xs.any (fun x => x == id) with
  | true => exact (hiff.1 h1).symm
  | false =>
    cases h2 : ys.any (fun x => x == id) with
    | false => rfl
    | true => rw [hiff.2 h2] at h1; cases h1

/-- **Permutation invariance (linear worlds).** Two linear worlds whose tables
are reorderings of one another (distinct IDs per table) have the SAME keyed
world: the keyed representation carries no list-order information. -/
theorem keyedOfLinear_eq_of_perm {lw₁ lw₂ : LinearAllocWorld}
    (hnext : lw₁.nextAllocId = lw₂.nextAllocId)
    (hexh : lw₁.idSupplyExhausted = lw₂.idSupplyExhausted)
    (hiss : lw₁.issued.Perm lw₂.issued)
    (hglob : lw₁.globals.Perm lw₂.globals) (hglobNd : (lw₁.globals.map Prod.fst).Nodup)
    (hlive : lw₁.live.Perm lw₂.live) (hliveNd : (lw₁.live.map Prod.fst).Nodup)
    (hdead : lw₁.dead.Perm lw₂.dead) (hdeadNd : (lw₁.dead.map Prod.fst).Nodup)
    (hrace : lw₁.race.Perm lw₂.race) (hraceNd : (lw₁.race.map Prod.fst).Nodup) :
    KeyedAllocWorld.ofLinear lw₁ = KeyedAllocWorld.ofLinear lw₂ := by
  have r1 := allocWorldRel_ofLinear lw₁
  have r2 := allocWorldRel_ofLinear lw₂
  apply KeyedAllocWorld.ext
  · rw [← r1.nextAllocId_eq, ← r2.nextAllocId_eq, hnext]
  · rw [← r1.idSupplyExhausted_eq, ← r2.idSupplyExhausted_eq, hexh]
  · intro id
    rw [← r1.issued_rel, ← r2.issued_rel]
    exact any_beq_eq_of_perm hiss id
  · intro id
    rw [← r1.globals_rel, ← r2.globals_rel]
    exact linearFind?_eq_of_perm hglob hglobNd id
  · intro id
    rw [← r1.live_rel, ← r2.live_rel]
    exact linearFind?_eq_of_perm hlive hliveNd id
  · intro id
    rw [← r1.dead_rel, ← r2.dead_rel]
    exact linearFind?_eq_of_perm hdead hdeadNd id
  · intro id
    rw [← r1.race_rel, ← r2.race_rel]
    exact linearFind?_eq_of_perm hrace hraceNd id

private theorem nodup_map_ofMiri {α : Type} (l : List α) (key : α → Miri.Memory.AllocId)
    (h : (l.map key).Nodup) : (l.map fun a => ofMiriAllocId (key a)).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨?_, ih h.2⟩
    intro hmem
    obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hmem
    exact h.1 (List.mem_map.mpr ⟨b, hb, ofMiriAllocId_injective hbeq⟩)

/-- **Permutation invariance (vendored rows).** Permuting distinct-ID rows of
the vendored `live`, `dead`, global, or issued tables leaves the projected
`KeyedAllocWorld` PROPOSITIONALLY IDENTICAL (`KeyedAllocWorld.ext`): no
list-order preservation obligation remains at the keyed level. -/
theorem rows_toKeyed_eq_of_perm {Prov Extra MachineKind : Type}
    (proj : RowProjection Prov Extra MachineKind)
    {rows₁ rows₂ : MiriAllocRows Prov Extra MachineKind}
    (hnext : rows₁.nextAllocId = rows₂.nextAllocId)
    (hexh : rows₁.idSupplyExhausted = rows₂.idSupplyExhausted)
    (hiss : rows₁.issued.toList.Perm rows₂.issued.toList)
    (hglob : rows₁.globals.toList.Perm rows₂.globals.toList)
    (hglobNd : (rows₁.globals.toList.map fun g => g.allocId).Nodup)
    (hlive : rows₁.live.toList.Perm rows₂.live.toList)
    (hliveNd : (rows₁.live.toList.map fun row => row.1).Nodup)
    (hdead : rows₁.dead.toList.Perm rows₂.dead.toList)
    (hdeadNd : (rows₁.dead.toList.map fun d => d.allocId).Nodup) :
    rows₁.toKeyed proj = rows₂.toKeyed proj := by
  unfold MiriAllocRows.toKeyed
  apply keyedOfLinear_eq_of_perm
  · exact hnext
  · exact hexh
  · exact hiss.map _
  · exact hglob.map _
  · show ((rows₁.globals.toList.map fun g =>
        (ofMiriAllocId g.allocId, globalEntryOfMiri proj g)).map Prod.fst).Nodup
    rw [List.map_map]
    exact nodup_map_ofMiri rows₁.globals.toList (fun g => g.allocId) hglobNd
  · exact hlive.map _
  · show ((rows₁.live.toList.map fun row =>
        (ofMiriAllocId row.1, liveEntryOfMiri proj row.2)).map Prod.fst).Nodup
    rw [List.map_map]
    exact nodup_map_ofMiri rows₁.live.toList (fun row => row.1) hliveNd
  · exact hdead.map _
  · show ((rows₁.dead.toList.map fun d =>
        (ofMiriAllocId d.allocId, deadEntryOfMiri d)).map Prod.fst).Nodup
    rw [List.map_map]
    exact nodup_map_ofMiri rows₁.dead.toList (fun d => d.allocId) hdeadNd
  · exact List.Perm.refl _
  · exact List.nodup_nil

/-- Keyed refinement of vendored memory rows: `kw` is the keyed allocation
world of `rows`. -/
def KeyedRowsRel {Prov Extra MachineKind : Type} (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (kw : KeyedAllocWorld) : Prop :=
  AllocWorldRel (rows.toLinear proj) kw

theorem keyedRowsRel_iff {Prov Extra MachineKind : Type}
    (proj : RowProjection Prov Extra MachineKind)
    (rows : MiriAllocRows Prov Extra MachineKind) (kw : KeyedAllocWorld) :
    KeyedRowsRel proj rows kw ↔ kw = rows.toKeyed proj :=
  allocWorldRel_rows_iff proj rows kw

/-- `KeyedRowsRel` is invariant under row permutations with distinct IDs. -/
theorem keyedRowsRel_perm_invariant {Prov Extra MachineKind : Type}
    (proj : RowProjection Prov Extra MachineKind)
    {rows₁ rows₂ : MiriAllocRows Prov Extra MachineKind} (kw : KeyedAllocWorld)
    (hnext : rows₁.nextAllocId = rows₂.nextAllocId)
    (hexh : rows₁.idSupplyExhausted = rows₂.idSupplyExhausted)
    (hiss : rows₁.issued.toList.Perm rows₂.issued.toList)
    (hglob : rows₁.globals.toList.Perm rows₂.globals.toList)
    (hglobNd : (rows₁.globals.toList.map fun g => g.allocId).Nodup)
    (hlive : rows₁.live.toList.Perm rows₂.live.toList)
    (hliveNd : (rows₁.live.toList.map fun row => row.1).Nodup)
    (hdead : rows₁.dead.toList.Perm rows₂.dead.toList)
    (hdeadNd : (rows₁.dead.toList.map fun d => d.allocId).Nodup) :
    KeyedRowsRel proj rows₁ kw ↔ KeyedRowsRel proj rows₂ kw := by
  rw [keyedRowsRel_iff, keyedRowsRel_iff,
    rows_toKeyed_eq_of_perm proj hnext hexh hiss hglob hglobNd hlive hliveNd hdead hdeadNd]

/-! ## Part 1E. Tree Borrows: `RetagPolicy.create`, protector-end access, traversal order -/

def refKindToMiri : RefParamKind → Miri.TreeBorrows.RetagPolicy.ReferenceKind
  | .shared => .Shared
  | .mutable => .Mutable
  | .box => .Box

def retagModeToMiri :
    MiriRetagPolicyMirror.RetagMode → Miri.TreeBorrows.RetagPolicy.RetagMode
  | .none => .None
  | .default => .Default
  | .twoPhase => .TwoPhase
  | .fnEntry => .FnEntry
  | .raw => .Raw

def typeFactsToMiri (f : ParamTypeFacts) : Miri.TreeBorrows.RetagPolicy.TypeFacts :=
  ⟨f.isUnpin, f.isUnsafeUnpin, f.isFreeze⟩

def policyConfigToMiri (a : ParamRetagAttrs) : Miri.TreeBorrows.RetagPolicy.PolicyConfig :=
  ⟨a.implicitWrites, a.rustcNoWritable⟩

def protectorKindToMiri :
    MiriRetagPolicyMirror.ProtectorKind → Miri.TreeBorrows.ProtectorKind
  | .weakProtector => .WeakProtector
  | .strongProtector => .StrongProtector

/-- The theory's mirrored `NewPermission` as the vendored
`Miri.TreeBorrows.RetagPolicy.NewPermission` (permissions through
`annealPermToMiri`). -/
def newPermissionToMiri (p : MiriRetagPolicyMirror.NewPermission) :
    Miri.TreeBorrows.RetagPolicy.NewPermission :=
  ⟨annealPermToMiri p.freezePermission, annealPermToMiri p.nonfreezePermission,
    annealPermToMiri p.outsidePermission, p.protector.map protectorKindToMiri⟩

/-- **`MiriRetagPolicyMirror.create` IS the vendored `RetagPolicy.create`**, on
every input: all type facts, reference kinds, retag modes, and attribute
configurations. This discharges the "verbatim functional mirror" claim of the
theory against the vendored definition itself. -/
theorem mirror_create_eq_miri_create (facts : ParamTypeFacts) (kind : RefParamKind)
    (mode : MiriRetagPolicyMirror.RetagMode) (attrs : ParamRetagAttrs) :
    (MiriRetagPolicyMirror.create facts kind mode attrs).map newPermissionToMiri =
      Miri.TreeBorrows.RetagPolicy.create (typeFactsToMiri facts) (refKindToMiri kind)
        (retagModeToMiri mode) (policyConfigToMiri attrs) := by
  cases facts with | mk u uu frz =>
  cases attrs with | mk iw rnw =>
  cases kind <;> cases mode <;> cases u <;> cases uu <;> cases frz <;> cases iw <;>
    cases rnw <;> rfl

/-- Classify a vendored `Option NewPermission` as a function-entry policy. -/
def classifyMiriFnEntry :
    Option Miri.TreeBorrows.RetagPolicy.NewPermission → FnEntryRetagPolicy
  | none => .skipRetag
  | some p =>
    match p.freezePermission with
    | .Unique => .writableChildWrite
    | _ => .rustcNoWritable

theorem classifyMiriFnEntry_map (p : Option MiriRetagPolicyMirror.NewPermission) :
    classifyMiriFnEntry (p.map newPermissionToMiri) = MiriRetagPolicyMirror.classifyFnEntry p := by
  cases p with
  | none => rfl
  | some p =>
    cases p with | mk fp np op pr =>
    cases fp <;> rfl

/-- **`selectFnEntryPolicy` against the vendored `RetagPolicy.create`** in
`FnEntry` mode, on every input (no mirror in the statement). -/
theorem selectFnEntryPolicy_eq_miri_create (facts : ParamTypeFacts) (kind : RefParamKind)
    (attrs : ParamRetagAttrs) :
    classifyMiriFnEntry
        (Miri.TreeBorrows.RetagPolicy.create (typeFactsToMiri facts) (refKindToMiri kind)
          .FnEntry (policyConfigToMiri attrs)) =
      selectFnEntryPolicy facts kind attrs := by
  have h := mirror_create_eq_miri_create facts kind .fnEntry attrs
  rw [show retagModeToMiri .fnEntry = Miri.TreeBorrows.RetagPolicy.RetagMode.FnEntry from rfl] at h
  rw [← h, classifyMiriFnEntry_map]
  exact selectFnEntryPolicy_eq_upstream_create facts kind attrs

/-- Child permissions minted by the vendored `RetagPolicy.create` for a
protected `&mut` / `Box` function-entry retag, by theory policy. -/
theorem miri_create_fnEntry_mutOrBox_childPerms (facts : ParamTypeFacts) (kind : RefParamKind)
    (attrs : ParamRetagAttrs) (hkind : kind ≠ .shared) :
    Miri.TreeBorrows.RetagPolicy.create (typeFactsToMiri facts) (refKindToMiri kind)
        .FnEntry (policyConfigToMiri attrs) =
      match selectFnEntryPolicy facts kind attrs with
      | .skipRetag => none
      | .writableChildWrite =>
        some ⟨.Unique, .Unique, .ReservedFrz false,
          some (if kind = .box then .WeakProtector else .StrongProtector)⟩
      | .rustcNoWritable =>
        some ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false,
          some (if kind = .box then .WeakProtector else .StrongProtector)⟩ := by
  cases facts with | mk u uu frz =>
  cases attrs with | mk iw rnw =>
  cases kind with
  | shared => exact absurd rfl hkind
  | mutable => cases u <;> cases uu <;> cases frz <;> cases iw <;> cases rnw <;> rfl
  | box => cases u <;> cases uu <;> cases frz <;> cases iw <;> cases rnw <;> rfl

/-- **Protector-end access kind against the vendored
`Permission.associatedAccess`.** The theory's `protectorEndAccessIsWrite?` is
the vendored associated access of the node permission, gated by the per-location
`accessed` bit (as in `BorrowTree.releaseProtector`). -/
theorem protectorEndAccessIsWrite?_eq_miri_associatedAccess (n : TreeTagNode) :
    protectorEndAccessIsWrite? n =
      if n.accessed then
        (Miri.TreeBorrows.Permission.associatedAccess (annealPermToMiri n.perm)).map
          (fun k => decide (k = Miri.TreeBorrows.AccessKind.Write))
      else none := by
  cases n with | mk tag parentTag perm off len prot accessed =>
  cases accessed <;> cases perm <;> rfl

local macro "miriNodeAt" : term =>
  `(miri_etm_private% Miri.TreeBorrows.Traversal Miri.TreeBorrows.Tree.TraversalTree.nodeAt)
local macro "miriAncestorPathAux" : term =>
  `(miri_etm_private% Miri.TreeBorrows.Traversal
    Miri.TreeBorrows.Tree.TraversalTree.ancestorPathAux)
local macro "miriInitialForeignRootsGo" : term =>
  `(miri_etm_private% Miri.TreeBorrows.Traversal
    Miri.TreeBorrows.Tree.TraversalTree.initialForeignRoots.go)
local macro "miriForeignPostorder" : term =>
  `(miri_etm_private% Miri.TreeBorrows.Traversal
    Miri.TreeBorrows.Tree.TraversalTree.foreignPostorder)

/-- Ordered children of node `t` of a vendored traversal tree (`[]` out of
range), as read by the vendored visitor. -/
def traversalChildren (tree : Miri.TreeBorrows.Tree.TraversalTree) (t : Nat) : List Nat :=
  (tree.nodes[t]?.getD ⟨none, []⟩).children

/-- Parent of node `t` of a vendored traversal tree (`none` out of range). -/
def traversalParent (tree : Miri.TreeBorrows.Tree.TraversalTree) (t : Nat) : Option Nat :=
  (tree.nodes[t]?.getD ⟨none, []⟩).parent

/-- The vendored (private) `TraversalTree.foreignPostorder` IS the theory's
`foreignPostorderTags`, for every tree, skip list, fuel, and start node. -/
theorem miri_foreignPostorder_eq (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (skipNodes : List Nat) (fuel index : Nat) :
    miriForeignPostorder tree skipNodes fuel index =
      (foreignPostorderTags (traversalChildren tree) (fun t => skipNodes.contains t) fuel
        index).map
        (fun t => (⟨t, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
    have hunf : miriForeignPostorder tree skipNodes (fuel + 1) index =
        if skipNodes.contains index then []
        else
          (traversalChildren tree index).reverse.flatMap
              (miriForeignPostorder tree skipNodes fuel) ++
            [⟨index, .ForeignAccess⟩] := rfl
    rw [hunf, show miriForeignPostorder tree skipNodes fuel = _ from funext ih]
    simp only [foreignPostorderTags]
    by_cases hskip : skipNodes.contains index = true
    · simp only [hskip, ↓reduceIte, List.map_nil]
    · simp only [hskip, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
        List.map_nil, List.map_flatMap]

/-- The vendored (private) `TraversalTree.initialForeignRoots` loop under
`VisitChildrenOfAccessed` IS the theory's `initialForeignRootTags`. -/
theorem miri_initialForeignRoots_go_eq (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (remaining : List Nat) (previous : Option Nat) (isStart : Bool) :
    miriInitialForeignRootsGo tree .VisitChildrenOfAccessed remaining previous isStart =
      initialForeignRootTags (traversalChildren tree) remaining previous := by
  induction remaining generalizing previous isStart with
  | nil => rfl
  | cons cur rest ih =>
    have hunf : miriInitialForeignRootsGo tree .VisitChildrenOfAccessed (cur :: rest) previous
          isStart =
        (if (!isStart ||
              Miri.TreeBorrows.Tree.ChildrenVisitMode.VisitChildrenOfAccessed ==
                Miri.TreeBorrows.Tree.ChildrenVisitMode.VisitChildrenOfAccessed) then
            ((traversalChildren tree cur).reverse).filter (fun child => previous != some child)
          else []) ++
          miriInitialForeignRootsGo tree .VisitChildrenOfAccessed rest (some cur) false := rfl
    rw [hunf, ih]
    cases isStart <;> rfl

/-- **Vendored `TraversalTree.traverse` visit order.** Under
`VisitChildrenOfAccessed` (the mode of `RetagPipeline.accessTreeForReborrow`),
the vendored visitor emits the access path as LOCAL events and then exactly
the theory's foreign schedule (`initialForeignRootTags` expanded by
`foreignPostorderTags`) as FOREIGN events, for every tree, start node, and skip
list. -/
theorem miri_traverse_eq_schedule (tree : Miri.TreeBorrows.Tree.TraversalTree) (start : Nat)
    (skipNodes : List Nat) :
    Miri.TreeBorrows.Tree.TraversalTree.traverse tree start .VisitChildrenOfAccessed skipNodes =
      ((Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start).getLast!,
        (Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start).map
            (fun index => (⟨index, .LocalAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) ++
          ((initialForeignRootTags (traversalChildren tree)
              (Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start) none).flatMap
            (foreignPostorderTags (traversalChildren tree) (fun t => skipNodes.contains t)
              tree.nodes.size)).map
            (fun t => (⟨t, .ForeignAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent))) := by
  have hunf : Miri.TreeBorrows.Tree.TraversalTree.traverse tree start .VisitChildrenOfAccessed
        skipNodes =
      ((Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start).getLast!,
        (Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start).map
            (fun index => (⟨index, .LocalAccess⟩ : Miri.TreeBorrows.Tree.TraversalEvent)) ++
          (miriInitialForeignRootsGo tree .VisitChildrenOfAccessed
              (Miri.TreeBorrows.Tree.TraversalTree.ancestorPath tree start) none true).flatMap
            (miriForeignPostorder tree skipNodes tree.nodes.size)) := rfl
  rw [hunf, miri_initialForeignRoots_go_eq,
    show miriForeignPostorder tree skipNodes tree.nodes.size = _ from
      funext (miri_foreignPostorder_eq tree skipNodes tree.nodes.size),
    List.map_flatMap]

/-- The vendored traversal tree of a theory node list whose tags are its list
positions: parents are `parentTag`, children are `childTagsInListOrder`. -/
def traversalTreeOfNodes (nodes : List TreeTagNode) : Miri.TreeBorrows.Tree.TraversalTree :=
  ⟨(nodes.map fun n =>
      (⟨n.parentTag, childTagsInListOrder nodes n.tag⟩ :
        Miri.TreeBorrows.Tree.TraversalNode)).toArray⟩

/-- Node tags are list positions (the vendored tree is position-indexed). -/
def DenseTags (nodes : List TreeTagNode) : Prop :=
  ∀ (i : Nat) (n : TreeTagNode), nodes[i]? = some n → n.tag = i

private theorem find?_tag_eq_getElem?_aux (xs : List TreeTagNode) (k t : Nat)
    (h : ∀ (i : Nat) (n : TreeTagNode), xs[i]? = some n → n.tag = k + i) :
    xs.find? (fun n => n.tag == k + t) = xs[t]? := by
  induction xs generalizing k t with
  | nil => rfl
  | cons x rest ih =>
    have hx : x.tag = k := h 0 x rfl
    cases t with
    | zero =>
      have hb : (x.tag == k + 0) = true := by
        rw [hx]
        exact beq_self_eq_true _
      simp only [List.find?, hb]
      rfl
    | succ t =>
      have hne : x.tag ≠ k + (t + 1) := by
        rw [hx]
        omega
      have hb : (x.tag == k + (t + 1)) = false := beq_false_of_ne hne
      simp only [List.find?, hb]
      have hrest : ∀ (i : Nat) (n : TreeTagNode), rest[i]? = some n → n.tag = (k + 1) + i := by
        intro i n hi
        have := h (i + 1) n hi
        omega
      have := ih (k + 1) t hrest
      rw [show k + (t + 1) = (k + 1) + t from by omega]
      exact this

/-- On dense tags, the theory's first-match `findNode?` is positional lookup. -/
theorem findNode?_eq_getElem?_of_denseTags {nodes : List TreeTagNode} (h : DenseTags nodes)
    (t : Nat) : findNode? nodes t = nodes[t]? := by
  have := find?_tag_eq_getElem?_aux nodes 0 t (by
    intro i n hi
    rw [Nat.zero_add]
    exact h i n hi)
  rw [Nat.zero_add] at this
  exact this

theorem traversalParent_traversalTreeOfNodes (nodes : List TreeTagNode) (t : Nat) :
    traversalParent (traversalTreeOfNodes nodes) t =
      match nodes[t]? with
      | some n => n.parentTag
      | none => none := by
  unfold traversalParent traversalTreeOfNodes
  simp only [List.getElem?_toArray, List.getElem?_map]
  cases nodes[t]? <;> rfl

/-- **Ancestor path.** At equal fuel, the theory's `ancestorPathTagsAux` IS the
vendored (private) `TraversalTree.ancestorPathAux` on the position-indexed tree
of a dense-tag node list. -/
theorem ancestorPathTagsAux_eq_miri {nodes : List TreeTagNode} (h : DenseTags nodes)
    (fuel start : Nat) :
    ancestorPathTagsAux nodes fuel start =
      miriAncestorPathAux (traversalTreeOfNodes nodes) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    have hunf : miriAncestorPathAux (traversalTreeOfNodes nodes) (fuel + 1) start =
        match traversalParent (traversalTreeOfNodes nodes) start with
        | none => [start]
        | some parent => start :: miriAncestorPathAux (traversalTreeOfNodes nodes) fuel parent :=
      rfl
    rw [hunf, traversalParent_traversalTreeOfNodes]
    simp only [ancestorPathTagsAux]
    rw [findNode?_eq_getElem?_of_denseTags h]
    cases nodes[start]? with
    | none => rfl
    | some n =>
      cases hp : n.parentTag with
      | none => simp only [hp]
      | some p =>
        simp only [hp]
        rw [ih]

/-- **Ancestor path on rooted trees.** On a rooted, dense-tag borrow tree the
theory's `ancestorPathTags` IS the vendored `TraversalTree.ancestorPath` of the
position-indexed tree (the theory's one extra unit of fuel is irrelevant). -/
theorem ancestorPathTags_eq_miri_ancestorPath {w : FnEntryBorrowWorld} {rootTag : Nat}
    (hwf : BorrowTreeRootedWF w rootTag) (hdense : DenseTags w.nodes)
    (n : TreeTagNode) (hn : n ∈ w.nodes) :
    ancestorPathTags w.nodes n.tag =
      Miri.TreeBorrows.Tree.TraversalTree.ancestorPath (traversalTreeOfNodes w.nodes) n.tag := by
  obtain ⟨d, hd, hreach⟩ := hwf.reachesRoot n hn
  have hsize : (traversalTreeOfNodes w.nodes).nodes.size = w.nodes.length := by
    unfold traversalTreeOfNodes
    rw [List.size_toArray, List.length_map]
  have hunf : Miri.TreeBorrows.Tree.TraversalTree.ancestorPath (traversalTreeOfNodes w.nodes)
        n.tag =
      miriAncestorPathAux (traversalTreeOfNodes w.nodes)
        (traversalTreeOfNodes w.nodes).nodes.size n.tag := rfl
  rw [hunf, hsize, ← ancestorPathTagsAux_eq_miri hdense]
  exact ancestorPathTagsAux_fuel_irrel hreach (w.nodes.length + 1) w.nodes.length
    (by omega) (by omega)

/-! ## Part 2. Validity: safe-pointer access classification and vtable traits -/

/-- Whether a step error is undefined behavior (as opposed to an interpreter
invariant failure or an unsupported operation). -/
def isUndefinedBehavior : Miri.Interpreter.StepError → Bool
  | .undefinedBehavior _ => true
  | _ => false

/-- The pointer-access failures that the vendored validity visitor
(`ValidityVisitor.checkSafe` through `classifyPointerAccessError`) reports as
undefined behavior. -/
def accessErrorIsUB : Miri.Memory.AccessError → Bool
  | .danglingIntegerPointer .. => true
  | .allocationLookup (.deadAllocation _) => true
  | .pointerOutOfBounds .. => true
  | .alignmentCheckFailed _ => true
  | _ => false

/-- **Access-failure classification of the vendored safe-pointer check**, for
every path, pointer kind, and access error: integer (provenance-free) pointers,
use-after-free, and out-of-bounds are validation UB; the `isize::MAX` size
gate, unavailable allocation metadata, and pointer-arithmetic failures are
interpreter invariant failures, NOT undefined behavior. -/
theorem classifyPointerAccessError_isUB (path : Miri.Memory.ValidationPath)
    (kind : Miri.Memory.SafePointerKind) (e : Miri.Memory.AccessError) :
    isUndefinedBehavior
        (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind e) =
      accessErrorIsUB e := by
  cases e with
  | allocationLookup reason => cases reason <;> rfl
  | _ => rfl

/-- On sizes that pass the `isize::MAX` gate, every failure of the vendored
access check against a keyed world is validation UB, except unavailable
allocation metadata and target pointer-arithmetic failures. -/
theorem keyedAccessOutcome_error_isUB_of_fit {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld)
    (hfit : size.bytes.toNat < 9223372036854775808) (e : Miri.Memory.AccessError)
    (he : keyedAccessOutcome target ptr size msg resolve kw = .error e) :
    accessErrorIsUB e = true ∨
      (∃ id, e = .allocationLookup (.unavailable id)) ∨
      (∃ reason, e = .pointerArithmetic reason) := by
  have hnot : ¬ 9223372036854775808 ≤ size.bytes.toNat := Nat.not_le.mpr hfit
  unfold keyedAccessOutcome at he
  simp only [hnot, ↓reduceIte] at he
  by_cases hz : size.bytes.toNat = 0
  · simp only [hz, ↓reduceIte] at he
    cases he
  · simp only [hz, ↓reduceIte] at he
    cases hres : resolve ptr (Int.ofNat size.bytes.toNat) with
    | error addr =>
      rw [hres] at he
      cases he
      exact Or.inl rfl
    | ok r =>
      rw [hres] at he
      simp only [] at he
      cases hinfo : kw.getAllocInfo (ofMiriAllocId r.allocId) with
      | none =>
        rw [hinfo] at he
        cases he
        exact Or.inr (Or.inl ⟨_, rfl⟩)
      | some info =>
        rw [hinfo] at he
        simp only [] at he
        by_cases hdead : info.kind = .dead
        · simp only [hdead, ↓reduceIte] at he
          cases he
          exact Or.inl rfl
        · simp only [hdead, ↓reduceIte] at he
          by_cases hib : r.offset.bytes.toNat + size.bytes.toNat ≤ info.sizeBytes.toNat
          · simp only [hib, ↓reduceIte] at he
            cases he
          · simp only [hib, ↓reduceIte] at he
            cases hse : target.signExtendToTargetIsize r.offset.bytes with
            | ok signedOffset =>
              rw [hse] at he
              cases he
              exact Or.inl rfl
            | error reason =>
              rw [hse] at he
              cases he
              exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- **Size-gate classification separation.** For an access of at least
`2 ^ 63` bytes the vendored check fails with `sizeDoesNotFitI64`, which the
vendored validity visitor classifies as an interpreter invariant failure (the
source `unwrap` on `isize::MAX`), not as undefined behavior; the theory's
`KeyedAllocWorld.checkPtrAccess` merely returns `false`, which
`validateSafeThinRef` reports as a dangling or null reference. The two agree
on REJECTION but not on the failure class for such sizes. -/
theorem sizeGate_failure_class_separation {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic) (ptr : Miri.Memory.Pointer (Option Prov))
    (size : Miri.ABI.Size) (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra) (kw : KeyedAllocWorld)
    (path : Miri.Memory.ValidationPath) (kind : Miri.Memory.SafePointerKind)
    (prov : Option (MiriAllocId × UInt64))
    (hbig : 9223372036854775808 ≤ size.bytes.toNat) :
    Miri.Memory.checkPtrAccess target ptr size msg resolve (keyedLookup kw) =
        .error (.sizeDoesNotFitI64 size) ∧
      isUndefinedBehavior
          (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
            (.sizeDoesNotFitI64 size)) = false ∧
      kw.checkPtrAccess prov size.bytes.toNat = false := by
  refine ⟨?_, rfl, ?_⟩
  · rw [checkPtrAccess_keyed_eq]
    unfold keyedAccessOutcome
    simp only [hbig, ↓reduceIte]
    rfl
  · unfold KeyedAllocWorld.checkPtrAccess
    simp only [ge_iff_le, hbig, ↓reduceIte]

/-- The vendored `VTablePredicate` of a theory predicate. -/
def predSpecToMiri (p : VTablePredSpec) : Miri.Interpreter.VTablePredicate :=
  ⟨p.id, p.stableKey, p.autoTrait⟩

/-- The vendored predicate array of a theory existential specification (its
effective predicates: the optional principal followed by the listed ones). -/
def specPredicates (s : DynExistentialSpec) : Array Miri.Interpreter.VTablePredicate :=
  (s.effectivePreds.map predSpecToMiri).toArray

/-- Vendored vtable read hooks over a table of existential specifications:
`predicates` reads the table and `normalizePredicate` is the predicate ID. The
pointer, global, and layout leaves are not consulted by `checkForTypeRead`. -/
def specReadHooks (P : Type) (table : Nat → DynExistentialSpec) :
    Miri.Interpreter.VTableReadHooks P Unit Unit where
  resolvePointer := fun _ _ => pure (.error .danglingInteger)
  globalVTable := fun _ _ => pure none
  predicates := fun _ n => pure (specPredicates (table n))
  normalizePredicate := fun _ p => pure p.id
  layoutOf := fun _ _ => throw (.invalidProgram "layoutOf is not consulted")

/-- Whether the vendored `VTable.checkForTypeRead` accepts `actual` against
`expected` over a specification table. -/
def miriVTableTraitCheckOk (table : Nat → DynExistentialSpec) (actual expected : Nat) : Bool :=
  match Miri.Interpreter.VTable.checkForTypeRead (specReadHooks Unit table) () actual
      expected () with
  | .ok _ _ => true
  | .error _ _ => false

local macro "miriSortedPredicates" : term =>
  `(miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.sortedPredicates)
local macro "miriSortPredicates" : term =>
  `(miri_etm_private% Miri.Interpreter.VTable Miri.Interpreter.VTable.sortPredicates)

private theorem filter_nonAuto_eq_nil (xs : List Miri.Interpreter.VTablePredicate)
    (h : ∀ q ∈ xs, q.autoTrait = true) : xs.filter (fun q => !q.autoTrait) = [] := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx : x.autoTrait = true := h x List.mem_cons_self
    have hrest := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.filter_cons, hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrest]

/-- The vendored (private) `sortedPredicates` drops auto-trait predicates: an
all-auto-trait predicate array canonicalizes to the empty list. -/
theorem miri_sortedPredicates_autoOnly (preds : Array Miri.Interpreter.VTablePredicate)
    (h : ∀ q ∈ preds.toList, q.autoTrait = true) : miriSortedPredicates preds = [] := by
  have hunf : miriSortedPredicates preds =
      (miriSortPredicates (preds.toList.filter (!·.autoTrait))).eraseDups := rfl
  rw [hunf, filter_nonAuto_eq_nil preds.toList h]
  rfl

/-- **Auto traits are ignored by the vendored trait check** (`lean-miri#75`):
whenever both the actual and the expected existential consist of auto-trait
predicates only (principal-less `dyn Send`, `dyn Send + Sync`, ...), the
vendored `VTable.checkForTypeRead` accepts. -/
theorem miri_checkForTypeRead_autoOnly_ok (P : Type) (table : Nat → DynExistentialSpec)
    (actual expected : Nat)
    (ha : ∀ q ∈ (specPredicates (table actual)).toList, q.autoTrait = true)
    (he : ∀ q ∈ (specPredicates (table expected)).toList, q.autoTrait = true) :
    Miri.Interpreter.VTable.checkForTypeRead (specReadHooks P table) () actual expected () =
      .ok () () := by
  unfold Miri.Interpreter.VTable.checkForTypeRead
  simp only [specReadHooks, bind, EStateM.bind, pure, EStateM.pure]
  rw [miri_sortedPredicates_autoOnly _ ha, miri_sortedPredicates_autoOnly _ he]
  rfl

/-! ## Part 3. Closed non-vacuity canaries -/

/-- Canary resolver: the provenance is the allocation identifier and the
pointer offset is allocation-relative. -/
def canaryResolve : Miri.Memory.PointerResolver Miri.Memory.AllocId Unit :=
  fun ptr _ =>
    match ptr.provenance with
    | some id => .ok ⟨id, ptr.offset, ()⟩
    | none => .error ptr.offset.bytes

/-- Canary world: a live 4-byte allocation `1`, a tombstone `2`, and a
function global `3`. -/
def canaryLinearWorld : LinearAllocWorld :=
  { nextAllocId := 4
    issued := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
    globals := [(⟨3, by decide⟩, ⟨.function, 0, 0, .not, []⟩)]
    live := [(⟨1, by decide⟩, ⟨4, 2, .heap, .mut, []⟩)]
    dead := [(⟨2, by decide⟩, ⟨4, 2⟩)] }

/-- Identifier bijection witnesses: `1`, the full-width maximum, and the
rejected `0` sentinel on both sides. -/
theorem allocId_canary :
    ofMiriAllocId ⟨1, by decide⟩ = MiriAllocId.one ∧
    toMiriAllocId MiriAllocId.maxValue = ⟨UInt64.ofNat (2 ^ 64 - 1), by decide⟩ ∧
    (ofMiriAllocId ⟨UInt64.ofNat (2 ^ 64 - 1), by decide⟩).toTrustedAllocId = 2 ^ 64 - 1 ∧
    Miri.Memory.AllocId.ofUInt64 0 = none ∧
    MiriAllocId.ofUInt64 0 = none := by
  refine ⟨rfl, rfl, by decide, by decide, by decide⟩

/-- Vendored `check_ptr_access` on the canary world, with the theory verdicts:
in-bounds success, the zero-size fast path through a tombstone, use-after-free,
unavailable metadata, a provenance-free null address, the `isize::MAX` gate
(checked before everything else), out-of-bounds, and a `0`-byte function
global. -/
theorem checkPtrAccess_canary :
    let target : Miri.Memory.PointerArithmetic := ⟨⟨8⟩⟩
    let msg := Miri.Memory.CheckInAllocMsg.memoryAccess
    let lookup := linearLookup canaryLinearWorld
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let id2 : Miri.Memory.AllocId := ⟨2, by decide⟩
    let id3 : Miri.Memory.AllocId := ⟨3, by decide⟩
    let id9 : Miri.Memory.AllocId := ⟨9, by decide⟩
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, some id1⟩ ⟨4⟩ msg canaryResolve lookup = .ok () ∧
    canaryLinearWorld.checkPtrAccess (some (ofMiriAllocId id1, 0)) 4 = true ∧
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, some id2⟩ ⟨0⟩ msg canaryResolve lookup = .ok () ∧
    canaryLinearWorld.checkPtrAccess (some (ofMiriAllocId id2, 0)) 0 = true ∧
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, some id2⟩ ⟨1⟩ msg canaryResolve lookup =
      .error (.allocationLookup (.deadAllocation id2)) ∧
    canaryLinearWorld.checkPtrAccess (some (ofMiriAllocId id2, 0)) 1 = false ∧
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, some id9⟩ ⟨1⟩ msg canaryResolve lookup =
      .error (.allocationLookup (.unavailable id9)) ∧
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, none⟩ ⟨4⟩ msg canaryResolve lookup =
      .error (.danglingIntegerPointer 0 4 msg) ∧
    canaryLinearWorld.checkPtrAccess none 4 = false ∧
    Miri.Memory.checkPtrAccess target ⟨⟨0⟩, none⟩ ⟨9223372036854775808⟩ msg canaryResolve lookup =
      .error (.sizeDoesNotFitI64 ⟨9223372036854775808⟩) ∧
    (Miri.Memory.checkPtrAccess target ⟨⟨1⟩, some id1⟩ ⟨4⟩ msg canaryResolve lookup).isOk =
      false ∧
    canaryLinearWorld.checkPtrAccess (some (ofMiriAllocId id1, 1)) 4 = false ∧
    (Miri.Memory.checkPtrAccess target ⟨⟨0⟩, some id3⟩ ⟨1⟩ msg canaryResolve lookup).isOk =
      false ∧
    canaryLinearWorld.checkPtrAccess (some (ofMiriAllocId id3, 0)) 1 = false := by
  intro target msg lookup id1 id2 id3 id9
  refine ⟨by decide +kernel, by decide, by decide +kernel, by decide, by decide +kernel,
    by decide, by decide +kernel, by decide +kernel, by decide, by decide +kernel,
    by decide +kernel, by decide, by decide +kernel, by decide⟩

/-- The same vendored check against the KEYED canary world. -/
theorem checkPtrAccess_keyed_canary :
    Miri.Memory.checkPtrAccess ⟨⟨8⟩⟩ ⟨⟨0⟩, some ⟨1, by decide⟩⟩ ⟨4⟩ .memoryAccess canaryResolve
        (keyedLookup (KeyedAllocWorld.ofLinear canaryLinearWorld)) = .ok () ∧
    Miri.Memory.checkPtrAccess ⟨⟨8⟩⟩ ⟨⟨0⟩, some ⟨2, by decide⟩⟩ ⟨1⟩ .memoryAccess canaryResolve
        (keyedLookup (KeyedAllocWorld.ofLinear canaryLinearWorld)) =
      .error (.allocationLookup (.deadAllocation ⟨2, by decide⟩)) := by
  rw [← linearLookup_eq_keyedLookup (allocWorldRel_ofLinear canaryLinearWorld)]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- Vendored `RetagPolicy.create` and theory `selectFnEntryPolicy` on concrete
inputs: writable `&mut`, `#[rustc_no_writable]` `&mut`, `!Unpin` `Box`, `Box`
weak protector, and shared `&` (frozen / cell). -/
theorem retagPolicy_canary :
    Miri.TreeBorrows.RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨true, false⟩ =
        some ⟨.Unique, .Unique, .ReservedFrz false, some .StrongProtector⟩ ∧
    selectFnEntryPolicy ⟨true, true, true⟩ .mutable ⟨true, false⟩ = .writableChildWrite ∧
    Miri.TreeBorrows.RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨true, true⟩ =
        some ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false,
          some .StrongProtector⟩ ∧
    selectFnEntryPolicy ⟨true, true, true⟩ .mutable ⟨true, true⟩ = .rustcNoWritable ∧
    Miri.TreeBorrows.RetagPolicy.create ⟨false, true, true⟩ .Box .FnEntry ⟨true, false⟩ = none ∧
    selectFnEntryPolicy ⟨false, true, true⟩ .box ⟨true, false⟩ = .skipRetag ∧
    Miri.TreeBorrows.RetagPolicy.create ⟨true, true, false⟩ .Box .FnEntry ⟨true, false⟩ =
        some ⟨.Unique, .Unique, .ReservedFrz false, some .WeakProtector⟩ ∧
    Miri.TreeBorrows.RetagPolicy.create ⟨true, true, false⟩ .Shared .FnEntry ⟨true, false⟩ =
        some ⟨.Frozen, .Cell, .Cell, some .StrongProtector⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Protector-end access kinds against the vendored `associatedAccess`:
accessed `.unique` writes, accessed `.frozen` reads, `.cell` and unaccessed
locations perform no access. -/
theorem protectorEnd_canary :
    protectorEndAccessIsWrite? ⟨1, none, .unique, 0, 4, some 7, true⟩ = some true ∧
    Miri.TreeBorrows.Permission.associatedAccess .Unique = some .Write ∧
    protectorEndAccessIsWrite? ⟨1, none, .frozen, 0, 4, some 7, true⟩ = some false ∧
    Miri.TreeBorrows.Permission.associatedAccess .Frozen = some .Read ∧
    protectorEndAccessIsWrite? ⟨1, none, .cell, 0, 4, some 7, true⟩ = none ∧
    Miri.TreeBorrows.Permission.associatedAccess .Cell = none ∧
    protectorEndAccessIsWrite? ⟨1, none, .unique, 0, 4, some 7, false⟩ = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary borrow tree: root `0`, children `1` and `2`, and grandchild `3`
below `1` (dense tags). -/
def canaryTreeNodes : List TreeTagNode :=
  [⟨0, none, .unique, 0, 4, none, true⟩,
   ⟨1, some 0, .reservedFrz false, 0, 4, none, true⟩,
   ⟨2, some 0, .reservedFrz false, 0, 4, none, true⟩,
   ⟨3, some 1, .reservedFrz false, 0, 4, none, true⟩]

/-- Vendored `TraversalTree.traverse` on the canary tree against the theory
schedule: an access through `1` visits `1`, `0` locally and then the foreign
nodes `3`, `2` in reverse-children postorder; skipping `3` prunes it. -/
theorem traversal_canary :
    let tree := traversalTreeOfNodes canaryTreeNodes
    let w : FnEntryBorrowWorld := ⟨canaryTreeNodes, [], 4, 0, true, false⟩
    (Miri.TreeBorrows.Tree.TraversalTree.traverse tree 1 .VisitChildrenOfAccessed []).2 =
      [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨3, .ForeignAccess⟩, ⟨2, .ForeignAccess⟩] ∧
    ancestorPathTags canaryTreeNodes 1 = [1, 0] ∧
    (foreignVisitScheduleNodes (childTagsInListOrder canaryTreeNodes) w 1 true 0 4).map
      (·.tag) = [3, 2] ∧
    (Miri.TreeBorrows.Tree.TraversalTree.traverse tree 1 .VisitChildrenOfAccessed [3]).2 =
      [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩] ∧
    (Miri.TreeBorrows.Tree.TraversalTree.traverse tree 3 .VisitChildrenOfAccessed []).2 =
      [⟨3, .LocalAccess⟩, ⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩] := by
  intro tree w
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Canary existential table: `0` principal-less `dyn Send`, `1` principal-less
`dyn Send + Sync`, `2` `dyn Trait7 + Send`, `3` `dyn Trait7`, `4` `dyn Trait8`. -/
def canarySpecTable : Nat → DynExistentialSpec
  | 0 => ⟨none, AutoTraitSet.empty, [⟨100, 100, true⟩]⟩
  | 1 => ⟨none, AutoTraitSet.empty, [⟨100, 100, true⟩, ⟨101, 101, true⟩]⟩
  | 2 => ⟨some 7, AutoTraitSet.empty, [⟨100, 100, true⟩]⟩
  | 3 => ⟨some 7, AutoTraitSet.empty, []⟩
  | _ => ⟨some 8, AutoTraitSet.empty, []⟩

/-- Vendored `VTable.checkForTypeRead` against the theory's
`vtableMatchesExpectedSpec`: auto traits are ignored (also on principal-less
vtables), a principal never matches a principal-less vtable, and distinct
principals are rejected with `InvalidVTableTrait`. -/
theorem vtableTrait_canary :
    miriVTableTraitCheckOk canarySpecTable 0 1 = true ∧
    vtableMatchesExpectedSpec (canarySpecTable 0) (canarySpecTable 1) = true ∧
    miriVTableTraitCheckOk canarySpecTable 2 3 = true ∧
    vtableMatchesExpectedSpec (canarySpecTable 2) (canarySpecTable 3) = true ∧
    miriVTableTraitCheckOk canarySpecTable 3 0 = false ∧
    vtableMatchesExpectedSpec (canarySpecTable 3) (canarySpecTable 0) = false ∧
    miriVTableTraitCheckOk canarySpecTable 0 3 = false ∧
    vtableMatchesExpectedSpec (canarySpecTable 0) (canarySpecTable 3) = false ∧
    miriVTableTraitCheckOk canarySpecTable 3 4 = false ∧
    vtableMatchesExpectedSpec (canarySpecTable 3) (canarySpecTable 4) = false ∧
    Miri.Interpreter.VTable.checkForTypeRead (specReadHooks Unit canarySpecTable) () 3 4 () =
      .error (.undefinedBehavior "InvalidVTableTrait") () := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, rfl⟩

/-- Failure classes of the vendored safe-pointer access stage on concrete
errors: a provenance-free pointer, use-after-free, and out-of-bounds are UB;
the size gate and unavailable metadata are not. -/
theorem accessClassification_canary :
    let path : Miri.Memory.ValidationPath := ⟨"T", #[]⟩
    let kind : Miri.Memory.SafePointerKind := .reference false
    let id : Miri.Memory.AllocId := ⟨2, by decide⟩
    isUndefinedBehavior (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
      (.danglingIntegerPointer 0 4 .memoryAccess)) = true ∧
    isUndefinedBehavior (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
      (.allocationLookup (.deadAllocation id))) = true ∧
    isUndefinedBehavior (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
      (.pointerOutOfBounds id ⟨4⟩ 1 4 .memoryAccess)) = true ∧
    isUndefinedBehavior (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
      (.sizeDoesNotFitI64 ⟨9223372036854775808⟩)) = false ∧
    isUndefinedBehavior (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError path kind
      (.allocationLookup (.unavailable id))) = false := by
  intro path kind id
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Row permutation canary on vendored row types: swapping two live rows (and
the issued rows) changes the linear row order but leaves the keyed world
identical, and both rows stay live. -/
theorem rowsPermutation_canary :
    let proj : RowProjection Miri.Memory.Provenance Unit Unit :=
      ⟨fun _ => .heap, fun _ => [], fun _ => []⟩
    let id1 : Miri.Memory.AllocId := ⟨1, by decide⟩
    let id2 : Miri.Memory.AllocId := ⟨2, by decide⟩
    let la1 : Miri.Memory.LocalAllocation Miri.Memory.Provenance Unit Unit :=
      ⟨.stack, baseRetagAllocation⟩
    let la2 : Miri.Memory.LocalAllocation Miri.Memory.Provenance Unit Unit :=
      ⟨.machine (), baseRetagAllocation⟩
    let rows₁ : MiriAllocRows Miri.Memory.Provenance Unit Unit :=
      { nextAllocId := 3, issued := #[id1, id2], live := #[(id1, la1), (id2, la2)] }
    let rows₂ : MiriAllocRows Miri.Memory.Provenance Unit Unit :=
      { nextAllocId := 3, issued := #[id2, id1], live := #[(id2, la2), (id1, la1)] }
    rows₁.toKeyed proj = rows₂.toKeyed proj ∧
    (rows₁.toLinear proj).live.map Prod.fst ≠ (rows₂.toLinear proj).live.map Prod.fst ∧
    (rows₁.toKeyed proj).isAllocLive (ofMiriAllocId id2) = true ∧
    (rows₂.toKeyed proj).isAllocLive (ofMiriAllocId id2) = true ∧
    (rows₁.toKeyed proj).isAllocLive (ofMiriAllocId ⟨9, by decide⟩) = false := by
  intro proj id1 id2 la1 la2 rows₁ rows₂
  have hkeyed : rows₁.toKeyed proj = rows₂.toKeyed proj := by
    apply rows_toKeyed_eq_of_perm proj (rows₁ := rows₁) (rows₂ := rows₂) rfl rfl
    · exact List.Perm.swap id2 id1 []
    · exact List.Perm.refl _
    · exact List.nodup_nil
    · exact List.Perm.swap (id2, la2) (id1, la1) []
    · show [id1, id2].Nodup
      decide
    · exact List.Perm.refl _
    · exact List.nodup_nil
  refine ⟨hkeyed, ?_, ?_, ?_, ?_⟩
  · show [ofMiriAllocId id1, ofMiriAllocId id2] ≠ [ofMiriAllocId id2, ofMiriAllocId id1]
    decide
  · rw [toKeyed_isAllocLive]
    rfl
  · rw [toKeyed_isAllocLive]
    rfl
  · rw [toKeyed_isAllocLive]
    rfl

/-! ## Part 4. Axiom pins

### 4A. Every public theorem of this module: at most `propext` and `Quot.sound` -/

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ofMiriAllocId_value'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ofMiriAllocId_value

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toMiriAllocId_value'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms toMiriAllocId_value

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ofMiriAllocId_toMiriAllocId'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ofMiriAllocId_toMiriAllocId

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toMiriAllocId_ofMiriAllocId'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms toMiriAllocId_ofMiriAllocId

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ofMiriAllocId_injective'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ofMiriAllocId_injective

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toMiriAllocId_injective'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms toMiriAllocId_injective

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocId_bijection'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms allocId_bijection

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocId_ofUInt64_comm'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms allocId_ofUInt64_comm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miriAllocId_ofUInt64_comm'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miriAllocId_ofUInt64_comm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toTrustedAllocId_ofMiriAllocId'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms toTrustedAllocId_ofMiriAllocId

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toTrustedAllocId_ofMiriAllocId_pos'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms toTrustedAllocId_ofMiriAllocId_pos

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toTrustedAllocId_ofMiriAllocId_injective'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms toTrustedAllocId_ofMiriAllocId_injective

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ofMiriAllocId_beq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ofMiriAllocId_beq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toMiriAllocId_beq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toMiriAllocId_beq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.compare_ofMiriAllocId'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms compare_ofMiriAllocId

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.globalKindOfMiri_toMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms globalKindOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.globalKindToMiri_ofMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms globalKindToMiri_ofMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.mutabilityOfMiri_toMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms mutabilityOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.mutabilityToMiri_ofMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms mutabilityToMiri_ofMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.infoKindOfMiri_toMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms infoKindOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.infoKindOfMiri_eq_none_iff'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms infoKindOfMiri_eq_none_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.infoKindToMiri_beq_dead'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms infoKindToMiri_beq_dead

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocIdErrOfMiri_toMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms allocIdErrOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocIdErrToMiri_ofMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms allocIdErrToMiri_ofMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.globalRegErrOfMiri_toMiri'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms globalRegErrOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.deallocErrOfMiri_toMiri'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms deallocErrOfMiri_toMiri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.linearLookup_eq_keyedLookup'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearLookup_eq_keyedLookup

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.sizeAsI64_eq'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms sizeAsI64_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkAndDerefPtr_keyed_eq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkAndDerefPtr_keyed_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkPtrAccess_keyed_eq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkPtrAccess_keyed_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.getPtrAccess_keyed_eq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms getPtrAccess_keyed_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkPtrAccess_isOk_eq_keyed'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkPtrAccess_isOk_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkPtrAccess_isOk_eq_linear'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkPtrAccess_isOk_eq_linear

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ptrRel_resolvesAs'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ptrRel_resolvesAs

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ptrRel_checkPtrAccess_isOk_eq_keyed'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ptrRel_checkPtrAccess_isOk_eq_keyed

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocWorldRel_rows'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms allocWorldRel_rows

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocWorldRel_rows_iff'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms allocWorldRel_rows_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_findLive?'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_findLive?

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_findDead?'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_findDead?

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_findGlobal?'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_findGlobal?

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_hasIssued'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_hasIssued

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_isAllocLive'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_isAllocLive

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.toKeyed_getAllocInfo'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toKeyed_getAllocInfo

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.linearFind?_eq_of_perm'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearFind?_eq_of_perm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedOfLinear_eq_of_perm'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedOfLinear_eq_of_perm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.rows_toKeyed_eq_of_perm'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rows_toKeyed_eq_of_perm

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedRowsRel_iff'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedRowsRel_iff

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedRowsRel_perm_invariant'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedRowsRel_perm_invariant

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.mirror_create_eq_miri_create'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms mirror_create_eq_miri_create

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.classifyMiriFnEntry_map'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms classifyMiriFnEntry_map

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.selectFnEntryPolicy_eq_miri_create'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms selectFnEntryPolicy_eq_miri_create

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_create_fnEntry_mutOrBox_childPerms'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_create_fnEntry_mutOrBox_childPerms

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.protectorEndAccessIsWrite?_eq_miri_associatedAccess'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms protectorEndAccessIsWrite?_eq_miri_associatedAccess

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_foreignPostorder_eq'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_foreignPostorder_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_initialForeignRoots_go_eq'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_initialForeignRoots_go_eq

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_traverse_eq_schedule'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_traverse_eq_schedule

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.findNode?_eq_getElem?_of_denseTags'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms findNode?_eq_getElem?_of_denseTags

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.traversalParent_traversalTreeOfNodes'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms traversalParent_traversalTreeOfNodes

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ancestorPathTagsAux_eq_miri'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ancestorPathTagsAux_eq_miri

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.ancestorPathTags_eq_miri_ancestorPath'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ancestorPathTags_eq_miri_ancestorPath

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.classifyPointerAccessError_isUB'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms classifyPointerAccessError_isUB

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.keyedAccessOutcome_error_isUB_of_fit'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms keyedAccessOutcome_error_isUB_of_fit

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.sizeGate_failure_class_separation'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sizeGate_failure_class_separation

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_sortedPredicates_autoOnly'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_sortedPredicates_autoOnly

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.miri_checkForTypeRead_autoOnly_ok'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms miri_checkForTypeRead_autoOnly_ok

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.allocId_canary'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms allocId_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkPtrAccess_canary'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkPtrAccess_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.checkPtrAccess_keyed_canary'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkPtrAccess_keyed_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.retagPolicy_canary'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms retagPolicy_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.protectorEnd_canary'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms protectorEnd_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.traversal_canary'
does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms traversal_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.vtableTrait_canary'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms vtableTrait_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.accessClassification_canary'
depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms accessClassification_canary

/--
info: 'LeanMiriSpec.ExtTreeMapAllocLM.rowsPermutation_canary'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rowsPermutation_canary

/-! ### 4B. The obstruction: vendored constants that depend on `Classical.choice`

These pins are about VENDORED and pre-existing constants, not about theorems of
this module. They record why no statement of this module can mention the
vendored memory state, the machine-level validity visitor, the `LM-3.x` state
relations, or `BorrowTree.releaseProtector` (see the module documentation). -/

/--
info: 'Std.HashMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Std.HashMap

/--
info: 'Miri.Memory.KeyedArray'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Memory.KeyedArray

/--
info: 'Miri.Memory.MemoryState'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Memory.MemoryState

/--
info: 'Miri.Memory.MemoryState.reserveAllocId'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Memory.MemoryState.reserveAllocId

/--
info: 'Miri.Memory.MemoryState.getAllocInfo'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Memory.MemoryState.getAllocInfo

/--
info: 'Miri.Memory.MemoryLifecycle.deallocatePtrWith'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Memory.MemoryLifecycle.deallocatePtrWith

/--
info: 'Miri.Interpreter.AllocationMachine.deallocate'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Interpreter.AllocationMachine.deallocate

/--
info: 'LeanMiriSpec.Correspondence.StateRelLM3_1'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.StateRelLM3_1

/--
info: 'LeanMiriSpec.Correspondence.StateRelLM3_2'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.StateRelLM3_2

/--
info: 'LeanMiriSpec.Correspondence.annealValidityHooks'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LeanMiriSpec.Correspondence.annealValidityHooks

/--
info: 'Miri.Interpreter.ValidityMachine.scalarMayBeNull'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Interpreter.ValidityMachine.scalarMayBeNull

/--
info: 'Miri.Interpreter.ValidityVisitor.validatePlace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.Interpreter.ValidityVisitor.validatePlace

/--
info: 'Miri.TreeBorrows.BorrowTree.releaseProtector'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Miri.TreeBorrows.BorrowTree.releaseProtector

end LeanMiriSpec.ExtTreeMapAllocLM
